package configfile

import (
	"log"
	"math"
	"os"
	//
	//"golang.org/x/crypto/argon2"
	// "golang.org/x/crypto/scrypt"
	"encoding/binary"
	"sync"
//
//	"golang.org/x/crypto/blake2b"
	"crypto/rand"
	"crypto/subtle"
	"encoding/base64"
	"errors"
	"fmt"
	"runtime"
	"strconv"
	"strings"

	"golang.org/x/crypto/argon2"
	"golang.org/x/crypto/blake2b"

	"github.com/rfjakob/gocryptfs/internal/cryptocore"
	"github.com/rfjakob/gocryptfs/internal/exitcodes"
	"github.com/rfjakob/gocryptfs/internal/tlog"
)

const (
	// ScryptDefaultLogN is the default scrypt logN configuration parameter.
	// logN=16 (N=2^16) uses 64MB of memory and takes 4 seconds on my Atom Z3735F
	// netbook.
	// ScryptDefaultLogN = 16
	// From RFC7914, section 2:
	// At the current time, r=8 and p=1 appears to yield good
	// results, but as memory latency and CPU parallelism increase, it is
	// likely that the optimum values for both r and p will increase.
	// We reject all lower values that we might get through modified config files.
	saltLen = 8
	argon2KeyLen = 32 
	argon2Time = 1
	// logN=10 takes 6ms on a Pentium G630. This should be fast enough for all
	// purposes. We reject lower values.
	argon2Memory = 64 * 1024
	// We always generate 32-byte salts. Anything smaller than that is rejected.
	// scryptMinSaltLen = 32
)

// ScryptKDF is an instance of the scrypt key deriviation function.
// type ScryptKDF struct {
	// Salt is the random salt that is passed to scrypt
//	Salt []byte
	// N: scrypt CPU/Memory cost parameter
//	N int
	// R: scrypt block size parameter
//	R int
	// P: scrypt parallelization parameter
//	P int
	// KeyLen is the output data length
//	KeyLen int
// }

// NewScryptKDF returns a new instance of ScryptKDF.
func NewArgon2KDF(password, salt []byte, argon2Time, argon2Memory uint32, threads uint8, keyLen uint32) []byte {
	return deriveKey(argon2id, password, salt, nil, nil, argon2Time, argon2Memory, threads, keyLen)
}

// func NewScryptKDF(logN int) ScryptKDF {
//	var s ScryptKDF
//	s.Salt = cryptocore.RandBytes(cryptocore.KeyLen)
//	if logN <= 0 {
//		s.N = 1 << ScryptDefaultLogN
//	} else {
//		s.N = 1 << uint32(logN)
//	}
//	s.R = 8 // Always 8
//	s.P = 1 // Always 1
//	s.KeyLen = cryptocore.KeyLen
//	return s
// }

// DeriveKey returns a new key from a supplied password.

func deriveKey(mode int, password, salt, secret, data []byte, argon2Time, argon2Memory uint32, threads uint8, keyLen uint32) []byte {
	if argon2Time < 1 {
		panic("argon2: number of rounds too small")
	}
	if threads < 1 {
		panic("argon2: parallelism degree too low")
	}
	h0 := initHash(password, salt, secret, data, argon2Time, argon2Memory, uint32(threads), keyLen, mode)

	argon2Memory = argon2Memory / (syncPoints * uint32(threads)) * (syncPoints * uint32(threads))
	if argon2Memory < 2*syncPoints*uint32(threads) {
		argon2Memory = 2 * syncPoints * uint32(threads)
	}
	B := initBlocks(&h0, argon2Memory, uint32(threads))
	processBlocks(B, argon2Time, argon2Memory, uint32(threads), mode)
	return extractKey(B, argon2Memory, uint32(threads), keyLen)
}

const (
	blockLength = 128
	syncPoints  = 4
)

type block [blockLength]uint64

func initHash(password, salt, key, data []byte, argon2Time, argon2Memory, threads, keyLen uint32, mode int) [blake2b.Size + 8]byte {
	var (
		h0     [blake2b.Size + 8]byte
		params [24]byte
		tmp    [4]byte
	)

	b2, _ := blake2b.New512(nil)
	binary.LittleEndian.PutUint32(params[0:4], threads)
	binary.LittleEndian.PutUint32(params[4:8], keyLen)
	binary.LittleEndian.PutUint32(params[8:12], argon2Memory)
	binary.LittleEndian.PutUint32(params[12:16], argon2Time)
	binary.LittleEndian.PutUint32(params[16:20], uint32(Version))
	binary.LittleEndian.PutUint32(params[20:24], uint32(mode))
	b2.Write(params[:])
	binary.LittleEndian.PutUint32(tmp[:], uint32(len(password)))
	b2.Write(tmp[:])
	b2.Write(password)
	binary.LittleEndian.PutUint32(tmp[:], uint32(len(salt)))
	b2.Write(tmp[:])
	b2.Write(salt)
	binary.LittleEndian.PutUint32(tmp[:], uint32(len(key)))
	b2.Write(tmp[:])
	b2.Write(key)
	binary.LittleEndian.PutUint32(tmp[:], uint32(len(data)))
	b2.Write(tmp[:])
	b2.Write(data)
	b2.Sum(h0[:0])
	return h0
}

func initBlocks(h0 *[blake2b.Size + 8]byte, argon2Memory, threads uint32) []block {
	var block0 [1024]byte
	B := make([]block, argon2Memory)
	for lane := uint32(0); lane < threads; lane++ {
		j := lane * (argon2Memory / threads)
		binary.LittleEndian.PutUint32(h0[blake2b.Size+4:], lane)

		binary.LittleEndian.PutUint32(h0[blake2b.Size:], 0)
		blake2bHash(block0[:], h0[:])
		for i := range B[j+0] {
			B[j+0][i] = binary.LittleEndian.Uint64(block0[i*8:])
		}

		binary.LittleEndian.PutUint32(h0[blake2b.Size:], 1)
		blake2bHash(block0[:], h0[:])
		for i := range B[j+1] {
			B[j+1][i] = binary.LittleEndian.Uint64(block0[i*8:])
		}
	}
	return B
}

func processBlocks(B []block, argon2Time, argon2Memory, threads uint32, mode int) {
	lanes := argon2Memory / threads
	segments := lanes / syncPoints

	processSegment := func(n, slice, lane uint32, wg *sync.WaitGroup) {
		var addresses, in, zero block
		if mode == argon2i || (mode == argon2id && n == 0 && slice < syncPoints/2) {
			in[0] = uint64(n)
			in[1] = uint64(lane)
			in[2] = uint64(slice)
			in[3] = uint64(argon2Memory)
			in[4] = uint64(argon2Time)
			in[5] = uint64(mode)
		}

		index := uint32(0)
		if n == 0 && slice == 0 {
			index = 2 // we have already generated the first two blocks
			if mode == argon2i || mode == argon2id {
				in[6]++
				processBlock(&addresses, &in, &zero)
				processBlock(&addresses, &addresses, &zero)
			}
		}

		offset := lane*lanes + slice*segments + index
		var random uint64
		for index < segments {
			prev := offset - 1
			if index == 0 && slice == 0 {
				prev += lanes // last block in lane
			}
			if mode == argon2i || (mode == argon2id && n == 0 && slice < syncPoints/2) {
				if index%blockLength == 0 {
					in[6]++
					processBlock(&addresses, &in, &zero)
					processBlock(&addresses, &addresses, &zero)
				}
				random = addresses[index%blockLength]
			} else {
				random = B[prev][0]
			}
			newOffset := indexAlpha(random, lanes, segments, threads, n, slice, lane, index)
			processBlockXOR(&B[offset], &B[prev], &B[newOffset])
			index, offset = index+1, offset+1
		}
		wg.Done()
	}

	for n := uint32(0); n < argon2Time; n++ {
		for slice := uint32(0); slice < syncPoints; slice++ {
			var wg sync.WaitGroup
			for lane := uint32(0); lane < threads; lane++ {
				wg.Add(1)
				go processSegment(n, slice, lane, &wg)
			}
			wg.Wait()
		}
	}

}

func extractKey(B []block, argon2Memory, threads, keyLen uint32) []byte {
	lanes := argon2Memory / threads
	for lane := uint32(0); lane < threads-1; lane++ {
		for i, v := range B[(lane*lanes)+lanes-1] {
			B[argon2Memory-1][i] ^= v
		}
	}

	var block [1024]byte
	for i, v := range B[argon2Memory-1] {
		binary.LittleEndian.PutUint64(block[i*8:], v)
	}
	key := make([]byte, keyLen)
	blake2bHash(key, block[:])
	return key
}

func indexAlpha(rand uint64, lanes, segments, threads, n, slice, lane, index uint32) uint32 {
	refLane := uint32(rand>>32) % threads
	if n == 0 && slice == 0 {
		refLane = lane
	}
	m, s := 3*segments, ((slice+1)%syncPoints)*segments
	if lane == refLane {
		m += index
	}
	if n == 0 {
		m, s = slice*segments, 0
		if slice == 0 || lane == refLane {
			m += index
		}
	}
	if index == 0 || lane == refLane {
		m--
	}
	return phi(rand, uint64(m), uint64(s), refLane, lanes)
}

func phi(rand, m, s uint64, lane, lanes uint32) uint32 {
	p := rand & 0xFFFFFFFF
	p = (p * p) >> 32
	p = (p * m) >> 32
	return lane*lanes + uint32((s+m-(p+1))%uint64(lanes))
}
