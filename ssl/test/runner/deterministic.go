// Copyright (c) 2016, Google Inc.
// SPDX-License-Identifier: ISC

package runner

import (
	"encoding/binary"

	"golang.org/x/crypto/chacha20"
)

// Use a different key from crypto/rand/deterministic.c.
var deterministicRandKey = []byte("runner deterministic key 0123456")

type deterministicRand struct {
	numCalls uint64
}

func (d *deterministicRand) Read(buf []byte) (int, error) {
	for i := range buf {
		buf[i] = 0
	}
	var nonce [12]byte
	binary.LittleEndian.PutUint64(nonce[:8], d.numCalls)
	cipher, err := chacha20.NewUnauthenticatedCipher(deterministicRandKey, nonce[:])
	if err != nil {
		return 0, err
	}
	cipher.XORKeyStream(buf, buf)
	d.numCalls++
	return len(buf), nil
}
