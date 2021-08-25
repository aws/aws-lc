// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// This script is used to generate the ECDH test vectors for secp256k1 curve.

package main

import (
	"crypto/sha256"
	"math/big"
	"strconv"
	"fmt"
)

import "github.com/ethereum/go-ethereum/crypto/secp256k1"

// Number of test vectors to be generated
const numOfTests = 25

// Initialize the counter used for generating pseudo-random numbers
// using the SHA-256 hash function.
var prng_ctr = 1

func printPadded(key string, n, max *big.Int) {
	padded := make([]byte, len(max.Bytes()))
	b := n.Bytes()
	copy(padded[len(padded)-len(b):], b)
	fmt.Printf("%s = %x\n", key, padded)
}

func genRandModN(N *big.Int) *big.Int {
	res := new(big.Int)
	for {
		dgst := sha256.Sum256([]byte("Dummy string" + strconv.Itoa(prng_ctr)))
		prng_ctr++
		res.SetBytes(dgst[:])
		if res.Cmp(N) == -1 {
			break
		}
	}
	return res
}

func main() {

	curve := secp256k1.S256()

	for i := 0; i < numOfTests; i++ {
		// Generate a private key for Alice and for Bob
		sA := genRandModN(curve.Params().P)
		sB := genRandModN(curve.Params().P)

		// Compute the corresponding public key
		xA, yA := curve.ScalarBaseMult(sA.Bytes())
		xB, yB := curve.ScalarBaseMult(sB.Bytes())

		// Compute shared keys zA and zB for Alice and Bob
		zA, _ := curve.ScalarMult(xB, yB, sA.Bytes())
		zB, _ := curve.ScalarMult(xA, yA, sB.Bytes())

		if zA.Cmp(zB) != 0 {
			fmt.Printf("Error, shared secret keys for Alice and Bob are different!")
			return
		}

		// Print all the required values
		fmt.Printf("Curve = secp256k1\n")
		printPadded("Private", sA, curve.Params().P)
		printPadded("X", xA, curve.Params().P)
		printPadded("Y", yA, curve.Params().P)
		printPadded("PeerX", xB, curve.Params().P)
		printPadded("PeerY", yB, curve.Params().P)
		printPadded("Z", zA, curve.Params().P)
		fmt.Printf("\n")
	}
}
