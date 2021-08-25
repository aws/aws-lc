/* Copyright (c) 2018, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

package main

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/sha512"
	"math/big"
	mathrand "math/rand"
	"hash"
	"fmt"
	"io"
	"os"
)

// secp256k1 curve is not available in crypto/elliptic module,
// so we use the implementation from the module listed below.
import "github.com/ethereum/go-ethereum/crypto/secp256k1"

// START - Deterministic RNG helper functions.
type deterministicRandom struct {
	stream cipher.Stream
}

func newDeterministicRand() io.Reader {
	block, err := aes.NewCipher(make([]byte, 128/8))
	if err != nil {
		panic(err)
	}
	stream := cipher.NewCTR(block, make([]byte, block.BlockSize()))
	return &deterministicRandom{stream}
}

func (r *deterministicRandom) Read(b []byte) (n int, err error) {
	for i := range b {
		b[i] = 0
	}
	r.stream.XORKeyStream(b, b)
	return len(b), nil
}

var deterministicRand io.Reader

// END - Deterministic RNG helper functions.

// Print big integer (hex representation) left padded with zeros
// according to the max argument.
func printPadded(key string, n, max *big.Int) {
	padded := make([]byte, len(max.Bytes()))
	b := n.Bytes()
	copy(padded[len(padded)-len(b):], b)
	fmt.Printf("%s = %x\n", key, padded)
}

func randNonZeroInt(max *big.Int) *big.Int {
	for {
		r, err := rand.Int(deterministicRand, max)
		if err != nil {
			panic(err)
		}
		if r.Sign() != 0 {
			return r
		}
	}
}

// Generate a random curve point
func randPoint(curve elliptic.Curve) (x, y *big.Int) {
	k := randNonZeroInt(curve.Params().N)
	return curve.ScalarBaseMult(k.Bytes())
}

// This function is copied from ecdsa module because
// it is not exported by the module but we need it here.
func hashToInt(hash []byte, c elliptic.Curve) *big.Int {
	orderBits := c.Params().N.BitLen()
	orderBytes := (orderBits + 7) / 8
	if len(hash) > orderBytes {
		hash = hash[:orderBytes]
	}

	ret := new(big.Int).SetBytes(hash)
	excess := len(hash)*8 - orderBits
	if excess > 0 {
		ret.Rsh(ret, uint(excess))
	}
	return ret
}

// Helper function needed for generating the ECDSA Sign/Verify test vectors.
// We don't use the Sign function from the ecdsa module because:
//  1) it is not deterministic (even when provided with a deterministic RNG).
//  2) we need to know the chosen nonce k to generate signing test vectors.
// This function implements ECDSA signing of a message digest dgst with
// private key priv and nonce k.
func signWithGivenK(priv *ecdsa.PrivateKey, dgst []byte, k *big.Int) (r, s *big.Int) {

	// Group order of the curve
	N := priv.Curve.Params().N

	r, _ = priv.Curve.ScalarBaseMult(k.Bytes())
	r.Mod(r, N)

	// Compute the inverse of K modulo N
	kInv := new(big.Int).ModInverse(k, N)

	e := hashToInt(dgst, priv.Curve)
	s = new(big.Int).Mul(priv.D, r)
	s.Add(s, e)
	s.Mul(s, kInv)
	s.Mod(s, N)

	return
}

const numTestsPerHash = 15

// Generate and print test vectors for ECDSA Verify test
// for the given curve and hash function.
func printVerifyTestVectors(curve elliptic.Curve, curveName string, hash hash.Hash) {

	for i := 0; i < numTestsPerHash; i++ {
		// Generate a random private key
		priv, _ := ecdsa.GenerateKey(curve, deterministicRand)

		// Generate random nonce to be used for signing
		k := randNonZeroInt(curve.Params().N)

		// Generate 1024 bits long random message
		msg := make([]byte, 128)
		deterministicRand.Read(msg)

		// Compute the digest of the message
		hash.Reset()
		hash.Write(msg)
		dgst := hash.Sum(nil)

		// Sign the digest with ECDSA
		r, s := signWithGivenK(priv, dgst, k)

		// Randomly choose one of the following events:
		//   0 - valid signature
		//   1 - invalid (digest changed)
		//   2 - invalid (R changed)
		//   3 - invalid (S changed)
		//   4 - invalid (public key changed)
		// math/rand is already deterministic as per the docs.
		event := mathrand.Intn(5)

		// Constant used for invalidating the data
		one := new(big.Int).SetUint64(1)

		// x and y coordinates of the public key to be printed
		xOut, yOut := priv.PublicKey.X, priv.PublicKey.Y

		switch event {
			case 1:
				dgst[0] ^= 1 // Invalidate the digest
			case 2:
				r.Xor(r, one) // Invalidate R
			case 3:
				s.Xor(s, one) // Invalidate S
			case 4:
				xOut, yOut = randPoint(curve) // Invalidate the public key
		}

		// Print out the test vector
		fmt.Printf("\nCurve = %s\n", curveName)
		printPadded("X", xOut, curve.Params().P)
		printPadded("Y", yOut, curve.Params().P)
		fmt.Printf("Digest = %x\n", dgst)
		printPadded("R", r, curve.Params().P)
		printPadded("S", s, curve.Params().P)
		if event != 0 {
			fmt.Printf("Invalid =\n")
		}
	}
}

// Generate and print test vectors for ECDSA Sign test
// for the given curve and hash function.
func printSignTestVectors(curve elliptic.Curve, curveName string, hash hash.Hash) {

	for i := 0; i < numTestsPerHash; i++ {
		// Generate a random private key
		priv, _ := ecdsa.GenerateKey(curve, deterministicRand)

		// Generate random nonce to be used for signing
		k := randNonZeroInt(curve.Params().N)

		// Generate 1024 bits long random message
		msg := make([]byte, 128)
		deterministicRand.Read(msg)

		// Compute the digest of the message
		hash.Reset()
		hash.Write(msg)
		dgst := hash.Sum(nil)

		r, s := signWithGivenK(priv, dgst, k)

		// Print out the test vector
		fmt.Printf("\nCurve = %s\n", curveName)
		printPadded("Private", priv.D, curve.Params().P)
		printPadded("X", priv.PublicKey.X, curve.Params().P)
		printPadded("Y", priv.PublicKey.Y, curve.Params().P)
		fmt.Printf("Digest = %x\n", dgst)
		printPadded("K", k, curve.Params().P)
		printPadded("R", r, curve.Params().P)
		printPadded("S", s, curve.Params().P)
	}
}

// P-192 curve is not available in the crypto/elliptic module
// so we instantiate it here ourselves. This works because P-192
// has the 'a' constant a = -3 as assumed by the module.
var P192 *elliptic.CurveParams

func initP192() {
	// See FIPS 186-3, section D.2.2
	P192 = &elliptic.CurveParams{Name: "P-192"}
	P192.P, _ = new(big.Int).SetString("6277101735386680763835789423207666416083908700390324961279", 10)
	P192.N, _ = new(big.Int).SetString("6277101735386680763835789423176059013767194773182842284081", 10)
	P192.B, _ = new(big.Int).SetString("2455155546008943817740293915197451784769108058161191238065", 10)
	P192.Gx, _ = new(big.Int).SetString("188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012", 16)
	P192.Gy, _ = new(big.Int).SetString("07192b95ffc8da78631011ed6b24cdd573f977a11e794811", 16)
	P192.BitSize = 192
}

func main() {

	if len(os.Args) != 2 {
		fmt.Printf("Missing command line argument: specify 0 for Verify; anything else for Sign test vectors.")
		return
	}

	deterministicRand = newDeterministicRand()

	// Initialize the curves
	S256 := secp256k1.S256()
	initP192()

	// Initialize the hash functions
	hashFuncs := []hash.Hash {sha1.New(), sha256.New224(), sha256.New(), sha512.New384(), sha512.New()}

	if os.Args[1] == "0" {

		for i := 0; i < len(hashFuncs); i++ {
			printVerifyTestVectors(S256, "secp256k1", hashFuncs[i])
		}

		for i := 0; i < len(hashFuncs); i++ {
			printVerifyTestVectors(P192, "P-192", hashFuncs[i])
		}
	} else {

		for i := 0; i < len(hashFuncs); i++ {
			printSignTestVectors(S256, "secp256k1", hashFuncs[i])
		}

		for i := 0; i < len(hashFuncs); i++ {
			printSignTestVectors(P192, "P-192", hashFuncs[i])
		}
	}
}
