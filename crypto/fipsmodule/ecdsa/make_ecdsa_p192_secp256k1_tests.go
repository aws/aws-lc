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
)

import "github.com/ethereum/go-ethereum/crypto/secp256k1"

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

func randPoint(curve elliptic.Curve) (x, y *big.Int) {
	k := randNonZeroInt(curve.Params().N)
	return curve.ScalarBaseMult(k.Bytes())
}

// P-192 curve is not available in the crypto/elliptic module
// so we instantiate it her ourselves. This works because P-192
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

const numTestsPerHash = 15

func printVerifyTestVectors(curve elliptic.Curve, curveName string, hash hash.Hash) {

  for i := 0; i < numTestsPerHash; i++ {
    // Generate a random private key
    priv, _ := ecdsa.GenerateKey(curve, deterministicRand)

    // Generate 1024 bits long random message
    msg := make([]byte, 128)
    deterministicRand.Read(msg)

    // Compute the digest of the message
    hash.Reset()
    hash.Write(msg)
    dgst := hash.Sum(nil)

    // Sign the digest with ECDSA
    R, S, _ := ecdsa.Sign(rand.Reader, priv, dgst)

    // Randomly choose one of the following events:
    //   0 - valid signature
    //   1 - invalid (digest changed)
    //   2 - invalid (R changed)
    //   3 - invalid (S changed)
    //   4 - invalid (public key changed)
    event := mathrand.Intn(5)

    one := new(big.Int).SetUint64(1)
    // x and y coordinates of the public key to be printed
    xOut, yOut := priv.PublicKey.X, priv.PublicKey.Y
    switch event {
      case 1:
        dgst[0] ^= 1 // Invalidate the digest
      case 2:
        R = R.Xor(R, one) // Invalidate R
      case 3:
        S = S.Xor(S, one) // Invalidate S
      case 4:
        xOut, yOut = randPoint(curve) // Invalidate the public key
    }

    fmt.Printf("\nCurve = %s\n", curveName)
    printPadded("X", xOut, curve.Params().P)
    printPadded("Y", yOut, curve.Params().P)
    fmt.Printf("Digest = %x\n", dgst)
    printPadded("R", R, curve.Params().P)
    printPadded("S", S, curve.Params().P)
    if event != 0 {
      fmt.Printf("Invalid =\n")
    }
  }
}

var deterministicRand io.Reader

func main() {

  deterministicRand = newDeterministicRand()

  curve := secp256k1.S256()
  printVerifyTestVectors(curve, "secp256k1", sha1.New())
  printVerifyTestVectors(curve, "secp256k1", sha256.New224())
  printVerifyTestVectors(curve, "secp256k1", sha256.New())
  printVerifyTestVectors(curve, "secp256k1", sha512.New384())
  printVerifyTestVectors(curve, "secp256k1", sha512.New())

  initP192()
  printVerifyTestVectors(P192, "P-192", sha1.New())
  printVerifyTestVectors(P192, "P-192", sha256.New224())
  printVerifyTestVectors(P192, "P-192", sha256.New())
  printVerifyTestVectors(P192, "P-192", sha512.New384())
  printVerifyTestVectors(P192, "P-192", sha512.New())
}
