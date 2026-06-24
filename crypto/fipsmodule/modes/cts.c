// Copyright (c) 2008-2016 The OpenSSL Project. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <string.h>

#include <openssl/modes.h>

#include "internal.h"
#include "../../internal.h"

// AES Ciphertext Stealing (CTS), CS1 / RFC 2040 variant.
//
// CTS extends CBC mode to handle inputs whose length is not a multiple of the
// block size, without padding. This file implements the CS1 convention used by
// OpenSSL's legacy |CRYPTO_cts128_encrypt|/|CRYPTO_cts128_decrypt| API (the
// shape MIT krb5 1.x calls into for |aes128-cts-hmac-*| and friends): the last
// two ciphertext blocks are unconditionally swapped, and an exact-block-length
// input is treated as a 16-byte residue rather than zero residue. (The NIST
// CS2 / CS3 conventions are intentionally not provided here.)
//
// All four entry points return zero if |len| <= 16 (CTS requires at least one
// full block of input plus a partial block; for exact-length inputs callers
// should use plain CBC). On success they return the number of bytes written,
// which equals |len|.

size_t CRYPTO_cts128_encrypt(const uint8_t *in, uint8_t *out, size_t len,
                             const AES_KEY *key, uint8_t ivec[16],
                             cbc128_f cbc) {
  size_t residue = 0;
  alignas(16) uint8_t tmp[16];

  if (len <= 16) {
    return 0;
  }

  if ((residue = len % 16) == 0) {
    residue = 16;
  }
  len -= residue;

  (*cbc)(in, out, len, key, ivec, 1 /* enc */);

  in += len;
  out += len;

  // We don't assume |cbc| handles truncated I/O. Build up a 16-byte buffer
  // containing the |residue| plaintext bytes (zero-padded), CBC-encrypt it,
  // then perform the CTS swap.
  OPENSSL_memset(tmp, 0, sizeof(tmp));
  OPENSSL_memcpy(tmp, in, residue);
  OPENSSL_memcpy(out, out - 16, residue);
  (*cbc)(tmp, out - 16, 16, key, ivec, 1 /* enc */);

  return len + residue;
}

size_t CRYPTO_cts128_decrypt(const uint8_t *in, uint8_t *out, size_t len,
                             const AES_KEY *key, uint8_t ivec[16],
                             cbc128_f cbc) {
  size_t residue = 0;
  alignas(16) uint8_t tmp[32];

  if (len <= 16) {
    return 0;
  }

  if ((residue = len % 16) == 0) {
    residue = 16;
  }
  len -= 16 + residue;

  if (len) {
    (*cbc)(in, out, len, key, ivec, 0 /* dec */);
    in += len;
    out += len;
  }

  // Decrypt the second-to-last (swapped) ciphertext block in-place into
  // |tmp[0..15]| using a scratch IV at |tmp[16..31]|, so the running |ivec|
  // is preserved for the final XOR step below.
  OPENSSL_memset(tmp, 0, sizeof(tmp));
  (*cbc)(in, tmp, 16, key, tmp + 16, 0 /* dec */);

  // Reconstruct the full last-but-one ciphertext block by overlaying the
  // |residue| stolen ciphertext bytes from the final block. Then decrypt
  // both blocks with the original |ivec|.
  OPENSSL_memcpy(tmp, in + 16, residue);
  (*cbc)(tmp, tmp, 32, key, ivec, 0 /* dec */);
  OPENSSL_memcpy(out, tmp, 16 + residue);

  return 16 + len + residue;
}
