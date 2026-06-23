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

size_t CRYPTO_cts128_encrypt_block(const uint8_t *in, uint8_t *out, size_t len,
                                   const AES_KEY *key, uint8_t ivec[16],
                                   block128_f block) {
  size_t residue, n;

  if (len <= 16) {
    return 0;
  }

  if ((residue = len % 16) == 0) {
    residue = 16;
  }
  len -= residue;

  CRYPTO_cbc128_encrypt(in, out, len, key, ivec, block);

  in += len;
  out += len;

  for (n = 0; n < residue; ++n) {
    ivec[n] ^= in[n];
  }
  (*block)(ivec, ivec, key);
  // Swap the last two output blocks: the just-encrypted residue-sized block
  // moves into the |out - 16| slot, and the previous full ciphertext block
  // (currently at |out - 16|) is truncated to |residue| bytes at |out|.
  OPENSSL_memcpy(out, out - 16, residue);
  OPENSSL_memcpy(out - 16, ivec, 16);

  return len + residue;
}

size_t CRYPTO_cts128_encrypt(const uint8_t *in, uint8_t *out, size_t len,
                             const AES_KEY *key, uint8_t ivec[16],
                             cbc128_f cbc) {
  size_t residue;
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

size_t CRYPTO_cts128_decrypt_block(const uint8_t *in, uint8_t *out, size_t len,
                                   const AES_KEY *key, uint8_t ivec[16],
                                   block128_f block) {
  size_t residue, n;
  alignas(16) uint8_t tmp[32];

  if (len <= 16) {
    return 0;
  }

  if ((residue = len % 16) == 0) {
    residue = 16;
  }
  len -= 16 + residue;

  if (len) {
    CRYPTO_cbc128_decrypt(in, out, len, key, ivec, block);
    in += len;
    out += len;
  }

  // Decrypt the swapped second-to-last ciphertext block (which holds the
  // last full encryption output) into |tmp[16..31]|. Then form |tmp[0..15]|
  // by overlaying the |residue| ciphertext bytes from the final stolen
  // block on top of the just-decrypted block, and decrypt that.
  (*block)(in, tmp + 16, key);

  OPENSSL_memcpy(tmp, tmp + 16, 16);
  OPENSSL_memcpy(tmp, in + 16, residue);
  (*block)(tmp, tmp, key);

  // CBC-style XOR with the running IV for the last full-block of plaintext;
  // update |ivec| to the last full ciphertext block as we go.
  for (n = 0; n < 16; ++n) {
    uint8_t c = in[n];
    out[n] = tmp[n] ^ ivec[n];
    ivec[n] = c;
  }
  // Recover the |residue| trailing plaintext bytes by XOR-ing the
  // (post-decryption) tmp tail with the corresponding ciphertext.
  for (residue += 16; n < residue; ++n) {
    out[n] = tmp[n] ^ in[n];
  }

  return 16 + len + residue;
}

size_t CRYPTO_cts128_decrypt(const uint8_t *in, uint8_t *out, size_t len,
                             const AES_KEY *key, uint8_t ivec[16],
                             cbc128_f cbc) {
  size_t residue;
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
