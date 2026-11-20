// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_RUST_FIPSMODULE_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RUST_FIPSMODULE_INTERNAL_H

#include <openssl/sha.h>

#if defined(__cplusplus)
extern "C" {
#endif

// Rust builds link the Rust code under crypto/rust/fipsmodule into libcrypto
// as bcm-rust.o. The fold (cmake/cargo.cmake) hides the Rust functions, so
// libcrypto doesn't export them. crypto/rust/sha256.c defines the public C
// functions as calls to them.

// In a BORINGSSL_PREFIX build the Rust functions always carry the prefix
// (src/lib.rs), so C has to use the prefixed names too, whether or not the
// prefix headers' symbol list names them.
#if defined(BORINGSSL_PREFIX)
#define BCM_RUST_PREFIXED(name) BORINGSSL_ADD_PREFIX(BORINGSSL_PREFIX, name)
#undef bcm_rust_sha256_init
#define bcm_rust_sha256_init BCM_RUST_PREFIXED(bcm_rust_sha256_init)
#undef bcm_rust_sha256_init_from_state
#define bcm_rust_sha256_init_from_state \
  BCM_RUST_PREFIXED(bcm_rust_sha256_init_from_state)
#undef bcm_rust_sha256_update
#define bcm_rust_sha256_update BCM_RUST_PREFIXED(bcm_rust_sha256_update)
#undef bcm_rust_sha256_final
#define bcm_rust_sha256_final BCM_RUST_PREFIXED(bcm_rust_sha256_final)
#undef bcm_rust_sha256
#define bcm_rust_sha256 BCM_RUST_PREFIXED(bcm_rust_sha256)
#undef bcm_rust_sha256_transform_blocks
#define bcm_rust_sha256_transform_blocks \
  BCM_RUST_PREFIXED(bcm_rust_sha256_transform_blocks)
#undef bcm_rust_sha256_get_state
#define bcm_rust_sha256_get_state BCM_RUST_PREFIXED(bcm_rust_sha256_get_state)
#endif  // BORINGSSL_PREFIX

// SHA-224 and SHA-256, in src/sha256.rs. |md_len| is 28 for SHA-224 and 32
// for SHA-256, and a chaining value |h| is 32 bytes. Each function that
// returns int returns one on success and zero on a NULL pointer, or as
// described.

// bcm_rust_sha256_init sets |*ctx| up for a |md_len|-byte digest. It returns
// zero for any other |md_len|.
int bcm_rust_sha256_init(SHA256_CTX *ctx, size_t md_len);

// bcm_rust_sha256_init_from_state sets |*ctx| up for a |md_len|-byte digest
// that continues from the big-endian chaining value |h| after |n| bits. It
// returns zero if |n| isn't a multiple of the block size.
int bcm_rust_sha256_init_from_state(SHA256_CTX *ctx, size_t md_len,
                                    const uint8_t *h, uint64_t n);

// bcm_rust_sha256_update adds the |len| bytes at |data| to |ctx|. |data| may
// be NULL if |len| is zero.
int bcm_rust_sha256_update(SHA256_CTX *ctx, const void *data, size_t len);

// bcm_rust_sha256_final finishes |ctx| and writes its |md_len|-byte digest to
// |out|. It returns zero, with |ctx| still finished, if |ctx| was set up for
// another digest length.
int bcm_rust_sha256_final(uint8_t *out, size_t md_len, SHA256_CTX *ctx);

// bcm_rust_sha256 writes the |md_len|-byte digest of the |len| bytes at |data|
// to |out|.
int bcm_rust_sha256(const uint8_t *data, size_t len, uint8_t *out,
                    size_t md_len);

// bcm_rust_sha256_transform_blocks runs |num| blocks at |data| through
// |state|.
void bcm_rust_sha256_transform_blocks(uint32_t state[8], const uint8_t *data,
                                      size_t num);

// bcm_rust_sha256_get_state writes |ctx|'s big-endian chaining value to
// |out_h| and the number of bits hashed to |*out_n|. It returns zero if |ctx|
// holds a partial block.
int bcm_rust_sha256_get_state(const SHA256_CTX *ctx, uint8_t *out_h,
                              uint64_t *out_n);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_RUST_FIPSMODULE_INTERNAL_H
