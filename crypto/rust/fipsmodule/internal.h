// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_RUST_FIPSMODULE_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RUST_FIPSMODULE_INTERNAL_H

#include <openssl/sha.h>

#if defined(__cplusplus)
extern "C" {
#endif

// Rust builds put the Rust code under crypto/rust/fipsmodule in the FIPS
// module, beside bcm.c (cmake/cargo.cmake), and the module's C code calls it.
// libcrypto doesn't export these functions: static FIPS builds make them local
// to bcm.o, and other builds fold them in as hidden symbols of bcm-rust.o.

// In a BORINGSSL_PREFIX build the Rust functions carry the prefix (src/lib.rs),
// so C has to use the prefixed names too, whether or not the prefix headers'
// symbol list names them.
#if defined(BORINGSSL_PREFIX)
#define BCM_RUST_PREFIXED(name) BORINGSSL_ADD_PREFIX(BORINGSSL_PREFIX, name)
#undef bcm_rust_sha256_init
#define bcm_rust_sha256_init BCM_RUST_PREFIXED(bcm_rust_sha256_init)
#undef bcm_rust_sha256_update
#define bcm_rust_sha256_update BCM_RUST_PREFIXED(bcm_rust_sha256_update)
#undef bcm_rust_sha256_final
#define bcm_rust_sha256_final BCM_RUST_PREFIXED(bcm_rust_sha256_final)
#undef bcm_rust_sha256_block_data_order
#define bcm_rust_sha256_block_data_order \
  BCM_RUST_PREFIXED(bcm_rust_sha256_block_data_order)
#endif  // BORINGSSL_PREFIX

// SHA-256 and SHA-224, in src/sha256.rs. Each returns one on success and zero
// on a NULL pointer, or as described.

// bcm_rust_sha256_init sets |*ctx| up for a |md_len|-byte digest: SHA-224 for
// 28 and SHA-256 for 32. It returns zero for any other |md_len|.
int bcm_rust_sha256_init(SHA256_CTX *ctx, size_t md_len);

// bcm_rust_sha256_update adds the |len| bytes at |data| to |ctx|. |data| may
// be NULL if |len| is zero.
int bcm_rust_sha256_update(SHA256_CTX *ctx, const void *data, size_t len);

// bcm_rust_sha256_final finishes |ctx| and writes its |md_len|-byte digest to
// |out|. It returns zero, with |ctx| still finished, if |ctx| was set up for
// another digest length.
int bcm_rust_sha256_final(uint8_t *out, size_t md_len, SHA256_CTX *ctx);

// bcm_rust_sha256_block_data_order is the portable block function. It runs
// |num| blocks at |data| through |state|.
void bcm_rust_sha256_block_data_order(uint32_t state[8], const uint8_t *data,
                                      size_t num);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_RUST_FIPSMODULE_INTERNAL_H
