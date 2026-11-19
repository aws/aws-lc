// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_RUST_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RUST_INTERNAL_H

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

// -DENABLE_RUST=ON links the Rust code under crypto/rust into libcrypto. The
// Rust symbols themselves are not exported from libcrypto; C code wraps them.

// CRYPTO_rust_byte_sum writes the sum of the |in_len| bytes at |in| to |*out|
// using the Rust implementation. It returns one on success and zero on error.
// It is a placeholder that exists to test the C-to-Rust call path.
OPENSSL_EXPORT int CRYPTO_rust_byte_sum(const uint8_t *in, size_t in_len,
                                        uint64_t *out);

// Rust functions, defined in src/lib.rs. rustc gives them default visibility,
// and an ELF linker keeps the strictest visibility of any declaration, so
// declaring them hidden keeps them out of libcrypto's exports.
#if defined(__GNUC__) || defined(__clang__)
#define AWSLC_RUST_HIDDEN __attribute__((visibility("hidden")))
#else
#define AWSLC_RUST_HIDDEN
#endif

// In a BORINGSSL_PREFIX build the Rust functions always carry the prefix
// (src/lib.rs), so C has to use the prefixed names too. The prefix headers
// rename them only if the symbols list names them.
#if defined(BORINGSSL_PREFIX) && !defined(caracal_byte_sum)
#define caracal_byte_sum BORINGSSL_ADD_PREFIX(BORINGSSL_PREFIX, caracal_byte_sum)
#endif

// caracal_byte_sum writes the sum of the |input_len| bytes at |input| to
// |*out|. It returns one on success, or zero if |out| is NULL or |input| is
// NULL with a non-zero |input_len|.
AWSLC_RUST_HIDDEN int caracal_byte_sum(const uint8_t *input, size_t input_len,
                                       uint64_t *out);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_RUST_INTERNAL_H
