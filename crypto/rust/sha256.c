// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// In Rust builds, libcrypto's SHA-224 and SHA-256 functions are Rust's, in
// fipsmodule/src/sha256.rs. They're defined here in C, as calls into Rust,
// because Rust can't define exported functions through the fold: Windows
// exports only functions C marks for export, and Apple's fold hides every
// symbol. bcm.c keeps C's sha256.c under private names for its own users
// (crypto/fipsmodule/sha/sha256_private_names.h).

#include <openssl/sha.h>

#include <openssl/crypto.h>

#include "../internal.h"
#include "../fipsmodule/service_indicator/internal.h"
#include "../fipsmodule/sha/internal.h"
#include "fipsmodule/internal.h"

#if defined(OPENSSL_MSAN)
#include <sanitizer/msan_interface.h>
#endif

// Rust and C both use |SHA256_CTX|, so both assert its layout (Sha256Ctx in
// sha256.rs).
OPENSSL_STATIC_ASSERT(sizeof(SHA256_CTX) == 112, sha256_ctx_size_matches_rust)
OPENSSL_STATIC_ASSERT(alignof(SHA256_CTX) == 4, sha256_ctx_align_matches_rust)
OPENSSL_STATIC_ASSERT(offsetof(SHA256_CTX, h) == 0 &&
                          offsetof(SHA256_CTX, Nl) == 32 &&
                          offsetof(SHA256_CTX, Nh) == 36 &&
                          offsetof(SHA256_CTX, data) == 40 &&
                          offsetof(SHA256_CTX, num) == 104 &&
                          offsetof(SHA256_CTX, md_len) == 108,
                      sha256_ctx_offsets_match_rust)

// Stable Rust can't be built with MSan's instrumentation, so MSan doesn't see
// Rust's reads and writes. |rust_reads| checks that the bytes Rust will read
// are initialized, and |rust_wrote| marks the bytes it wrote initialized.
static void rust_reads(const void *p, size_t len) {
#if defined(OPENSSL_MSAN)
  if (p != NULL) {
    __msan_check_mem_is_initialized(p, len);
  }
#endif
}

static void rust_wrote(const void *p, size_t len) {
#if defined(OPENSSL_MSAN)
  if (p != NULL) {
    __msan_unpoison(p, len);
  }
#endif
}

#if !defined(AWSLC_FIPS) && !defined(BORINGSSL_SHARED_LIBRARY)
// crypto.c's constructor fills in the CPU capability flags Rust reads. A
// static link takes crypto.o only if something refers to it, which bcm.c's
// |dummy_func_for_constructor| does for bcm.o. SHA-256 isn't in bcm.o in Rust
// builds, so this file refers to it too, or a program that only hashes would
// run the slowest assembly.
#if defined(BORINGSSL_PREFIX)
#define bcm_rust_dummy_func_for_constructor \
  BORINGSSL_ADD_PREFIX(BORINGSSL_PREFIX, bcm_rust_dummy_func_for_constructor)
#endif
void bcm_rust_dummy_func_for_constructor(void);
void bcm_rust_dummy_func_for_constructor(void) { CRYPTO_library_init(); }
#endif

static int sha256_init(SHA256_CTX *sha, size_t md_len) {
  int ok = bcm_rust_sha256_init(sha, md_len);
  rust_wrote(sha, sizeof(*sha));
  return ok;
}

int SHA224_Init(SHA256_CTX *sha) {
  return sha256_init(sha, SHA224_DIGEST_LENGTH);
}

int SHA256_Init(SHA256_CTX *sha) {
  return sha256_init(sha, SHA256_DIGEST_LENGTH);
}

static int sha256_init_from_state(SHA256_CTX *sha, size_t md_len,
                                  const uint8_t h[SHA256_CHAINING_LENGTH],
                                  uint64_t n) {
  rust_reads(h, SHA256_CHAINING_LENGTH);
  int ok = bcm_rust_sha256_init_from_state(sha, md_len, h, n);
  if (ok) {
    rust_wrote(sha, sizeof(*sha));
  }
  return ok;
}

int SHA224_Init_from_state(SHA256_CTX *sha,
                           const uint8_t h[SHA224_CHAINING_LENGTH],
                           uint64_t n) {
  return sha256_init_from_state(sha, SHA224_DIGEST_LENGTH, h, n);
}

int SHA256_Init_from_state(SHA256_CTX *sha,
                           const uint8_t h[SHA256_CHAINING_LENGTH],
                           uint64_t n) {
  return sha256_init_from_state(sha, SHA256_DIGEST_LENGTH, h, n);
}

int SHA256_Update(SHA256_CTX *sha, const void *data, size_t len) {
  rust_reads(sha, sizeof(*sha));
  rust_reads(data, len);
  int ok = bcm_rust_sha256_update(sha, data, len);
  rust_wrote(sha, sizeof(*sha));
  return ok;
}

int SHA224_Update(SHA256_CTX *sha, const void *data, size_t len) {
  return SHA256_Update(sha, data, len);
}

static int sha256_final(uint8_t *out, size_t md_len, SHA256_CTX *sha) {
  rust_reads(sha, sizeof(*sha));
  int ok = bcm_rust_sha256_final(out, md_len, sha);
  rust_wrote(sha, sizeof(*sha));
  if (ok) {
    rust_wrote(out, md_len);
    FIPS_service_indicator_update_state();
  }
  return ok;
}

int SHA224_Final(uint8_t out[SHA224_DIGEST_LENGTH], SHA256_CTX *sha) {
  return sha256_final(out, SHA224_DIGEST_LENGTH, sha);
}

int SHA256_Final(uint8_t out[SHA256_DIGEST_LENGTH], SHA256_CTX *sha) {
  return sha256_final(out, SHA256_DIGEST_LENGTH, sha);
}

static uint8_t *sha256_oneshot(const uint8_t *data, size_t len, uint8_t *out,
                               size_t md_len) {
  rust_reads(data, len);
  if (bcm_rust_sha256(data, len, out, md_len)) {
    rust_wrote(out, md_len);
    FIPS_service_indicator_update_state();
  }
  return out;
}

uint8_t *SHA224(const uint8_t *data, size_t len,
                uint8_t out[SHA224_DIGEST_LENGTH]) {
  return sha256_oneshot(data, len, out, SHA224_DIGEST_LENGTH);
}

uint8_t *SHA256(const uint8_t *data, size_t len,
                uint8_t out[SHA256_DIGEST_LENGTH]) {
  return sha256_oneshot(data, len, out, SHA256_DIGEST_LENGTH);
}

void SHA256_TransformBlocks(uint32_t state[8], const uint8_t *data,
                            size_t num_blocks) {
  rust_reads(state, 8 * sizeof(uint32_t));
  rust_reads(data, num_blocks * SHA256_CBLOCK);
  bcm_rust_sha256_transform_blocks(state, data, num_blocks);
  rust_wrote(state, 8 * sizeof(uint32_t));
}

void SHA256_Transform(SHA256_CTX *sha, const uint8_t data[SHA256_CBLOCK]) {
  SHA256_TransformBlocks(sha->h, data, 1);
}

static int sha256_get_state(SHA256_CTX *sha,
                            uint8_t out_h[SHA256_CHAINING_LENGTH],
                            uint64_t *out_n) {
  rust_reads(sha, sizeof(*sha));
  int ok = bcm_rust_sha256_get_state(sha, out_h, out_n);
  if (ok) {
    rust_wrote(out_h, SHA256_CHAINING_LENGTH);
    rust_wrote(out_n, sizeof(*out_n));
  }
  return ok;
}

int SHA224_get_state(SHA256_CTX *sha, uint8_t out_h[SHA224_CHAINING_LENGTH],
                     uint64_t *out_n) {
  return sha256_get_state(sha, out_h, out_n);
}

int SHA256_get_state(SHA256_CTX *sha, uint8_t out_h[SHA256_CHAINING_LENGTH],
                     uint64_t *out_n) {
  return sha256_get_state(sha, out_h, out_n);
}
