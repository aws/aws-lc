/* Copyright (c) 2015, Google Inc.
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

#ifndef OPENSSL_HEADER_CRYPTO_RAND_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RAND_INTERNAL_H

#include <openssl/aes.h>
#include <openssl/ctrdrbg.h>
#include <openssl/rand.h>

#include "../../internal.h"
#include "../modes/internal.h"

#if defined(__cplusplus)
extern "C" {
#endif

#if defined(BORINGSSL_UNSAFE_DETERMINISTIC_MODE)
#define OPENSSL_RAND_DETERMINISTIC
#elif defined(OPENSSL_WINDOWS)
#define OPENSSL_RAND_WINDOWS
#elif defined(OPENSSL_MACOS) || defined(OPENSSL_OPENBSD) || defined(OPENSSL_FREEBSD)
#define OPENSSL_RAND_GETENTROPY
#else
#define OPENSSL_RAND_URANDOM
#endif

// kCtrDrbgReseedInterval is the number of generate calls made to CTR-DRBG,
// for a specific state, before reseeding.
static const uint64_t kCtrDrbgReseedInterval = 4096;

#define RAND_NO_USER_PRED_RESISTANCE 0
#define RAND_USE_USER_PRED_RESISTANCE 1

OPENSSL_EXPORT uint64_t get_thread_generate_calls_since_seed(void);
OPENSSL_EXPORT uint64_t get_thread_reseed_calls_since_initialization(void);

// Functions:
// CRYPTO_init_sysrand
// CRYPTO_sysrand
// CRYPTO_sysrand_for_seed
// CRYPTO_sysrand_if_available
// are the operating system entropy source interface used in the randomness
// generation implementation.

// CRYPTO_sysrand fills |len| bytes at |buf| with entropy from the operating
// system.
OPENSSL_EXPORT void CRYPTO_sysrand(uint8_t *buf, size_t len);

// CRYPTO_sysrand_for_seed fills |len| bytes at |buf| with entropy from the
// operating system. It may draw from the |GRND_RANDOM| pool on Android,
// depending on the vendor's configuration.
OPENSSL_EXPORT void CRYPTO_sysrand_for_seed(uint8_t *buf, size_t len);

#if defined(OPENSSL_RAND_URANDOM) || defined(OPENSSL_RAND_WINDOWS)
// CRYPTO_init_sysrand initializes long-lived resources needed to draw entropy
// from the operating system.
void CRYPTO_init_sysrand(void);
#else
OPENSSL_INLINE void CRYPTO_init_sysrand(void) {}
#endif  // defined(OPENSSL_RAND_URANDOM) || defined(OPENSSL_RAND_WINDOWS)

#if defined(OPENSSL_RAND_URANDOM)
// CRYPTO_sysrand_if_available fills |len| bytes at |buf| with entropy from the
// operating system, or early /dev/urandom data, and returns 1, _if_ the entropy
// pool is initialized or if getrandom() is not available and not in FIPS mode.
// Otherwise it will not block and will instead fill |buf| with all zeros and
// return 0.
int CRYPTO_sysrand_if_available(uint8_t *buf, size_t len);
#else
OPENSSL_INLINE int CRYPTO_sysrand_if_available(uint8_t *buf, size_t len) {
  CRYPTO_sysrand(buf, len);
  return 1;
}
#endif  // defined(OPENSSL_RAND_URANDOM)

// CTR_DRBG_STATE contains the state of a CTR_DRBG based on AES-256. See SP
// 800-90Ar1.
struct ctr_drbg_state_st {
  AES_KEY ks;
  block128_f block;
  ctr128_f ctr;
  uint8_t counter[16];
  uint64_t reseed_counter;
};

// CTR_DRBG_init initialises |*drbg| given |CTR_DRBG_ENTROPY_LEN| bytes of
// entropy in |entropy| and, optionally, a personalization string up to
// |CTR_DRBG_ENTROPY_LEN| bytes in length. It returns one on success and zero
// on error.
OPENSSL_EXPORT int CTR_DRBG_init(CTR_DRBG_STATE *drbg,
                                 const uint8_t entropy[CTR_DRBG_ENTROPY_LEN],
                                 const uint8_t *personalization,
                                 size_t personalization_len);

int rdrand(uint8_t *buf, const size_t len);

#if defined(OPENSSL_X86_64) && !defined(OPENSSL_NO_ASM)

// Certain operating environments will disable RDRAND for both security and
// performance reasons. See initialization of CPU capability vector for details.
// At the moment, we must implement this logic there because the CPU capability
// vector does not carry CPU family/model information which is required to
// determine restrictions.
OPENSSL_INLINE int have_hw_rng_x86_64(void) {
  return CRYPTO_is_RDRAND_capable();
}

// TODO only allow multiples of 8 from rdrand

// CRYPTO_rdrand writes eight bytes of random data from the hardware RNG to
// |out|. It returns one on success or zero on hardware failure.
int CRYPTO_rdrand(uint8_t out[8]);

// CRYPTO_rdrand_multiple8_buf fills |len| bytes at |buf| with random data from
// the hardware RNG. The |len| argument must be a multiple of eight. It returns
// one on success and zero on hardware failure.
int CRYPTO_rdrand_multiple8_buf(uint8_t *buf, size_t len);

#else  // defined(OPENSSL_X86_64) && !defined(OPENSSL_NO_ASM)

OPENSSL_INLINE int have_hw_rng_x86_64(void) {
  return 0;
}

#endif  // defined(OPENSSL_X86_64) && !defined(OPENSSL_NO_ASM)

// Don't retry forever. There is no science in picking this number and can be
// adjusted in the future if need be. We do not backoff forever, because we
// believe that it is easier to detect failing calls than detecting infinite
// spinning loops.
#define MAX_BACKOFF_RETRIES 9
OPENSSL_EXPORT void HAZMAT_set_urandom_test_mode_for_testing(void);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_RAND_INTERNAL_H
