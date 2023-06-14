/* Copyright (c) 2014, Google Inc.
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

#include <openssl/rand.h>

#include <assert.h>
#include <limits.h>
#include <string.h>

#if defined(BORINGSSL_FIPS)
#if !defined(OPENSSL_WINDOWS)
#include <unistd.h>
#else
#include <io.h>
#endif
#include "../../../third_party/jitterentropy/jitterentropy.h"
#endif

#include <openssl/chacha.h>
#include <openssl/mem.h>
#include <openssl/type_check.h>

#include "internal.h"
#include "fork_detect.h"
#include "../../internal.h"
#include "../delocate.h"


// It's assumed that the operating system always has an unfailing source of
// entropy which is accessed via |CRYPTO_sysrand[_for_seed]|. (If the operating
// system entropy source fails, it's up to |CRYPTO_sysrand| to abort the
// process—we don't try to handle it.)
//
// In addition, the hardware may provide a low-latency RNG. Intel's rdrand
// instruction is the canonical example of this. When a hardware RNG is
// available we don't need to worry about an RNG failure arising from fork()ing
// the process or moving a VM, so we can keep thread-local RNG state and use it
// as an additional-data input to CTR-DRBG.
//
// (We assume that the OS entropy is safe from fork()ing and VM duplication.
// This might be a bit of a leap of faith, esp on Windows, but there's nothing
// that we can do about it.)

// When in FIPS mode we use the CPU Jitter entropy source to seed our DRBG.  
// This entropy source is very slow and can incur a cost anywhere between 10-60ms
// depending on configuration and CPU.  Increasing to 2^24 will amortize the 
// penalty over more requests.  This is the same value used in OpenSSL 3.0  
// and meets the requirements defined in SP 800-90B for a max reseed of interval (2^48)
//
// CPU Jitter:  https://www.chronox.de/jent/doc/CPU-Jitter-NPTRNG.html
// 
// kReseedInterval is the number of generate calls made to CTR-DRBG before
// reseeding.

#if defined(BORINGSSL_FIPS)
static const unsigned kReseedInterval = 16777216;
#else
static const unsigned kReseedInterval = 4096;
#endif

// CRNGT_BLOCK_SIZE is the number of bytes in a “block” for the purposes of the
// continuous random number generator test in FIPS 140-2, section 4.9.2.
#define CRNGT_BLOCK_SIZE 16

// rand_thread_state contains the per-thread state for the RNG.
struct rand_thread_state {
  CTR_DRBG_STATE drbg;
  uint64_t fork_generation;
  // calls is the number of generate calls made on |drbg| since it was last
  // (re)seeded. This is bound by |kReseedInterval|.
  unsigned calls;
  // last_block_valid is non-zero iff |last_block| contains data from
  // |get_seed_entropy|.
  int last_block_valid;

#if defined(BORINGSSL_FIPS)
  // last_block contains the previous block from |get_seed_entropy|.
  uint8_t last_block[CRNGT_BLOCK_SIZE];
  // next and prev form a NULL-terminated, double-linked list of all states in
  // a process.
  struct rand_thread_state *next, *prev;

  // In FIPS mode the entropy source is CPU Jitter so we assign an instance
  // of Jitter to each thread. The instance is initialized/destroyed at the same
  // time as the thread state is created/destroyed.
  struct rand_data *jitter_ec;
#endif
};

#if defined(BORINGSSL_FIPS)
// thread_states_list is the head of a linked-list of all |rand_thread_state|
// objects in the process, one per thread. This is needed because FIPS requires
// that they be zeroed on process exit, but thread-local destructors aren't
// called when the whole process is exiting.
DEFINE_BSS_GET(struct rand_thread_state *, thread_states_list)
DEFINE_STATIC_MUTEX(thread_states_list_lock)
DEFINE_STATIC_MUTEX(state_clear_all_lock)

#if defined(_MSC_VER)
#pragma section(".CRT$XCU", read)
static void rand_thread_state_clear_all(void);
static void windows_install_rand_thread_state_clear_all(void) {
  atexit(&rand_thread_state_clear_all);
}
__declspec(allocate(".CRT$XCU")) void(*fips_library_destructor)(void) =
    windows_install_rand_thread_state_clear_all;
#else
static void rand_thread_state_clear_all(void) __attribute__ ((destructor));
#endif


static void rand_thread_state_clear_all(void) {
  CRYPTO_STATIC_MUTEX_lock_write(thread_states_list_lock_bss_get());
  CRYPTO_STATIC_MUTEX_lock_write(state_clear_all_lock_bss_get());
  for (struct rand_thread_state *cur = *thread_states_list_bss_get();
       cur != NULL; cur = cur->next) {
    CTR_DRBG_clear(&cur->drbg);
    OPENSSL_cleanse(cur->last_block, sizeof(cur->last_block));

    jent_entropy_collector_free(cur->jitter_ec);
  }
  // The locks are deliberately left locked so that any threads that are still
  // running will hang if they try to call |RAND_bytes|.
}
#endif

// rand_thread_state_free frees a |rand_thread_state|. This is called when a
// thread exits.
static void rand_thread_state_free(void *state_in) {
  struct rand_thread_state *state = state_in;

  if (state_in == NULL) {
    return;
  }

#if defined(BORINGSSL_FIPS)
  CRYPTO_STATIC_MUTEX_lock_write(thread_states_list_lock_bss_get());

  if (state->prev != NULL) {
    state->prev->next = state->next;
  } else {
    *thread_states_list_bss_get() = state->next;
  }

  if (state->next != NULL) {
    state->next->prev = state->prev;
  }

  CRYPTO_STATIC_MUTEX_unlock_write(thread_states_list_lock_bss_get());

  CTR_DRBG_clear(&state->drbg);
  OPENSSL_cleanse(state->last_block, sizeof(state->last_block));

  jent_entropy_collector_free(state->jitter_ec);
#endif

  OPENSSL_free(state);
}

#if defined(OPENSSL_X86_64) && !defined(OPENSSL_NO_ASM) && \
    !defined(BORINGSSL_UNSAFE_DETERMINISTIC_MODE)

// rdrand maximum retries as suggested by:
// Intel® Digital Random Number Generator (DRNG) Software Implementation Guide
// Revision 2.1
// https://software.intel.com/content/www/us/en/develop/articles/intel-digital-random-number-generator-drng-software-implementation-guide.html
#define RDRAND_MAX_RETRIES 10

OPENSSL_STATIC_ASSERT(RDRAND_MAX_RETRIES > 0, rdrand_max_retries_must_be_positive)
#define CALL_RDRAND_WITH_RETRY(rdrand_func, fail_ret_value)       \
    for (size_t tries = 0; tries < RDRAND_MAX_RETRIES; tries++) { \
      if ((rdrand_func) == 1) {                                   \
        break;                                                    \
      }                                                           \
      else if (tries >= RDRAND_MAX_RETRIES - 1) {                 \
        return fail_ret_value;                                    \
      }                                                           \
    }

// rdrand should only be called if either |have_rdrand| or |have_fast_rdrand|
// returned true.
static int rdrand(uint8_t *buf, const size_t len) {
  const size_t len_multiple8 = len & ~7;
  CALL_RDRAND_WITH_RETRY(CRYPTO_rdrand_multiple8_buf(buf, len_multiple8), 0)
  const size_t remainder = len - len_multiple8;

  if (remainder != 0) {
    assert(remainder < 8);

    uint8_t rand_buf[8];
    CALL_RDRAND_WITH_RETRY(CRYPTO_rdrand(rand_buf), 0)
    OPENSSL_memcpy(buf + len_multiple8, rand_buf, remainder);
  }

  return 1;
}

#else

static int rdrand(uint8_t *buf, size_t len) {
  return 0;
}

#endif

#if defined(BORINGSSL_FIPS)

static void CRYPTO_get_fips_seed(uint8_t *out_entropy, size_t out_entropy_len,
                                 int *out_want_additional_input) {
  *out_want_additional_input = 0;
  // Every thread has its own Jitter instance so we fetch the one assigned
  // to the current thread.
  struct rand_thread_state *state =
      CRYPTO_get_thread_local(OPENSSL_THREAD_LOCAL_RAND);
  if (state == NULL || state->jitter_ec == NULL) {
    abort();
  }

  // |jent_read_entropy| has a false positive health test failure rate of 2^-22.
  // To avoid aborting so frequently, we retry 3 times.
  size_t num_tries;
  for (num_tries = 1; num_tries <= JITTER_MAX_NUM_TRIES; num_tries++) {
    // Try to generate the required number of bytes with Jitter.
    // If successful break out from the loop, otherwise try again.
    if (jent_read_entropy(state->jitter_ec, (char *) out_entropy,
                          out_entropy_len) == (ssize_t) out_entropy_len) {
        break;
    }
    // If Jitter entropy failed to produce entropy we need to reset it.
    jent_entropy_collector_free(state->jitter_ec);
    state->jitter_ec = NULL;
    state->jitter_ec = jent_entropy_collector_alloc(0, JENT_FORCE_FIPS);
    if (state->jitter_ec == NULL) {
      abort();
    }
  }

  if (num_tries > JITTER_MAX_NUM_TRIES) {
    abort();
  }

  if (boringssl_fips_break_test("CRNG")) {
    // This breaks the "continuous random number generator test" defined in FIPS
    // 140-2, section 4.9.2, and implemented in |rand_get_seed|.
    OPENSSL_memset(out_entropy, 0, out_entropy_len);
  }
}

// rand_get_seed fills |seed| with entropy and sets |*out_want_additional_input|
// to one if that entropy came directly from the CPU and zero otherwise.
static void rand_get_seed(struct rand_thread_state *state,
                          uint8_t seed[CTR_DRBG_ENTROPY_LEN],
                          int *out_want_additional_input) {
  if (!state->last_block_valid) {
    int unused;
    CRYPTO_get_fips_seed(state->last_block, sizeof(state->last_block), &unused);
    state->last_block_valid = 1;
  }

  uint8_t entropy[CTR_DRBG_ENTROPY_LEN];
  CRYPTO_get_fips_seed(entropy, sizeof(entropy), out_want_additional_input);

  // See FIPS 140-2, section 4.9.2. This is the “continuous random number
  // generator test” which causes the program to randomly abort. Hopefully the
  // rate of failure is small enough not to be a problem in practice.
  if (CRYPTO_memcmp(state->last_block, entropy, CRNGT_BLOCK_SIZE) == 0) {
    fprintf(stderr, "CRNGT failed.\n");
    BORINGSSL_FIPS_abort();
  }

  OPENSSL_STATIC_ASSERT(sizeof(entropy) % CRNGT_BLOCK_SIZE == 0, _)
  for (size_t i = CRNGT_BLOCK_SIZE; i < sizeof(entropy);
       i += CRNGT_BLOCK_SIZE) {
    if (CRYPTO_memcmp(entropy + i - CRNGT_BLOCK_SIZE, entropy + i,
                      CRNGT_BLOCK_SIZE) == 0) {
      fprintf(stderr, "CRNGT failed.\n");
      BORINGSSL_FIPS_abort();
    }
  }
  OPENSSL_memcpy(state->last_block,
                 entropy + sizeof(entropy) - CRNGT_BLOCK_SIZE,
                 CRNGT_BLOCK_SIZE);

  OPENSSL_memcpy(seed, entropy, CTR_DRBG_ENTROPY_LEN);
}

#else // BORINGSSL_FIPS

// rand_get_seed fills |seed| with entropy and sets |*out_want_additional_input|
// to one if that entropy came directly from the CPU and zero otherwise.
static void rand_get_seed(struct rand_thread_state *state,
                          uint8_t seed[CTR_DRBG_ENTROPY_LEN],
                          int *out_want_additional_input) {
  // If not in FIPS mode, we don't overread from the system entropy source and
  // we don't depend only on the hardware RDRAND.
  CRYPTO_sysrand_for_seed(seed, CTR_DRBG_ENTROPY_LEN);
  *out_want_additional_input = 0;
}

#endif // BORINGSSL_FIPS

void RAND_bytes_with_additional_data(uint8_t *out, size_t out_len,
                                     const uint8_t user_additional_data[32]) {
  if (out_len == 0) {
    return;
  }

  const uint64_t fork_generation = CRYPTO_get_fork_generation();

  // Additional data is mixed into every CTR-DRBG call to protect, as best we
  // can, against forks & VM clones. We do not over-read this information and
  // don't reseed with it so, from the point of view of FIPS, this doesn't
  // provide “prediction resistance”. But, in practice, it does.
  uint8_t additional_data[32];
  // Intel chips have fast RDRAND instructions while, in other cases, RDRAND can
  // be _slower_ than a system call.
  if (!have_fast_rdrand() ||
      !rdrand(additional_data, sizeof(additional_data))) {
    // Without a hardware RNG to save us from address-space duplication, the OS
    // entropy is used. This can be expensive (one read per |RAND_bytes| call)
    // and so is disabled when we have fork detection, or if the application has
    // promised not to fork.
    if (fork_generation != 0 || rand_fork_unsafe_buffering_enabled()) {
      OPENSSL_memset(additional_data, 0, sizeof(additional_data));
    } else if (!have_rdrand()) {
      // No alternative so block for OS entropy.
      CRYPTO_sysrand(additional_data, sizeof(additional_data));
    } else if (!CRYPTO_sysrand_if_available(additional_data,
                                            sizeof(additional_data)) &&
               !rdrand(additional_data, sizeof(additional_data))) {
      // RDRAND failed: block for OS entropy.
      CRYPTO_sysrand(additional_data, sizeof(additional_data));
    }
  }

  for (size_t i = 0; i < sizeof(additional_data); i++) {
    additional_data[i] ^= user_additional_data[i];
  }

  struct rand_thread_state stack_state;
  struct rand_thread_state *state =
      CRYPTO_get_thread_local(OPENSSL_THREAD_LOCAL_RAND);

  if (state == NULL) {
    state = OPENSSL_malloc(sizeof(struct rand_thread_state));
    if (state == NULL ||
        !CRYPTO_set_thread_local(OPENSSL_THREAD_LOCAL_RAND, state,
                                 rand_thread_state_free)) {
      // If the system is out of memory, use an ephemeral state on the
      // stack.
      state = &stack_state;
    }

#if defined(BORINGSSL_FIPS)
    // Initialize the thread-local Jitter instance.
    state->jitter_ec = NULL;
    // The first parameter passed to |jent_entropy_collector_alloc| function is
    // the desired oversampling rate. Passing a 0 tells Jitter module to use
    // the default rate (which is 3 in Jitter v3.1.0).
    state->jitter_ec = jent_entropy_collector_alloc(0, JENT_FORCE_FIPS);
    if (state->jitter_ec == NULL) {
      abort();
    }
#endif

    state->last_block_valid = 0;
    uint8_t seed[CTR_DRBG_ENTROPY_LEN];
    int want_additional_input;
    rand_get_seed(state, seed, &want_additional_input);

    uint8_t personalization[CTR_DRBG_ENTROPY_LEN] = {0};
    size_t personalization_len = 0;
#if defined(BORINGSSL_FIPS) && defined(OPENSSL_URANDOM)
    // In FIPS mode we get the entropy from CPU Jitter. In order to not rely
    // completely on Jitter we add to |CTR_DRBG_init| a personalization string
    // that we read from urandom.
    CRYPTO_sysrand(personalization, sizeof(personalization));
    personalization_len = sizeof(personalization);
#endif

    if (!CTR_DRBG_init(&state->drbg, seed, personalization,
                       personalization_len)) {
      abort();
    }
    state->calls = 0;
    state->fork_generation = fork_generation;

#if defined(BORINGSSL_FIPS)
    if (state != &stack_state) {
      CRYPTO_STATIC_MUTEX_lock_write(thread_states_list_lock_bss_get());
      struct rand_thread_state **states_list = thread_states_list_bss_get();
      state->next = *states_list;
      if (state->next != NULL) {
        state->next->prev = state;
      }
      state->prev = NULL;
      *states_list = state;
      CRYPTO_STATIC_MUTEX_unlock_write(thread_states_list_lock_bss_get());
    }
#endif
    OPENSSL_cleanse(seed, CTR_DRBG_ENTROPY_LEN);
    OPENSSL_cleanse(personalization, CTR_DRBG_ENTROPY_LEN);
  }

  if (state->calls >= kReseedInterval ||
      state->fork_generation != fork_generation) {
    uint8_t seed[CTR_DRBG_ENTROPY_LEN];
    int want_additional_input;
    rand_get_seed(state, seed, &want_additional_input);

    uint8_t add_data_for_reseed[CTR_DRBG_ENTROPY_LEN];
    size_t add_data_for_reseed_len = 0;
#if defined(BORINGSSL_FIPS)
    // Take a read lock around accesses to |state->drbg|. This is needed to
    // avoid returning bad entropy if we race with
    // |rand_thread_state_clear_all|.
    //
    // This lock must be taken after any calls to |CRYPTO_sysrand| to avoid a
    // bug on ppc64le. glibc may implement pthread locks by wrapping user code
    // in a hardware transaction, but, on some older versions of glibc and the
    // kernel, syscalls made with |syscall| did not abort the transaction.
    CRYPTO_STATIC_MUTEX_lock_read(state_clear_all_lock_bss_get());

    // In FIPS mode we get the entropy from CPU Jitter. In order to not rely
    // completely on Jitter we add to |CTR_DRBG_reseed| additional data
    // that we read from urandom.
    CRYPTO_sysrand(add_data_for_reseed, sizeof(add_data_for_reseed));
    add_data_for_reseed_len = sizeof(add_data_for_reseed);
#endif
    if (!CTR_DRBG_reseed(&state->drbg, seed,
                         add_data_for_reseed, add_data_for_reseed_len)) {
      abort();
    }
    state->calls = 0;
    state->fork_generation = fork_generation;
    OPENSSL_cleanse(seed, CTR_DRBG_ENTROPY_LEN);
    OPENSSL_cleanse(add_data_for_reseed, CTR_DRBG_ENTROPY_LEN);
  } else {
#if defined(BORINGSSL_FIPS)
    CRYPTO_STATIC_MUTEX_lock_read(state_clear_all_lock_bss_get());
#endif
  }

  int first_call = 1;
  while (out_len > 0) {
    size_t todo = out_len;
    if (todo > CTR_DRBG_MAX_GENERATE_LENGTH) {
      todo = CTR_DRBG_MAX_GENERATE_LENGTH;
    }

    if (!CTR_DRBG_generate(&state->drbg, out, todo, additional_data,
                           first_call ? sizeof(additional_data) : 0)) {
      abort();
    }

    out += todo;
    out_len -= todo;
    // Though we only check before entering the loop, this cannot add enough to
    // overflow a |size_t|.
    state->calls++;
    first_call = 0;
  }

  if (state == &stack_state) {
    CTR_DRBG_clear(&state->drbg);
  }

  OPENSSL_cleanse(additional_data, 32);

#if defined(BORINGSSL_FIPS)
  CRYPTO_STATIC_MUTEX_unlock_read(state_clear_all_lock_bss_get());
#endif
}

int RAND_bytes(uint8_t *out, size_t out_len) {
  static const uint8_t kZeroAdditionalData[32] = {0};
  RAND_bytes_with_additional_data(out, out_len, kZeroAdditionalData);
  return 1;
}

int RAND_pseudo_bytes(uint8_t *buf, size_t len) {
  return RAND_bytes(buf, len);
}

void RAND_get_system_entropy_for_custom_prng(uint8_t *buf, size_t len) {
  if (len > 256) {
    abort();
  }
  CRYPTO_sysrand_for_seed(buf, len);
}
