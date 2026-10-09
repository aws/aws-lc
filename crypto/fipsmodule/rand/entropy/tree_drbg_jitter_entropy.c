// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#if !defined(DISABLE_CPU_JITTER_ENTROPY)

#include <openssl/ctrdrbg.h>
#include <openssl/mem.h>
#include <openssl/type_check.h>

#include "internal.h"
#include "../internal.h"
#include "../../delocate.h"
#include "../../../internal.h"
#include "../../../rand_extra/internal.h"
#include "../../../ube/internal.h"

// Randomness generation implements thread-local "frontend" DRBGs that serve
// requests for randomness from consumers through exported functions such as
// RAND_bytes(). This file implements a tree-DRBG from SP800-90C as a seed
// entropy source for the frontend DRBGs. The implemented tree-DRBG has the
// following characteristics:
//  - A per-thread seed DRBG that serves seed requests for a thread-local
//    frontend DRBG.
//  - A global seed DRBG that serves seed requests from the thread-local seed
//    DRBGs.
//  - A root seed source that serves seed requests from the global seed DRBG.
//    The root provider and its failure policy are selected by
//    entropy_sources.c. The tree consumes seeds and aborts if the root
//    provider fails; it does not choose alternative entropy sources.
//
// The dependency tree looks as follows:
//
//          entropy_source
//            interface
//                |
//    rand.c      |   tree_drbg_jitter_entropy.c
//                |
//  front-end     |   tree-DRBG
//  per-thread    |   per-thread
// +-----------+  |  +-----------+
// | CTR-DRBG  | --> | CTR-DRBG  | -|
// +-----------+  |  +-----------+   -|
// +-----------+  |  +-----------+     --|     per-process          per-process
// | CTR-DRBG  | --> | CTR-DRBG  | ---|   --> +-----------+     +----------------+
// +-----------+  |  +-----------+     -----> | CTR-DRBG  | --> | Root provider  |
//      ...       |      ...              --> +-----------+     +----------------+
// +-----------+  |  +-----------+  -----|
// | CTR-DRBG  | --> | CTR-DRBG  |-|
// +-----------+  |  +-----------+
//                |
//
// Memory life-cycle: The thread-local DRBGs have the same storage duration as
// their corresponding thread-local frontend DRBGs. The per-process DRBG and
// root provider have a storage duration that extends to the duration
// of AWS-LC being loaded into the process. The per-process memory is lazily
// allocated.

// To serve seed requests from the frontend DRBGs the following
// |struct entropy_source_methods| interface functions are implemented:
//  - tree_jitter_initialize
//  - tree_jitter_zeroize_thread_drbg
//  - tree_jitter_free_thread_drbg
//  - tree_jitter_get_seed


struct tree_jitter_drbg_t {
  // is_global is 1 if this object is the per-process seed DRBG. Otherwise 0.
  uint8_t is_global;

  // drbg is the DRBG state.
  CTR_DRBG_STATE drbg;

  // max_generate_calls is the maximum number of generate calls that can be
  // invoked on |drbg| without a reseed.
  uint64_t max_generate_calls;

  // reseed_calls_since_initialization is the number of seed/reseed calls made
  // on |drbg| since its initialization.
  // We assume 2^64 - 1 is an upper bound on the number of reseeds. Type must
  // support that.
  uint64_t reseed_calls_since_initialization;

  // generation_number caches the UBE generation number.
  uint64_t generation_number;

  // ube_protection denotes whether this object is protected from UBEs.
  uint8_t ube_protection;

  // Only the per-process seed DRBG owns a root provider. Its methods are
  // immutable; any permitted source transition is private to the provider.
  struct tree_root_entropy_source root_source;
};

// Per-process seed DRBG locks.
DEFINE_BSS_GET(struct tree_jitter_drbg_t *, global_seed_drbg)
// Protected by global_seed_drbg_lock, including publication after CRYPTO_once.
// Distinguishes an uninitialized tree from a destroyed one.
DEFINE_BSS_GET(int, global_seed_drbg_initialized)
DEFINE_STATIC_ONCE(global_seed_drbg_once)
DEFINE_STATIC_ONCE(global_seed_drbg_zeroize_once)
DEFINE_STATIC_MUTEX(global_seed_drbg_lock)

// tree_jitter_get_root_seed generates |CTR_DRBG_ENTROPY_LEN| bytes of output
// from the root provider configured in |tree_jitter_drbg|. The output is
// returned in |seed_out|. Aborts if the provider fails.
// Access to this function must be synchronized.
static void tree_jitter_get_root_seed(
  struct tree_jitter_drbg_t *tree_jitter_drbg,
  uint8_t seed_out[CTR_DRBG_ENTROPY_LEN]) {

  struct tree_root_entropy_source *root = &tree_jitter_drbg->root_source;
  if (root->methods->get_seed(root, seed_out) != 1) {
    abort();
  }
}

// tree_jitter_drbg_maybe_get_pred_resistance generates RAND_PRED_RESISTANCE_LEN
// bytes for prediction resistance and returns them in |pred_resistance|.
// However, it only generate bytes if |tree_jitter_drbg| meets the conditions:
// 1) is not the global seed DRBG 2) is not protected from UBEs. If bytes are
// generated, |pred_resistance_len| is set to RAND_PRED_RESISTANCE_LEN and is
// otherwise not mutated.
static void tree_jitter_drbg_maybe_get_pred_resistance(
  struct tree_jitter_drbg_t *tree_jitter_drbg,
  uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN],
  size_t *pred_resistance_len) {

  if (tree_jitter_drbg->is_global == 0 &&
      tree_jitter_drbg->ube_protection != 1) {
    CRYPTO_sysrand(pred_resistance, RAND_PRED_RESISTANCE_LEN);
    *pred_resistance_len = RAND_PRED_RESISTANCE_LEN;
  }
}

// tree_jitter_check_drbg_must_reseed computes whether |state| must be
// randomized to ensure uniqueness.
//
// Return 1 if |state| must be randomized. 0 otherwise.
static int tree_jitter_check_drbg_must_reseed(
  struct tree_jitter_drbg_t *tree_jitter_drbg) {

  uint64_t current_generation_number = 0;
  if (CRYPTO_get_ube_generation_number(&current_generation_number) == 1 &&
      current_generation_number != tree_jitter_drbg->generation_number) {
    tree_jitter_drbg->generation_number = current_generation_number;
    return 1;
  }

  // drbg.reseed_counter is initialized to 1, incremented after a generate call
  // on |drbg|. |max_generate_calls| is the maximum allowed invocation of the
  // generate function on |drbg|.
  if (tree_jitter_drbg->drbg.reseed_counter > tree_jitter_drbg->max_generate_calls) {
    return 1;
  }

  return 0;
}

// tree_jitter_drbg_derive_seed generates a CTR_DRBG_ENTROPY_LEN byte seed from
// the DRBG configured in |tree_jitter_drbg|. The generated bytes are returned
// in |seed_out|.
//
// |tree_jitter_drbg_derive_seed| automatically handles reseeding the
// associated DRBG if required. In addition, if UBE detection is not supported
// prediction resistance is used to ensure bytes are generated safely.
static void tree_jitter_drbg_derive_seed(
  struct tree_jitter_drbg_t *tree_jitter_drbg,
  uint8_t seed_out[CTR_DRBG_ENTROPY_LEN]) {

  if (tree_jitter_drbg == NULL) {
    abort();
  }

  if (tree_jitter_check_drbg_must_reseed(tree_jitter_drbg) == 1) {
    uint8_t seed_drbg[CTR_DRBG_ENTROPY_LEN];
    if (tree_jitter_drbg->is_global == 1) {
      tree_jitter_get_root_seed(tree_jitter_drbg, seed_drbg);
    } else {
      CRYPTO_STATIC_MUTEX_lock_write(global_seed_drbg_lock_bss_get());
      tree_jitter_drbg_derive_seed(*global_seed_drbg_bss_get(), seed_drbg);
      CRYPTO_STATIC_MUTEX_unlock_write(global_seed_drbg_lock_bss_get());
    }

    if (CTR_DRBG_reseed(&(tree_jitter_drbg->drbg), seed_drbg, NULL, 0) != 1) {
      abort();
    }
    OPENSSL_cleanse(seed_drbg, CTR_DRBG_ENTROPY_LEN);
    tree_jitter_drbg->reseed_calls_since_initialization += 1;
  }

  uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN];
  size_t pred_resistance_len = 0;
  tree_jitter_drbg_maybe_get_pred_resistance(tree_jitter_drbg,
    pred_resistance, &pred_resistance_len);

  OPENSSL_STATIC_ASSERT(CTR_DRBG_ENTROPY_LEN <= CTR_DRBG_MAX_GENERATE_LENGTH,
    CTR_DRBG_ENTROPY_LEN_is_too_large_compared_to_CTR_DRBG_MAX_GENERATE_LENGTH)

  if (!CTR_DRBG_generate(&(tree_jitter_drbg->drbg), seed_out, CTR_DRBG_ENTROPY_LEN,
        pred_resistance, pred_resistance_len)) {
    abort();
  }
  OPENSSL_cleanse(pred_resistance, RAND_PRED_RESISTANCE_LEN);
}

// tree_jitter_get_seed generates a CTR_DRBG_ENTROPY_LEN byte seed from the DRBG
// configured in |entropy_source|. The generated bytes are returned in
// |seed_out|. This function is the entry point for generating output from the
// tree DRBG.
//
// Return 1 on success and 0 otherwise.
int tree_jitter_get_seed(const struct entropy_source_t *entropy_source,
  uint8_t seed_out[CTR_DRBG_ENTROPY_LEN]) {

  GUARD_PTR_ABORT(entropy_source);
  GUARD_PTR_ABORT(seed_out);

  struct tree_jitter_drbg_t *tree_jitter_drbg_thread =
    (struct tree_jitter_drbg_t *) entropy_source->state;
  tree_jitter_drbg_derive_seed(tree_jitter_drbg_thread, seed_out);

  return 1;
}

// tree_jitter_initialize initializes the global seed DRBG.
static void tree_jitter_initialize_once(void) {

  struct tree_jitter_drbg_t *tree_jitter_drbg_global =
    OPENSSL_zalloc(sizeof(struct tree_jitter_drbg_t));
  if (tree_jitter_drbg_global == NULL) {
    abort();
  }

  tree_jitter_drbg_global->is_global = 1;
  tree_jitter_drbg_global->max_generate_calls = TREE_JITTER_GLOBAL_DRBG_MAX_GENERATE;
  tree_jitter_drbg_global->reseed_calls_since_initialization = 0;
  uint64_t current_generation_number = 0;
  if (CRYPTO_get_ube_generation_number(&current_generation_number) != 1) {
    tree_jitter_drbg_global->generation_number = 0;
  } else {
    tree_jitter_drbg_global->generation_number = current_generation_number;
  }

  struct tree_root_entropy_source *root = &tree_jitter_drbg_global->root_source;
  root->methods = get_tree_root_entropy_source_methods();
  if (root->methods->initialize(root) != 1) {
    abort();
  }

  uint8_t seed_drbg[CTR_DRBG_ENTROPY_LEN];
  tree_jitter_get_root_seed(tree_jitter_drbg_global, seed_drbg);
  if (!CTR_DRBG_init(&(tree_jitter_drbg_global->drbg), seed_drbg, NULL, 0)) {
    abort();
  }
  tree_jitter_drbg_global->reseed_calls_since_initialization += 1;
  OPENSSL_cleanse(seed_drbg, CTR_DRBG_ENTROPY_LEN);

  // Publish under the lock because |tree_jitter_root_is_cpu_jitter| reads the
  // global seed DRBG without going through |CRYPTO_once|.
  CRYPTO_STATIC_MUTEX_lock_write(global_seed_drbg_lock_bss_get());
  *global_seed_drbg_bss_get() = tree_jitter_drbg_global;
  *global_seed_drbg_initialized_bss_get() = 1;
  CRYPTO_STATIC_MUTEX_unlock_write(global_seed_drbg_lock_bss_get());
}

int tree_jitter_root_is_cpu_jitter(void) {
  CRYPTO_STATIC_MUTEX_lock_read(global_seed_drbg_lock_bss_get());
  struct tree_jitter_drbg_t *global = *global_seed_drbg_bss_get();
  int ret = !*global_seed_drbg_initialized_bss_get();
  if (global != NULL) {
    ret = global->root_source.methods->is_cpu_jitter(&global->root_source);
  }
  CRYPTO_STATIC_MUTEX_unlock_read(global_seed_drbg_lock_bss_get());
  return ret;
}

// tree_jitter_initialize initializes a thread-local seed DRBG and configures
// it in |entropy_source|. If the global seed DRBG has not been initialized yet
// it's also initialized.
//
// Returns 1 on success and 0 otherwise.
int tree_jitter_initialize(struct entropy_source_t *entropy_source) {

  GUARD_PTR_ABORT(entropy_source);

  // Initialize the per-thread seed drbg.
  struct tree_jitter_drbg_t *tree_jitter_drbg =
    OPENSSL_zalloc(sizeof(struct tree_jitter_drbg_t));
  if (tree_jitter_drbg == NULL) {
    abort();
  }

  // Initialize the global seed DRBG if haven't already.
  CRYPTO_once(global_seed_drbg_once_bss_get(), tree_jitter_initialize_once);

  // Initialize the per-thread seed DRBG.
  uint8_t seed_drbg[CTR_DRBG_ENTROPY_LEN];
  CRYPTO_STATIC_MUTEX_lock_write(global_seed_drbg_lock_bss_get());
  tree_jitter_drbg_derive_seed(*global_seed_drbg_bss_get(), seed_drbg);
  CRYPTO_STATIC_MUTEX_unlock_write(global_seed_drbg_lock_bss_get());

  if (!CTR_DRBG_init(&(tree_jitter_drbg->drbg), seed_drbg, NULL, 0)) {
    abort();
  }
  tree_jitter_drbg->reseed_calls_since_initialization = 1;
  OPENSSL_cleanse(seed_drbg, CTR_DRBG_ENTROPY_LEN);

  tree_jitter_drbg->is_global = 0;
  tree_jitter_drbg->max_generate_calls = TREE_JITTER_THREAD_DRBG_MAX_GENERATE;
  uint64_t current_generation_number = 0;
  if (CRYPTO_get_ube_generation_number(&current_generation_number) != 1) {
    tree_jitter_drbg->ube_protection = 0;
    tree_jitter_drbg->generation_number = 0;
  } else {
    tree_jitter_drbg->ube_protection = 1;
    tree_jitter_drbg->generation_number = current_generation_number;
  }

  entropy_source->state = tree_jitter_drbg;

  return 1;
}

#if defined(_MSC_VER)
#pragma section(".CRT$XCU", read)
static void tree_jitter_free_global_drbg(void);
static void windows_install_tree_jitter_free_global_drbg(void) {
  atexit(&tree_jitter_free_global_drbg);
}
__declspec(allocate(".CRT$XCU")) void(*tree_jitter_drbg_destructor)(void) =
    windows_install_tree_jitter_free_global_drbg;
#else
static void tree_jitter_free_global_drbg(void) __attribute__ ((destructor));
#endif

// The memory life-time for thread-local seed DRBGs is handled differently
// compared to the global seed DRBG and its root provider. The frontend
// DRBG thread-local destuctors will invoke |tree_jitter_free_thread_drbg| using
// their reference to it. The global seed DRBG and its root provider will
// be released by a destructor. This ensures that the global seed DRBG life-time
// extends to the entire process life-time if the lazy initialization happened.
// Obviously, any dlclose on AWS-LC will release the memory early but that's
// correct behaviour.

// tree_jitter_free_global_drbg frees the memory allocated for the global seed
// DRBG and its root provider.
static void tree_jitter_free_global_drbg(void) {

  CRYPTO_STATIC_MUTEX_lock_write(global_seed_drbg_lock_bss_get());

  struct tree_jitter_drbg_t *global_tree_jitter_drbg = *global_seed_drbg_bss_get();
  if (global_tree_jitter_drbg == NULL) {
    CRYPTO_STATIC_MUTEX_unlock_write(global_seed_drbg_lock_bss_get());
    return;
  }

  if (global_tree_jitter_drbg->is_global != 1) {
    // Should not happen.
    abort();
  }

  struct tree_root_entropy_source *root = &global_tree_jitter_drbg->root_source;
  root->methods->cleanup(root);
  OPENSSL_free(global_tree_jitter_drbg);

  *global_seed_drbg_bss_get() = NULL;

  CRYPTO_STATIC_MUTEX_unlock_write(global_seed_drbg_lock_bss_get());
}

// tree_jitter_free_thread_drbg frees the thread-local seed DRBG
// associated with the entropy source |entropy_source|.
void tree_jitter_free_thread_drbg(struct entropy_source_t *entropy_source) {

  GUARD_PTR_ABORT(entropy_source);

  struct tree_jitter_drbg_t *tree_jitter_drbg =
    (struct tree_jitter_drbg_t *) entropy_source->state;
  if (tree_jitter_drbg == NULL) {
    return;
  }

  OPENSSL_free(tree_jitter_drbg);
  entropy_source->state = NULL;
}

// Per ISO/IEC 19790-2012 7.9.7 "zeroization" can be random data just not other
// SSP/CSP's. The Jitter Entropy instance doesn't have any practical state; it's
// a live entropy source. The zeroization strategy used for the DRBG's is to
// reseed with random data, that in turn, will override all states in the tree
// with random data. The zeroization of the tree DRBG executes after the
// frontend DRBGs have been locked - they can't release any generated output.
// Therefore, the randomness generation layer ensures that no output from the
// tree DRBG is used to generate any output that is later released. Randomizing
// the tree DRBG states therefore effectively "zeroize" the state.
//
// If there aren't any threads running, the zeroizer for the global seed DRBG
// won't execute. But  the destructor responsible for releasing the memory
// allocated for the global seed DRBG and Jitter Entropy instance, will still
// execute, in turn, zeroize it.
//
// One could override the DRBG states with zero's. However, doing the small
// extra work to use random data (from the OS source) ensures that even if some
// output were to escape from the randomness generation, it will still be sound
// practically.
//
// Windows shared builds take the zeros option: there this runs from a libcrypto
// global destructor on |DLL_PROCESS_DETACH|, after |ExitProcess|, where
// |CRYPTO_sysrand| faults on bcryptprimitives.dll (loaded on demand, so not
// kept alive by libcrypto's dependency graph). Static builds run it from the
// executable's |atexit| and are unaffected. Zeros still override every state in
// the tree, losing only the defence in depth above, which the write-locked
// frontend DRBGs already cover.

// tree_jitter_zeroize_drbg zeroizes the DRBG state configured in
// |tree_jitter_drbg|.
static void tree_jitter_zeroize_drbg(
  struct tree_jitter_drbg_t *tree_jitter_drbg) {

  uint8_t random_data[CTR_DRBG_ENTROPY_LEN];
#if defined(OPENSSL_WINDOWS) && defined(BORINGSSL_SHARED_LIBRARY)
  OPENSSL_memset(random_data, 0, CTR_DRBG_ENTROPY_LEN);
#else
  CRYPTO_sysrand_if_available(random_data, CTR_DRBG_ENTROPY_LEN);
#endif

  if (CTR_DRBG_reseed(&(tree_jitter_drbg->drbg), random_data, NULL, 0) != 1) {
    abort();
  }
  OPENSSL_cleanse(random_data, CTR_DRBG_ENTROPY_LEN);
  tree_jitter_drbg->reseed_calls_since_initialization += 1;
}

// tree_jitter_zeroize_global_drbg is similar to |tree_jitter_zeroize_drbg| but
// also handles synchronizing access to the global seed DRBG
static void tree_jitter_zeroize_global_drbg(void) {

  CRYPTO_STATIC_MUTEX_lock_write(global_seed_drbg_lock_bss_get());

  struct tree_jitter_drbg_t *tree_jitter_drbg = *global_seed_drbg_bss_get();
  if (tree_jitter_drbg == NULL) {
    CRYPTO_STATIC_MUTEX_unlock_write(global_seed_drbg_lock_bss_get());
    return;
  }

  if (tree_jitter_drbg->is_global != 1) {
    // Should not happen.
    abort();
  }

  tree_jitter_zeroize_drbg(tree_jitter_drbg);

  CRYPTO_STATIC_MUTEX_unlock_write(global_seed_drbg_lock_bss_get());
}

// tree_jitter_zeroize_thread_drbg zeroizes the thread-local seed DRBG
// associated with the entropy source |entropy_source|. It also executes
// zeroization of the global seed DRBG if applicable.
void tree_jitter_zeroize_thread_drbg(struct entropy_source_t *entropy_source) {

  GUARD_PTR_ABORT(entropy_source);

  CRYPTO_once(global_seed_drbg_zeroize_once_bss_get(), tree_jitter_zeroize_global_drbg);

  struct tree_jitter_drbg_t *tree_jitter_drbg =
    (struct tree_jitter_drbg_t *) entropy_source->state;
  if (tree_jitter_drbg == NULL) {
    return;
  }

  if (tree_jitter_drbg->is_global == 1) {
    // Should not happen.
    abort();
  }

  tree_jitter_zeroize_drbg(tree_jitter_drbg);
}

int get_thread_and_global_tree_drbg_calls_FOR_TESTING(
  const struct entropy_source_t *entropy_source,
  struct test_tree_drbg_t *test_tree_drbg) {

  if (test_tree_drbg == NULL || entropy_source == NULL) {
    return 0;
  }

  int ret = 0;

  CRYPTO_STATIC_MUTEX_lock_read(global_seed_drbg_lock_bss_get());
  struct tree_jitter_drbg_t *global_tree_jitter_drbg = *global_seed_drbg_bss_get();

  struct tree_jitter_drbg_t *thread_tree_jitter_drbg =
    (struct tree_jitter_drbg_t *) entropy_source->state;

  if (global_tree_jitter_drbg == NULL || thread_tree_jitter_drbg == NULL) {
    goto out;
  }

  // Note that |drbg.reseed_counter| is initialized to 1.
  test_tree_drbg->thread_generate_calls_since_seed = thread_tree_jitter_drbg->drbg.reseed_counter;
  test_tree_drbg->thread_reseed_calls_since_initialization = thread_tree_jitter_drbg->reseed_calls_since_initialization;
  test_tree_drbg->global_generate_calls_since_seed = global_tree_jitter_drbg->drbg.reseed_counter;
  test_tree_drbg->global_reseed_calls_since_initialization = global_tree_jitter_drbg->reseed_calls_since_initialization;

  ret = 1;

out:
  CRYPTO_STATIC_MUTEX_unlock_read(global_seed_drbg_lock_bss_get());
  return ret;
}

OPENSSL_EXPORT int set_thread_and_global_tree_drbg_reseed_counter_FOR_TESTING(
  struct entropy_source_t *entropy_source, uint64_t thread_reseed_calls,
  uint64_t global_reseed_calls) {

  if (entropy_source == NULL) {
    return 0;
  }

  int ret = 0;

  CRYPTO_STATIC_MUTEX_lock_write(global_seed_drbg_lock_bss_get());
  struct tree_jitter_drbg_t *global_tree_jitter_drbg = *global_seed_drbg_bss_get();

  struct tree_jitter_drbg_t *thread_tree_jitter_drbg =
    (struct tree_jitter_drbg_t *) entropy_source->state;

  if (global_tree_jitter_drbg == NULL || thread_tree_jitter_drbg == NULL) {
    goto out;
  }

  if (thread_reseed_calls != 0) {
    thread_tree_jitter_drbg->drbg.reseed_counter = thread_reseed_calls;
  }

  if (global_reseed_calls != 0) {
    global_tree_jitter_drbg->drbg.reseed_counter = global_reseed_calls;
  }

  ret = 1;

out:
  CRYPTO_STATIC_MUTEX_unlock_write(global_seed_drbg_lock_bss_get());
  return ret;
}

#endif // !defined(DISABLE_CPU_JITTER_ENTROPY)
