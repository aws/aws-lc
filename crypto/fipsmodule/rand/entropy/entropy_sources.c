// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/mem.h>
#include <openssl/target.h>

#include "internal.h"
#include "../internal.h"
#include "../../delocate.h"
#include "../../../rand_extra/internal.h"
#include "../../../ube/vm_ube_detect.h"

#if !defined(DISABLE_CPU_JITTER_ENTROPY)
#include "../../../../third_party/jitterentropy/jitterentropy-library/jitterentropy.h"
#endif

DEFINE_BSS_GET(const struct entropy_source_methods *, entropy_source_methods_override)
DEFINE_BSS_GET(int, allow_entropy_source_methods_override)
DEFINE_STATIC_MUTEX(global_entropy_source_lock)

static int entropy_cpu_get_entropy_multiple8(uint8_t *entropy, size_t entropy_len) {
#if defined(OPENSSL_X86_64)
  if (rdrand_multiple8(entropy, entropy_len) == 1) {
    return 1;
  }
#elif defined(OPENSSL_AARCH64)
  if (rndr_multiple8(entropy, entropy_len) == 1) {
    return 1;
  }
#endif
  return 0;
}

static int entropy_cpu_get_extra_entropy(
  const struct entropy_source_t *entropy_source,
  uint8_t extra_entropy[CTR_DRBG_ENTROPY_LEN]) {
  return entropy_cpu_get_entropy_multiple8(extra_entropy, CTR_DRBG_ENTROPY_LEN);
}

#if !defined(DISABLE_CPU_JITTER_ENTROPY)

static int entropy_cpu_get_prediction_resistance(
  const struct entropy_source_t *entropy_source,
  uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN]) {
  return entropy_cpu_get_entropy_multiple8(pred_resistance, RAND_PRED_RESISTANCE_LEN);
}

static int entropy_os_get_extra_entropy(
  const struct entropy_source_t *entropy_source,
  uint8_t extra_entropy[CTR_DRBG_ENTROPY_LEN]) {
  CRYPTO_sysrand(extra_entropy, CTR_DRBG_ENTROPY_LEN);
  return 1;
}

// The provider owns the source transition, not the tree or its method table.
// Collector nullness alone cannot identify the source: Jitter's safe reader
// may free the collector on failure before the provider chooses a fallback.
enum tree_root_source { TREE_ROOT_JITTER, TREE_ROOT_OS };

struct tree_root_state {
  struct rand_data *collector;
  enum tree_root_source active_source;
};

static void tree_root_cleanup(struct tree_root_entropy_source *source) {
  struct tree_root_state *state = source->state;
  if (state != NULL) {
    jent_entropy_collector_free(state->collector);
    OPENSSL_free(state);
    source->state = NULL;
  }
}

static int tree_root_is_cpu_jitter(const struct tree_root_entropy_source *source) {
  const struct tree_root_state *state = source->state;
  return state != NULL && state->active_source == TREE_ROOT_JITTER;
}

#if defined(BORINGSSL_FIPS)

// Required-Jitter policy: preserve the default OSR, flags, and three-attempt
// retry sequence. This provider never uses OS entropy; it reports failure and
// the tree aborts.
static int required_jitter_root_initialize(
    struct tree_root_entropy_source *source) {
  struct tree_root_state *state = OPENSSL_zalloc(sizeof(struct tree_root_state));
  if (state == NULL) {
    return 0;
  }
  source->state = state;
  state->active_source = TREE_ROOT_JITTER;
  // An oversampling rate of 0 selects the Jitter library's default.
  state->collector = jent_entropy_collector_alloc(0, JENT_FORCE_FIPS);
  if (state->collector == NULL) {
    tree_root_cleanup(source);
    return 0;
  }
  return 1;
}

static int required_jitter_root_get_seed(struct tree_root_entropy_source *source,
                                       uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
  struct tree_root_state *state = source->state;
  if (state->collector == NULL) {
    return 0;
  }

  // |jent_read_entropy| has a false positive health test failure rate of
  // 2^-22, so retry with a new collector at the same OSR.
  for (size_t i = 0; i < ENTROPY_JITTER_MAX_NUM_TRIES; i++) {
    ssize_t ret =
      jent_read_entropy(state->collector, (char *)seed, CTR_DRBG_ENTROPY_LEN);
    if (ret == (ssize_t)CTR_DRBG_ENTROPY_LEN) {
      return 1;
    }
    jent_entropy_collector_free(state->collector);
    state->collector = jent_entropy_collector_alloc(0, JENT_FORCE_FIPS);
    if (state->collector == NULL) {
      return 0;
    }
  }
  return 0;
}

#else

// Test hooks exist only in non-FIPS builds; see |tree_jitter_test_hooks|.
DEFINE_BSS_GET(const struct tree_jitter_test_hooks *, tree_jitter_test_hooks)

OPENSSL_STATIC_ASSERT(TREE_JITTER_MAX_OSR >= JENT_MIN_OSR,
  TREE_JITTER_MAX_OSR_must_be_at_least_JENT_MIN_OSR)

// Pinning the memory size at the library default prevents the safe reader
// from increasing memory usage as it raises the oversampling rate.
#define TREE_JITTER_JENT_FLAGS (JENT_FORCE_FIPS | JENT_MAX_MEMSIZE_128kB)

static struct rand_data *tree_root_collector_alloc(unsigned int osr,
                                                 unsigned int flags) {
  const struct tree_jitter_test_hooks *hooks = *tree_jitter_test_hooks_bss_get();
  return hooks != NULL ? hooks->collector_alloc(osr, flags)
                       : jent_entropy_collector_alloc(osr, flags);
}

static struct rand_data *adaptive_jitter_collector_alloc(void) {
  const struct tree_jitter_test_hooks *hooks = *tree_jitter_test_hooks_bss_get();
  int (*power_up)(unsigned int, unsigned int) =
    hooks != NULL ? hooks->power_up : jent_entropy_init_ex;
  for (unsigned int osr = JENT_MIN_OSR; osr <= TREE_JITTER_MAX_OSR; osr++) {
    int ret = power_up(osr, TREE_JITTER_JENT_FLAGS);
    if (ret == 0) {
      return tree_root_collector_alloc(osr, TREE_JITTER_JENT_FLAGS);
    }
    if (ret != EHEALTH && ret != ERCT && ret != EMINVARVAR) {
      break;
    }
  }
  return NULL;
}

// Jitter-with-OS-fallback policy: use adaptive Jitter while it works, then
// irrevocably select OS entropy for this process's tree root. Personalization
// and prediction-resistance sources do not change when the root transitions.
static int jitter_with_os_fallback_root_initialize(
    struct tree_root_entropy_source *source) {
  struct tree_root_state *state = OPENSSL_zalloc(sizeof(struct tree_root_state));
  if (state == NULL) {
    return 0;
  }
  source->state = state;
  state->collector = adaptive_jitter_collector_alloc();
  state->active_source =
    state->collector != NULL ? TREE_ROOT_JITTER : TREE_ROOT_OS;
  return 1;
}

static int jitter_with_os_fallback_root_get_seed(
    struct tree_root_entropy_source *source,
    uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
  struct tree_root_state *state = source->state;
  if (state->active_source == TREE_ROOT_JITTER) {
    const struct tree_jitter_test_hooks *hooks = *tree_jitter_test_hooks_bss_get();
    ssize_t ret = hooks != NULL
      ? hooks->read_entropy(&state->collector, seed)
      : jent_read_entropy_safe(&state->collector, (char *)seed, CTR_DRBG_ENTROPY_LEN);
    if (ret == (ssize_t)CTR_DRBG_ENTROPY_LEN) {
      return 1;
    }
    // The safe reader may already have freed and cleared the collector.
    jent_entropy_collector_free(state->collector);
    state->collector = NULL;
    state->active_source = TREE_ROOT_OS;
  }

  // Discard all output from a failed Jitter read, including a partial prefix.
  CRYPTO_sysrand(seed, CTR_DRBG_ENTROPY_LEN);
  return 1;
}

#endif  // BORINGSSL_FIPS

// Bind the complete frontend configuration and its root provider together.
// This is the only build-mode choice for tree entropy. Both configurations use
// OS personalization and hardware prediction resistance when available; only
// the explicitly named composite configuration permits root-source fallback.
struct tree_entropy_configuration {
  struct entropy_source_methods source;
  struct tree_root_entropy_source_methods root;
};

DEFINE_LOCAL_DATA(struct tree_entropy_configuration, tree_entropy_configuration) {
  out->source.initialize = tree_jitter_initialize;
  out->source.zeroize_thread = tree_jitter_zeroize_thread_drbg;
  out->source.free_thread = tree_jitter_free_thread_drbg;
  out->source.get_seed = tree_jitter_get_seed;
  out->source.get_extra_entropy = entropy_os_get_extra_entropy;
  out->source.get_prediction_resistance =
    (have_hw_rng_x86_64() == 1 || have_hw_rng_aarch64() == 1)
      ? entropy_cpu_get_prediction_resistance : NULL;
  out->root.cleanup = tree_root_cleanup;
  out->root.is_cpu_jitter = tree_root_is_cpu_jitter;
#if defined(BORINGSSL_FIPS)
  out->source.id = TREE_DRBG_JITTER_ENTROPY_SOURCE;
  out->root.initialize = required_jitter_root_initialize;
  out->root.get_seed = required_jitter_root_get_seed;
#else
  out->source.id = TREE_DRBG_JITTER_WITH_OS_FALLBACK_ENTROPY_SOURCE;
  out->root.initialize = jitter_with_os_fallback_root_initialize;
  out->root.get_seed = jitter_with_os_fallback_root_get_seed;
#endif
}

const struct tree_root_entropy_source_methods *
get_tree_root_entropy_source_methods(void) {
  return &tree_entropy_configuration()->root;
}

void tree_jitter_get_root_seed_FOR_TESTING(struct rand_data **jitter_ec,
                                        uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
  struct tree_root_state state = {
    *jitter_ec, *jitter_ec != NULL ? TREE_ROOT_JITTER : TREE_ROOT_OS};
  struct tree_root_entropy_source source = {
    &state, get_tree_root_entropy_source_methods()};
  if (!source.methods->get_seed(&source, seed)) {
    abort();
  }
  *jitter_ec = state.collector;
}

#if !defined(BORINGSSL_FIPS)
void tree_jitter_set_hooks_FOR_TESTING(const struct tree_jitter_test_hooks *hooks) {
  *tree_jitter_test_hooks_bss_get() = hooks;
}
#endif

#endif  // !defined(DISABLE_CPU_JITTER_ENTROPY)

static int opt_out_cpu_jitter_initialize(
  struct entropy_source_t *entropy_source) {
  return 1;
}

static void opt_out_cpu_jitter_zeroize_thread(struct entropy_source_t *entropy_source) {}

static void opt_out_cpu_jitter_free_thread(struct entropy_source_t *entropy_source) {}

static int opt_out_cpu_jitter_get_seed_wrap(
  const struct entropy_source_t *entropy_source, uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
  return vm_ube_fallback_get_seed(seed);
}

// Define conditions for not using CPU Jitter
static int is_vm_ube_environment(void) {
  return CRYPTO_get_vm_ube_supported();
}

static int has_explicitly_opted_out_of_cpu_jitter(void) {
#if defined(DISABLE_CPU_JITTER_ENTROPY)
  return 1;
#else
  return 0;
#endif
}

static int use_opt_out_cpu_jitter_entropy(void) {
  if (has_explicitly_opted_out_of_cpu_jitter() == 1 ||
      is_vm_ube_environment() == 1) {
    return 1;
  }
  return 0;
}

// Out-out CPU Jitter configurations. CPU source required for rule-of-two.
// - OS as seed source source.
// - Uses rdrand or rndr, if supported, for personalization string. Otherwise
// falls back to OS source.
DEFINE_LOCAL_DATA(struct entropy_source_methods, opt_out_cpu_jitter_entropy_source_methods) {
  out->initialize = opt_out_cpu_jitter_initialize;
  out->zeroize_thread = opt_out_cpu_jitter_zeroize_thread;
  out->free_thread = opt_out_cpu_jitter_free_thread;
  out->get_seed = opt_out_cpu_jitter_get_seed_wrap;
  if (have_hw_rng_x86_64() == 1 ||
      have_hw_rng_aarch64() == 1) {
    out->get_extra_entropy = entropy_cpu_get_extra_entropy;
  } else {
    // Fall back to seed source because a second source must always be present.
    out->get_extra_entropy = opt_out_cpu_jitter_get_seed_wrap;
  }
  out->get_prediction_resistance = NULL;
  out->id = OPT_OUT_CPU_JITTER_ENTROPY_SOURCE;
}

static const struct entropy_source_methods * get_entropy_source_methods(void) {
  if (*allow_entropy_source_methods_override_bss_get() == 1) {
    return *entropy_source_methods_override_bss_get();
  }

  if (use_opt_out_cpu_jitter_entropy()) {
    return opt_out_cpu_jitter_entropy_source_methods();
  }

#if !defined(DISABLE_CPU_JITTER_ENTROPY)
  return &tree_entropy_configuration()->source;
#else
  return opt_out_cpu_jitter_entropy_source_methods();
#endif
}

struct entropy_source_t * get_entropy_source(void) {

  struct entropy_source_t *entropy_source = OPENSSL_zalloc(sizeof(struct entropy_source_t));
  if (entropy_source == NULL) {
    return NULL;
  }

  entropy_source->methods = get_entropy_source_methods();

  // Make sure that the function table contains the minimal number of callbacks
  // that we expect. Also make sure that the entropy source is initialized such
  // that calling code can assume that.
  if (entropy_source->methods == NULL ||
      entropy_source->methods->zeroize_thread == NULL ||
      entropy_source->methods->free_thread == NULL ||
      entropy_source->methods->get_seed == NULL ||
      entropy_source->methods->initialize == NULL ||
      entropy_source->methods->initialize(entropy_source) != 1) {
    OPENSSL_free(entropy_source);
    return NULL;
  }

  return entropy_source;
}

// hw_rng_multiple8_func is the type of a hardware rng wrapper such as
// |CRYPTO_rndr_multiple8| and |CRYPTO_rdrand_multiple8|. It writes |len| bytes
// to |buf| and returns 1 on success, 0 otherwise.
typedef int (*hw_rng_multiple8_func)(uint8_t *buf, size_t len);

// hw_rng_multiple8_with_retry validates |len| and then calls |hw_rng| until it
// succeeds or |max_attempts| calls have been made. |max_attempts| must be
// positive.
// A hardware rng wrapper will typically execute the underlying instruction
// multiple times and a failing call can therefore leave a prefix of |buf|
// written. This is not an issue, because the retry re-generates the entire
// |buf| and the contents of |buf| are only consumed on success. Retrying the
// entire request, instead of only the failed instruction execution, is easier
// to implement on the C-level and it should be a very rare event.
// Outputs 1 on success, 0 otherwise.
static int hw_rng_multiple8_with_retry(hw_rng_multiple8_func hw_rng,
  uint8_t *buf, size_t len, size_t max_attempts) {

  if (len == 0 || ((len & 0x7) != 0)) {
    return 0;
  }

  for (size_t attempts = 0; attempts < max_attempts; attempts++) {
    if (hw_rng(buf, len) == 1) {
      return 1;
    }
  }

  return 0;
}

int hw_rng_multiple8_with_retry_FOR_TESTING(
  int (*hw_rng)(uint8_t *buf, size_t len), uint8_t *buf, size_t len,
  size_t max_attempts) {
  return hw_rng_multiple8_with_retry(hw_rng, buf, len, max_attempts);
}

// rndr_multiple8 should only be called if |have_hw_rng_aarch64| returned true.
int rndr_multiple8(uint8_t *buf, const size_t len) {
  return hw_rng_multiple8_with_retry(CRYPTO_rndr_multiple8, buf, len,
                                     RNDR_MAX_ATTEMPTS);
}

int have_hw_rng_aarch64_for_testing(void) {
  return have_hw_rng_aarch64();
}

// rdrand_multiple8 should only be called if |have_hw_rng_x86_64| returned true.
int rdrand_multiple8(uint8_t *buf, size_t len) {
  return hw_rng_multiple8_with_retry(CRYPTO_rdrand_multiple8, buf, len,
                                     RDRAND_MAX_ATTEMPTS);
}

int have_hw_rng_x86_64_for_testing(void) {
  return have_hw_rng_x86_64();
}

void override_entropy_source_method_FOR_TESTING(
  const struct entropy_source_methods *override_entropy_source_methods) {

  CRYPTO_STATIC_MUTEX_lock_write(global_entropy_source_lock_bss_get());
  *allow_entropy_source_methods_override_bss_get() = 1;
  *entropy_source_methods_override_bss_get() = override_entropy_source_methods;
  CRYPTO_STATIC_MUTEX_unlock_write(global_entropy_source_lock_bss_get());
}

int entropy_source_uses_cpu_jitter(void) {
  // Do not hold the configuration lock while acquiring the tree lock.
  CRYPTO_STATIC_MUTEX_lock_read(global_entropy_source_lock_bss_get());
  int id = get_entropy_source_methods()->id;
  CRYPTO_STATIC_MUTEX_unlock_read(global_entropy_source_lock_bss_get());
  if (id == OPT_OUT_CPU_JITTER_ENTROPY_SOURCE) {
    return 0;
  }
  if (id == TREE_DRBG_JITTER_ENTROPY_SOURCE ||
      id == TREE_DRBG_JITTER_WITH_OS_FALLBACK_ENTROPY_SOURCE) {
    return tree_jitter_root_is_cpu_jitter();
  }
  return 1;
}

int get_entropy_source_method_id_FOR_TESTING(void) {
  int id;
  CRYPTO_STATIC_MUTEX_lock_read(global_entropy_source_lock_bss_get());
  const struct entropy_source_methods *entropy_source_method = get_entropy_source_methods();
  id = entropy_source_method->id;
  CRYPTO_STATIC_MUTEX_unlock_read(global_entropy_source_lock_bss_get());
  return id;
}
