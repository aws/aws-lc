// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/rand.h>
#include <openssl/mem.h>
#include <openssl/ctrdrbg.h>
#include <openssl/type_check.h>

#include "new_rand_internal.h"
#include "internal.h"
#include "../../internal.h"
#include "../../ube/internal.h"

#include "new_rand_prefix.h"
#include "entropy/internal.h"

// rand_thread_state contains the per-thread state for the RNG.
struct rand_thread_local_state {
  // Thread-local CTR-DRBG state. UBE volatile state.
  CTR_DRBG_STATE drbg;

  // generate_calls_since_seed is the number of generate calls made on |drbg|
  // since it was last (re)seeded. Must be bounded by |kReseedInterval|.
  uint64_t generate_calls_since_seed;

  // reseed_calls_since_initialization is the number of reseed calls made of
  // |drbg| since its initialization.
  uint64_t reseed_calls_since_initialization;

  // generation_number caches the UBE generation number.
  uint64_t generation_number;

  // Entropy source. UBE volatile state.
  const struct entropy_source *entropy_source;
};

// rand_thread_local_state frees a |rand_thread_local_state|. This is called
// when a thread exits.
static void rand_thread_local_state_free(void *state_in) {

  struct rand_thread_local_state *state = state_in;
  if (state_in == NULL) {
    return;
  }

  // Potentially, something could kill the thread before an entropy source has
  // been associated to the thread-local randomness generator object.
  if (state->entropy_source != NULL) {
    state->entropy_source->cleanup();
  }

  OPENSSL_free(state);
}

// rand_ensure_valid_state determines whether |state| is in a valid state. The
// reasons are documented with inline comments in the function.
//
// Returns 1 if |state| is in a valid state and 0 otherwise.
static int rand_ensure_valid_state(struct rand_thread_local_state *state) {

  // We do not allow the UBE generation number to change while executing AWS-LC
  // randomness generation code e.g. while |RAND_bytes| executes. One way to hit
  // this error is if snapshotting the address space while executing
  // |RAND_bytes| and while snapsafe is active.
  uint64_t current_generation_number = 0;
  if (CRYPTO_get_ube_generation_number(&current_generation_number) == 1 &&
      current_generation_number != state->generation_number) {
    return 0;
  }

  return 1;
}

// rand_ensure_ctr_drbg_uniqueness computes whether |state| must be randomized
// to ensure uniqueness.
//
// Note: If |rand_ensure_ctr_drbg_uniqueness| returns 1 it does not necessarily
// imply that an UBE occurred. It can also mean that no UBE detection is
// supported or that UBE detection failed. In these cases, |state| must also be
// randomized to ensure uniqueness. Any special future cases can be handled in
// this function. 
//
// Return 1 if |state| must be randomized. 0 otherwise.
static int rand_ensure_ctr_drbg_uniqueness(struct rand_thread_local_state *state) {

  uint64_t current_generation_number = 0;
  if (CRYPTO_get_ube_generation_number(&current_generation_number) != 1) {
    return 1;
  }

  if (current_generation_number != state->generation_number) {
    state->generation_number = current_generation_number;
    return 1;
  }

  return 0;
}

// rand_maybe_get_ctr_drbg_pred_resistance maybe fills |pred_resistance| with
// |RAND_PRED_RESISTANCE_LEN| bytes. The bytes are sourced from the prediction
// resistance source from the entropy source in |state|, if such a source has
// been configured.
//
// |*pred_resistance_len| is set to 0 if no prediction resistance source is
// available and |RAND_PRED_RESISTANCE_LEN| otherwise.
static void rand_maybe_get_ctr_drbg_pred_resistance(
  const struct entropy_source *entropy_source,
  uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN],
  size_t *pred_resistance_len) {

  GUARD_PTR_ABORT(entropy_source);
  GUARD_PTR_ABORT(pred_resistance_len);

  *pred_resistance_len = 0;

  if (entropy_source->get_prediction_resistance != NULL) {
    if (entropy_source->get_prediction_resistance(pred_resistance) != 1) {
      abort();
    }
    *pred_resistance_len = RAND_PRED_RESISTANCE_LEN;
  }
}

// rand_get_ctr_drbg_seed_entropy source entropy for seeding and reseeding the
// CTR-DRBG state. Firstly, |seed| is filled with |CTR_DRBG_ENTROPY_LEN| bytes
// from the seed source configured in |entropy_source|. Secondly, if available,
// |CTR_DRBG_ENTROPY_LEN| bytes is filled into |personalization_string| sourced
// from the personalization string source configured in |entropy_source|.
//
// |*personalization_string_len| is set to 0 if no personalization string source
// is available and |CTR_DRBG_ENTROPY_LEN| otherwise.
static void rand_get_ctr_drbg_seed_entropy(
  const struct entropy_source *entropy_source,
  uint8_t seed[CTR_DRBG_ENTROPY_LEN],
  uint8_t personalization_string[CTR_DRBG_ENTROPY_LEN],
  size_t *personalization_string_len) {

  GUARD_PTR_ABORT(entropy_source);
  GUARD_PTR_ABORT(personalization_string_len);

  *personalization_string_len = 0;

  // If the seed source is missing it is impossible to source any entropy.
  if (entropy_source->get_seed(seed) != 1) {
    abort();
  }

  // Not all entropy source configurations will have a personalization string
  // source. Hence, it's optional. But use it if configured.
  if (entropy_source->get_personalization_string != NULL) {
    if(entropy_source->get_personalization_string(personalization_string) != 1) {
      abort();
    }
    *personalization_string_len = CTR_DRBG_ENTROPY_LEN;
  }
}

// rand_ctr_drbg_reseed reseeds the CTR-DRBG state in |state|.
static void rand_ctr_drbg_reseed(struct rand_thread_local_state *state) {

  GUARD_PTR_ABORT(state);

  uint8_t seed[CTR_DRBG_ENTROPY_LEN];
  uint8_t personalization_string[CTR_DRBG_ENTROPY_LEN];
  size_t personalization_string_len = 0;
  rand_get_ctr_drbg_seed_entropy(state->entropy_source, seed,
    personalization_string, &personalization_string_len);

  assert(personalization_string_len == 0 ||
         personalization_string_len == CTR_DRBG_ENTROPY_LEN);

  if (CTR_DRBG_reseed(&(state->drbg), seed, personalization_string,
        personalization_string_len) != 1) {
    abort();
  }

  state->reseed_calls_since_initialization++;
  state->generate_calls_since_seed = 0;

  OPENSSL_cleanse(seed, CTR_DRBG_ENTROPY_LEN);
  OPENSSL_cleanse(personalization_string, CTR_DRBG_ENTROPY_LEN);
}

// rand_state_initialize initializes the thread-local state |state|. In
// particular initializes the CTR-DRBG state with the initial seed material.
static void rand_state_initialize(struct rand_thread_local_state *state) {

  GUARD_PTR_ABORT(state);

  state->entropy_source = get_entropy_source();
  if (state->entropy_source == NULL) {
    abort();
  }

  uint8_t seed[CTR_DRBG_ENTROPY_LEN];
  uint8_t personalization_string[CTR_DRBG_ENTROPY_LEN];
  size_t personalization_string_len = 0;
  rand_get_ctr_drbg_seed_entropy(state->entropy_source, seed,
    personalization_string, &personalization_string_len);

  assert(personalization_string_len == 0 ||
         personalization_string_len == CTR_DRBG_ENTROPY_LEN);

  if (!CTR_DRBG_init(&(state->drbg), seed, personalization_string,
        personalization_string_len)) {
    abort();
  }

  state->reseed_calls_since_initialization = 0;
  state->generate_calls_since_seed = 0;
  state->generation_number = 0;

  OPENSSL_cleanse(seed, CTR_DRBG_ENTROPY_LEN);
  OPENSSL_cleanse(personalization_string, CTR_DRBG_ENTROPY_LEN);
}

// RAND_bytes_core generates |out_len| bytes of randomness and puts them in
// |out|. The CTR-DRBG state in |state| is managed to ensure uniqueness and
// usage requirements are met.
//
// The argument |use_user_pred_resistance| must be either
// |RAND_USE_USER_PRED_RESISTANCE| or |RAND_NO_USER_PRED_RESISTANCE|. The former
// cause the content of |user_pred_resistance| to be mixed in as prediction
// resistance. The latter ensures that |user_pred_resistance| is not used.
static void RAND_bytes_core(
  struct rand_thread_local_state *state,
  uint8_t *out, size_t out_len,
  const uint8_t user_pred_resistance[RAND_PRED_RESISTANCE_LEN],
  int use_user_pred_resistance) {

  GUARD_PTR_ABORT(state);
  GUARD_PTR_ABORT(out);

  // Ensure the CTR-DRBG state is unique.
  if (rand_ensure_ctr_drbg_uniqueness(state) == 1) {
    rand_ctr_drbg_reseed(state);
  }

  // If a prediction resistance source is available, use it.
  // Prediction resistance is only used on first invocation of the CTR-DRBG,
  // ensuring that its state is randomized before generating output.
  size_t first_pred_resistance_len = 0;
  uint8_t pred_resistance[RAND_PRED_RESISTANCE_LEN] = {0};
  rand_maybe_get_ctr_drbg_pred_resistance(state->entropy_source,
    pred_resistance, &first_pred_resistance_len);

  // If caller input user-controlled prediction resistance, use it.
  if (use_user_pred_resistance == RAND_USE_USER_PRED_RESISTANCE) {
    for (size_t i = 0; i < RAND_PRED_RESISTANCE_LEN; i++) {
      pred_resistance[i] ^= user_pred_resistance[i];
    }
    first_pred_resistance_len = RAND_PRED_RESISTANCE_LEN;
  }

  assert(first_pred_resistance_len == 0 ||
         first_pred_resistance_len == RAND_PRED_RESISTANCE_LEN);

  // Iterate CTR-DRBG generate until we |out_len| bytes of randomness have been
  // generated. CTR_DRBG_generate can maximally generate
  // |CTR_DRBG_MAX_GENERATE_LENGTH| bytes per usage of its state see
  // SP800-90A Rev 1 Table 3. If user requests more, we most generate output in
  // chunks and concatenate.
  while (out_len > 0) {
    size_t todo = out_len;

    if (todo > CTR_DRBG_MAX_GENERATE_LENGTH) {
      todo = CTR_DRBG_MAX_GENERATE_LENGTH;
    }

    // Each reseed interval can generate up to
    // |CTR_DRBG_MAX_GENERATE_LENGTH*kCtrDrbgReseedInterval| bytes.
    // Determining the time(s) to reseed prior to entering the CTR-DRBG generate
    // loop is a doable strategy. But tracking reseed times adds unnecessary
    // complexity. Instead our strategy is optimizing for simplicity.
    // |out_len < CTR_DRBG_MAX_GENERATE_LENGTH| will be the majority case
    // (by far) and requires a single check in either strategy.
    // Note if we already reseeded through |rand_ctr_drbg_reseed()|, we won't
    // reseed again here.
    if( state->generate_calls_since_seed + 1 >= kCtrDrbgReseedInterval) {
      rand_ctr_drbg_reseed(state);
    }

    if (!CTR_DRBG_generate(&(state->drbg), out, todo, pred_resistance,
          first_pred_resistance_len)) {
      abort();
    }

    out += todo;
    out_len -= todo;
    state->generate_calls_since_seed++;
    first_pred_resistance_len = 0;
  }

  OPENSSL_cleanse(pred_resistance, RAND_PRED_RESISTANCE_LEN);

  if (rand_ensure_valid_state(state) != 1) {
    abort();
  }
}

static void RAND_bytes_private(uint8_t *out, size_t out_len,
  const uint8_t user_pred_resistance[RAND_PRED_RESISTANCE_LEN],
  int use_user_pred_resistance) {

  if (out_len == 0) {
    return;
  }

  struct rand_thread_local_state *state =
      CRYPTO_get_thread_local(OPENSSL_THREAD_LOCAL_PRIVATE_RAND);

  if (state == NULL) {
    state = OPENSSL_zalloc(sizeof(struct rand_thread_local_state));
    if (state == NULL ||
        CRYPTO_set_thread_local(OPENSSL_THREAD_LOCAL_PRIVATE_RAND, state,
                                   rand_thread_local_state_free) != 1) {
      abort();
    }

    rand_state_initialize(state);
  }

  RAND_bytes_core(state, out, out_len, user_pred_resistance,
    use_user_pred_resistance);
}

// TOOD
// Retire and replace call sites with RAND_bytes_with_user_prediction_resistance
int NR_PREFIX(RAND_bytes_with_additional_data)(uint8_t *out, size_t out_len,
  const uint8_t user_pred_resistance[RAND_PRED_RESISTANCE_LEN]) {
  
  RAND_bytes_private(out, out_len, user_pred_resistance,
    RAND_USE_USER_PRED_RESISTANCE);
  return 1;
}

int RAND_bytes_with_user_prediction_resistance(uint8_t *out, size_t out_len,
  const uint8_t user_pred_resistance[RAND_PRED_RESISTANCE_LEN]) {
  
  RAND_bytes_private(out, out_len, user_pred_resistance,
    RAND_USE_USER_PRED_RESISTANCE);
  return 1;
}

int NR_PREFIX(RAND_bytes)(uint8_t *out, size_t out_len) {

  static const uint8_t kZeroPredResistance[RAND_PRED_RESISTANCE_LEN] = {0};
  RAND_bytes_private(out, out_len, kZeroPredResistance,
    RAND_NO_USER_PRED_RESISTANCE);
  return 1;
}

int NR_PREFIX(RAND_priv_bytes)(uint8_t *out, size_t out_len) {
  return NR_PREFIX(RAND_bytes)(out, out_len);
}

int NR_PREFIX(RAND_pseudo_bytes)(uint8_t *out, size_t out_len) {
  return NR_PREFIX(RAND_bytes)(out, out_len);
}

// Returns the number of generate calls made on the thread-local state since
// last seed/reseed. Returns 0 if thread-local state has not been initialized.
uint64_t get_thread_generate_calls_since_seed(void) {

  struct rand_thread_local_state *state =
      CRYPTO_get_thread_local(OPENSSL_THREAD_LOCAL_PRIVATE_RAND);
  if (state == NULL) {
    return 0;
  }

  return state->generate_calls_since_seed;
}

// Returns the number of reseed calls made on the thread-local state since
// initialization. Returns 0 if thread-local state has not been initialized.
uint64_t get_thread_reseed_calls_since_initialization(void) {

  struct rand_thread_local_state *state =
      CRYPTO_get_thread_local(OPENSSL_THREAD_LOCAL_PRIVATE_RAND);
  if (state == NULL) {
    return 0;
  }

  return state->reseed_calls_since_initialization;
}
