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
#include "../delocate.h"

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

  // Backward and forward references to nodes in a double-linked list.
  struct rand_thread_local_state *next;
  struct rand_thread_local_state *previous;

  // Lock used when globally clearing (zeroising) all thread-local states at
  // process exit.
  CRYPTO_MUTEX state_clear_lock;
};

DEFINE_BSS_GET(struct rand_thread_local_state *, thread_states_list_head)
DEFINE_STATIC_MUTEX(thread_states_list_lock)

// At process exit not all threads will be scheduled and proper exited. To
// ensure no secret state is left, globally clear all thread-local states. This
// is a FIPS derived requirement: SSPs must be cleared.
//
// This is problematic because a thread might be scheduled and return
// randomness from a non-valid state. The linked application should obviously
// arrange that all threads are gracefully exited before existing the process.
// Yet, in cases where such graceful exit does not happen we ensure that no
// output can be returned by locking all thread-local states and deliberately
// not releasing the lock. A synchronization step in the core randomness
// generation routines (|RAND_bytes_core|) then ensures that no randomness
// generation can occur after a thread-local state has been locked. It also
// ensures |rand_thread_local_state_free| cannot free any thread state while we
// own the lock.
static void rand_thread_local_state_clear_all(void) __attribute__((destructor));
static void rand_thread_local_state_clear_all(void) {
  CRYPTO_STATIC_MUTEX_lock_write(thread_states_list_lock_bss_get());
  for (struct rand_thread_local_state *state = *thread_states_list_head_bss_get();
    state != NULL; state = state->next) {
    CRYPTO_MUTEX_lock_write(&state->state_clear_lock);
    CTR_DRBG_clear(&state->drbg);
  }
}

static void thread_local_list_delete_node(
  struct rand_thread_local_state *node_delete) {

  // Mutating the global linked list. Need to synchronize over all threads.
  CRYPTO_STATIC_MUTEX_lock_write(thread_states_list_lock_bss_get());
  struct rand_thread_local_state *node_head = *thread_states_list_head_bss_get();

  // We have [node_delete->previous] <--> [node_delete] <--> [node_delete->next]
  // and must end up with [node_delete->previous] <--> [node_delete->next]
  if (node_head == node_delete) {
    // If node node_delete is the head, we know that the backwards reference
    // does not exist but we need to update the head pointer.
    *thread_states_list_head_bss_get() = node_delete->next;
  } else {
    // On the other hand, if node_delete is not the head, then we need to update
    // the node node_delete->previous to point to the node node_delete->next.
    // But only if node_delete->previous actually exists.
    if (node_delete->previous != NULL) {
      (node_delete->previous)->next = node_delete->next;
    }
  }

  // Now [node_delete->previous] --> [node_delete->next]
  //                                          |
  //                         [node_delete] <--|
  // Final thing to do is to update the backwards reference for the node
  // node_delete->next, if it exists.
  if (node_delete->next != NULL) {
    // If node_delete is the head, then node_delete->previous is NULL. But that
    // is OK because node_delete->next is the new head and should therefore have
    // a backwards reference that is NULL.
    (node_delete->next)->previous = node_delete->previous;
  }

  CRYPTO_STATIC_MUTEX_unlock_write(thread_states_list_lock_bss_get());
}

// thread_local_list_add adds the state |node_add| to the linked list. Note that
// |node_add| is not added at the end of the linked list, but is replacing the
// current head to avoid having to run through the entire linked list to add.
static void thread_local_list_add_node(
  struct rand_thread_local_state **node_add) {

  struct rand_thread_local_state *node_add_p = *node_add;

  // node_add will be the new head and will not have a backwards reference.
  node_add_p->previous = NULL;

  // Mutating the global linked list. Need to synchronize over all threads.
  CRYPTO_STATIC_MUTEX_lock_write(thread_states_list_lock_bss_get());

  // First get a reference to the pointer of the head of the linked list.
  // That is, the pointer to the head node node_head is *thread_states_list.
  struct rand_thread_local_state **thread_states_list = thread_states_list_head_bss_get();

  // We have [node_head] <--> [node_head->next] and must end up with
  // [node_add] <--> [node_head] <--> [node_head->next]
  // First make the forward reference
  node_add_p->next = *thread_states_list;

  // Only add a backwards reference if a head already existed (this might be
  // the first add).
  if (node_add_p->next != NULL) {
    (node_add_p->next)->previous = node_add_p;
  }

  // The last thing is to assign the new head.
  *thread_states_list = node_add_p;

  CRYPTO_STATIC_MUTEX_unlock_write(thread_states_list_lock_bss_get());
}

// rand_thread_local_state frees a |rand_thread_local_state|. This is called
// when a thread exits.
static void rand_thread_local_state_free(void *state_in) {

  struct rand_thread_local_state *state = state_in;
  if (state_in == NULL) {
    return;
  }

  thread_local_list_delete_node(state);

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
  CRYPTO_MUTEX_init(&state->state_clear_lock);

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

    // Synchronize with |rand_thread_local_state_clear_all|. In cases a
    // thread-local has been cleared, thread execution will block here because
    // there is no secure way to generate randomness from the state.
    // Note that this lock is thread-local and therefore not contended except at
    // process exit. Furthermore, even though the lock-unlock is under the
    // loop iteration, practically all request sizes (i.e. the value
    // of |out_len|), will be strictly less than |CTR_DRBG_MAX_GENERATE_LENGTH|.
    // Hence, practically, only one lock-unlock rotation will be required.
    //
    // Locks are located here to not acquire any locks while we might perform
    // system calls (e.g. when sourcing OS entropy). This shields against known
    // bugs. For example, glibc can implement locks using memory transactions on
    // powerpc that has been observed to break when reaching |getrandom| through
    // |syscall|. For this, see
    // https://github.com/google/boringssl/commit/17ce286e0792fc2855fb7e34a968bed17ae914af
    // https://www.kernel.org/doc/Documentation/powerpc/transactional_memory.txt
    //
    // Clearing the thread-local state will only zeroise the DRBG state. It's
    // not a valid state to generate output. We can keep operating on it without
    // issues (e.g. source entropy and reseed). No output will ever be generated
    // from the invalid state since we block here.
    CRYPTO_MUTEX_lock_read(&state->state_clear_lock);
    if (!CTR_DRBG_generate(&(state->drbg), out, todo, pred_resistance,
          first_pred_resistance_len)) {
      abort();
    }
    CRYPTO_MUTEX_unlock_read(&state->state_clear_lock);

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
    thread_local_list_add_node(&state);
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
