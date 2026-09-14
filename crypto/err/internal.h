// Copyright (c) 2017, Google Inc.
// SPDX-License-Identifier: ISC

#ifndef OPENSSL_HEADER_CRYPTO_ERR_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_ERR_INTERNAL_H

#include <openssl/err.h>

#if defined(__cplusplus)
extern "C" {
#endif


// Private error queue functions.

// ERR_SAVE_STATE contains a saved representation of the error queue. It is
// slightly more compact than |ERR_STATE| as the error queue will typically not
// contain |ERR_NUM_ERRORS| entries.
typedef struct err_save_state_st ERR_SAVE_STATE;

// ERR_SAVE_STATE_free releases all memory associated with |state|.
OPENSSL_EXPORT void ERR_SAVE_STATE_free(ERR_SAVE_STATE *state);

// ERR_save_state returns a newly-allocated |ERR_SAVE_STATE| structure
// containing the current state of the error queue or NULL on allocation
// error. It should be released with |ERR_SAVE_STATE_free|.
OPENSSL_EXPORT ERR_SAVE_STATE *ERR_save_state(void);

// ERR_restore_state clears the error queue and replaces it with |state|. Marks
// are not part of a saved state: they are neither captured nor restored.
OPENSSL_EXPORT void ERR_restore_state(const ERR_SAVE_STATE *state);

// ERR_num_errors returns the number of errors in the current thread's error
// queue. The queue is a ring holding |ERR_NUM_ERRORS| - 1 entries, so the count
// saturates there and further errors evict the oldest.
OPENSSL_EXPORT size_t ERR_num_errors(void);

// ERR_pop_to_count removes errors from the top of the current thread's error
// queue until at most |count| remain, normally a count taken with
// |ERR_num_errors| before running code whose errors are to be discarded.
//
// It drops those errors without disturbing what the caller had queued: unlike
// |ERR_clear_error| and |ERR_restore_state| it leaves the surviving entries and
// the pointer from the last |ERR_get_error_line_data| alone, and unlike
// |ERR_pop_to_mark| it needs no entry to mark, so it works on an empty queue and
// leaves a caller's mark as it found it.
//
// It only removes entries, so it recovers nothing the code in between destroyed.
// Errors a nested |ERR_clear_error| may wipe, as when an |SSL| I/O call is
// reentered, still need |ERR_save_state| and |ERR_restore_state|. Likewise, if
// the queue saturates in between, the evicted entries are gone and |count| no
// longer marks where the new errors begin.
OPENSSL_EXPORT void ERR_pop_to_count(size_t count);

// ERR_suppress_errors_begin makes the current thread's error queue reject new
// errors until the matching |ERR_suppress_errors_end|. Use it around
// best-effort work whose failures are not the caller's business.
//
// The queue is left bit-for-bit as it was found, so the caller keeps its
// entries, its marks, and the pointer from its last |ERR_get_error_line_data|.
// Rejecting the errors is what makes that hold once the queue saturates, where
// every new error evicts one of the caller's and trimming the queue afterward
// cannot bring an evicted entry back.
//
// Scopes nest, and errors raised outside them are unaffected. Errors a nested
// |ERR_clear_error| may wipe, as when an |SSL| I/O call is reentered, still need
// |ERR_save_state| and |ERR_restore_state|.
OPENSSL_EXPORT void ERR_suppress_errors_begin(void);

// ERR_suppress_errors_end ends the innermost |ERR_suppress_errors_begin| scope.
OPENSSL_EXPORT void ERR_suppress_errors_end(void);


#if defined(__cplusplus)
}  // extern C

extern "C++" {

BSSL_NAMESPACE_BEGIN

BORINGSSL_MAKE_DELETER(ERR_SAVE_STATE, ERR_SAVE_STATE_free)

BSSL_NAMESPACE_END

}  // extern C++
#endif

#endif  // OPENSSL_HEADER_CRYPTO_ERR_INTERNAL_H
