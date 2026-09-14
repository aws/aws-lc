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
