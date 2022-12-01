// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_HEADER_KBKDF_H
#define AWSLC_HEADER_KBKDF_H

#include <openssl/base.h>

#include <stdbool.h>

#if defined(__cplusplus)
extern "C" {
#endif

// Key-Based Key Derivation Function (KBKDF) in Feedback mode from NIST SP
// 800-108:
// https://csrc.nist.gov/publications/detail/sp/800-108/rev-1/final
//
// Generates |out_len| bytes of keying material from |key_in|, |label|,
// |context|, and |iv| using the given |digest|, and outputs the result to
// |out_key|. It returns one on success and zero on error.
//
// The |use_counter| option enables the "KDF in Feedback Mode with Counter"
// mode.
//
// If your fixed-input data (|label| and |context|) are provided as a single
// buffer formatted according to your protocol, |context| is optional. The |iv|
// is also optional. If you omit these, you must pass NULL and a length of 0.
OPENSSL_EXPORT int KBKDF_feedback(uint8_t *out_key, size_t out_len,
                                  const EVP_MD *digest,
                                  const uint8_t *key_in, size_t key_in_len,
                                  const uint8_t *label, size_t label_len,
                                  const uint8_t *context, size_t context_len,
                                  const uint8_t *iv, size_t iv_len,
                                  bool use_counter);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // AWSLC_HEADER_KBKDF_H
