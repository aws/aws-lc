// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This implements the "KDF in Feedback Mode" described in section 4.2:
// https://csrc.nist.gov/publications/detail/sp/800-108/rev-1/final

#include <stdbool.h>

#include <openssl/hmac.h>
#include <openssl/kbkdf.h>

#include "../../internal.h"
#include "../service_indicator/internal.h"

static inline size_t ct_min(size_t a, size_t b) {
    crypto_word_t lt = constant_time_lt_w(a, b);
    return constant_time_select_w(lt, a, b);
}

static inline size_t ct_max(size_t a, size_t b) {
    crypto_word_t gt = constant_time_ge_w(a, b);
    return constant_time_select_w(gt, a, b);
}

#ifndef BYTEBITS
#define BYTEBITS 8
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
// buffer, |context| is optional. The |iv| is also optional. If you omit these,
// you must pass NULL and a length of 0.
OPENSSL_EXPORT int KBKDF_feedback(uint8_t *out_key, size_t out_len,
                                  const EVP_MD *digest,
                                  const uint8_t *key_in, size_t key_in_len,
                                  const uint8_t *label, size_t label_len,
                                  const uint8_t *context, size_t context_len,
                                  const uint8_t *iv, size_t iv_len,
                                  bool use_counter)
{
    // Sanity checking.
    if (out_key == NULL || digest == NULL || key_in == NULL ||
        out_len < 1 || key_in_len < 1 ||
        (key_in == NULL && key_in_len > 0) ||
        (label == NULL && label_len > 0) ||
        (context == NULL && context_len > 0) ||
        (iv == NULL && iv_len > 0)) {
        return 0;
    }

    // The horrible variable names below (ki, L, h, i, n) are all courtesy of
    // SP800-108r1.
    int retval = 0;
    uint8_t *ki = NULL;

    // We have to avoid the underlying HMAC services updating the indicator
    // state, so we lock the state here.
    FIPS_service_indicator_lock_state();

    HMAC_CTX hmac;
    HMAC_CTX_init(&hmac);
    if (!HMAC_Init_ex(&hmac, key_in, key_in_len, digest, NULL)) {
        goto out;
    }

    size_t L = out_len * BYTEBITS;

    size_t hmac_size = HMAC_size(&hmac);
    size_t h = hmac_size * BYTEBITS;
    uint32_t i = 0;
    // r = sizeof(i) * BYTEBITS is listed as a parameter in SP800-108r1,
    // specified when a counter is used as input. It's not actually used in
    // the KDF in Feedback Mode algorithm though.
    uint8_t zero = 0x00;

    size_t n = 1 + ((L - 1) / h);  // ceil(L/h)

    if (n > UINT32_MAX) {
        // SP 800-108r1 section 4.0, n <= 2^r - 1
        goto out;
    }

    ki = OPENSSL_malloc(ct_max(iv_len, hmac_size));
    if (ki == NULL) {
        OPENSSL_PUT_ERROR(CRYPTO, ERR_R_MALLOC_FAILURE);
        goto out;
    }
    size_t ki_len = key_in_len;
    if (iv != NULL && iv_len > 0) {
        // Set k(0) to the IV.
        OPENSSL_memcpy(ki, iv, iv_len);
        ki_len = iv_len;
    }

    size_t written = 0;
    size_t to_write = out_len;

    for (i = 1; i <= n; i++) {
        if (!(i == 1 && iv_len == 0)) {
            // If no IV was specified, we don't include k(0).
            if (!HMAC_Update(&hmac, ki, ki_len)) {
                goto out;
            }
        }
        if (use_counter) {
            uint32_t be_i = CRYPTO_bswap4(i);
            if(!HMAC_Update(&hmac, (const uint8_t *)&be_i, sizeof(be_i))) {
                goto out;
            }
        }
        if (!HMAC_Update(&hmac, label, label_len)) {
            goto out;
        }
        // The current iteration's ki data is generated via:
        //
        // ki = PRF(key_in, previous ki || i || Label || 0x00 || Context || L)
        //
        // The test data from the CAVP Testing: SP 800-108 Key Derivation Using
        // Pseudorandom Functions - Key-Based (KBKDF) page
        // https://csrc.nist.gov/Projects/cryptographic-algorithm-validation-program/key-derivation
        // provides fully-formed fixed data, so we don't use the NUL byte,
        // Context, or L when working with pre-configured fixed data.
        //
        // The spec doesn't indicate whether L should be appended in big-endian
        // format, or how large (in bits) it should be. This is copying the
        // implementation found in OpenSSL 3.x, which just appends the full
        // size value in host format (little-endian in AWS-LC's case).
        if (context != NULL && context_len > 0) {
            if (!HMAC_Update(&hmac, &zero, sizeof(zero)) ||
                !HMAC_Update(&hmac, context, context_len) ||
                !HMAC_Update(&hmac, (const uint8_t *)&L, sizeof(L))) {
                goto out;
            }
        }

        ki_len = hmac_size;
        if (!HMAC_Final(&hmac, ki, (unsigned int *)&ki_len)) {
            goto out;
        }

        size_t this_write = ct_min(ki_len, to_write);
        if (written + this_write > out_len) {
            // Double-check buffer bounds.
            this_write = out_len - written;
        }
        OPENSSL_memcpy(out_key + written, ki, this_write);
        written += this_write;
        to_write -= this_write;

        if (to_write > 0) {
            // Reset HMAC.
            if (!HMAC_Init_ex(&hmac, key_in, key_in_len, digest, NULL)) {
                goto out;
            }
        }
    }

    retval = 1;

out:
    FIPS_service_indicator_unlock_state();
    if (retval) {
        KBKDF_verify_service_indicator(digest);
    }

    OPENSSL_free(ki);
    HMAC_CTX_cleanse(&hmac);

    return retval;
}
