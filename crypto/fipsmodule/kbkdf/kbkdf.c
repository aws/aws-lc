// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This implements the "KDF in Feedback Mode" described in section 4.2:
// https://csrc.nist.gov/publications/detail/sp/800-108/rev-1/final

#include <stdbool.h>

#include <openssl/hmac.h>
#include <openssl/kbkdf.h>

#include "../../internal.h"
#include "../service_indicator/internal.h"

// Convert a 32-bit little-endian value into a 32-bit big-endian value.
// AWS-LC only supports little-endian hosts.
static uint32_t to_be32(uint32_t host)
{
    uint32_t value = 0;

    value |= (host & 0xff000000) >> 24;
    value |= (host & 0x00ff0000) >> 8;
    value |= (host & 0x0000ff00) << 8;
    value |= (host & 0x000000ff) << 24;

    return value;
}

// Surprised min32/min64/etc. didn't end up in stdint.h...
static inline size_t min(size_t a, size_t b) {
    return a < b ? a : b;
}

static inline size_t max(size_t a, size_t b) {
    return a > b ? a : b;
}

#ifndef BYTEBITS
#define BYTEBITS 8
#endif

// Generates |out_len| bytes of keying material from |key_in|, |label|,
// |context|, and |iv| using the given |digest|, and outputs the result to
// |out_key|. It returns one on success and zero on error.
//
// The |use_counter| option enables the "KDF in Feedback Mode with Counter"
// mode.
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
        out_len < 1 || key_in_len < 1) {
        return 0;
    }

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

    ki = OPENSSL_malloc(max(iv_len, hmac_size));
    size_t ki_len = key_in_len;
    if (iv != NULL && iv_len > 0) {
        // Set k(0) to the IV.
        memcpy(ki, iv, iv_len);
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
            uint32_t be_i = to_be32(i);
            if(!HMAC_Update(&hmac, (const uint8_t *)&be_i, sizeof(be_i))) {
                goto out;
            }
        }
        if (!HMAC_Update(&hmac, label, label_len)) {
            goto out;
        }
        if (context != NULL && context_len > 0) {
            if (!HMAC_Update(&hmac, &zero, sizeof(zero)) ||
                !HMAC_Update(&hmac, context, context_len)) {
                goto out;
            }
        }
        // Another mystery in SP800-108r1; this iteration's ki data is
        // generated via:
        //
        // ki = PRF(key_in, previous ki || i || Label || 0x00 || Context || L)
        //
        // The test data from the CAVP Testing: SP 800-108 Key Derivation Using
        // Pseudorandom Functions - Key-Based (KBKDF) page
        // https://csrc.nist.gov/Projects/cryptographic-algorithm-validation-program/key-derivation
        // seems to require us to ignore L.
        //
        // The spec also doesn't indicate whether L should be appended in
        // big-endian format, or how large (in bits) it should be.
        /*
        if (!HMAC_Update(&hmac, (const uint8_t *)&L, sizeof(L))) {
            goto out;
        }
        */

        ki_len = hmac_size;
        if (!HMAC_Final(&hmac, ki, (unsigned int *)&ki_len)) {
            goto out;
        }

        size_t this_write = min(ki_len, to_write);
        memcpy(out_key + written, ki, this_write);
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
    FIPS_service_indicator_lock_state();
    KBKDF_verify_service_indicator(digest);

    if (ki != NULL) {
        OPENSSL_cleanse(ki, max(iv_len, hmac_size));
        OPENSSL_free(ki);
    }
    HMAC_CTX_cleanse(&hmac);

    return retval;
}
