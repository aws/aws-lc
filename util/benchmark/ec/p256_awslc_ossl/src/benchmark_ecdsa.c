/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#include <string.h>     /* for memset() */

#include <openssl/evp.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#ifdef AWSLC_BENCHMARK
#include <openssl/mem.h>
#endif

#include "benchmark.h"

#define ECDSA_SIGNATURE_BYTE_SIZE     256
#define DIGEST_BYTE_SIZE               20

/* OPENSSL_memset definition is copied from /boringssl/crypto/internal.h */
static inline void *OPENSSL_memset(void *dst, int c, size_t n) {
  if (n == 0) {
    return dst;
  }

  return memset(dst, c, n);
}

void benchmark_ecdsa_p256(uint64_t msec)
{
    EC_KEY *key = NULL;
    uint8_t signature[ECDSA_SIGNATURE_BYTE_SIZE];
    uint8_t digest[DIGEST_BYTE_SIZE];
    int ecdsa_checks = 1;
    unsigned sig_len;
    uint64_t start, now, end, num_itr;
    uint64_t usec = msec * 1000;

    /* Instantiate a key on the ANSI X9.62 Prime 256v1 (P-256) curve */
    key = EC_KEY_new_by_curve_name(NID_X9_62_prime256v1);

    if (!key ||
        /* Generate key */
        !EC_KEY_generate_key(key) ||
        /* Check key size */
        ECDSA_SIGNATURE_BYTE_SIZE < ECDSA_size(key)
        )
    {
        ecdsa_checks = 0;
        BIO_printf(bio_err, "ECDSA EC key generation failure.\n");
        ERR_print_errors(bio_err);
    }

    if (1 == ecdsa_checks)
    {
        /* Pre-fill digest buffer */
        OPENSSL_memset(digest, 42, sizeof(digest));

        /* Test ECDSA signing and verifying*/
        if (!ECDSA_sign(0, digest, sizeof(digest), signature, &sig_len, key) ||
            !ECDSA_verify(0, digest, sizeof(digest), signature, sig_len, key)
            )
        {
            ecdsa_checks = 0;
            BIO_printf(bio_err, "ECDSA signing and verifying failure.\n");
            ERR_print_errors(bio_err);
        }

    }

    if (1 == ecdsa_checks)
    {
        /*
         * ECDSA signing
         */

        /* Warm up and instrument the function to calculate how many iterations it should run for */
        start = time_now();
        /* key generation and key derivation on A's side */
        for (int i = 0; i < WARM_UP_NUM_ITER; i++)
        {
            ECDSA_sign(0, digest, sizeof(digest), signature, &sig_len, key);
        }
        end = time_now();
        num_itr = calculate_iterations(start, end, WARM_UP_NUM_ITER, usec);

        /* Benchmark ECDSA signing */
        start = time_now();
        for (int i = 0; i < num_itr; i++)
        {
            ECDSA_sign(0, digest, sizeof(digest), signature, &sig_len, key);
        }
        end = time_now();

        report_results(start, end, num_itr, "ECDSA P-256 sign");

        /*
         * ECDSA verification
         */

        /* Warm up and instrument the function to calculate how many iterations it should run for */
        start = time_now();
        /* key generation and key derivation on A's side */
        for (int i = 0; i < WARM_UP_NUM_ITER; i++)
        {
            ECDSA_verify(0, digest, sizeof(digest), signature, sig_len, key);
        }
        end = time_now();
        num_itr = calculate_iterations(start, end, WARM_UP_NUM_ITER, usec);

        /* Benchmark ECDSA verification */
        start = time_now();
        for (int i = 0; i < num_itr; i++)
        {
            ECDSA_verify(0, digest, sizeof(digest), signature, sig_len, key);
        }

        end = time_now();

        report_results(start, end, num_itr, "ECDSA P-256 verify");
    }

    if (1 == ecdsa_checks)
    {
        BIO_printf(bio_out, "SUCCESS: ECDSA Test.\n");
    }

    EC_KEY_free(key);
}
