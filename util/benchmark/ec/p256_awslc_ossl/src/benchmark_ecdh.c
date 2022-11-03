/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#include <openssl/evp.h>
#include <openssl/ec.h>
#ifdef AWSLC_BENCHMARK
#include <openssl/mem.h>
#endif

#include "benchmark.h"

#define MAX_ECDH_SIZE   256

void benchmark_ecdh_p256(uint64_t msec)
{
    EVP_PKEY_CTX *kctx = NULL;
    EVP_PKEY_CTX *test_ctx = NULL;
    EVP_PKEY_CTX *ctx = NULL;
    EVP_PKEY_CTX *pctx = NULL;
    EVP_PKEY *params = NULL;
    EVP_PKEY *key_A = NULL;
    EVP_PKEY *key_B = NULL;
    unsigned char *secret_a = NULL;
    unsigned char *secret_b = NULL;
    size_t outlen;
    size_t test_outlen;
    int ecdh_checks = 1;
    uint64_t start, end, num_itr;
    uint64_t usec = msec * 1000;

    /* The correctness of the key generation and ECDH key derivation
     * is first tested. Benchmarking starts afterwards.
     */
    if (
        /* Create the context for parameter generation */
        (NULL == (pctx = EVP_PKEY_CTX_new_id(EVP_PKEY_EC, NULL))) ||
        /* Initialise the parameter generation */
        (1 != EVP_PKEY_paramgen_init(pctx)) ||
        /* We're going to use the ANSI X9.62 Prime 256v1 curve */
        (1 != EVP_PKEY_CTX_set_ec_paramgen_curve_nid(pctx, NID_X9_62_prime256v1)) ||
        /* Create the parameter object params */
        (!EVP_PKEY_paramgen(pctx, &params)) )
    {
        ecdh_checks = 0;
        BIO_printf(bio_err, "ECDH EC params init failure.\n");
        ERR_print_errors(bio_err);

    }

    if (1 == ecdh_checks)
    {
        /* Create the context for the key generation */
        kctx = EVP_PKEY_CTX_new(params, NULL);

        if (kctx == NULL ||      /* keygen ctx is not null */
            EVP_PKEY_keygen_init(kctx) <= 0 /* init keygen ctx */ ||
            EVP_PKEY_keygen(kctx, &key_B) <= 0  /* generate secret key B (peer) */ )
        {
            ecdh_checks = 0;
            BIO_printf(bio_err, "ECDH keygen failure.\n");
            ERR_print_errors(bio_err);
        }
    }
    EVP_PKEY_free(params);
    params = NULL;
    EVP_PKEY_CTX_free(pctx);
    pctx = NULL;

    if (1 == ecdh_checks)
    {

        if (EVP_PKEY_keygen(kctx, &key_A) <= 0 || /* generate secret key A */
            !(ctx = EVP_PKEY_CTX_new(key_A, NULL)) || /* derivation ctx from skeyA */
            EVP_PKEY_derive_init(ctx) <= 0 || /* init derivation ctx */
            EVP_PKEY_derive_set_peer(ctx, key_B) <= 0 || /* set peer pubkey in ctx */
            EVP_PKEY_derive(ctx, NULL, &outlen) <= 0 || /* determine max length */
            outlen == 0 ||  /* ensure outlen is a valid size */
            outlen > MAX_ECDH_SIZE /* avoid buffer overflow */)
        {
            ecdh_checks = 0;
            BIO_printf(bio_err, "ECDH secret length output failure.\n");
            ERR_print_errors(bio_err);
        }
    }

    if (1 == ecdh_checks)
    {
        /* Allocate buffer for shared secret and test shared secret */
        if (NULL == (secret_a = OPENSSL_malloc(outlen)) ||
            NULL == (secret_b = OPENSSL_malloc(outlen)))
        {
            ecdh_checks = 0;
            BIO_printf(bio_err, "ECDH buffer allocation failure.\n");
            ERR_print_errors(bio_err);
        }
    }

    if (1 == ecdh_checks)
    {
        /* Test the key derivation by computing the shared secret on B's side */
        if (!(test_ctx = EVP_PKEY_CTX_new(key_B, NULL)) || /* test ctx from skeyB */
            !EVP_PKEY_derive_init(test_ctx) || /* init derivation test_ctx */
            !EVP_PKEY_derive_set_peer(test_ctx, key_A) || /* set peer pubkey in test_ctx */
            !EVP_PKEY_derive(test_ctx, NULL, &test_outlen) || /* determine max length */
            !EVP_PKEY_derive(ctx, secret_a, &outlen) || /* compute a*B */
            !EVP_PKEY_derive(test_ctx, secret_b, &test_outlen) || /* compute b*A */
            test_outlen != outlen /* compare output length */ ||
            CRYPTO_memcmp(secret_a, secret_b, outlen)) /* compare A's and B's shared secret bytes */
        {
            ecdh_checks = 0;
            BIO_printf(bio_err, "ECDH shared secret test failure.\n");
            ERR_print_errors(bio_err);
        }
    }

    if (1 == ecdh_checks)
    {
        /* Test the key derivation after regenerating A's key using the same context */
        if (EVP_PKEY_keygen(kctx, &key_A) <= 0 || /* generate secret key A again */
            !EVP_PKEY_derive(ctx, secret_a, &outlen) || /* compute a*B */
            !CRYPTO_memcmp(secret_a, secret_b, outlen) || /* ensure not same shared secret as before */
            !EVP_PKEY_derive(test_ctx, secret_b, &test_outlen) || /* compute b*A */
            CRYPTO_memcmp(secret_a, secret_b, outlen)) /* compare A's and B's shared secret bytes */
        {
            ecdh_checks = 0;
            BIO_printf(bio_err, "ECDH shared secret with new A key test failure.\n");
            ERR_print_errors(bio_err);
        }
    }

    /* Benchmarking key generation and key derivation together:
     * - this follows the speed test of AWS-LC
     * - and practically, both operations are done together for ephemeral ECDH;
     *   for example, in TLS handshake.
     */
    if (1 == ecdh_checks)
    {
        /* Warm up and instrument the function to calculate how many iterations it should run for */
        start = time_now();
        /* key generation and key derivation on A's side */
        for (int i = 0; i < WARM_UP_NUM_ITER; i++)
        {
            EVP_PKEY_keygen(kctx, &key_A);
            EVP_PKEY_derive(ctx, secret_a, &outlen);
        }
        end = time_now();
        num_itr = calculate_iterations(start, end, WARM_UP_NUM_ITER, usec);

        start = time_now();

        /* Benchmark key generation and key derivation on A's side */
        for (int i = 0; i < num_itr; i++)
        {
            EVP_PKEY_keygen(kctx, &key_A);
            EVP_PKEY_derive(ctx, secret_a, &outlen);
        }
        end = time_now();

        report_results(start, end, num_itr, "ECDH P-256");
    }

    if (1 == ecdh_checks)
    {
        BIO_printf(bio_out, "SUCCESS: ECDH Test.\n");
    }

    EVP_PKEY_free(key_A);
    EVP_PKEY_free(key_B);
    EVP_PKEY_CTX_free(kctx);
    kctx = NULL;
    EVP_PKEY_CTX_free(ctx);
    ctx = NULL;
    EVP_PKEY_CTX_free(test_ctx);
    test_ctx = NULL;

    if (NULL != secret_a)
    {
        OPENSSL_free(secret_a);
    }

    if (NULL != secret_b)
    {
        OPENSSL_free(secret_b);
    }
}
