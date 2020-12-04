#include <string.h>     /* for memset() */

#include <openssl/evp.h>
#include <openssl/ec.h>
#ifdef AWSLC_BENCHMARK
#include <openssl/mem.h>
#include <openssl/ecdsa.h>
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

void benchmark_ecdsa_p256(int num_itr)
{
    EC_KEY *key = NULL;
    uint8_t signature[ECDSA_SIGNATURE_BYTE_SIZE];
    uint8_t digest[DIGEST_BYTE_SIZE];
    int ecdsa_checks = 1;
    unsigned sig_len;
    uint64_t start, now, us;
    int num_itr_sign = 10 * num_itr;


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
        /* Benchmark ECDSA signing */
        start = time_now();

        for (int i = 0; i < num_itr_sign; i++)
        {
            ECDSA_sign(0, digest, sizeof(digest), signature, &sig_len, key);
        }

        now = time_now();
        us = now - start;
        BIO_printf(bio_out, "ECDSA P-256 sign: %u operations in %luus (%.1f ops/sec)\n",
                   num_itr_sign, (long unsigned)us,
                   ((double)num_itr_sign/us) * 1000000);

        /* Benchmark ECDSA verification */
        start = time_now();

        for (int i = 0; i < num_itr; i++)
        {
            ECDSA_verify(0, digest, sizeof(digest), signature, sig_len, key);
        }

        now = time_now();
        us = now - start;
        BIO_printf(bio_out, "ECDSA P-256 verify: %u operations in %luus (%.1f ops/sec)\n",
                   num_itr, (long unsigned)us,
                   ((double)num_itr/us) * 1000000);

    }

    if (1 == ecdsa_checks)
    {
        BIO_printf(bio_out, "SUCCESS: ECDSA Test.\n");
    }


    EC_KEY_free(key);

	return;
}
