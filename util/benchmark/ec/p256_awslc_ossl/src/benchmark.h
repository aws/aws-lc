#include <sys/types.h>
#include <stdint.h>
#include <openssl/err.h>
#include <openssl/bio.h>

#if defined(__aarch64__) && defined(COUNTER_REGISTER)
#define AARCH64_COUNTER_TIMER   1
#endif

#define NUM_ELEM(x)    (sizeof(x)/sizeof((x)[0]))
#define WARM_UP_NUM_ITER    60
#define DEFAULT_USEC_RUN    100000  /* 100 ms */

/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

extern BIO *bio_err;
extern BIO *bio_out;

/*
 * Open output streams
 */
void open_test_streams(void);

/*
 * Close output streams
 */
void close_test_streams(void);

/*
 * Get the current time, or the current timer counter if available on this platform
 */
uint64_t time_now(void);

/*
 * Calculate the number of iterations to be run
 * based on the time taken to run iterations_run and the desired number of microseconds to run
 */
uint64_t calculate_iterations(uint64_t start, uint64_t end,
                              uint64_t iterations_run, uint64_t usec_desired);

/*
 * Output the benchmark results
 */
void report_results(uint64_t start, uint64_t end,
                    uint64_t iterations, const char *benchmark);
/*
 * Benchmark ECDH P-256
 */
void benchmark_ecdh_p256(uint64_t msec);
/*
 * Benchmark ECDSA P-256
 */
void benchmark_ecdsa_p256(uint64_t msec);
