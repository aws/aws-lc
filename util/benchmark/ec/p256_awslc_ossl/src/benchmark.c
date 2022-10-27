/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#include <stdio.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>
#include <sys/times.h>
#include <string.h>

#include "benchmark.h"

BIO *bio_out = NULL;
BIO *bio_err = NULL;

void open_test_streams(void)
{
    bio_out = BIO_new_fp(stdout, BIO_NOCLOSE);
    bio_err = BIO_new_fp(stderr, BIO_NOCLOSE);

    assert(bio_out != NULL);
    assert(bio_err != NULL);
}

void close_test_streams(void)
{
    (void)BIO_flush(bio_out);
    (void)BIO_flush(bio_err);

    BIO_free_all(bio_out);
    BIO_free_all(bio_err);
}

uint64_t time_now(void)
{
    struct timespec ts;
    uint64_t ret = 0;

#if defined(AARCH64_COUNTER_TIMER)
    int64_t virtual_timer_value;
    /* In the following assembly call:
     * ISB: Instruction Synchronization Barrier; i.e. ensures the previous instructions
     *      are done executing and changing the context, e.g. system registers, cache, ...
     *      before the ones following it, where the context changes would be visible.
     * Read CNTVCT_EL0, the counter-timer virtual count register
     * similarly to https://github.com/google/benchmark/blob/master/src/cycleclock.h
     */
    asm volatile("isb; mrs %0, cntvct_el0" : "=r"(ret));
#else
    clock_gettime(CLOCK_MONOTONIC, &ts);
    ret = ts.tv_sec;
    ret *= 1000000;
    ret += ts.tv_nsec / 1000;
#endif
    return ret;
}

uint64_t calculate_iterations(uint64_t start, uint64_t end,
                              uint64_t iterations_run, uint64_t usec_desired)
{
    double usec_spent_per_iter;
#if defined(AARCH64_COUNTER_TIMER)
    uint64_t timer_freq, usec_spent;

    /* Read CNTFRQ_EL0, the counter-timer frequency register */
    asm volatile("mrs %0, cntfrq_el0" : "=r"(timer_freq));

    usec_spent = ((double)(end - start) / timer_freq) * 1000000;
    usec_spent_per_iter = usec_spent / iterations_run;
#else
    usec_spent_per_iter = (double)(end - start) / iterations_run;
#endif
    uint64_t num_itr = (uint64_t)(usec_desired / usec_spent_per_iter);

    return num_itr;/* (uint64_t)(usec_desired / usec_spent_per_iter);*/
}

void report_results(uint64_t start, uint64_t end,
                    uint64_t iterations, const char *benchmark)
{
    int64_t usec;
#if defined(AARCH64_COUNTER_TIMER)
    int64_t timer_freq;
    /* Read CNTFRQ_EL0, the counter-timer frequency register */
    asm volatile("mrs %0, cntfrq_el0" : "=r"(timer_freq));

    usec = ((double)(end - start) / timer_freq) * 1000000;
#else
    usec = end - start;
#endif
    BIO_printf(bio_out, "%s: %lu operations in %luus (%.1f ops/sec)\n",
               benchmark, (unsigned long)iterations, (long unsigned)usec, ((double)iterations/usec) * 1000000);

}
