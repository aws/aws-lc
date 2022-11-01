/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include "benchmark.h"

/* Default number of milliseconds if not provided to the algorithm */
#define DEFAULT_NUM_MSEC         500    /* 1/2 second */
#define MAX_NUM_MSEC           60000    /* 60 sec */

typedef void (*bench_fn_t)(uint64_t);

bench_fn_t bench_fns[] = {
    benchmark_ecdh_p256,
    benchmark_ecdsa_p256,
};

#define NUM_BENCH       NUM_ELEM(bench_fns)

const char *bench_choices[NUM_BENCH] = {
        "ecdhp256",
        "ecdsap256"
};

int main(int argc, char *argv[])
{
    int bench_doit[NUM_BENCH] = {0};
    int i;
    int valid_choice = 0;
    int choice_made = 0;
    uint64_t msec;

    int option;
    opterr = 0;

    /* Open output messages streams */
    open_test_streams();

    /* Set the default number of milliseconds to run the benchmark */
    msec = DEFAULT_NUM_MSEC;

    /* Parse the arguments, if any */
    if (1 != argc)
    {
        while ((option = getopt(argc, argv, "t:m:")) != -1)
        {
            //BIO_printf(bio_out,"option: %s %s", option, optarg);
            switch (option)
            {
                case 't':
                    valid_choice = 0;
                    /* Check that the benchmark choice is valid */
                    for (i = 0; i < NUM_BENCH; i++) {
                        if (0 == strcmp(optarg, bench_choices[i])) {
                            /* Mark the benchmark for running */
                            bench_doit[i] = 1;
                            valid_choice = 1;
                            choice_made = 1;
                        }
                    }
                    /* If the choice is not valid, print the valid choices and exit with an error */
                    if (!valid_choice)
                    {
                            BIO_printf(bio_err, "\nERROR: Invalid benchmark choice: %s\n"
                                                "Please choose from:\n", optarg);
                        for (i = 0; i < NUM_BENCH; i++) {
                            BIO_printf(bio_err, " %s", bench_choices[i]);
                        }
                        BIO_printf(bio_err, "\n");

                        return 1;
                    }
                    break;
                case 'm':
                    /* Get the number of milliseconds */
                    msec = (uint64_t)atoi(optarg);
                    if ((msec > MAX_NUM_MSEC) || (msec < 1))
                    {
                        BIO_printf(bio_err, "\nERROR: Invalid number of milliseconds\n"
                                            "Please enter a number between 1 and %d:\n", MAX_NUM_MSEC);
                        return 1;
                    }
                    break;
                case '?':
                    BIO_printf(bio_err, "\nERROR: Unknown arguments\n"
                                        "Permissible arguments are:\n"
                                        " ec_benchmark_<awslc|ossl> [-t <benchmark_choice>] [-m <number of milliseconds>]\n");
                    return 1;

                default:
                    return 1;
            }
        }
    }

    /* If there are no arguments, mark all benchmarks for running */
    if (1 != choice_made)
    {
        for (i = 0; i < NUM_BENCH; i++)
        {
            bench_doit[i] = 1;
        }
    }

    /* Run the benchmarks marked for running */
    for (i = 0; i < NUM_BENCH; i++)
    {
        if (bench_doit[i])
        {
            bench_fns[i](msec);
        }
    }

    // Close output messages streams
    close_test_streams();

    return 0;
}
