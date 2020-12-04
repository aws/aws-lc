#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include "benchmark.h"

// Default number of iterations if not provided to the algorithm
// Note: The number of iterations of ECDSA Sign is 10x this number
#define DEFAULT_NUM_ITERATIONS 40000
#define MAX_NUM_ITERATIONS    100000

typedef void (*bench_fn_t)(int);

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
    int i, num_iter;
    int valid_choice = 0;
    int choice_made = 0;

    int option;
    opterr = 0;

    // Open output messages streams
    test_open_streams();

    // Set the default number of iterations
    num_iter = DEFAULT_NUM_ITERATIONS;

    // If there are no arguments, mark all benchmarks for running
    // and set the number of iterations to the default number

    // Otherwise, parse the arguments
    if (1 != argc)
    {
        while ((option = getopt(argc, argv, "t:i:")) != -1)
        {
            //BIO_printf(bio_out,"option: %s %s", option, optarg);
            switch (option)
            {
                case 't':
                    valid_choice = 0;
                    // Check that the benchmark choice is valid
                    for (i = 0; i < NUM_BENCH; i++) {
                        if (0 == strcmp(optarg, bench_choices[i])) {
                            // Mark the benchmark for running
                            bench_doit[i] = 1;
                            valid_choice = 1;
                            choice_made = 1;
                        }
                    }
                    // If the choice is not valid, print the valid choices and exit with an error
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
                case 'i':
                    num_iter = atoi(optarg);
                    if ((num_iter > MAX_NUM_ITERATIONS) || (num_iter < 1))
                    {
                        BIO_printf(bio_err, "\nERROR: Invalid number of iterations\n"
                                            "Please enter a number between 1 and %d:\n", MAX_NUM_ITERATIONS);
                        return 1;
                    }
                    break;
                case '?':
                    BIO_printf(bio_err, "\nERROR: Unknown arguments\n"
                                        "Permissible arguments are:\n"
                                        " ec_benchmark_<awslc|ossl> [-t <benchmark_choice>] [-i <number of iterations>]\n");
                    return 1;

                default:
                    return 1;
            }
        }
    }

    if (1 != choice_made)
    {
        for (i = 0; i < NUM_BENCH; i++)
        {
            bench_doit[i] = 1;
        }
    }

    for (i = 0; i < NUM_BENCH; i++)
    {
        if (bench_doit[i])
        {
            bench_fns[i](num_iter);
        }
    }

    // Close output messages streams
    test_close_streams();

    return 0;
}
