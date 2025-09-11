# Jitter RNG Kernel Space SP800-90B Data Collector

This tool collects the raw data used for SP800-90B analysis. I.e. the collected
raw entropy data is obtained before any post processing.

The collected data is simply the execution time of the functions
jent_memaccess and jent_lfsrtime which both are the heart of the Jitter RNG.
The reader should understand that additional functions in the Jitter RNG
contribute to the entropy. However, this collection tool disregards them
which implies that the analysis tool already applies a worst case analysis.

## Test Implementations

The following test implementations are available:

- `Makefile.foldtime`: This tool is used for Linux kernels <= 5.1

- `Makefile.lfsrtime`: This tools is used for Linux kernel > 5.1

## Getting Started

When standard testing shall be performed, the collection of raw entropy is
performed with the script `invoke_testing.sh`.

Before executing the script, the following files from the used Jitter RNG
noise source shall be copied into this directory:

	* crypto/jitterentropy.c

The results are stored in `../results-measurements` which then needs to be
processed with the `validation` and `validation-restart` logic.

Please see the caveats for obtaining Jitter RNG output below.

## Obtain Raw Entropy

To use the data collection tool, follow these steps:

1. Copy the file crypto/jitterentropy.c from the kernel code into this
   directory.

2. Compile the code with the available Makefile

3. Execute the test and collect the output

	`./jitterentropy-kernel-lfsrtime > ../validation/jent-raw-noise.data`

or

	`./jitterentropy-kernel-foldtime > ../validation/jent-raw-noise.data`

4. Analyze the output with the code in the validation directory

# Obtain Jitter RNG Output

To generate Jitter RNG output, the Linux kernel AF_ALG interface can be used.
This implies that the kcapi-rng tool from [1] must be present.

The following invocation provides the Jitter RNG output for further analysis:

	`kcapi-rng -n "jitterentropy_rng" -b <NUMBER_OF_BYTES>`

Analyze the output with the code in the validation directory.

[1] https://www.chronox.de/libkcapi.html

# Author
Stephan Mueller <smueller@chronox.de>
