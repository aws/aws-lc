# Linux Entropy Recording and Validation

The test provided here is split into two aspects: the recording of the raw
entropy data and the validation of the data. Both aspects are implemented
with the code in the respective directories.

The idea is that you give the recording directory to the customer
so that he obtains the data. Once you receive the data, you process it
with the code in the validation directory.

## Getting Started

When standard testing shall be performed, the collection of raw entropy is
performed with the script `invoke_testing.sh`.

Before executing the script, the following files from the used Jitter RNG
noise source shall be copied into this directory:

	* jitterentropy-base.c

	* jitterentropy.h

	* jitterentropy-base-user.h

The results are stored in `../results-measurements` which then needs to be
processed with the `validation-runtime` and `validation-restart` logic.

## Recording of Raw Entropy Data

If the `invoke_testing.sh` is not helpful for performing the test, the following
explanation outlines the specific test steps to be invoked manually.

For recoding the raw entropic data, the user has to compile the code.
To do that, he has to copy the following files into the recording directory
prior compilation. These files are taken from his Jitter RNG implementation
that he uses:

	* jitterentropy-base.c

	* jitterentropy.h

	* jitterentropy-base-user.h

Depending on the version of the Jitter RNG, the following commands have to
be invoked for compiling the test tool:

	* Jitter RNG 1.x and older: make -f Makefile.foldtime

	* Jitter RNG 2.x: make -f Makefile.lfsrtime

	* Jitter RNG 3.x: make -f Makefile.hashtime

The test is now invoked with the following command:

	* Jitter RNG 1.x and older:

		./jitterentropy-foldtime > /dev/shm/jent-raw.data

	* Jitter RNG 2.x:

		./jitterentropy-lfsrtime > /dev/shm/jent-raw.data

	* Jitter RNG 3.x:

		./jitterentropy-hashtime > /dev/shm/jent-raw.data

In addition, the collection of output data from the Jitter RNG must be
compiled with the following command:

	make -f Makefile.rng

To generate output data from the Jitter RNG for validation, invoke:

	./jitterentropy-rng 2> /dev/shm/jent.rngout

The recording program collects two sets of sample of time deltas obtained 
from the Jitter RNG:

	* var:	this is the normal behavior of the Jitter RNG. The time delta 
		is not only used to feed the pool, but also to determine the 
		number of LFSR operations (1 to 15 in the current configuration)
		that will be performed before returning each bit to the pool. 
		The different number of cycles used on each bit produce 
		variations in the memory access time, increasing the entropy of
		the noise source. 

	* single: in this case, there is only one cycle of LFSR operations per
		bit.  This is the worst case scenario forced by the recording 
		program in order to have the lowest minimum entropy estimation. 

The program is compiled to collect two samples of 10000000 events each (see 
the ROUNDS parameter in Makefile). The file contains one line per item, each 
line contains two decimal numbers: the first is for the var noise source, 
the second for the single noise source.

