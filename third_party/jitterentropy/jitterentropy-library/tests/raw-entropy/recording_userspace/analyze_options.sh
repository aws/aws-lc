#!/bin/bash
#
# Tool to generate test results for various Jitter RNG memory settings
#
# This tool is only needed if you have insufficient entropy. See ../README.md
# for details
#

OUTDIR="../results-measurements"

if (grep JENT_RANDOM_MEMACCESS ../../../jitterentropy.h | head -n 1 | grep -q define)
then
	for bits in 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26
	do
		export CFLAGS="-DJENT_MEMORY_BITS=$bits"

		./invoke_testing.sh

		mv $OUTDIR $OUTDIR-random_memaccess-${bits}bits

	done
else

	for memsize in 32768 65536 131072 262144 524288 1048576 2097152 4194304 8388608 16777216 33554432 67108864 134217728 268435456 536870912
	do
		for blocks in 64 128 256 512 1024 2048 4096 8192 16384
		do
			for blocksize in 32 64 128 256 512 1024 2048 4096 8192 16384
			do
				export CFLAGS="-DJENT_MEMORY_BLOCKS=$blocks -DJENT_MEMORY_BLOCKSIZE=$blocksize -DJENT_MEMORY_SIZE=$memsize"

				./invoke_testing.sh

				mv $OUTDIR $OUTDIR-${blocks}blocks-${blocksize}blocksize-${memsize}bytes
			done
		done
	done
fi
