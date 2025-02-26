#!/bin/bash
#
# Tool to validaets the test results for various Jitter RNG memory settings
#
# This tool is only needed if you have insufficient entropy. See ../README.md
# for details
#

RESULT="../results-restart-multi"
ENT_DIR="../results-measurements"
RES_DIR="../results-analysis-restart"
NUM_CPU=1
USED_CPUS=0

echo -e "Number of blocks\tBlocksize\tmin entropy" > $RESULT

trap "make clean" 0 1 2 3 15
make clean
make

crunch_numbers() {
	local source=$1
	local target=$2

	if [ $USED_CPUS -eq $NUM_CPU ]
	then
		# wait for all
		wait
		USED_CPUS=0
	fi

	if [ ! -d $target ]
	then
		USED_CPUS=$(($USED_CPUS+1))

		( BUILD_EXTRACT="no" ENTROPYDATA_DIR=$source RESULTS_DIR=$target ./processdata.sh ) &
	fi
}

linearmem_written=0
calc() {
	local crunch=$1

	for memsize in 32768 65536 131072 262144 524288 1048576 2097152 4194304 8388608 16777216 33554432 67108864 134217728 268435456 536870912
	do
		for blocks in 64 128 256 512 1024 2048 4096 8192 16384
		do
			for blocksize in 32 64 128 256 512 1024 2048 4096 8192 16384
			do
				local target="$RES_DIR-${blocks}blocks-${blocksize}blocksize-${memsize}bytes"
				local source="$ENT_DIR-${blocks}blocks-${blocksize}blocksize-${memsize}bytes"

				if [ ! -d "$source" ]
				then
					continue
				fi

				if [ $linearmem_written -eq 0 ]
				then
					echo -e "Max memory size\tNumber of blocks\tBlocksize\tmin entropy" > $RESULT
					linearmem_written=1
				fi

				if [ $crunch -eq 0 ]
				then
					ent=$(grep min $target/jent-raw-noise-restart-consolidated.minentropy_FF_8bits.var.txt | cut -d ":" -f 2)
					echo -e "$memsize\t$blocks\t$blocksize\t$ent" >> $RESULT
				else
					crunch_numbers $source $target
				fi
			done
		done
	done
}

randmem_written=0
calc_randmem() {
	local crunch=$1

	for bits in 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26
	do
		local target="$RES_DIR-random_memaccess-${bits}bits-${memsize}bytes"
		local source="$ENT_DIR-random_memaccess-${bits}bits-${memsize}bytes"

		if [ ! -d "$source" ]
		then
			continue
		fi

		if [ $randmem_written -eq 0 ]
		then
			echo -e "Number of bits\tmin entropy" > $RESULT
			randmem_written=1
		fi

		if [ $crunch -eq 0 ]
		then
			ent=$(grep min $target/jent-raw-noise-restart-consolidated.minentropy_FF_8bits.var.txt | cut -d ":" -f 2)
			echo -e "$bits\t$ent" >> $RESULT
		else
			crunch_numbers $source $target
		fi
	done
}

if [ -f /proc/cpuinfo ]
then
	NUM_CPU=$(cat /proc/cpuinfo  | grep processor | tail -n1 | cut -d":" -f 2)
	NUM_CPU=$(($NUM_CPU+1))
fi

calc_randmem 1
wait
calc_randmem 0

calc 1
wait
calc 0
