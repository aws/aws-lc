#!/bin/bash

# Directory where to store the measurements
OUTDIR="../results-measurements"

# Maximum number of entries to be extracted from the original file
NUM_EVENTS=1000000

# Number of restart tests
NUM_EVENTS_RESTART=1000
NUM_RESTART=1000

NONIID_RESTART_DATA="jent-raw-noise-restart"
NONIID_DATA="jent-raw-noise"
IID_DATA="jent-conditioned.data"

initialization()
{
	if [ ! -d $OUTDIR ]
	then
		mkdir $OUTDIR
		if [ $? -ne 0 ]
		then
			echo "Creation of $OUTDIR failed"
			exit 1
		fi
	fi

	trap "make -s -f Makefile.lfsrtime clean; exit" 0 1 2 3 15
}

lfsroutput()
{
	echo "Obtaining $NUM_EVENTS blocks of output from Jitter RNG"

	local kcapi="/usr/bin/kcapi-rng"

	if [ ! -x "${kcapi}" ]
	then
		kcapi="/usr/local/bin/kcapi-rng"
	fi

	if [ ! -x "${kcapi}" ]
	then
		echo "Application kcapi-rng does not exist - this is needed to obtain the LFSR output data on the current system"
		return
	fi

	local bytes=$(($NUM_EVENTS*8))
	${kcapi} -n "jitterentropy_rng" -b $bytes > $OUTDIR/$IID_DATA
}

raw_entropy_restart()
{
	echo "Obtaining $NUM_RESTART raw entropy measurement with $NUM_EVENTS_RESTART restarts from Jitter RNG"

	make -s -f Makefile.lfsrtime

	./jitterentropy-kernel-lfsrtime $NUM_EVENTS_RESTART $NUM_RESTART $OUTDIR/$NONIID_RESTART_DATA

	make -s -f Makefile.lfsrtime clean
}

raw_entropy()
{
	echo "Obtaining $NUM_EVENTS raw entropy measurement from Jitter RNG"

	make -s -f Makefile.lfsrtime

	./jitterentropy-kernel-lfsrtime $NUM_EVENTS 1 $OUTDIR/$NONIID_DATA

	make -s -f Makefile.lfsrtime clean
}

initialization
lfsroutput
raw_entropy
raw_entropy_restart
