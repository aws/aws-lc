#!/bin/bash
#
# Process the entropy data

############################################################
# Configuration values                                     #
############################################################

# point to the directory that contains the results from the entropy collection
ENTROPYDATA_DIR=${ENTROPYDATA_DIR:-"../results-measurements"}

# this is where the resulting data and the entropy analysis will be stored
RESULTS_DIR=${RESULTS_DIR:-"../results-analysis-restart"}

# location of log file
LOGFILE="$RESULTS_DIR/processdata.log"

# point to the min entropy tool
EATOOL="../SP800-90B_EntropyAssessment/cpp/ea_restart"

# specify if you want to compile the extractlsb program in this script
BUILD_EXTRACT=${BUILD_EXTRACT:-"yes"}

# specify the list of significant bits and length that you want to analize.
# Indicate first the mask in hexa format and then the number of
# bits separated by a colon.
# The tool generates one set of var and single data files, and the EA results
# for each element.
# The mask can have a maximum of 8 bits on, the EA tool only manages samples
# up to one byte.

# List of masks usually analyzed (4 and 8 LSB)
MASK_LIST="0F:4 FF:8"

# List used for ARM Cortext A9 and A7 processors
#MASK_LIST="FF:4,8 7F8:4,8"

# Number of samples to be extracted from the original file
SAMPLES=1000

# Number of test runs to be concatenated
RESTARTS=1000

############################################################
# Code only after this line -- do not change               #
############################################################

#############################
# Preparation
#############################
EXTRACT="extractlsb"
CFILE="extractlsb.c"

if [ ! -d $ENTROPYDATA_DIR ]
then
	echo "ERROR: Directory with raw entropy data $ENTROPYDATA_DIR is missing"
	exit 1
fi

if [ ! -d $RESULTS_DIR ]
then
	mkdir $RESULTS_DIR
	if [ $? -ne 0 ]
	then
		echo "ERROR: Directory for results $RESULTS_DIR could not be created"
		exit 1
	fi
fi

if [ ! -f $EATOOL ]
then
	echo "ERROR: Path of Entropy Data tool $EATOOL is missing"
	exit 1
fi


rm -f $RESULTS_DIR/*.txt $RESULTS_DIR/*.data $RESULTS_DIR/*.log

trap "if [ "$BUILD_EXTRACT" = "yes" ]; then make clean; fi" 0 1 2 3 15

if [ "$BUILD_EXTRACT" = "yes" ]
then
	echo "Building $EXTRACT ..."
	make clean
	make
fi

if [ ! -x $EXTRACT ]
then
	echo "ERROR: Cannot execute $EXTRACT program"
	exit 1
fi

#############################
# Actual data processing
#############################

#
# Step 1: Concatenate all individual restart files into single file and convert
#
for item in $MASK_LIST
do
	mask=${item%:*}

	echo "Converting recorded entropy data into different bit output with mask $mask..." | tee -a $LOGFILE
	out_file=$RESULTS_DIR/raw_noise_restart_all.${mask}bitout.data
	rm -f $out_file

	for i in `seq -f "%05g" 0 $(($RESTARTS-1))`
	do
		in_file=$ENTROPYDATA_DIR/jent_raw_noise_restart.$i.data
		if [ ! -f $in_file ]
		then
			echo "ERROR: File $in_file not found"
			exit 1
		fi

		echo "Converting recorded entropy data $in_file into different bit output with mask $mask" >> $LOGFILE
		./$EXTRACT $in_file $out_file $SAMPLES $mask >> $LOGFILE 2>&1
	done
done

echo "" | tee -a $LOGFILE
echo "Extraction finished. Now analyzing entropy for noise source ..." | tee -a $LOGFILE
echo "" | tee -a $LOGFILE

#
# Step 2: Perform SP800-90B analysis
#
for item in $MASK_LIST
do
	mask=${item%:*}
	bits_field=${item#*:}
	bits_list=`echo $bits_field | sed -e "s/,/ /g"`

	in_file=$RESULTS_DIR/raw_noise_restart_all.${mask}bitout.data

	for bits in $bits_list
	do
		out_file=$RESULTS_DIR/raw_noise_restart_all.minentropy_${mask}_${bits}bits.txt
		if [ ! -f $out_file ]
		then
			echo "Analyzing entropy for $out_file ${bits}-bit..." | tee -a $LOGFILE
			$EATOOL -n -v $in_file ${bits} 1.0 > $out_file
		else
			echo "File $out_file already generated"
		fi
	done
done
