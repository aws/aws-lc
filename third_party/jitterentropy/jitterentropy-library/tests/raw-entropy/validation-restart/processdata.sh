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
EATOOL="../../SP800-90B_EntropyAssessment/cpp/ea_restart"

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

# Maximum number of entries to be extracted from the original file
MAX_EVENTS=1000000

############################################################
# Code only after this line -- do not change               #
############################################################

#############################
# Preparation
#############################
INPUT="$ENTROPYDATA_DIR/jent-raw-noise-restart*.data"
INPUTCONSOLIDATED="$RESULTS_DIR/jent-raw-noise-restart-consolidated.data"

EXTRACT="extractlsb"
CFILE="extractlsb.c"

if [ ! -d $ENTROPYDATA_DIR ]
then
	echo "Directory with raw entropy data $ENTROPYDATA_DIR is missing"
	exit 1
fi

if [ ! -d $RESULTS_DIR ]
then
	mkdir $RESULTS_DIR
	if [ $? -ne 0 ]
	then
		echo "Directory for results $RESULTS_DIR cannot be created"
		exit 1
	fi
fi

if [ ! -f $EA_TOOL ]
then
	echo "ERROR: Path of Entropy Data tool $EA_TOOL is missing"
	exit 1
fi


trap "if [ "$BUILD_EXTRACT" = "yes" ]; then make clean; fi" 0 1 2 3 15

rm -f $EXEC
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
# Step 1: Concatenate all individual restart files into single file
#
rm -f $INPUTCONSOLIDATED
for i in $INPUT
do
	echo "Process recorded entropy data $i"

	cat $i >> $INPUTCONSOLIDATED
done

#
# Step 2: extract data
#
for file in $INPUTCONSOLIDATED
do
	filepath=$RESULTS_DIR/`basename ${file%%.data}`
	echo "Converting recorded entropy data $file into different bit output" | tee -a $LOGFILE

	for item in $MASK_LIST
	do
		mask=${item%:*}
		bits=${item#*:}

		./$EXTRACT $file $filepath.${mask}bitout.var.data $filepath.${mask}bitout.single.data $MAX_EVENTS $mask 2>&1 | tee -a $LOGFILE
	done
done

#
# Step 3: Calculate SP800-90B
#
# Just like in step 2, we calculate the entropy column-wise
#

echo "" | tee -a $LOGFILE
echo "Extraction finished. Now analyzing entropy for noise source ..." | tee -a $LOGFILE
echo "" | tee -a $LOGFILE

for file in $INPUTCONSOLIDATED
do
	filepath=$RESULTS_DIR/`basename ${file%%.data}`

	for item in $MASK_LIST
	do
		mask=${item%:*}
		bits_field=${item#*:}
		bits_list=`echo $bits_field | sed -e "s/,/ /g"`

		infilesingle=$filepath.${mask}bitout.single.data
		infilevar=$filepath.${mask}bitout.var.data

		for bits in $bits_list
		do
			outfile=${filepath}.minentropy_${mask}_${bits}bits.single.txt
			inprocess_file=$outfile
			if [ ! -f $outfile ]
			then
				echo "Analyzing entropy for $infilesingle ${bits}-bit single" | tee -a $LOGFILE
				$EATOOL -n -v $infilesingle ${bits} 0.333 > $outfile
			else
				echo "File $outfile already generated"
			fi

			outfile=${filepath}.minentropy_${mask}_${bits}bits.var.txt
			inprocess_file=$outfile
			if [ ! -f $outfile ]
			then
				echo "Analyzing entropy for $infilevar ${bits}-bit var" | tee -a $LOGFILE
				$EATOOL -n -v $infilevar ${bits} 0.333 > $outfile
			else
				echo "File $outfile already generated"
			fi
		done
	done
done
