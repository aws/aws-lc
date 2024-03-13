#!/bin/bash

if [ "$#" -ne 2 ]; then
  echo "slothy.sh <input asm file name> <output dir>"
  exit 1
fi

SLOTHY_DIR=~/slothy

set -e

if [ ! -d "$SLOTHY_DIR" ]; then
  echo "slothy does not exist at $SLOTHY_DIR . Please adjust the path by "
  echo "modifying SLOTHY_DIR in this script (slothy.sh)."
  exit 1
fi

source ${SLOTHY_DIR}/venv/bin/activate

SRC_FILE=${1}
OUT_DIR=${2}
LOG_DIR=slothy-logs

echo "SRC_FILE: ${SRC_FILE}"
echo "OUT_DIR: ${OUT_DIR}"
echo "LOG_DIR: ${LOG_DIR}"

# Please properly adjust these parameters according to the description
# in the assembly file of s2n-bignum of interest

if [ "$OUTPUTS" == "" ]; then
  echo "Please set environment variable OUTPUTS as specified in the assembly"
  echo "file of interest"
  exit 1
elif [ "$RESERVED_REGS" == "" ]; then
  echo "Please set environment variable OUTPUTS as specified in the assembly"
  echo "file of interest"
  exit 1
fi

echo "OUTPUTS: ${OUTPUTS}"
echo "RESERVED_REGS: ${RESERVED_REGS}"

REDIRECT_OUTPUT="--log --logdir=${LOG_DIR}"
mkdir -p $LOG_DIR
mkdir -p $OUT_DIR

# "Rule of thumb is that you should pick the split factor so that the window size is somewhere around 100"
# Note that this will return a bloated number if the file contains many comments.
N_LINES=`wc -l ${SRC_FILE} | cut -d" " -f1`
echo "N_LINES=$N_LINES"
SPLIT_FACTOR=`python -c "print($N_LINES // 50)"`
echo "SPLIT_FACTOR=$SPLIT_FACTOR"

UARCH=Arm_Neoverse_N1_experimental

echo "** Step 1: Preprocessing"
${SLOTHY_DIR}/slothy-cli Arm_AArch64 $UARCH \
       ${SRC_FILE} \
    -o ${OUT_DIR}/1.preprocess.s \
    -c outputs=$OUTPUTS -c reserved_regs=$RESERVED_REGS \
    -c split_heuristic -c split_heuristic_repeat=0 \
    -c split_heuristic_preprocess_naive_interleaving \
    -c /visualize_reordering \
    $REDIRECT_OUTPUT

echo "** Steps 2: Stepwise optimization, ignoring latencies"
# The goal here is to get a good amount of interleaving
# The best order of subregions is still TBD, but presently we 'comb' all stalls
# towards the middle of the code and repeat the process. The idea/hope is that
# by doing this multiple times, the stalls will eventually be absorbed.

# When invoking slothy-cli, unuse -c variable_size by default because the
# timeout option is applied to its one large solver invocation. Without
# the option, slothy invokes a solver multiple times, each of which will take
# a shorter time & likely to fit in the given timeout (600s). A pitfall is that
# summation of the solver time without this option is very likely to be longer
# than the case when -c variable_size is enabled. Please feel free to add
# -c variable_time if you are familiar with the option & have a number
# that is confident enough to not cause timeout.

${SLOTHY_DIR}/slothy-cli Arm_AArch64 $UARCH \
       ${OUT_DIR}/1.preprocess.s \
    -o ${OUT_DIR}/2.interleave.s \
    -c outputs=$OUTPUTS -c reserved_regs=$RESERVED_REGS \
    -c max_solutions=512 \
    -c timeout=600 \
    -c split_heuristic \
    -c objective_precision=0.05 \
    -c split_heuristic_factor=$SPLIT_FACTOR \
    -c constraints.model_latencies=False \
    -c /visualize_reordering \
    -c split_heuristic_repeat=10 \
    $REDIRECT_OUTPUT

# Finally, also consider latencies

SPLIT_FACTOR=$((N_LINES / 30))

echo "** Step 3: Consider latencies"
${SLOTHY_DIR}/slothy-cli Arm_AArch64 $UARCH \
       ${OUT_DIR}/2.interleave.s \
    -o ${OUT_DIR}/3.opt.s \
    -c outputs=$OUTPUTS -c reserved_regs=$RESERVED_REGS \
    -c max_solutions=512 \
    -c timeout=600 \
    -c split_heuristic \
    -c objective_precision=0.05 \
    -c split_heuristic_factor=$SPLIT_FACTOR \
    -c split_heuristic_repeat=10 \
    -c /visualize_reordering \
    $REDIRECT_OUTPUT