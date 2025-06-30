#!/usr/bin/env sh
# Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.

set -e

# Optimize AES-GCM variant via SLOTHY
#
# Usage:
# > [SLOTHY_FLAGS=...] [UARCH={N1,V1}] optimize.sh variant
#
# SLOTHY_FLAGS is passed to slothy-cli unmodified.
#
# Only one size is implemented, 256
#
# Use
# > optimize.sh --help
# to list all available examples.

CLEAN_DIR=./clean
OPT_DIR=./opt
TMP_DIR=./tmp
ASM_DIR=../

if [ "$ENC" = "" ]; then
    echo "Environment variable ENC not set. Defaulting to ENC=1 (encryption)."
    ENC=1
fi

if [ "$ENC" = "1" ]; then
    ENCDEC="enc"
else
    ENCDEC="dec"
fi

if [ "$AWS_LC_BASE" = "" ]; then
    # Oof... bit gross
    AWS_LC_BASE=$(dirname $(dirname $(dirname $(dirname $(dirname $(pwd))))))
    echo "Environment variable AWS_LC_BASE not set. Defaulting to $AWS_LC_BASE."
fi

BUILD_DIR=build-release

CLEAN_STEM=aes-xts-armv8-${ENCDEC}-base
OPT_STEM=aes-xts-armv8-${ENCDEC}-opt
TMP_STEM=aes-xts-armv8-${ENCDEC}-tmp

UARCH=${UARCH:=N1}
if [ $UARCH = "N1" ]; then
    MODEL=Arm_Neoverse_N1_experimental
elif [ $UARCH = "V1" ]; then
    MODEL=Arm_Big_experimental
else
    echo "Unknown microarchitecture: Choose from {N1, V1}"
    exit 1
fi

## list_variants() {
##     SZ=$1
##     UNROLL=$2
##     DIR=$3
##     VARIANTS=$( (ls -1 ./${DIR}/*${SZ}*${UNROLL}*.S | sed -n 's/.*'"${UNROLL}"'_\(.*\)\.S/\1/p' | tr '\n' ' ') 2>/dev/null || echo "")
##     echo $VARIANTS
## }
##
## VARIANTS_ALL=""
## for UNROLL in x4 x6 x8
## do
##     for V in $(list_variants $SZ $UNROLL "clean/${ENCDEC}");
##     do
##     VARIANTS_ALL="$VARIANTS_ALL
##       ${UNROLL}_$V"
##     done
## done

VARIANTS_ALL="x5_basic"

VERBOSE=${VERBOSE:=0}
TIMEOUT=${TIMEOUT:=1200} # 20min timeout by default

if [ "$1" = "--help" ]; then
    echo "Usage: optimize.sh variant"
    echo "Known variants:"
    for var in $VARIANTS_ALL; do
        echo "- $var"
    done
    exit 1
fi

TODO=$@
if [ "$TODO" = "" ]; then
    echo "No variant provided -- optimizing all."
    echo "WARNING: This will take a long time."
    TODO=$VARIANTS_ALL
fi

if [ "$DRY_RUN" = "1" ]; then
    echo "NOTE: Performing dry run -- no renaming/rescheduling allowed, but checking that SLOTHY understands the code and commands."
    DRY_RUN_FLAGS=" -c /constraints.allow_reordering -c /constraints.allow_renaming -c constraints.stalls_first_attempt=256"
else
    DRY_RUN_FLAGS=""
fi

if [ "$LLVM_MCA" = "1" ]; then
    LLVM_MCA_FLAGS="-c with_llvm_mca -c llvm_mca_full"
else
    LLVM_MCA_FLAGS=""
fi

if [ "$SKIP_EXISTING" = "" ]; then
    SKIP_EXISTING=0
fi

#    -l Loop_enc_iv_enc                                 \

optimize_x5() {
    slothy-cli Arm_AArch64 $MODEL                      \
    ${INFILE}                                          \
    -l Loop5x_xts_enc                                  \
    -c inputs_are_outputs                              \
    -c sw_pipelining.enabled=true                      \
    -c sw_pipelining.optimize_preamble=false         \
    -c sw_pipelining.optimize_postamble=false        \
    -c inputs_are_outputs                              \
    -c sw_pipelining.minimize_overlapping=False        \
    -c sw_pipelining.unknown_iteration_count=true    \
    -c variable_size                                   \
    -c constraints.stalls_first_attempt=64             \
    -c reserved_regs="[x18,x23--x30,w19,x2,x3,x21,x0,x1,x4,x5,sp]" \
    -c selftest=false                                  \
    -c constraints.allow_reordering=true             \
    -c constraints.allow_renaming=true             \
    -o $OUTFILE                                        \
    ${SLOTHY_FLAGS} ${DRY_RUN_FLAGS}
}

optimize_variant() {
    printf "Optimizing variant $1 ... "
    INFILE=$CLEAN_DIR/${ENCDEC}/${CLEAN_STEM}_$1.S
    OUTFILE=$OPT_DIR/${ENCDEC}/${OPT_STEM}_$1.S
    TMP0=$TMP_DIR/${TMP_STEM}_$1_0.S
    TMP1=$TMP_DIR/${TMP_STEM}_$1_1.S
    TMP2=$TMP_DIR/${TMP_STEM}_$1_2.S

    optimize_x5
}

for v in $TODO
do
    optimize_variant $v
done
