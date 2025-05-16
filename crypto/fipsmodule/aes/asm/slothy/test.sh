#!/usr/bin/env sh
# Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Build and test AES-GCM variants
#
# Usage:
# > [ENC=0/1] [BENCH=0/1] [AWS_LC_BASE=PATH] [BUILD_DIR=DIRNAME] [VERBOSE=0/1] [OPT=0/1] test.sh [variant]
#
# This script tests that the assembly files in clean/ or opt/ can be used as drop-in
# replacements for the default aesv8-gcm-armv8-base-{128,192,256}
#
# If BENCH=1, it also runs OpenSSL's `bssl speed` to benchmark performance.

set -e

if [ "$AWS_LC_BASE" = "" ]; then
    # Oof... bit gross
    AWS_LC_BASE=$(dirname $(dirname $(dirname $(dirname $(dirname $(pwd))))))
    echo "Environment variable AWS_LC_BASE not set. Defaulting to $AWS_LC_BASE."
fi

if [ "$BUILD_DIR" = "" ]; then
    BUILD_DIR="build-slothy"
    echo "Environment variable BUILD_DIR not set. Defaulting to $BUILD_DIR."
fi

if [ "$OPT" = "" ]; then
    OPT=0
    echo "Environment variable OPT not set. Defaulting to OPT=0 (testing clean variants)."
fi

if [ "$OPT" = "0" ]; then
    OPT_STR="clean"
else
    OPT_STR="opt"
fi

if [ "$ENC" = "" ]; then
    echo "Environment variable ENC not set. Defaulting to ENC=1 (encryption)."
    ENC=1
fi

if [ "$ENC" = "1" ]; then
    ENCDEC="enc"
else
    ENCDEC="dec"
fi

if [ "$VERBOSE" = "" ]; then
    VERBOSE=1
    echo "Environment variable VERBOSE not set. Defaulting to VERBOSE=0 (silent mode)."
fi

TIMEOUT=5 # Run tests for 5 seconds -- they often hang upon a bug
KEEP_GOING=${KEEP_GOING:=0}

ASM_DIR=../

# Only size 256 is supported
if [ "$OPT" = "0" ]; then
    DIR=./clean/${ENCDEC}
    FILE_STEM=aes-xts-armv8-${ENCDEC}-base
else
    DIR=./opt/${ENCDEC}
    FILE_STEM=aes-xts-armv8-${ENCDEC}-opt
fi

AES_SLOTHY_ASM=aes-xts-armv8-${ENCDEC}-slothy.S

set_variant() {
    cp $DIR/${FILE_STEM}_$1.S $ASM_DIR/$AES_SLOTHY_ASM
}

build_variant() {
    if [ $VERBOSE -eq 1 ]; then
        ninja -C $AWS_LC_BASE/$BUILD_DIR
    else
        ninja -C $AWS_LC_BASE/$BUILD_DIR > /dev/null 2>&1
    fi
}

test_variant() {
    if [ $VERBOSE -eq 1 ]; then
        timeout --foreground $TIMEOUT ${AWS_LC_BASE}/${BUILD_DIR}/crypto/crypto_test --gtest_filter="XTSTest.*"
    else
        timeout --foreground $TIMEOUT ${AWS_LC_BASE}/${BUILD_DIR}/crypto/crypto_test --gtest_filter="XTSTest.*" > /dev/null
    fi
}

BENCH_TIMEOUT=7
bench_variant() {
    timeout --foreground $BENCH_TIMEOUT ${AWS_LC_BASE}/${BUILD_DIR}/tool/bssl speed -filter "XTS"
}

do_variant() {
    echo "* Testing variant: ${OPT_STR}/${ENCDEC}/$1"
    printf " - Copy... "
    set_variant $1
    printf "OK!\n"
    printf " - Build... "
    build_variant
    printf "OK!\n"
    printf " - Test... "

    test_variant && res=$? || res=$?

    if [ "$res" = "0" ]; then
        printf "OK!\n"
    elif [ "$res" = "124" ]; then # TIMEOUT
        printf "FAIL (timeout after ${TIMEOUT}s) -- likely a bug causing tests to hang\n"
        if [ "$KEEP_GOING" = "0" ]; then
            exit 1
        fi
    else
        printf "FAIL\n"
        if [ "$KEEP_GOING" = "0" ]; then
            exit 1
        fi
    fi

    if [ "$BENCH" = "1" ]; then
        printf " - Bench...\n"
        bench_variant && res=$? || res=$?
    fi
}

## list_variants() {
##     SZ=$1
##     UNROLL=$2
##     DIR=$3
##     VARIANTS=$( (ls -1 ./${DIR}/*${SZ}*${UNROLL}*.S | sed -n 's/.*'"${UNROLL}"'_\(.*\)\.S/\1/p' | tr '\n' ' ') 2>/dev/null || echo "")
##     echo $VARIANTS
## }
##
## VARIANTS=""
## for UNROLL in x4 x6 x8
## do
##     for V in $(list_variants $SZ $UNROLL $DIR);
##     do
##     VARIANTS="$VARIANTS
##       ${UNROLL}_$V"
##     done
## done
##

VARIANTS="x5_basic"
if [ "$1" = "--help" ]; then
    echo "Usage: [ENC=0/1] [BENCH=0/1] [AWS_LC_BASE=PATH] [BUILD_DIR=DIRNAME] [VERBOSE=0/1] [OPT=0/1] test.sh [variant]"
    echo "Valid values for 'variant' are:"
    for var in $VARIANTS; do
        echo "* $var"
    done
    exit 0
fi

TODO=$@
if [ "$TODO" = "" ]; then
    TODO=$VARIANTS
fi

for var in $TODO; do
    do_variant $var
done
