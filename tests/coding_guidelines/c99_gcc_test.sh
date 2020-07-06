#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# This test is aimed to run with GCC 6 and above on x86-64 architectures.

echo "Testing the C99 compatibility of AWS-LC headers."

AWSLC_ROOT_DIR="."
AWSLC_INC_DIR=$AWSLC_ROOT_DIR/include

INC_FILES=`ls $AWSLC_INC_DIR/awslc/*.h | grep -v $AWSLC_INC_DIR/awslc/arm_arch.h`

INC_FILES_STR=""
for f in $INC_FILES; do
  INC_FILES_STR+="-include $f "
done

TMP_C_FILE_NAME=`mktemp --suffix .c`

# - This compilation line gets no source file as its input (it uses the -c flag).
# Instead it uses the force include flag (-include) to include all of 
# AWS-LC headers except for arm_arch.h, which cannot run on x86-64 architectures.
# - The -Wpedantic flag ensures that the compiler will fault if a non C99 line
# exists in the code
# - The -fsyntax-only tells the compiler to check the symtax without producing 
#   any outputs.
$CC -std=c99 $TMP_C_FILE_NAME -c -I$AWSLC_INC_DIR $INC_FILES_STR -Wpedantic -fsyntax-only

