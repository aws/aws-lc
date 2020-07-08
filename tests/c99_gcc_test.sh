#!/bin/bash

# This test is aimed to run with GCC 6 and above on x86-64 architectures.

ROOT_DIR="./third_party/boringssl/"
INCLUDE_DIR="$ROOT_DIR/include"

INCLUDE_FILES=`ls $INCLUDE_DIR/openssl/*.h | grep -v $INCLUDE_DIR/openssl/arm_arch.h`

# - This compilation line gets no source files as its input (it uses the -c flag).
#   Instead it uses the force include flag (-include) to include all of headers
#   except for arm_arch.h, which cannot run on x86-64 architectures.
# - The -Wpedantic flag ensures that the compiler will fault if a non C99 line 
#   exists in the code.
# - The -fsyntax-only tells the compiler to check the syntax without producing 
#   any outputs.

$CC -std=c99 -c -I$INCLUDE_DIR -include $INCLUDE_FILES -Wpedantic -fsyntax-only

