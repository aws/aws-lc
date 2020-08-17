#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


set -e

Z3_URL='https://github.com/Z3Prover/z3/releases/download/z3-4.8.8/z3-4.8.8-x64-ubuntu-16.04.zip'
YICES_URL='https://yices.csl.sri.com/releases/2.6.2/yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz'
SAW_URL=' https://saw.galois.com/builds/nightly/saw-0.4.0.99-2020-08-13-Ubuntu14.04-64.tar.gz'

mkdir -p bin deps

# fetch Z3
if [ ! -f bin/z3 ]
then
    mkdir -p deps/z3
    wget $Z3_URL -O deps/z3.zip
    unzip deps/z3.zip -d deps/z3
    cp deps/z3/*/bin/z3 bin/z3
fi

# fetch Yices
if [ ! -f bin/yices ]
then
    mkdir -p deps/yices
    wget $YICES_URL -O deps/yices.tar.gz
    tar -x -f deps/yices.tar.gz --one-top-level=deps/yices
    cp deps/yices/*/bin/yices bin/yices
    cp deps/yices/*/bin/yices-smt2 bin/yices-smt2
fi

# fetch SAW
if [ ! -f bin/saw ]
then
    mkdir -p deps/saw
    wget $SAW_URL -O deps/saw.tar.gz
    tar -x -f deps/saw.tar.gz --one-top-level=deps/saw
    cp deps/saw/*/bin/saw bin/saw
fi
