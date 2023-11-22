#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

Z3_URL='https://github.com/Z3Prover/z3/releases/download/z3-4.11.2/z3-4.11.2-x64-glibc-2.31.zip'
CVC5_URL='https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.8/cvc5-Linux'
MESON_URL='https://github.com/mesonbuild/meson/releases/download/1.2.3/meson-1.2.3.tar.gz'
# YICES_URL='https://yices.csl.sri.com/releases/2.6.2/yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz'

mkdir -p /bin /deps

# fetch Z3
if [ ! -f /bin/z3 ]
then
    mkdir -p /deps/z3
    wget $Z3_URL -O /deps/z3.zip
    unzip /deps/z3.zip -d /deps/z3
    cp /deps/z3/*/bin/z3 /bin/z3
fi

# install wllvm
if [ ! -f /usr/local/bin/wllvm ]
then
    git clone https://github.com/travitch/whole-program-llvm /deps/whole-program-llvm
    cd /deps/whole-program-llvm
    git checkout cd8774483917f4de15da5a535179136bb55d5ae3
    pip3 install -e .
fi

# install CVC5
if [ ! -f /bin/cvc5 ]
then
    mkdir -p /deps/cvc5
    wget $CVC5_URL -O /deps/cvc5/cvc5
    chmod +x /deps/cvc5/cvc5
    cp /deps/cvc5/cvc5 /bin/cvc5
fi

# install meson for bitwuzla
if [ ! -f /usr/local/bin/meson ]
then
    mkdir -p /deps/meson
    wget $MESON_URL -O /deps/meson.tar.gz
    tar -x -f /deps/meson.tar.gz --one-top-level=/deps/meson
    cd /deps/meson/*
    pip3 install meson
fi

# install bitwuzla
if [ ! -f /usr/local/bin/bitwuzla ]
then
    mkdir -p /deps/bitwuzla
    git clone https://github.com/bitwuzla/bitwuzla.git /deps/bitwuzla
    cd /deps/bitwuzla
    git checkout 0f91309246bec2a5037a770137bc79e2489ed714
    ./configure.py
    cd build && ninja install
fi

# # fetch Yices
# if [ ! -f /bin/yices ]
# then
#     mkdir -p /deps/yices
#     wget $YICES_URL -O /deps/yices.tar.gz
#     tar -x -f /deps/yices.tar.gz --one-top-level=/deps/yices
#     cp /deps/yices/*/bin/yices /bin/yices
#     cp /deps/yices/*/bin/yices-smt2 /bin/yices-smt2
# fi
