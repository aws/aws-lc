#!/bin/bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

PKG=NSym
PKG_NAME=nsym
ARCH=Linux_x86_64

DATE=`date +%F`
LIB_PATH=/root/.opam/4.14.0/lib

CUR_PATH=`pwd`
SRC_PATH=/root/${PKG}
cd ${SRC_PATH}
git config --global --add safe.directory ${SRC_PATH}
COMMIT_HASH=`git rev-parse --short HEAD`
dune build -p nsym_config @install
dune install nsym_config
dune build -p air @install
dune install air
dune build -p arm @install
dune install arm
dune build -p specs @install
dune install specs
dune build -p cosim @install
dune install cosim

echo $DATE
echo $COMMIT_HASH

RELEASE=${PKG_NAME}-${DATE}-${COMMIT_HASH}-${ARCH}
TARGET=tmp/${RELEASE}

echo ${RELEASE}

cd ${CUR_PATH}
rm -rf ./tmp
mkdir -p ${TARGET}/lib
cp -r ${LIB_PATH}/nsym_config ${TARGET}/lib/
cp -r ${LIB_PATH}/air ${TARGET}/lib/
cp -r ${LIB_PATH}/arm ${TARGET}/lib/
cp -r ${LIB_PATH}/specs ${TARGET}/lib/
cp -r ${LIB_PATH}/cosim ${TARGET}/lib/

cd tmp
find ${RELEASE}/lib -type f -name '*.ml' -delete
tar cvfz ${RELEASE}.tar.gz ${RELEASE}

echo
echo "RELEASED PACKAGE to `pwd`/${RELEASE}.tar.gz"
