#!/bin/bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

PKG=OCaml-SMT-Interface
PKG_NAME=ocaml_smt_interface
ARCH=Linux_x86_64

DATE=`date +%F`
LIB_PATH=/root/.opam/4.14.0/lib

CUR_PATH=`pwd`
SRC_PATH=/root/${PKG}
cd ${SRC_PATH}
git config --global --add safe.directory ${SRC_PATH}
COMMIT_HASH=`git rev-parse --short HEAD`
dune build -p ${PKG_NAME} @install
dune install ${PKG_NAME}

echo $DATE
echo $COMMIT_HASH

RELEASE=${PKG_NAME}-${DATE}-${COMMIT_HASH}-${ARCH}
TARGET=tmp/${RELEASE}

echo ${RELEASE}

cd ${CUR_PATH}
rm -rf ./tmp
mkdir -p ${TARGET}/lib
cp -r ${LIB_PATH}/${PKG_NAME} ${TARGET}/lib/

cd tmp
find ${RELEASE}/lib -type f -name '*.ml' -delete
tar cvfz ${RELEASE}.tar.gz ${RELEASE}

echo
echo "RELEASED PACKAGE to `pwd`/${RELEASE}.tar.gz"
