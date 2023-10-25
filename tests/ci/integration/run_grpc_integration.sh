#!/bin/bash -exu
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

source tests/ci/common_posix_setup.sh

# SYS_ROOT
#  |
#  - SRC_ROOT(aws-lc)
#  |
#  - SCRATCH_FOLDER
#    |
#    - grpc
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER
#    - GRPC_BUILD_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER=${SYS_ROOT}/"GRPC_BUILD_ROOT"
GRPC_SRC_FOLDER="${SCRATCH_FOLDER}/grpc"
GRPC_BUILD_FOLDER="${SCRATCH_FOLDER}/grpc/cmake/build"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf ${SCRATCH_FOLDER}/*
cd ${SCRATCH_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}

git clone --depth 1 https://github.com/grpc/grpc.git ${GRPC_SRC_FOLDER}
cd ${GRPC_SRC_FOLDER}
git submodule update --init

aws_lc_build ${SRC_ROOT} ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER} -DBUILD_SHARED_LIBS=1

# gRPC has a ton of tests focus on just the tests relevant to AWS-LC --regex '.*(tls|ssl|cert).*'
# https://github.com/grpc/grpc/tree/master/tools/run_tests#overview
# Why the spaces in the cmake parameters? It's due to a bug in argparse not being able to decide what to do with:
# -foo '-bar'
# Is -bar is a value for the -foo argument or the name of a new argument bar? https://bugs.python.org/issue9334
python3 tools/run_tests/run_tests.py -l c++ --regex '.*(tls|ssl|cert).*' --cmake_configure_extra_args \
  " -DgRPC_SSL_PROVIDER=package" " -DOPENSSL_ROOT_DIR=${AWS_LC_INSTALL_FOLDER}"
