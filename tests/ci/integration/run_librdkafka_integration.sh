#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source tests/ci/common_posix_setup.sh

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#    - SCRATCH_FOLDER
#      - KAFKA_SRC_FOLDER
#      - AWS_LC_BUILD_FOLDER
#      - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SRC_ROOT}/KAFKA_BUILD_ROOT"
KAFKA_SRC_FOLDER="${SCRATCH_FOLDER}/librdkafka"
KAFKA_BUILD_PREFIX="${KAFKA_SRC_FOLDER}/build/install"

AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function kafka_build() {
  export CFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include ${CFLAGS}"
  export CXXFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include ${CXXFLAGS}"
  export LDFLAGS="-L${AWS_LC_INSTALL_FOLDER}/lib -L${AWS_LC_INSTALL_FOLDER}/lib64 ${LDFLAGS}"
  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib ${AWS_LC_INSTALL_FOLDER}/lib64"

  ./configure --prefix="$KAFKA_BUILD_PREFIX"
  make -j install
  make check

  local kafka_executable="${KAFKA_BUILD_PREFIX}/lib/librdkafka.so"
  ldd ${kafka_executable} \
    | grep "${AWS_LC_INSTALL_FOLDER}" | grep "libcrypto.so" || exit 1
}

function kafka_run_tests() {
  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib ${AWS_LC_INSTALL_FOLDER}/lib64"
  python3 -m venv venv
  source venv/bin/activate

  pushd ${KAFKA_SRC_FOLDER}/tests
  python3 -m pip install -U -r requirements.txt
  python3 -m trivup.clusters.KafkaCluster --version 2.8.0
  sleep 30
  TESTS_SKIP=0092 make quick
}

git clone https://github.com/confluentinc/librdkafka.git ${KAFKA_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1

# Build openvpn from source.
pushd ${KAFKA_SRC_FOLDER}
kafka_build
kafka_run_tests
popd
