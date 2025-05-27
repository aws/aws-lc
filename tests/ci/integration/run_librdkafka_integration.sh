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
KAFKA_TEST_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/librdkafka_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"

mkdir -p ${SCRATCH_FOLDER}
rm -rf "${SCRATCH_FOLDER:?}"/*
cd ${SCRATCH_FOLDER}

function kafka_build() {
  export CFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include ${CFLAGS}"
  export CXXFLAGS="-I${AWS_LC_INSTALL_FOLDER}/include ${CXXFLAGS}"
  export LDFLAGS="-L${AWS_LC_INSTALL_FOLDER}/lib ${LDFLAGS}"
  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"

  ./configure --prefix="$KAFKA_BUILD_PREFIX"
  make -j install
  make check

  local kafka_executable="${KAFKA_BUILD_PREFIX}/lib/librdkafka.so"
  ldd ${kafka_executable} \
    | grep "${AWS_LC_INSTALL_FOLDER}/lib/libcrypto.so" || exit 1
}

function kafka_run_tests() {
  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"
  python3 -m venv venv
  source venv/bin/activate

  pushd ${KAFKA_SRC_FOLDER}/tests
  python3 -m pip install -U -r requirements.txt
  python3 -m trivup.clusters.KafkaCluster --version 3.9.0 << EOF
  make -j quick
  exit
EOF
}

# This patch is only needed to execute the tests. A run_test executable is not
# available with the make quick target, this patch allows us to build that executable first.
function kafka_patch_test() {
  patchfile="${KAFKA_TEST_PATCH_FOLDER}/librdkafka-testing.patch"
  echo "Apply patch $patchfile..."
  patch -p1 --quiet -i "$patchfile"
}

git clone https://github.com/confluentinc/librdkafka.git ${KAFKA_SRC_FOLDER}
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DCMAKE_INSTALL_LIBDIR=lib -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1

# Build openvpn from source.
pushd ${KAFKA_SRC_FOLDER}
kafka_patch_test
kafka_build
kafka_run_tests
popd
