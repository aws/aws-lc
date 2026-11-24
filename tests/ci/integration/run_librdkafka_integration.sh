#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

source tests/ci/common_posix_setup.sh

# Optional first argument: the librdkafka git ref (tag or branch) to test
# against. Defaults to the default branch when unset so local runs keep
# working.
LIBRDKAFKA_REF="${1:-}"

# Optional second argument: comma-separated librdkafka test numbers to skip
# during `make quick`. The upstream runner treats TESTS_SKIP as a substring
# match on the test number (for example "0151,0182"). Unset runs the full
# quick suite.
LIBRDKAFKA_TESTS_SKIP="${2:-}"

# Set up environment.

# SYS_ROOT
#  - SRC_ROOT(aws-lc)
#  - SCRATCH_FOLDER
#    - KAFKA_SRC_FOLDER
#    - AWS_LC_BUILD_FOLDER
#    - AWS_LC_INSTALL_FOLDER

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SYS_ROOT}/KAFKA_BUILD_ROOT"
KAFKA_SRC_FOLDER="${SCRATCH_FOLDER}/librdkafka"
KAFKA_BUILD_PREFIX="${KAFKA_SRC_FOLDER}/build/install"
KAFKA_TEST_PATCH_FOLDER="${SRC_ROOT}/tests/ci/integration/librdkafka_patch"
AWS_LC_BUILD_FOLDER="${SCRATCH_FOLDER}/aws-lc-build"
AWS_LC_INSTALL_FOLDER="${SCRATCH_FOLDER}/aws-lc-install"
KAFKA_VERSION="3.9.1"
KAFKA_ARCHIVE="${SCRATCH_FOLDER}/kafka_2.13-${KAFKA_VERSION}.tgz"
KAFKA_DOWNLOAD_URL="https://archive.apache.org/dist/kafka/${KAFKA_VERSION}/kafka_2.13-${KAFKA_VERSION}.tgz"

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
  ${AWS_LC_BUILD_FOLDER}/check-linkage.sh "${kafka_executable}" crypto || exit 1
}

function kafka_run_tests() {
  export LD_LIBRARY_PATH="${AWS_LC_INSTALL_FOLDER}/lib"
  python3 -m venv venv
  source venv/bin/activate

  pushd ${KAFKA_SRC_FOLDER}/tests
  python3 -m pip install -U -r requirements.txt
  # Trivup streams each download directly into tar without retrying the same
  # URL. Download and validate once so truncated responses do not fail CI.
  curl --fail --location --retry 5 --retry-all-errors --silent --show-error \
    --output "${KAFKA_ARCHIVE}" "${KAFKA_DOWNLOAD_URL}"
  tar -tzf "${KAFKA_ARCHIVE}" > /dev/null
  export KAFKA_URL="file://${KAFKA_ARCHIVE}"
  # Export TESTS_SKIP inside the trivup shell so `make quick` actually sees it.
  local quick_cmd="make -j quick"
  if [[ -n "${LIBRDKAFKA_TESTS_SKIP}" ]]; then
    quick_cmd="export TESTS_SKIP=${LIBRDKAFKA_TESTS_SKIP}; ${quick_cmd}"
  fi
  python3 -m trivup.clusters.KafkaCluster --version "${KAFKA_VERSION}" << EOF
  ${quick_cmd}
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

# Clone librdkafka. When LIBRDKAFKA_REF is set (e.g. a release tag), check out
# that ref; otherwise track the default branch.
if [[ -n "${LIBRDKAFKA_REF}" ]]; then
  git clone --depth 1 --branch "${LIBRDKAFKA_REF}" https://github.com/confluentinc/librdkafka.git "${KAFKA_SRC_FOLDER}"
else
  git clone https://github.com/confluentinc/librdkafka.git "${KAFKA_SRC_FOLDER}"
fi
mkdir -p ${AWS_LC_BUILD_FOLDER} ${AWS_LC_INSTALL_FOLDER}
ls

aws_lc_build "$SRC_ROOT" "$AWS_LC_BUILD_FOLDER" "$AWS_LC_INSTALL_FOLDER" -DCMAKE_INSTALL_LIBDIR=lib -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF -DCMAKE_BUILD_TYPE=Debug -DBUILD_SHARED_LIBS=1

# Build openvpn from source.
pushd ${KAFKA_SRC_FOLDER}
kafka_patch_test
kafka_build
kafka_run_tests
popd
