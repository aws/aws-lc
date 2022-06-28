#!/usr/bin/env bash
set -e

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.

function usage {
  echo
  echo "Usage: $(basename $0) [AWS_ACCOUNT_ID]"
  echo
  echo "    AWS_ACCOUNT_ID - The account providing docker images for the build."
  echo
}

# if [ -z "${1}" ]; then
#   usage
#   exit 1
# fi

AWS_ACCOUNT_ID="${1}"
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
CRATE_TEMPLATE_DIR="${AWS_LC_DIR}"/bindings/rust/aws-lc-sys-template
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp

if [[ ! -d ${AWS_LC_DIR} || ! -d ${TMP_DIR} ]]; then
  echo "$(basename $0)" Sanity Check Failed
  exit 1
fi

if [[ ! -r "${TMP_DIR}/symbols.txt" ]]; then
  echo Symbol file not found.
  echo Performing build for supported platforms.
  ${SCRIPT_DIR}/_run_supported_symbol_builds.sh ${AWS_ACCOUNT_ID}
fi

if [[ ! -r "${TMP_DIR}/symbols.txt" ]]; then
  echo Symbol file not found after builds performed.
  exit 1
fi

CRATE_DIR="${TMP_DIR}"/aws-lc-sys
CRATE_DEPS_DIR="${CRATE_DIR}"/deps
echo Preparing crate directory: ${CRATE_DIR}
rm -rf "${CRATE_DIR}"
mkdir -p "${CRATE_DIR}"
mkdir -p "${CRATE_DEPS_DIR}"/aws-lc/

cp -r "${CRATE_TEMPLATE_DIR}"/* "${CRATE_DIR}"/

cp -r "${AWS_LC_DIR}"/crypto  \
      "${AWS_LC_DIR}"/ssl  \
      "${AWS_LC_DIR}"/include \
      "${AWS_LC_DIR}"/tool \
      "${AWS_LC_DIR}"/decrepit \
      "${AWS_LC_DIR}"/CMakeLists.txt \
      "${AWS_LC_DIR}"/LICENSE \
      "${AWS_LC_DIR}"/sources.cmake \
      "${CRATE_DEPS_DIR}"/aws-lc/

mkdir -p "${CRATE_DEPS_DIR}"/aws-lc/util
cp -r  "${AWS_LC_DIR}"/util/fipstools "${CRATE_DEPS_DIR}"/aws-lc/util

mkdir -p "${CRATE_DEPS_DIR}"/aws-lc/third_party/
cp -r  "${AWS_LC_DIR}"/third_party/googletest "${AWS_LC_DIR}"/third_party/s2n-bignum "${AWS_LC_DIR}"/third_party/fiat "${CRATE_DEPS_DIR}"/aws-lc/third_party/

mkdir -p  "${CRATE_DEPS_DIR}"/aws-lc/tests/compiler_features_tests
cp "${AWS_LC_DIR}"/tests/compiler_features_tests/*.c "${CRATE_DEPS_DIR}"/aws-lc/tests/compiler_features_tests
