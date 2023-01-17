#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -e

function usage {
  echo "Usage: $(basename "${0}")"
}

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
AWS_LC_FIPS_DIR="${TMP_DIR}"/aws-lc
BUILD_DIR="$(mktemp -d)"
SYMBOLS_TEMP_FILE="${BUILD_DIR}"/symbols-temp.txt
SYMBOLS_COLLECT_FILE="${TMP_DIR}"/symbols-collect.txt

if [[ ! -d ${TMP_DIR} ]]; then
  echo "$(basename "$0")" Sanity Check Failed
  exit 1
fi

echo Building in: "${BUILD_DIR}"
mkdir -p "${BUILD_DIR}"
pushd "${BUILD_DIR}"

if [[ $(type -P "cmake3") ]]; then
  CMAKE=cmake3
else
  CMAKE=cmake
fi

go env -w GOPROXY=direct
${CMAKE} "${AWS_LC_FIPS_DIR}" -DFIPS=1 -DBUILD_LIBSSL=ON
${CMAKE} --build . --target clean 
${CMAKE} --build . --target crypto ssl

pushd "${AWS_LC_FIPS_DIR}"
go run ./util/read_symbols.go -out "${SYMBOLS_TEMP_FILE}" "${BUILD_DIR}"/crypto/libcrypto.a "${BUILD_DIR}"/ssl/libssl.a
popd

cat "${SYMBOLS_TEMP_FILE}" >> "${SYMBOLS_COLLECT_FILE}"

popd
echo DONE


