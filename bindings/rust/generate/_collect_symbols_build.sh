#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e

function usage {
  echo "Usage: $(basename "${0}")"
}

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
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
${CMAKE} "${AWS_LC_DIR}" -DDISABLE_GO=ON -DDISABLE_PERL=ON
${CMAKE} --build . --target clean
${CMAKE} --build . --target crypto

pushd "${AWS_LC_DIR}"
go run ./util/read_symbols.go -out "${SYMBOLS_TEMP_FILE}" "${BUILD_DIR}"/crypto/libcrypto.a
popd

cat "${SYMBOLS_TEMP_FILE}" >> "${SYMBOLS_COLLECT_FILE}"

popd
echo DONE

