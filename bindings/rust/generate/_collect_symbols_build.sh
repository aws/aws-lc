#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e

function usage {
  echo "Usage: $(basename $0)"
}

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
AWS_LC_DIR=$( cd -- "${SCRIPT_DIR}/../../../" &> /dev/null && pwd)
TMP_DIR="${AWS_LC_DIR}"/bindings/rust/tmp
RAND_NAME=$(od -vN 8 -An -tx1 /dev/urandom | tr -d " \n" )
BUILD_DIR=${TMP_DIR}/BUILD-${RAND_NAME}

if [[ ! -d ${TMP_DIR} ]]; then
  echo "$(basename $0)" Sanity Check Failed
  exit 1
fi

echo Building in: ${BUILD_DIR}
mkdir -p ${BUILD_DIR}
pushd ${BUILD_DIR}

if [[ $(type -P "cmake3") ]]; then
  CMAKE=cmake3
else
  CMAKE=cmake
fi

go env -w GOPROXY=direct
${CMAKE} ${AWS_LC_DIR} -GNinja
${CMAKE} --build . --target ssl

go run ${AWS_LC_DIR}/util/read_symbols.go -out symbols-crypto.txt ./crypto/libcrypto.a
go run ${AWS_LC_DIR}/util/read_symbols.go -out symbols-ssl.txt ./ssl/libssl.a
cat symbols-crypto.txt symbols-ssl.txt | sort | uniq | grep -v -e '^_\?bignum' > symbols.txt

popd
echo DONE
