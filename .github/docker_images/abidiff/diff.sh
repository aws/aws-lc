#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

cd /previous && /build.sh
cd /next && /build.sh

CHECK_LIB="$1"
ARTIFACT_PATH="build"
if [[ "${CHECK_LIB}" == "crypto" ]]; then
  ARTIFACT_PATH="${ARTIFACT_PATH}/crypto/libcrypto.so"
elif [[ "${CHECK_LIB}" == "ssl" ]]; then
  ARTIFACT_PATH="${ARTIFACT_PATH}/ssl/libssl.so"
else
  exit 1
fi

set +e
abidiff --hd1 "/previous/include" --hd2 "/next/include" "/previous/${ARTIFACT_PATH}" "/next/${ARTIFACT_PATH}"
if [[ $? -ge 8 ]]; then
  exit 1
else
  exit 0
fi
