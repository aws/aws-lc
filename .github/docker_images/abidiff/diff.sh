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

# https://sourceware.org/libabigail/manual/abidiff.html
abidiff --hd1 "/previous/include" --hd2 "/next/include" "/previous/${ARTIFACT_PATH}" "/next/${ARTIFACT_PATH}"

# From the manual page:
#
# The exit code of the abidiff command is either 0 if the ABI of the binaries being compared are equal,
# or non-zero if they differ or if the tool encountered an error.
# ...
# The third bit, of value 4, named ABIDIFF_ABI_CHANGE means the ABI of the binaries being compared are different.
# The fourth bit, of value 8, named ABIDIFF_ABI_INCOMPATIBLE_CHANGE means the ABI of the binaries compared are different
# in an incompatible way. If this bit is set, then the ABIDIFF_ABI_CHANGE bit must be set as well. If the
# ABIDIFF_ABI_CHANGE is set and the ABIDIFF_INCOMPATIBLE_CHANGE is NOT set, then it means that the ABIs being compared
# might or might not be compatible. In that case, a human being needs to review the ABI changes to decide if they are
# compatible or not.
if [[ $? -ge 4 ]]; then
  exit 1
else
  exit 0
fi
