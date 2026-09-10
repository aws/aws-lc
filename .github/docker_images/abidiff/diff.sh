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
ABIDIFF_RC=$?
set -e

# https://sourceware.org/libabigail/manual/abidiff.html
#
# The status is a bitmask and no non-zero value is a pass: bits 1 and 2 mean the
# comparison did not complete, and bit 4 on its own still needs a human to judge
# whether the difference is acceptable. Name the bits that are set, then exit
# with the status so the raw bitmask survives into the failed step.
if (( ABIDIFF_RC != 0 )); then
  echo "abidiff exited ${ABIDIFF_RC}:" >&2
  if (( ABIDIFF_RC & 1 )); then echo "  1 ABIDIFF_ERROR: abidiff failed to run" >&2; fi
  if (( ABIDIFF_RC & 2 )); then echo "  2 ABIDIFF_USAGE_ERROR: bad invocation" >&2; fi
  if (( ABIDIFF_RC & 4 )); then echo "  4 ABIDIFF_ABI_CHANGE: lib${CHECK_LIB} ABI differs, needs review" >&2; fi
  if (( ABIDIFF_RC & 8 )); then echo "  8 ABIDIFF_ABI_INCOMPATIBLE_CHANGE: lib${CHECK_LIB} ABI incompatible" >&2; fi
  exit "${ABIDIFF_RC}"
fi
