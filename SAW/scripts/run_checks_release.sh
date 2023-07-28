#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

# The following proofs use Release settings in CMake.

# TODO: reenable proof on SHA-256 when resolved https://github.com/awslabs/aws-lc-verification/issues/32
# If |*_SELECTCHECK| env variable exists, skip quick check of other algorithms.
if [ -n "${AES_GCM_SELECTCHECK}" ]; then
  # The proof for aesni_gcm_en[de]crypt requires having more than 6 function arguments.
  # Disabling the following proof due to lack of support of such a scenario in SAW.
  # The existing proof works on AWS-LC commit 7bdae64
  # (https://github.com/aws/aws-lc/commit/7bdae649ee6a723a5197e27ec3770c37f6a64e85) and before
  # (cd proof/AES && go run AES-GCM-check-entrypoint.go)
  return
fi

# If |*_SELECTCHECK| env variable does not exist, run quick check of all algorithms.
/usr/bin/python3 ./scripts/parallel.py --file ./scripts/release_jobs.sh
