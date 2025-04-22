#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

# Get absolute path to script directory
SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

# Check for openssl binary in same directory
if [ -x "${SCRIPT_DIR}/openssl" ]; then
    "${SCRIPT_DIR}/openssl" rehash "$@"
else
    echo "Error: AWS-LC openssl binary not found at '${SCRIPT_DIR}/openssl'"
    exit 1
fi
