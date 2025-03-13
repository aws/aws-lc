#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Get the directory where the script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Run c_rehash with -help
output=$("${SCRIPT_DIR}/c_rehash" -help 2>&1)

# Check for either expected output
if [[ "$output" =~ "Usage: openssl rehash" ]] || [[ "$output" =~ "RehashTool: Not implemented for windows" ]]; then
    echo "Test passed: Found expected output"
    echo "PASS"
    exit 0
else
    echo "Test failed: Unexpected output"
    echo "Actual output was:"
    echo "$output"
    exit 1
fi