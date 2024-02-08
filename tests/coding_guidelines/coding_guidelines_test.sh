#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

./tests/coding_guidelines/style.sh
./tests/coding_guidelines/c99_gcc_test.sh
