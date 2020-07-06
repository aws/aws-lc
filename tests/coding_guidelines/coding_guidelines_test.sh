#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

./tests/coding_guidelines/style.sh
# TODO: re-enable c99_gcc_test.sh when header files are moved to ./include/awslc
# ./tests/coding_guidelines/c99_gcc_test.sh
