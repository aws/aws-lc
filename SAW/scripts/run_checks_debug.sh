#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

# The RSA proofs currently require the source code to be built with Debug
# settings in CMake.

saw proof/RSA/verify-RSA.saw
