#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

/usr/bin/python3 ./scripts/parallel.py --file ./scripts/aarch64/release_jobs.sh
