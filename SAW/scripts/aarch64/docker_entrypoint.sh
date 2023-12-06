#!/bin/sh -ex

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

(cd SAW && ./scripts/aarch64/install.sh && ./scripts/aarch64/entrypoint_check.sh)
