#!/bin/sh -ex

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

(cd SAW && ./scripts/install.sh && ./scripts/entrypoint_check.sh)
