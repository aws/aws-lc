#!/bin/sh -ex

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

(cd SAW && ./scripts/x86_64/install_aes_gcm.sh && ./scripts/x86_64/entrypoint_check_aes_gcm.sh)
