#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

arch="$(uname -m)"
if [[ "${arch}" == "x86_64" ]]; then
    curl "https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip" -o "awscliv2.zip"
elif [[ "${arch}" == "aarch64" ]]; then
    curl "https://awscli.amazonaws.com/awscli-exe-linux-aarch64.zip" -o "awscliv2.zip"
else
    exit 1
fi

unzip awscliv2.zip
./aws/install --bin-dir /usr/bin
rm -rf awscliv2.zip aws
