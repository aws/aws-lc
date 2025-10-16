#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

GO_ENVROOT="/.goenv"
GO_VERSION=${GO_VERSION:-1.25.1}

git clone https://github.com/go-nv/goenv.git "${GO_ENVROOT}"

goenv install "${GO_VERSION}"

goenv global "${GO_VERSION}"
