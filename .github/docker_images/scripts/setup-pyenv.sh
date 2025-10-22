#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

PYENV_ROOT="${PYENV_ROOT:-/.pyenv}"

git clone --depth 1 https://github.com/pyenv/pyenv.git "${PYENV_ROOT}"
