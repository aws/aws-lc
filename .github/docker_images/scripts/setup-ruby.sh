#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

RBENV_ROOT="${RBENV_ROOT:-/.rbenv}"
RUBY_VERSION=${RUBY_VERSION:-3.4.3}

git clone --depth 1 https://github.com/rbenv/rbenv.git "${RBENV_ROOT}"
mkdir -p "${RBENV_ROOT}/plugins"
git clone --depth 1 https://github.com/rbenv/ruby-build.git "${RBENV_ROOT}/plugins/ruby-build"
sh ${RBENV_ROOT}/plugins/ruby-build/install.sh

rbenv install "${RUBY_VERSION}"

rbenv global "${RUBY_VERSION}"
