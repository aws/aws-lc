#!/bin/bash -ex

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# The container runs as root, but the git checkout was performed by another user.
# Disable git security checks that ensure files are owned by the current user.
git config --global --add safe.directory '*'
(pushd SAW; ./scripts/install.sh; popd)
export CI=true
export OPAMROOT=/root/.opam
eval $(opam env)
NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
(pushd Coq; make -j $NUM_CPU_THREADS; popd)
