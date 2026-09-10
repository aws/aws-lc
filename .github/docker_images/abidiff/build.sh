#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

# abidiff only reads libcrypto.so and libssl.so, so skip the test targets and
# the command-line tools. Both options already exist and default to ON, and
# neither changes the libraries: BUILD_TESTING adds test subdirectories and
# executables, and its one global side effect (-DBORINGSSL_HAVE_LIBUNWIND) is
# consumed only by crypto/test/abi_test.cc. BUILD_LIBSSL is independent of both
# and stays on, so libssl is still built.
cmake -S . -B build -GNinja -DBUILD_SHARED_LIBS=1 -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DBUILD_TESTING=OFF -DBUILD_TOOL=OFF
cmake --build build
