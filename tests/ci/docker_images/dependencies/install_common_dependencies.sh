#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

PLATFORM=$(uname -m)

# Install golang
mkdir "$GOROOT"
GO_VERSION=1.20.1
if [[ "$PLATFORM" == *x86* ]]; then
  GO_ARCHIVE="go${GO_VERSION}.linux-amd64.tar.gz"
else
  GO_ARCHIVE="go${GO_VERSION}.linux-arm64.tar.gz"
fi
wget "https://dl.google.com/go/${GO_ARCHIVE}"
tar -xvf $GO_ARCHIVE
mv go/* "$GOROOT"
rm $GO_ARCHIVE
# Common Go configuration
go env -w GO111MODULE=on
go env -w GOFLAGS=-buildvcs=false