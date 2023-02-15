#!/bin/bash
set -exo pipefail

# Install golang
mkdir $GOROOT
GO_VERSION=1.20.1
GO_ARCHIVE="go${GO_VERSION}.linux-arm64.tar.gz"
wget "https://dl.google.com/go/${GO_ARCHIVE}"
tar -xvf $GO_ARCHIVE
mv go/* "$GOROOT"
rm $GO_ARCHIVE

go env -w GO111MODULE=on
go env -w GOPROXY=https://proxy.golang.org,direct
go env -w GOFLAGS=-buildvcs=false