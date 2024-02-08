#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

echo "Running objects.go to update files"
pushd crypto/obj
go run objects.go
popd

echo "Adding all changed files to the git tree"
git add -A

echo "Checking for any changes"
git diff --exit-code HEAD

echo "Running make_errors.go to update files"
go run ./util/make_errors.go ssl evp ocsp pem

echo "Adding all changed files to the git tree"
git add -A

echo "Checking for any changes"
git diff --exit-code HEAD
