#!/bin/bash -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

echo "Running objects.go to update files"
pushd crypto/obj
go run objects.go
popd

echo "Adding all changed files to the git tree"
git add -A

echo "Checking for any changes"
git diff --exit-code HEAD

# Needs to be kept in sync with crypto/CMakeLists.txt
echo "Running make_errors.go to update files"
go run ./util/make_errors.go asn1 bio bn cipher conf dh digest dsa ec ecdh ecdsa engine evp hkdf obj ocsp pem pkcs7 pkcs8 rsa ssl trust_token x509 x509v3

echo "Adding all changed files to the git tree"
git add -A

echo "Checking for any changes"
git diff --exit-code HEAD
