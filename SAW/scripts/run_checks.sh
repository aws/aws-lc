#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

saw proof/SHA256/SHA256.saw
(cd proof/SHA512 && go run SHA512-384-check-entrypoint.go)
saw proof/SHA512/verify-SHA512-512-quickcheck.saw
(cd proof/HMAC && go run HMAC-check-entrypoint.go)
# TODO: add select check flavors for AES-GCM.
saw proof/AES/verify-AES-GCM.saw
