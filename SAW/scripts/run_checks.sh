#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

saw proof/SHA256/SHA256.saw
(cd proof/SHA512 && go run SHA512-384-check-entrypoint.go)
saw proof/SHA512/verify-SHA512-512-quickcheck.saw
# TODO: add select check flavors for HMAC-SHA384 and AES-GCM.
saw proof/HMAC/verify-HMAC-SHA384-quickcheck.saw
saw proof/AES/verify-AES-GCM.saw
