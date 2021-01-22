#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

# TODO: reenable proof on SHA-256 when resolved https://github.com/awslabs/aws-lc-verification/issues/32
(cd proof/SHA512 && go run SHA512-384-check-entrypoint.go)
saw proof/SHA512/verify-SHA512-512-quickcheck.saw
(cd proof/HMAC && go run HMAC-check-entrypoint.go)
# TODO: add select check flavors for AES-GCM and AES-KW
saw proof/AES/verify-AES-GCM.saw
saw proof/AES_KW/verify-AES_KW.saw
saw proof/AES_KW/verify-AES_KWP.saw
saw proof/ECDSA/verify-ECDSA.saw
saw proof/ECDH/verify-ECDH.saw

