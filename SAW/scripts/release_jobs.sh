#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# If |*_SELECTCHECK| env variable does not exist, run quick check of all algorithms.
saw proof/SHA512/verify-SHA512-384.saw
saw proof/SHA512/verify-SHA512-512.saw
saw proof/HMAC/verify-HMAC.saw
saw proof/KDF/verify-HKDF.saw
cd proof/AES && go run AES-GCM-check-entrypoint.go
saw proof/AES_KW/verify-AES_KW.saw
saw proof/AES_KW/verify-AES_KWP.saw
saw proof/ECDSA/verify-ECDSA.saw
saw proof/ECDH/verify-ECDH.saw
