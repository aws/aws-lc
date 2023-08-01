#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# If |*_SELECTCHECK| env variable does not exist, run quick check of all algorithms.
saw proof/SHA512/verify-SHA512-384.saw
saw proof/SHA512/verify-SHA512-512.saw
saw proof/HMAC/verify-HMAC.saw
saw proof/KDF/verify-HKDF.saw
# The proof for aesni_gcm_en[de]crypt requires having more than 6 function arguments.
# Disabling the following proof due to lack of support of such a scenario in SAW.
# The existing proof works on AWS-LC commit 7bdae64
# (https://github.com/aws/aws-lc/commit/7bdae649ee6a723a5197e27ec3770c37f6a64e85) and before
# cd proof/AES && go run AES-GCM-check-entrypoint.go
saw proof/AES_KW/verify-AES_KW.saw
saw proof/AES_KW/verify-AES_KWP.saw
saw proof/EC/verify-P384.saw
saw proof/ECDSA/verify-ECDSA.saw
saw proof/ECDH/verify-ECDH.saw
