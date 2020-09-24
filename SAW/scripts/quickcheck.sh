#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e

saw proof/SHA256/SHA256.saw
saw proof/SHA512/verify-SHA512-384-quickcheck.saw
saw proof/SHA512/verify-SHA512-512-quickcheck.saw
saw proof/HMAC/verify-HMAC-SHA384-quickcheck.saw
