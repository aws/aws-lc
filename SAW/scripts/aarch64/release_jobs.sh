#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

saw proof/SHA512/verify-SHA384-aarch64-neoverse-n1.saw
saw proof/SHA512/verify-SHA384-aarch64-neoverse-v1.saw
# TODO: Currently SHA512 proofs are disabled due to a safety check failure
# saw proof/SHA512/verify-SHA512-aarch64-neoverse-n1.saw
# saw proof/SHA512/verify-SHA512-aarch64-neoverse-v1.saw
