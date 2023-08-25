#!/bin/sh
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

exec /usr/bin/qemu-ppc64-static -cpu e6500 "$@"
