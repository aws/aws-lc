#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

SAW_URL='https://saw-builds.s3.us-west-2.amazonaws.com/saw-0.9.0.99-2023-03-03-Linux-x86_64.tar.gz'

mkdir -p /bin /deps

# fetch SAW
# This will override the current SAW in the docker in AWS-LC's CI
rm -rf /deps/saw
mkdir -p /deps/saw
wget $SAW_URL -O /deps/saw.tar.gz
tar -x -f /deps/saw.tar.gz --one-top-level=/deps/saw
cp /deps/saw/*/bin/saw /bin/saw
cp /deps/saw/*/bin/cryptol /bin/cryptol
