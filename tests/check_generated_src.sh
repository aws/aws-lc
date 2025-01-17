#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

function decompress_generated_src() {
  pushd ./generated-src
  tar jxvf crypto_test_data.cc.tar.bz2
  rm -f crypto_test_data.cc.tar.bz2
  popd
}

decompress_generated_src

# Take current contents of generated-src and move to another directory
mv ./generated-src ./generated-src-bak

# Regenerate contents of generated-src
python3 ./util/generate_build_files.py

decompress_generated_src

# Check whether or not
if [[ $(diff -qr ./generated-src ./generated-src-bak) ]]; then 
    echo "Contents of generated-src are not up-to-date."
    exit 1;
fi

echo "Contents of generated-src are up-to-date."
