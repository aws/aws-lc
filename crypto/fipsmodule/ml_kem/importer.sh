#!/bin/bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

#
# mlkem-native -> AWS-LC importer script
#
# This script imports a version of mlkem-native into AWS-LC.
# It is meant to do all import work and leave AWS-LC in a fully
# working state.
#
# Usage:
#
# ```
# rm -rf ./mlkem # Remove any previous import
# ./import.sh
# ```
#
# This imports github.com/pq-code-package/mlkem-native/main and
# and leaves commit hash and timestamp in META.yml.
#
# If you want to import a specific commit, and/or change the
# upstream repository (for example, to your fork of mlkem-native), use
#
# ```
# GITHUB_REPOSITORY={YOUR REPOSITORY} GITHUB_SHA={COMMIT_HASH} ./import.sh [--force]
# ```
#

# Dependencies:
# - unifdef

GITHUB_SERVER_URL=https://github.com/
GITHUB_REPOSITORY=${GITHUB_REPOSITORY:=pq-code-package/mlkem-native.git}
GITHUB_SHA=${GITHUB_SHA:=main}

SRC=mlkem
TMP=$(mktemp -d) || exit 1
echo "Temporary working directory: $TMP"

# Check if necessary tools are installed
if !(which unifdef >/dev/null 2>&1); then
    echo "You need to install 'unifdef' to run the importer script."
    exit 1
fi

# Check if source directory already exists
if [ -d "$SRC" ]; then
    if [[ "$1" == "--force" ]]; then
        echo "Removing previous source directory $SRC as requested by --force"
        rm -rf $SRC
    else
        echo "Source directory $SRC does already exist -- please remove it before re-running the importer or pass --force to force removal"
        exit 1
    fi
fi

# Work in temporary directory
pushd $TMP

# Fetch repository
echo "Fetching repository ..."
git init >/dev/null
git remote add origin $GITHUB_SERVER_URL/$GITHUB_REPOSITORY >/dev/null
git fetch origin --depth 1 $GITHUB_SHA >/dev/null
git checkout FETCH_HEAD >/dev/null
GITHUB_COMMIT=$(git rev-parse FETCH_HEAD)

# Get back to AWS-LC
popd

echo "Pull source code from remote repository..."

# Copy mlkem-native source tree -- C-only, no FIPS-202
mkdir $SRC
cp $TMP/mlkem/* $SRC

# We use the custom `mlkem_native_config.h`, so can remove the default one
rm $SRC/config.h

# Copy formatting file
cp $TMP/.clang-format $SRC

# Copy and statically simplify BCM file
# The static simplification is not necessary, but improves readability
# by removing directives related to native backends that are irrelevant
# for the C-only import.
unifdef -DMLK_CONFIG_MONOBUILD_CUSTOM_FIPS202                          \
        -UMLK_CONFIG_MONOBUILD_WITH_NATIVE_ARITH                       \
        -UMLK_CONFIG_MONOBUILD_WITH_NATIVE_FIPS202                     \
        $TMP/examples/monolithic_build/mlkem_native_monobuild.c \
        > $SRC/mlkem_native_bcm.c

# Modify include paths to match position of mlkem_native_bcm.c
# In mlkem-native, the include path is "mlkem/*", while here we
# embed mlkem_native_bcm.c in the main source directory of mlkem-native,
# hence the relative import path is just ".".
if [[ "$(uname)" == "Darwin" ]]; then
  SED_I=(-i "")
else
  SED_I=(-i)
fi
echo "Fixup include paths"
sed "${SED_I[@]}" 's/#include "mlkem\/\([^"]*\)"/#include "\1"/' $SRC/mlkem_native_bcm.c

echo "Remove temporary artifacts ..."
rm -rf $TMP

# Log timestamp, repository, and commit

echo "Generating META.yml file ..."
cat <<EOF > META.yml
name: mlkem-native
source: $GITHUB_REPOSITORY
branch: $GITHUB_SHA
commit: $GITHUB_COMMIT
imported-at: $(date "+%Y-%m-%dT%H:%M:%S%z")
EOF
