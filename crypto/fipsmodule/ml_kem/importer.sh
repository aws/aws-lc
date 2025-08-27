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

# Copy mlkem-native source tree -- C source
mkdir $SRC
cp $TMP/mlkem/src/* $SRC

# Copy AArch64 backend
mkdir -p $SRC/native/aarch64/src
# Backend API and specification assumed by mlkem-native frontend
cp $TMP/mlkem/src/native/api.h $SRC/native
# Copy AArch64 backend implementation
cp $TMP/mlkem/src/native/aarch64/meta.h $SRC/native/aarch64
cp $TMP/mlkem/src/native/aarch64/src/* $SRC/native/aarch64/src

# Copy x86_64 backend
mkdir -p $SRC/native/x86_64/src
# Backend API and specification assumed by mlkem-native frontend
cp $TMP/mlkem/src/native/api.h $SRC/native
# Copy x86_64 backend implementation
cp $TMP/mlkem/src/native/x86_64/meta.h $SRC/native/x86_64
cp $TMP/mlkem/src/native/x86_64/src/* $SRC/native/x86_64/src

# We use the custom `mlkem_native_config.h`, so can remove the default one
rm $SRC/config.h

# Copy formatting file
cp $TMP/.clang-format $SRC

# Copy and statically simplify BCM file
# The static simplification is not necessary, but improves readability
# by removing directives related to the FIPS-202 backend and the x86_64
# arithmetic backend that are not yet imported.
# Moreover, exclude POLY_COMPRESS/DECOMPRESS functions from the x86 backend.
unifdef -DMLK_CONFIG_FIPS202_CUSTOM_HEADER                             \
        -UMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202                        \
        $TMP/mlkem/mlkem_native.c                                      \
        > $SRC/mlkem_native_bcm.c

if [[ "$(uname)" == "Darwin" ]]; then
  SED_I=(-i "")
else
  SED_I=(-i)
fi

# Exclude POLY_COMPRESS/DECOMPRESS functions from the x86 backend for now.
sed "${SED_I[@]}" '/compress_avx2.c/d' $SRC/mlkem_native_bcm.c
sed "${SED_I[@]}" '/MLK_USE_NATIVE_POLY_COMPRESS_D4/d' $SRC/native/x86_64/meta.h
sed "${SED_I[@]}" '/MLK_USE_NATIVE_POLY_COMPRESS_D5/d' $SRC/native/x86_64/meta.h
sed "${SED_I[@]}" '/MLK_USE_NATIVE_POLY_COMPRESS_D10/d' $SRC/native/x86_64/meta.h
sed "${SED_I[@]}" '/MLK_USE_NATIVE_POLY_COMPRESS_D11/d' $SRC/native/x86_64/meta.h
sed "${SED_I[@]}" '/MLK_USE_NATIVE_POLY_DECOMPRESS_D4/d' $SRC/native/x86_64/meta.h
sed "${SED_I[@]}" '/MLK_USE_NATIVE_POLY_DECOMPRESS_D5/d' $SRC/native/x86_64/meta.h
sed "${SED_I[@]}" '/MLK_USE_NATIVE_POLY_DECOMPRESS_D10/d' $SRC/native/x86_64/meta.h
sed "${SED_I[@]}" '/MLK_USE_NATIVE_POLY_DECOMPRESS_D11/d' $SRC/native/x86_64/meta.h

# Copy mlkem-native header
# This is only needed for access to the various macros defining key sizes.
# The function declarations itself are all visible in ml_kem.c by virtue
# of everything being inlined into that file.
cp $TMP/mlkem/mlkem_native.h $SRC

# Modify include paths to match position of mlkem_native_bcm.c
# In mlkem-native, the include path is "mlkem/*", while here we
# embed mlkem_native_bcm.c in the main source directory of mlkem-native,
# hence the relative import path is just ".".
echo "Fixup include paths"
sed "${SED_I[@]}" 's/#include "src\/\([^"]*\)"/#include "\1"/' $SRC/mlkem_native_bcm.c

echo "Fixup AArch64 and x86_64 assembly backend to use s2n-bignum macros"
for file in $SRC/native/aarch64/src/*.S $SRC/native/x86_64/src/*.S; do
  echo "Processing $file"
  tmp_file=$(mktemp)

  backend_define=$(if [[ "$file" == *"aarch64"* ]]; then echo "MLK_ARITH_BACKEND_AARCH64"; else echo "MLK_ARITH_BACKEND_X86_64_DEFAULT"; fi)

  # Flatten multiline preprocessor directives, then process with unifdef
  sed -e ':a' -e 'N' -e '$!ba' -e 's/\\\n/ /g' "$file" | \
    unifdef -D$backend_define -UMLK_CONFIG_MULTILEVEL_NO_SHARED -DMLK_CONFIG_MULTILEVEL_WITH_SHARED > "$tmp_file"
  mv "$tmp_file" "$file"

  # Replace common.h include and assembly macros
  sed "${SED_I[@]}" 's/#include "\.\.\/\.\.\/\.\.\/common\.h"/#include "_internal_s2n_bignum.h"/' "$file"

  func_name=$(grep -o '\.global MLK_ASM_NAMESPACE(\([^)]*\))' "$file" | sed 's/\.global MLK_ASM_NAMESPACE(\([^)]*\))/\1/')
  if [ -n "$func_name" ]; then
    sed "${SED_I[@]}" "s/\.global MLK_ASM_NAMESPACE($func_name)/        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_$func_name)\n        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_$func_name)/" "$file"
    sed "${SED_I[@]}" "s/MLK_ASM_FN_SYMBOL($func_name)/S2N_BN_SYMBOL(mlkem_$func_name):/" "$file"
  fi
done

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
