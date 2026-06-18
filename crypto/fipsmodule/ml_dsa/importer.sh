#!/bin/bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

#
# mldsa-native -> AWS-LC importer script
#
# This script imports a version of mldsa-native into AWS-LC.
# It is meant to do all import work and leave AWS-LC in a fully
# working state.
#
# Usage:
#
# ```
# rm -rf ./mldsa # Remove any previous import
# ./importer.sh
# ```
#
# This imports github.com/pq-code-package/mldsa-native/main and
# and leaves commit hash and timestamp in META.yml.
#
# If you want to import a specific commit, and/or change the
# upstream repository (for example, to your fork of mldsa-native), use
#
# ```
# GITHUB_REPOSITORY={YOUR REPOSITORY} GITHUB_SHA={COMMIT_HASH} ./importer.sh [--force]
# ```
#

# Dependencies:
# - unifdef

GITHUB_SERVER_URL=https://github.com/
GITHUB_REPOSITORY=${GITHUB_REPOSITORY:=pq-code-package/mldsa-native.git}
GITHUB_SHA=${GITHUB_SHA:=main}

SRC=mldsa
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

# Copy mldsa-native source tree -- C source
mkdir $SRC
# Copy only files (not subdirectories like native/ and fips202/)
find $TMP/mldsa/src -maxdepth 1 -type f -exec cp {} $SRC \;

# Copy x86_64 backend
# We import all assembly (.S) files and shared headers/constants from the
# upstream x86_64 backend. The AVX2 C-intrinsic .c files (rej_uniform,
# decompose, use_hint, chknorm, polyz_unpack) are excluded — their includes
# are stripped from the BCM below.
#
# The upstream meta.h advertises both assembly and C-intrinsic operations.
# Rather than modify it, we keep a hand-maintained replacement in
# ../mldsa_x86_64_meta.h (referenced via MLD_CONFIG_ARITH_BACKEND_FILE) that
# declares only the assembly-backed subset. Upstream meta.h is not copied.
mkdir -p $SRC/native/x86_64/src
cp $TMP/mldsa/src/native/api.h $SRC/native
cp $TMP/mldsa/src/native/x86_64/src/arith_native_x86_64.h $SRC/native/x86_64/src
cp $TMP/mldsa/src/native/x86_64/src/consts.h $SRC/native/x86_64/src
cp $TMP/mldsa/src/native/x86_64/src/consts.c $SRC/native/x86_64/src
# NOTE: all imported .S files must have verified proofs in s2n-bignum.
cp $TMP/mldsa/src/native/x86_64/src/*.S $SRC/native/x86_64/src

# We use the custom `mldsa_native_config.h`, so can remove the default one
rm -f $SRC/config.h

# Copy formatting file
cp $TMP/.clang-format $SRC

# ================================================================
# Process mldsa_native_bcm.c
# ================================================================

# Copy and statically simplify BCM file
# The static simplification is not necessary, but improves readability
# by removing directives related to the FIPS-202 backend that we provide
# via our own glue layer.
unifdef -DMLD_CONFIG_FIPS202_CUSTOM_HEADER                             \
        -UMLD_CONFIG_USE_NATIVE_BACKEND_FIPS202                        \
        -UMLD_SYS_AARCH64                                              \
        $TMP/mldsa/mldsa_native.c                                      \
        > $SRC/mldsa_native_bcm.c

if [[ "$(uname)" == "Darwin" ]]; then
  SED_I=(-i "")
else
  SED_I=(-i)
fi

# Copy mldsa-native header
# This is only needed for access to the various macros defining key sizes.
# The function declarations itself are all visible in ml_dsa.c by virtue
# of everything being inlined into that file.
cp $TMP/mldsa/mldsa_native.h $SRC

# Modify include paths to match position of mldsa_native_bcm.c
# In mldsa-native, the include path is "mldsa/*", while here we
# embed mldsa_native_bcm.c in the main source directory of mldsa-native,
# hence the relative import path is just ".".
echo "Fixup include paths"
sed "${SED_I[@]}" 's/#include "src\/\([^"]*\)"/#include "\1"/' $SRC/mldsa_native_bcm.c

# Drop #include directives for the C-intrinsic .c files we did not import.
# Only consts.c (shared with the assembly backend) is kept.
echo "Strip C-intrinsic includes from mldsa_native_bcm.c"
BCM=$SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/[^"]*\.c"/{/consts\.c/!d;}' "$BCM"

# ================================================================
# Fixup x86_64 assembly backend to use s2n-bignum macros
# ================================================================

echo "Fixup x86_64 assembly backend to use s2n-bignum macros"
for file in $SRC/native/x86_64/src/*.S; do
  echo "Processing $file"
  tmp_file=$(mktemp)

  backend_define="MLD_ARITH_BACKEND_X86_64_DEFAULT"

  # Flatten multiline preprocessor directives, then process with unifdef
  sed -e ':a' -e 'N' -e '$!ba' -e 's/\\\n/ /g' "$file" | \
    unifdef -D$backend_define -UMLD_CONFIG_MULTILEVEL_NO_SHARED -DMLD_CONFIG_MULTILEVEL_WITH_SHARED > "$tmp_file"
  mv "$tmp_file" "$file"

  # Replace common.h include and assembly macros
  s2n_header="_internal_s2n_bignum_x86_att.h"
  sed "${SED_I[@]}" "s/#include \"\.\.\/\.\.\/\.\.\/common\.h\"/#include \"$s2n_header\"/" "$file"

  func_name=$(grep -o '\.global MLD_ASM_NAMESPACE(\([^)]*\))' "$file" | sed 's/\.global MLD_ASM_NAMESPACE(\([^)]*\))/\1/')
  if [ -n "$func_name" ]; then
    sed "${SED_I[@]}" "s/\.global MLD_ASM_NAMESPACE($func_name)/        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_$func_name)\n        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_$func_name)/" "$file"
    sed "${SED_I[@]}" "s/MLD_ASM_FN_SYMBOL($func_name)/S2N_BN_SYMBOL(mldsa_$func_name):/" "$file"
    sed "${SED_I[@]}" "s/MLD_ASM_FN_SIZE($func_name)/S2N_BN_SIZE_DIRECTIVE(mldsa_$func_name)/" "$file"
  fi
done

echo "Remove temporary artifacts ..."
rm -rf $TMP

# Log timestamp, repository, and commit

echo "Generating META.yml file ..."
cat <<EOF > META.yml
name: mldsa-native
source: $GITHUB_REPOSITORY
branch: $GITHUB_SHA
commit: $GITHUB_COMMIT
imported-at: $(date "+%Y-%m-%dT%H:%M:%S%z")
EOF

echo "Import complete!"
echo "Imported mldsa-native commit: $GITHUB_COMMIT"
