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
cp $TMP/mldsa/src/* $SRC

# Copy x86_64 backend (NTT/INTT only)
mkdir -p $SRC/native/x86_64/src
# Backend API and specification assumed by mldsa-native frontend
cp $TMP/mldsa/src/native/api.h $SRC/native
# Copy x86_64 backend implementation - NTT/INTT only
cp $TMP/mldsa/src/native/x86_64/meta.h $SRC/native/x86_64
# Copy only NTT/INTT assembly and supporting constants
cp $TMP/mldsa/src/native/x86_64/src/ntt.S $SRC/native/x86_64/src/
cp $TMP/mldsa/src/native/x86_64/src/intt.S $SRC/native/x86_64/src/
cp $TMP/mldsa/src/native/x86_64/src/nttunpack.S $SRC/native/x86_64/src/
cp $TMP/mldsa/src/native/x86_64/src/consts.c $SRC/native/x86_64/src/
cp $TMP/mldsa/src/native/x86_64/src/consts.h $SRC/native/x86_64/src/
cp $TMP/mldsa/src/native/x86_64/src/arith_native_x86_64.h $SRC/native/x86_64/src/

# We use the custom `mldsa_native_config.h`, so can remove the default one
rm -f $SRC/config.h

# Copy formatting file
cp $TMP/.clang-format $SRC

# Copy and statically simplify BCM file
# The static simplification is not necessary, but improves readability
# by removing directives related to the FIPS-202 backend that we provide
# via our own glue layer.
unifdef -DMLD_CONFIG_FIPS202_CUSTOM_HEADER                             \
        -UMLD_CONFIG_USE_NATIVE_BACKEND_FIPS202                        \
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

# Remove non-NTT/INTT includes from the BCM file (files not imported)
echo "Remove unused native backend includes from BCM file"
# Remove all aarch64 includes (not imported)
sed "${SED_I[@]}" '/native\/aarch64/d' $SRC/mldsa_native_bcm.c
# Remove x86_64 AVX2 C files (not imported)
sed "${SED_I[@]}" '/poly_caddq_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/poly_chknorm_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/poly_decompose_32_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/poly_decompose_88_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/poly_use_hint_32_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/poly_use_hint_88_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/polyz_unpack_17_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/polyz_unpack_19_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/rej_uniform_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/rej_uniform_eta2_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/rej_uniform_eta4_avx2.c/d' $SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/rej_uniform_table.c/d' $SRC/mldsa_native_bcm.c

# Strip arith_native_x86_64.h to only NTT/INTT/nttunpack declarations
echo "Strip arith_native_x86_64.h to only NTT/INTT/nttunpack declarations"
# Create minimal header with only NTT/INTT/nttunpack
cat > $SRC/native/x86_64/src/arith_native_x86_64.h << 'HEADER_EOF'
/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLD_ARITH_NATIVE_X86_64_H
#define MLD_ARITH_NATIVE_X86_64_H

#include <stdint.h>
#include "../../../params.h"
#include "consts.h"

/* NTT forward transformation */
#define mld_ntt_avx2 MLD_NAMESPACE(ntt_avx2)
void mld_ntt_avx2(int32_t r[MLDSA_N], const int32_t *qdata);

/* Inverse NTT transformation */
#define mld_invntt_avx2 MLD_NAMESPACE(invntt_avx2)
void mld_invntt_avx2(int32_t r[MLDSA_N], const int32_t *qdata);

/* NTT unpack - permute from bitreversed to custom order */
#define mld_nttunpack_avx2 MLD_NAMESPACE(nttunpack_avx2)
void mld_nttunpack_avx2(int32_t *r);

#endif /* MLD_ARITH_NATIVE_X86_64_H */
HEADER_EOF

# Strip meta.h to only NTT/INTT with custom order - create minimal version
echo "Strip meta.h to only NTT/INTT with custom order"
cat > $SRC/native/x86_64/meta.h << 'META_EOF'
/*
* Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLD_NATIVE_X86_64_META_H
#define MLD_NATIVE_X86_64_META_H

/* Identifier for this backend so that source and assembly files
 * in the build can be appropriately guarded. */
#define MLD_ARITH_BACKEND_X86_64_DEFAULT

#define MLD_USE_NATIVE_NTT_CUSTOM_ORDER
#define MLD_USE_NATIVE_NTT
#define MLD_USE_NATIVE_INTT

#if !defined(__ASSEMBLER__)
#include <string.h>
#include "../../common.h"
#include "../api.h"
#include "src/arith_native_x86_64.h"

static MLD_INLINE void mld_poly_permute_bitrev_to_custom(int32_t data[MLDSA_N])
{
  if (mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    mld_nttunpack_avx2(data);
  }
}

MLD_MUST_CHECK_RETURN_VALUE
static MLD_INLINE int mld_ntt_native(int32_t data[MLDSA_N])
{
  if (!mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    return MLD_NATIVE_FUNC_FALLBACK;
  }

  mld_ntt_avx2(data, mld_qdata);
  return MLD_NATIVE_FUNC_SUCCESS;
}

MLD_MUST_CHECK_RETURN_VALUE
static MLD_INLINE int mld_intt_native(int32_t data[MLDSA_N])
{
  if (!mld_sys_check_capability(MLD_SYS_CAP_AVX2))
  {
    return MLD_NATIVE_FUNC_FALLBACK;
  }
  mld_invntt_avx2(data, mld_qdata);
  return MLD_NATIVE_FUNC_SUCCESS;
}

#endif /* !__ASSEMBLER__ */

#endif /* !MLD_NATIVE_X86_64_META_H */
META_EOF

echo "Fixup include paths"
sed "${SED_I[@]}" 's/#include "src\/\([^"]*\)"/#include "\1"/' $SRC/mldsa_native_bcm.c

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
  sed "${SED_I[@]}" 's/#include "\.\.\/\.\.\/\.\.\/common\.h"/#include "_internal_s2n_bignum.h"/' "$file"

  func_name=$(grep -o '\.global MLD_ASM_NAMESPACE(\([^)]*\))' "$file" | sed 's/\.global MLD_ASM_NAMESPACE(\([^)]*\))/\1/')
  if [ -n "$func_name" ]; then
    sed "${SED_I[@]}" "s/\.global MLD_ASM_NAMESPACE($func_name)/        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_$func_name)\n        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_$func_name)/" "$file"
    sed "${SED_I[@]}" "s/MLD_ASM_FN_SYMBOL($func_name)/S2N_BN_SYMBOL(mldsa_$func_name):/" "$file"
    # Remove MLD_ASM_FN_SIZE line (not present in s2n-bignum convention)
    sed "${SED_I[@]}" "/MLD_ASM_FN_SIZE($func_name)/d" "$file"
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