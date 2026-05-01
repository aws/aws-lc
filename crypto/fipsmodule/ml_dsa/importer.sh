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
mkdir -p $SRC/native/x86_64/src
# Backend API and specification assumed by mldsa-native frontend
cp $TMP/mldsa/src/native/api.h $SRC/native
# Copy x86_64 backend implementation
cp $TMP/mldsa/src/native/x86_64/meta.h $SRC/native/x86_64
# Copy only assembly-backed source files (skip C intrinsics)
cp $TMP/mldsa/src/native/x86_64/src/arith_native_x86_64.h $SRC/native/x86_64/src
cp $TMP/mldsa/src/native/x86_64/src/consts.h $SRC/native/x86_64/src
cp $TMP/mldsa/src/native/x86_64/src/consts.c $SRC/native/x86_64/src
cp $TMP/mldsa/src/native/x86_64/src/*.S $SRC/native/x86_64/src

# Rename assembly files with mldsa_ prefix to avoid basename collisions
# with ML-KEM assembly files (e.g., ntt.S exists in both). This matters
# because s2n-tls's libcrypto interning uses `ar x` which extracts into
# a flat directory and would overwrite files with the same basename.
for file in $SRC/native/x86_64/src/*.S; do
  base=$(basename "$file")
  case "$base" in
    mldsa_*) ;; # already prefixed
    *) mv "$file" "$SRC/native/x86_64/src/mldsa_$base" ;;
  esac
done

# We use the custom `mldsa_native_config.h`, so can remove the default one
rm -f $SRC/config.h

# Copy formatting file
cp $TMP/.clang-format $SRC

if [[ "$(uname)" == "Darwin" ]]; then
  SED_I=(-i "")
else
  SED_I=(-i)
fi

# ================================================================
# Strip C-intrinsic content from x86_64 backend headers
#
# We only import assembly-backed operations (NTT, INTT, nttunpack,
# pointwise, polyvecl_pointwise_acc). C-intrinsic operations
# (rej_uniform, decompose, use_hint, chknorm, polyz_unpack, caddq)
# are intentionally excluded.
# ================================================================

echo "Strip C-intrinsic content from arith_native_x86_64.h"
ARITH_H=$SRC/native/x86_64/src/arith_native_x86_64.h
# Remove #include <stdint.h>
sed "${SED_I[@]}" '/#include <stdint.h>/d' "$ARITH_H"
# Remove everything between #include "consts.h" and #define mld_ntt_avx2
# (buffer length macros, comments, rej_uniform_table extern),
# but preserve one blank line separator
sed "${SED_I[@]}" '/^#include "consts.h"$/,/^#define mld_ntt_avx2/{/^#include "consts.h"$/b; /^#define mld_ntt_avx2/b; d;}' "$ARITH_H"
# Replace __contract__ annotated mld_ntt_avx2 declaration with plain declaration
sed "${SED_I[@]}" '/^void mld_ntt_avx2/,/^);$/c\void mld_ntt_avx2(int32_t *r, const int32_t *qdata);' "$ARITH_H"
# Fix mld_invntt_avx2 parameter name (upstream uses mld_qdata, we use qdata)
sed "${SED_I[@]}" 's/const int32_t \*mld_qdata);/const int32_t *qdata);/' "$ARITH_H"
# Remove C-intrinsic function declarations (rej_uniform through polyz_unpack_19)
# and the trailing blank line
sed "${SED_I[@]}" '/^#define mld_rej_uniform_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_rej_uniform_eta2_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_rej_uniform_eta4_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_poly_decompose_32_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_poly_decompose_88_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_poly_caddq_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_poly_use_hint_32_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_poly_use_hint_88_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_poly_chknorm_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_polyz_unpack_17_avx2/,/^$/d' "$ARITH_H"
sed "${SED_I[@]}" '/^#define mld_polyz_unpack_19_avx2/,/^$/d' "$ARITH_H"
# Clean up: remove consecutive blank lines left by deletions
sed "${SED_I[@]}" '/^$/N;/^\n$/d' "$ARITH_H"
# Re-insert blank line between #include "consts.h" and #define mld_ntt_avx2
sed "${SED_I[@]}" 's/^#include "consts.h"$/#include "consts.h"\n/' "$ARITH_H"

echo "Strip C-intrinsic content from meta.h"
META_H=$SRC/native/x86_64/meta.h
# Remove C-intrinsic #define MLD_USE_NATIVE_* lines
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_REJ_UNIFORM$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_REJ_UNIFORM_ETA2$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_REJ_UNIFORM_ETA4$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_POLY_DECOMPOSE_32$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_POLY_DECOMPOSE_88$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_POLY_CADDQ$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_POLY_USE_HINT_32$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_POLY_USE_HINT_88$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_POLY_CHKNORM$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_POLYZ_UNPACK_17$/d' "$META_H"
sed "${SED_I[@]}" '/#define MLD_USE_NATIVE_POLYZ_UNPACK_19$/d' "$META_H"
# Remove #include <string.h>
sed "${SED_I[@]}" '/#include <string.h>/d' "$META_H"
# Remove C-intrinsic inline function bodies (from mld_rej_uniform_native
# through mld_polyz_unpack_19_native closing brace)
sed "${SED_I[@]}" '/^static MLD_INLINE int mld_rej_uniform_native/,/^static MLD_INLINE int mld_poly_pointwise_montgomery_native/{/^static MLD_INLINE int mld_poly_pointwise_montgomery_native/!d;}' "$META_H"
# Clean up consecutive blank lines
sed "${SED_I[@]}" '/^$/N;/^\n$/d' "$META_H"

echo "Add MLD_INTERNAL_API to consts.c and consts.h"
# consts.c: add MLD_INTERNAL_API to the array definition
sed "${SED_I[@]}" 's/MLD_ALIGN const int32_t mld_qdata/MLD_ALIGN MLD_INTERNAL_API const int32_t mld_qdata/' "$SRC/native/x86_64/src/consts.c"
# consts.h: replace extern with MLD_INTERNAL_API
sed "${SED_I[@]}" 's/extern const int32_t mld_qdata\[624\]/MLD_INTERNAL_API const int32_t mld_qdata[624]/' "$SRC/native/x86_64/src/consts.h"

# ================================================================
# Process mldsa_native_bcm.c
# ================================================================

# Copy and statically simplify BCM file
# The static simplification is not necessary, but improves readability
# by removing directives related to the FIPS-202 backend that we provide
# via our own glue layer.
# Also strip AArch64 backend since we only import x86_64.
unifdef -DMLD_CONFIG_FIPS202_CUSTOM_HEADER                             \
        -UMLD_CONFIG_USE_NATIVE_BACKEND_FIPS202                        \
        -UMLD_SYS_AARCH64                                              \
        $TMP/mldsa/mldsa_native.c                                      \
        > $SRC/mldsa_native_bcm.c

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

# Strip C-intrinsic .c file includes from BCM (keep only consts.c)
echo "Strip C-intrinsic includes from mldsa_native_bcm.c"
BCM=$SRC/mldsa_native_bcm.c
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/poly_caddq_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/poly_chknorm_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/poly_decompose_32_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/poly_decompose_88_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/poly_use_hint_32_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/poly_use_hint_88_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/polyz_unpack_17_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/polyz_unpack_19_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/rej_uniform_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/rej_uniform_eta2_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/rej_uniform_eta4_avx2\.c"/d' "$BCM"
sed "${SED_I[@]}" '/^#include "native\/x86_64\/src\/rej_uniform_table\.c"/d' "$BCM"

# Strip C-intrinsic #undef entries from the x86_64 undef block
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_POLYZ_UNPACK_17$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_POLYZ_UNPACK_19$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_POLY_CADDQ$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_POLY_CHKNORM$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_POLY_DECOMPOSE_32$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_POLY_DECOMPOSE_88$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_POLY_USE_HINT_32$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_POLY_USE_HINT_88$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_REJ_UNIFORM$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_REJ_UNIFORM_ETA2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_USE_NATIVE_REJ_UNIFORM_ETA4$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_AVX2_REJ_UNIFORM_BUFLEN$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_AVX2_REJ_UNIFORM_ETA2_BUFLEN$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef MLD_AVX2_REJ_UNIFORM_ETA4_BUFLEN$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_poly_caddq_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_poly_chknorm_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_poly_decompose_32_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_poly_decompose_88_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_poly_use_hint_32_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_poly_use_hint_88_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_polyz_unpack_17_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_polyz_unpack_19_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_rej_uniform_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_rej_uniform_eta2_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_rej_uniform_eta4_avx2$/d' "$BCM"
sed "${SED_I[@]}" '/^#undef mld_rej_uniform_table$/d' "$BCM"

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

    # Add S2N_BN_SIZE_DIRECTIVE after .cfi_endproc
    sed "${SED_I[@]}" "/.cfi_endproc/a\\
\\
S2N_BN_SIZE_DIRECTIVE(mldsa_$func_name)" "$file"
  fi

  # Move ELF section before .text (match s2n-bignum convention)
  sed "${SED_I[@]}" '/#if defined(__ELF__)/,/#endif/d' "$file"
  sed "${SED_I[@]}" '/^\.text$/i\
#if defined(__ELF__)\
.section .note.GNU-stack,"",@progbits\
#endif\
' "$file"

  # Clean up: strip leading whitespace from lines left indented after unifdef
  sed "${SED_I[@]}" 's/^ \(\/\*\)/\1/' "$file"
  sed "${SED_I[@]}" 's/^ \(#include\)/#include/' "$file"
  # Remove consecutive blank lines
  sed "${SED_I[@]}" '/^$/N;/^\n$/d' "$file"
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
