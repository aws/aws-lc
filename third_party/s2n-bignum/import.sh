#!/usr/bin/env bash

set -euo pipefail

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# https://github.com/awslabs/s2n-bignum -> AWS-LC importer script
#
# This script imports a version of s2n-bignum source into AWS-LC.
#
# Usage:
#
# ```
# rm -rf ./s2n-bignum-imported
# ./import.sh
# ```
#
# This imports s2n-bignum from https://github.com/awslabs/s2n-bignum
# and leaves import meta data in META.yml.
#
# If you want to import a specific branch/tag or from a specific repository
# either set GITHUB_TARGET or GITHUB_REPOSITORY as below:
#
# ```
# GITHUB_REPOSITORY=<repo owner>/<repo name> GITHUB_TARGET=<branch or tag> ./import.sh
# ```

GITHUB_SERVER_URL="https://github.com/"
GITHUB_REPOSITORY=${GITHUB_REPOSITORY:=awslabs/s2n-bignum.git}
GITHUB_TARGET=${GITHUB_TARGET:=main}

SRC="s2n-bignum-imported"
TMP="TEMP_CAN_DELETE"

# Check if TMP directory already exists
if [ -d "${TMP}" ]; then
  echo "Source directory or symlink ${TMP} does already exist -- please remove it before re-running the importer"
  exit 1
fi

# Check if source directory already exists
if [ -d "${SRC}" ]; then
  echo "Source directory or symlink ${SRC} does already exist -- please remove it before re-running the importer"
  exit 1
fi

mkdir ${TMP}

echo "Fetching repository ..."
git clone ${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY} ${TMP} --branch ${GITHUB_TARGET} --single-branch > /dev/null
GITHUB_COMMIT=$(cd ${TMP} >/dev/null; git rev-parse HEAD)

echo "Cloned s2n-bignum folder"
ls -la ${TMP}

# ---------------------------------------------------------------------------
# Allowlist of files to import.
#
# Only files actually compiled by aws-lc (referenced in
# crypto/fipsmodule/CMakeLists.txt) plus headers and legal files are imported.
# ---------------------------------------------------------------------------

# Assembly files compiled on both x86_64 (x86_att/) and aarch64 (arm/).
# Paths are relative to the architecture directory.
COMMON_ASM_FILES=(
  # p256
  p256/p256_montjscalarmul.S
  p256/p256_montjscalarmul_alt.S
  p256/bignum_montinv_p256.S
  # p384
  p384/bignum_add_p384.S
  p384/bignum_sub_p384.S
  p384/bignum_neg_p384.S
  p384/bignum_tomont_p384.S
  p384/bignum_deamont_p384.S
  p384/bignum_montmul_p384.S
  p384/bignum_montmul_p384_alt.S
  p384/bignum_montsqr_p384.S
  p384/bignum_montsqr_p384_alt.S
  p384/bignum_nonzero_6.S
  p384/bignum_littleendian_6.S
  p384/p384_montjdouble.S
  p384/p384_montjdouble_alt.S
  p384/p384_montjscalarmul.S
  p384/p384_montjscalarmul_alt.S
  p384/bignum_montinv_p384.S
  # p521
  p521/bignum_add_p521.S
  p521/bignum_sub_p521.S
  p521/bignum_neg_p521.S
  p521/bignum_mul_p521.S
  p521/bignum_mul_p521_alt.S
  p521/bignum_sqr_p521.S
  p521/bignum_sqr_p521_alt.S
  p521/bignum_tolebytes_p521.S
  p521/bignum_fromlebytes_p521.S
  p521/p521_jdouble.S
  p521/p521_jdouble_alt.S
  p521/p521_jscalarmul.S
  p521/p521_jscalarmul_alt.S
  p521/bignum_inv_p521.S
  # curve25519
  curve25519/bignum_mod_n25519.S
  curve25519/bignum_neg_p25519.S
  curve25519/bignum_madd_n25519.S
  curve25519/bignum_madd_n25519_alt.S
  curve25519/edwards25519_decode.S
  curve25519/edwards25519_decode_alt.S
  curve25519/edwards25519_encode.S
  curve25519/edwards25519_scalarmulbase.S
  curve25519/edwards25519_scalarmulbase_alt.S
  curve25519/edwards25519_scalarmuldouble.S
  curve25519/edwards25519_scalarmuldouble_alt.S
  # sha3
  sha3/sha3_keccak_f1600.S
)

# Assembly files compiled only on x86_64.
X86_ONLY_ASM_FILES=(
  p384/bignum_tomont_p384_alt.S
  p384/bignum_deamont_p384_alt.S
  curve25519/curve25519_x25519.S
  curve25519/curve25519_x25519_alt.S
  curve25519/curve25519_x25519base.S
  curve25519/curve25519_x25519base_alt.S
)

# Assembly files compiled only on aarch64.
ARM_ONLY_ASM_FILES=(
  curve25519/curve25519_x25519_byte.S
  curve25519/curve25519_x25519_byte_alt.S
  curve25519/curve25519_x25519base_byte.S
  curve25519/curve25519_x25519base_byte_alt.S
  fastmul/bignum_kmul_16_32.S
  fastmul/bignum_kmul_32_64.S
  fastmul/bignum_ksqr_16_32.S
  fastmul/bignum_ksqr_32_64.S
  fastmul/bignum_emontredc_8n.S
  generic/bignum_ge.S
  generic/bignum_mul.S
  generic/bignum_optsub.S
  generic/bignum_sqr.S
  generic/bignum_copy_row_from_table.S
  generic/bignum_copy_row_from_table_8n.S
  generic/bignum_copy_row_from_table_16.S
  generic/bignum_copy_row_from_table_32.S
  sha3/sha3_keccak_f1600_alt.S
  sha3/sha3_keccak2_f1600.S
  sha3/sha3_keccak4_f1600_alt.S
  sha3/sha3_keccak4_f1600_alt2.S
)

echo "Copy source code ..."
mkdir ${SRC}

# Copy headers, legal files, and documentation
mkdir -p ${SRC}/include
cp -H ${TMP}/include/s2n-bignum.h ${TMP}/include/s2n-bignum-c89.h \
     ${TMP}/include/_internal_s2n_bignum.h ${TMP}/include/_internal_s2n_bignum_arm.h \
     ${TMP}/include/_internal_s2n_bignum_x86.h ${TMP}/include/_internal_s2n_bignum_x86_att.h \
     ${SRC}/include/
cp -H ${TMP}/LICENSE ${TMP}/NOTICE ${TMP}/README.md ${TMP}/SOUNDNESS.md ${TMP}/non_ct_functions.txt ${SRC}/
mkdir -p ${SRC}/doc
cp -H ${TMP}/doc/s2n_bignum_soundness.md ${TMP}/doc/s2n_bignum_soundness.svg ${SRC}/doc/
mkdir -p ${SRC}/x86_att
cp -H ${TMP}/x86_att/README.md ${SRC}/x86_att/README.md

# Copy assembly files using the allowlists above.
# Helper: copy a single .S file from TMP to SRC, creating parent dirs as needed.
copy_asm() {
  local relpath="$1"
  mkdir -p "${SRC}/$(dirname "${relpath}")"
  cp -H "${TMP}/${relpath}" "${SRC}/${relpath}"
}

for f in "${COMMON_ASM_FILES[@]}"; do
  copy_asm "x86_att/${f}"
  copy_asm "arm/${f}"
done

for f in "${X86_ONLY_ASM_FILES[@]}"; do
  copy_asm "x86_att/${f}"
done

for f in "${ARM_ONLY_ASM_FILES[@]}"; do
  copy_asm "arm/${f}"
done

echo "Copied s2n-bignum source code..."
ls -la ${SRC}

echo "Remove temporary artifacts ..."
rm -rf ${TMP}

echo "Adding ASM prefix header include to _internal_s2n_bignum[_arm|_x86|_x86_att].h ..."
for INTERNAL_HEADER_BASE in _internal_s2n_bignum.h _internal_s2n_bignum_arm.h _internal_s2n_bignum_x86.h _internal_s2n_bignum_x86_att.h
do
   INTERNAL_HEADER="${SRC}/include/${INTERNAL_HEADER_BASE}"
   if [ ! -f "${INTERNAL_HEADER}" ]; then
     echo "Error: ${INTERNAL_HEADER} not found"
     exit 1
   fi

   # Create a temporary file with the prefix include at the top
   TEMP_FILE=$(mktemp)
   echo '// Auto-added during import for AWS-LC symbol prefixing support' > "${TEMP_FILE}"
   echo '#include <openssl/boringssl_prefix_symbols_asm.h>' >> "${TEMP_FILE}"
   echo '' >> "${TEMP_FILE}"
   cat "${INTERNAL_HEADER}" >> "${TEMP_FILE}"
   mv "${TEMP_FILE}" "${INTERNAL_HEADER}"
   echo "Added ASM prefix header include to ${INTERNAL_HEADER}"
done

echo "Generating META.yml file ..."
cat <<EOF > META.yml
name: ${SRC}
source: ${GITHUB_REPOSITORY}
commit: ${GITHUB_COMMIT}
target: ${GITHUB_TARGET}
imported-at: $(env TZ=UTC date "+%Y-%m-%dT%H:%M:%S%z")
EOF

# Submodule path might be cached.
echo ""
echo "Post actions: Run"
echo "$ git add ${SRC} META.yml ; git commit -m \"Imported s2n-bignum version: ${GITHUB_TARGET}/${GITHUB_COMMIT}\""
echo "to add new source to git tree"
