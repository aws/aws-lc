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

echo "Remove source code from s2n-bignum that is not needed..."
code_not_needed=("benchmarks" "codebuild" "common" "tests" "tools" "x86" "arm/proofs")
for code in "${code_not_needed[@]}"; do
  rm -rf ${TMP}/${code}
done

echo "Cloned s2n-bignum folder after removing unneeded source code..."
ls -la ${TMP}

echo "Copy source code ..."
mkdir ${SRC}
cp -rH ${TMP}/* ${SRC}

echo "Copied s2n-bignum source code..."
ls -la ${SRC}

echo "Remove temporary artifacts ..."
rm -rf ${TMP}

echo "Adding ASM prefix header include to _internal_s2n_bignum.h ..."
INTERNAL_HEADER="${SRC}/include/_internal_s2n_bignum.h"
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
