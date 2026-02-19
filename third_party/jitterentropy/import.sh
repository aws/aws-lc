#!/usr/bin/env bash

set -euo pipefail

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# https://github.com/smuellerDD/jitterentropy-library -> AWS-LC importer script
#
# This script imports a version of Jitter Entropy source into AWS-LC.
#
# Usage:
#
# ```
# rm -rf ./jitterentropy-library
# ./import.sh
# ```
#
# This imports Jitter Entropy from https://github.com/smuellerDD/jitterentropy-library
# and leaves import meta data in META.yml.
#
# If you want to import a specific branch/tag or from a specific repository
# either set GITHUB_TARGET or GITHUB_REPOSITORY as below:
#
# ```
# GITHUB_REPOSITORY=<repo owner>/<repo name> GITHUB_TARGET=<branch or tag> ./import.sh
# ```

GITHUB_SERVER_URL="https://github.com/"
GITHUB_REPOSITORY=${GITHUB_REPOSITORY:=smuellerDD/jitterentropy-library.git}
GITHUB_TARGET=${GITHUB_TARGET:=master}

SRC="jitterentropy-library"
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

echo "Copy source code ..."
mkdir ${SRC}
cp -rH ${TMP}/* ${SRC}

echo "Remove temporary artifacts ..."
rm -rf ${TMP}

echo "Remove upstream repository build scripts to avoid them being invoked ..."
rm "${SRC}/CMakeLists.txt"
rm "${SRC}/Makefile"

echo "Remove test folder which is unused and contains recursive paths..."
rm -rf ${SRC}/tests

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
echo "$ git add jitterentropy-library META.yml ; git commit -m \"Imported Jitter Entropy version: ${GITHUB_TARGET}\""
echo "to add new source to git tree"
echo "A submodule path have have been cached. To remove the submodule run:"
echo "$ git rm --cached third_party/jitterentropy/jitterentropy-library/tests/raw-entropy/recording_userspace/jitterentropy"
