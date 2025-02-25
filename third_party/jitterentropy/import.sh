#!/bin/bash -xu

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

#
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
# This imports Jitter Entroopy from https://github.com/smuellerDD/jitterentropy-library
# and leaves import meta data in META.yml.
#
# If you want to import a specific branch/tag or from a specific repository
# either GITHUB_TARGET or GITHUB_REPOSITORY as below:
#
# ```
# GITHUB_REPOSITORY=<repo owner>/<repo name> GITHUB_TARGET=<branch or tag> ./import.sh
# ```

GITHUB_SERVER_URL="https://github.com/"
GITHUB_REPOSITORY=${GITHUB_REPOSITORY:=smuellerDD/jitterentropy-library.git}
GITHUB_TARGET=${GITHUB_TARGET:=master}

SRC="jitterentropy-library"
TMP="TEMP_CAN_DELETE"

# Check if source directory already exists
if [ -d "${SRC}" ]; then
    echo "Source directory or symlink ${SRC} does already exist -- please remove it before re-running the importer"
    exit 1
fi

mkdir ${TMP}

echo "Fetching repository ..."
git clone ${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY} ${TMP} --branch ${GITHUB_TARGET} --single-branch >/dev/null
GITHUB_COMMIT=$(cd ${TMP} >/dev/null; git rev-parse HEAD)
 
echo "Copy source code ..."
mkdir ${SRC}
cp -r ${TMP}/* ${SRC}

echo "Remove temporary artifacts ..."
rm -rf ${TMP}

# Remove upstream repo build scripts from being invoked.
rm "${SRC}/CMakeLists.txt"
rm "${SRC}/Makefile"

# submodule path might be cached
git rm --cached third_party/jitterentropy/jitterentropy-library/t
ests/raw-entropy/recording_userspace/jitterentrop | true

echo "Generating META.yml file ..."
cat <<EOF > META.yml
name: ${SRC}
source: ${GITHUB_REPOSITORY}
commit: ${GITHUB_COMMIT}
target: ${GITHUB_TARGET}
imported-at: $(date "+%Y-%m-%dT%H:%M:%S%z")
EOF
