#!/bin/bash

GITHUB_SERVER_URL=https://github.com/
GITHUB_REPOSITORY=${GITHUB_REPOSITORY:=pq-code-package/mlkem-native.git}
GITHUB_SHA=${GITHUB_SHA:=main}

SRC=mlkem
TMP=$(mktemp -d) || exit 1
echo "Temporary working directory: $TMP"

# Check if source directory already exists
if [ -d "$SRC" ]; then
    echo "Source directory or symlink $SRC does already exist -- please remove it before re-running the importer"
    exit 1
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

popd

echo "Pull source code from remote repository..."

# Copy mlkem-native source tree -- C-only, no FIPS-202
mkdir $SRC
cp $TMP/mlkem/* $SRC
# Copy and statically simplify BCM file
unifdef -DMLK_MONOBUILD_CUSTOM_FIPS202                          \
        -UMLK_MONOBUILD_WITH_NATIVE_ARITH                       \
        -UMLK_MONOBUILD_WITH_NATIVE_FIPS202                     \
        $TMP/examples/monolithic_build/mlkem_native_monobuild.c \
        > mlkem_native_bcm.c

echo "Remove temporary artifacts ..."
rm -rf $TMP

echo "Generating META.yml file ..."
cat <<EOF > META.yml
name: mlkem-native
source: $GITHUB_REPOSITORY
branch: $GITHUB_SHA
commit: $GITHUB_COMMIT
imported-at: $(date "+%Y-%m-%dT%H:%M:%S%z")
EOF
