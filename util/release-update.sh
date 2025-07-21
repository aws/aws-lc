#!/bin/bash

# Check if version number is provided
if [ $# -ne 1 ]; then
    echo "Usage: $0 <new_version_number>"
    echo "Example: $0 1.55.0"
    exit 1
fi

NEW_VERSION=$1
BRANCH_NAME="update-awslc-version-to-${NEW_VERSION}"

# Detect OS for sed compatibility
if [[ "$OSTYPE" == "darwin"* ]]; then
    # macOS
    SED_CMD="sed -i ''"
else
    # Linux and others
    SED_CMD="sed -i"
fi

# Create and checkout new branch
git checkout -b "$BRANCH_NAME"

# Update version numbers using sed
# Note: Using different delimiters (|) since version numbers contain dots
$SED_CMD "s|\"AWS-LC FIPS [0-9.]*\"|\"AWS-LC FIPS ${NEW_VERSION}\"|g" crypto/fipsmodule/service_indicator/service_indicator_test.cc
$SED_CMD "s|\"AWS-LC [0-9.]*\"|\"AWS-LC ${NEW_VERSION}\"|g" crypto/fipsmodule/service_indicator/service_indicator_test.cc
$SED_CMD "s|AWSLC_VERSION_NUMBER_STRING \"[0-9.]*\"|AWSLC_VERSION_NUMBER_STRING \"${NEW_VERSION}\"|g" include/openssl/base.h

# Stage changes
git add crypto/fipsmodule/service_indicator/service_indicator_test.cc include/openssl/base.h

# Commit changes
git commit -m "Prepare AWS-LC v${NEW_VERSION}"

# Push to fork (assuming 'origin' is your fork)
git push origin "$BRANCH_NAME"

echo "Changes have been committed and pushed to branch: $BRANCH_NAME"
