#!/usr/bin/env bash
set -e

# Read and validate the release input parameter
RELEASE="${INPUT_RELEASE:-main}"
REPO_PATH="${INPUT_PATH:-.}"

# Validate that the release parameter is one of the allowed values
if [[ ! "$RELEASE" =~ ^(main|fips1|fips2|fips3)$ ]]; then
  echo "Error: Invalid release parameter. Allowed values are: main, fips1, fips2, fips3"
  exit 1
fi

echo "Using release type: $RELEASE"

# Validate that the directory exists
if [ ! -d "$REPO_PATH" ]; then
  echo "Error: Directory '$REPO_PATH' does not exist"
  exit 1
fi

# Validate that the directory is a git repository
if [ ! -d "$REPO_PATH/.git" ] && ! git -C "$REPO_PATH" rev-parse --git-dir > /dev/null 2>&1; then
  echo "Error: Directory '$REPO_PATH' is not a git repository"
  exit 1
fi

echo "Using git repository in directory: $REPO_PATH"

# Ensure we have all tags
git -C "$REPO_PATH" fetch --tags

# Different tag format based on release type
if [[ "$RELEASE" == "main" ]]; then
  # For main release, use vX.Y.Z format
  echo "Looking for tags in vX.Y.Z format..."
  LATEST_TAG=$(git -C "$REPO_PATH" tag -l 'v[0-9]*.[0-9]*.[0-9]*' | sort -V | tail -n 1)
  
  # Extract version without the 'v' prefix
  LATEST_VERSION=${LATEST_TAG#v}
else
  # Extract the FIPS version number from the release parameter (e.g., fips1 -> 1)
  FIPS_VERSION=${RELEASE#fips}
  
  # For FIPS releases, use AWS-LC-FIPS-N.Y.Z format where N is the FIPS version
  echo "Looking for tags in AWS-LC-FIPS-${FIPS_VERSION}.Y.Z format..."
  LATEST_TAG=$(git -C "$REPO_PATH" tag -l "AWS-LC-FIPS-${FIPS_VERSION}.[0-9]*.[0-9]*" | sort -V | tail -n 1)
  
  # Extract version without the AWS-LC-FIPS- prefix
  LATEST_VERSION=${LATEST_TAG#AWS-LC-FIPS-}
fi

# Handle case where no matching tag was found
if [[ -z "$LATEST_TAG" ]]; then
  echo "error: No matching tags found for release type: $RELEASE"
  exit 1
fi

# Set outputs for GitHub Actions
echo "latest-tag=${LATEST_TAG}" >> $GITHUB_OUTPUT
echo "latest-version=${LATEST_VERSION}" >> $GITHUB_OUTPUT

# Print for logging
echo "Latest tag: ${LATEST_TAG}"
echo "Latest version: ${LATEST_VERSION}"
