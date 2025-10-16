#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

# Function to display usage
usage() {
    echo "Usage: $0 <expected_version_prefix>"
    echo "  expected_version_prefix: Version prefix to match (e.g., '2', '2.2', '2.2.4')"
    echo ""
    echo "This script checks if the installed AWS CLI version matches the expected prefix."
    echo "Prefix matching means all components of the expected prefix must match"
    echo "the corresponding components of the actual version."
    echo ""
    echo "Examples:"
    echo "  $0 2        # Matches any 2.x.x version (e.g., 2.1.0, 2.15.3)"
    echo "  $0 2.2      # Matches any 2.2.x version (e.g., 2.2.0, 2.2.47)"
    echo "  $0 2.2.4    # Matches any 2.2.4.x version (e.g., 2.2.4, 2.2.4.1)"
    echo ""
    echo "Non-matching examples:"
    echo "  Version 2.2.4 does NOT match prefix 2.3 or 3"
    exit 1
}

# Function to get AWS CLI version
get_aws_cli_version() {
    local version_output
    local version
    
    # Check if aws command exists
    if ! command -v aws >/dev/null 2>&1; then
        echo "Error: AWS CLI is not installed or not in PATH" >&2
        return 1
    fi
    
    # Get version output from AWS CLI
    if ! version_output=$(aws --version 2>&1); then
        echo "Error: Failed to get version from AWS CLI" >&2
        return 1
    fi
    
    # Extract version number from output
    # AWS CLI version output format: "aws-cli/2.2.4 Python/3.8.8 Linux/5.4.0-74-generic exe/x86_64.ubuntu.20"
    # or: "aws-cli/1.18.69 Python/3.6.9 Linux/5.4.0-74-generic botocore/1.16.19"
    version=$(echo "$version_output" | grep -oE 'aws-cli/[0-9]+\.[0-9]+(\.[0-9]+)*' | sed 's/aws-cli\///')
    
    if [[ -z "$version" ]]; then
        echo "Error: Could not extract version from AWS CLI output: $version_output" >&2
        return 1
    fi
    
    echo "$version"
}

# Function to check if version matches prefix
version_matches_prefix() {
    local actual_version="$1"
    local expected_prefix="$2"
    
    # Split versions into arrays by dots
    IFS='.' read -ra actual_parts <<< "$actual_version"
    IFS='.' read -ra expected_parts <<< "$expected_prefix"
    
    # Check if expected prefix has more parts than actual version
    if [[ ${#expected_parts[@]} -gt ${#actual_parts[@]} ]]; then
        return 1
    fi
    
    # Compare each part of the prefix
    for i in "${!expected_parts[@]}"; do
        if [[ "${actual_parts[i]}" != "${expected_parts[i]}" ]]; then
            return 1
        fi
    done
    
    return 0
}

# Main script
main() {
    # Check arguments
    if [[ $# -ne 1 ]]; then
        echo "Error: Exactly 1 argument required" >&2
        usage
    fi
    
    local expected_prefix="$1"
    
    # Validate expected prefix format
    if ! echo "$expected_prefix" | grep -qE '^[0-9]+(\.[0-9]+)*$'; then
        echo "Error: Invalid version prefix format: $expected_prefix" >&2
        echo "Expected format: number or number.number (e.g., '2', '2.2', '2.2.4')" >&2
        exit 1
    fi
    
    # Get actual AWS CLI version
    local actual_version
    if ! actual_version=$(get_aws_cli_version); then
        exit 1
    fi
    
    echo "AWS CLI version: $actual_version"
    echo "Expected prefix: $expected_prefix"
    
    # Check if version matches prefix
    if version_matches_prefix "$actual_version" "$expected_prefix"; then
        echo "Version matches expected prefix"
        exit 0
    else
        echo "Version does not match expected prefix"
        exit 1
    fi
}

# Run main function with all arguments
main "$@"
