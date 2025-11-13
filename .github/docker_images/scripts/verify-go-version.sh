#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Script to verify that go command exists and matches a specified version prefix
# Usage: verify-go-version.sh <version_prefix>
# 
# Exit codes:
#   0 - Success (go command exists and version matches prefix)
#   1 - Go command not found or not go
#   2 - Version does not match prefix
#   3 - Invalid arguments

set -euo pipefail

# Function to display usage information
usage() {
    echo "Usage: $0 <version_prefix>"
    echo ""
    echo "Verifies that the go command exists and its version matches the given prefix."
    echo ""
    echo "Arguments:"
    echo "  version_prefix  Version prefix to match (e.g., '1', '1.21', '1.21.5')"
    echo ""
    echo "Examples:"
    echo "  $0 1"
    echo "  $0 1.21"
    echo "  $0 1.21.5"
    echo ""
    echo "Exit codes:"
    echo "  0 - Success (go command exists and version matches prefix)"
    echo "  1 - Go command not found or not go"
    echo "  2 - Version does not match prefix"
    echo "  3 - Invalid arguments"
}

# Function to extract version number from go version output
extract_version() {
    local version_output="$1"
    # Extract version using regex - handles format like "go version go1.21.5 linux/amd64"
    # Look for "go" followed by version number after "go version go"
    echo "$version_output" | grep -oE 'go version go[0-9]+(\.[0-9]+)*' | grep -oE '[0-9]+(\.[0-9]+)*'
}

# Function to check if actual version matches the expected prefix
version_matches_prefix() {
    local actual_version="$1"
    local expected_prefix="$2"
    
    # Split versions by dots into arrays
    IFS='.' read -ra actual_parts <<< "$actual_version"
    IFS='.' read -ra prefix_parts <<< "$expected_prefix"
    
    # Check if we have enough parts in actual version to match prefix
    if [ ${#actual_parts[@]} -lt ${#prefix_parts[@]} ]; then
        return 1
    fi
    
    # Compare each component of the prefix
    for i in "${!prefix_parts[@]}"; do
        if [ "${actual_parts[i]}" != "${prefix_parts[i]}" ]; then
            return 1
        fi
    done
    
    return 0
}

# Main script logic
main() {
    # Check argument count
    if [ $# -ne 1 ]; then
        echo "Error: Invalid number of arguments." >&2
        echo "" >&2
        usage >&2
        exit 3
    fi
    
    local version_prefix="$1"
    
    # Validate version prefix format (should contain only digits and dots)
    if ! [[ "$version_prefix" =~ ^[0-9]+(\.[0-9]+)*$ ]]; then
        echo "Error: Invalid version prefix format. Must contain only digits and dots (e.g., '1', '1.21', '1.21.5')." >&2
        exit 3
    fi
    
    # Check if go command exists and is executable
    if ! command -v go >/dev/null 2>&1; then
        echo "Error: 'go' command not found or not executable." >&2
        exit 1
    fi
    
    # Get version output from go
    local version_output
    if ! version_output=$(go version 2>&1); then
        echo "Error: Failed to execute 'go version'." >&2
        exit 1
    fi
    
    # Check if output contains "go" (case-insensitive)
    if ! echo "$version_output" | grep -qi "go"; then
        echo "Error: Command 'go' does not appear to be go. Version output:" >&2
        echo "$version_output" >&2
        exit 1
    fi
    
    # Extract version number from output
    local actual_version
    actual_version=$(extract_version "$version_output")
    
    if [ -z "$actual_version" ]; then
        echo "Error: Could not extract version number from go output:" >&2
        echo "$version_output" >&2
        exit 1
    fi
    
    # Check if version matches prefix
    if version_matches_prefix "$actual_version" "$version_prefix"; then
        echo "Success: 'go' is version $actual_version, which matches prefix '$version_prefix'."
        exit 0
    else
        echo "Error: go version $actual_version does not match expected prefix '$version_prefix'." >&2
        exit 2
    fi
}

# Run main function with all arguments
main "$@"
