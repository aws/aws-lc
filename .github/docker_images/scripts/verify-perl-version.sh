#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

# Function to display usage
usage() {
    echo "Usage: $0 <expected_version_prefix>"
    echo "Example: $0 5.32"
    echo "         $0 5"
    echo ""
    echo "This script checks if the installed Perl version matches the expected prefix."
    echo "For example, if Perl version is 5.32.1:"
    echo "  - Expected '5' will match"
    echo "  - Expected '5.32' will match"
    echo "  - Expected '5.33' will NOT match"
    echo "  - Expected '6' will NOT match"
    exit 1
}

# Function to get Perl version
get_perl_version() {
    if ! command -v perl >/dev/null 2>&1; then
        echo "ERROR: Perl is not installed or not in PATH" >&2
        exit 1
    fi
    
    # Get Perl version and extract the full version number (e.g., 5.32.1)
    perl -v | grep -oP 'v\K[\d.]+' | head -1
}

# Function to validate version prefix matching
validate_version_prefix() {
    local actual_version="$1"
    local expected_prefix="$2"
    
    # Check if the actual version starts with the expected prefix
    if [[ "$actual_version" == "$expected_prefix"* ]]; then
        # Additional check: ensure we're matching at version component boundaries
        # This prevents "2.3" from matching "2.34" when we want exact prefix matching
        local remaining="${actual_version#$expected_prefix}"
        
        # If remaining is empty, it's an exact match
        if [[ -z "$remaining" ]]; then
            return 0
        fi
        
        # If remaining starts with a dot, it's a valid prefix match
        if [[ "$remaining" == .* ]]; then
            return 0
        fi
        
        # Otherwise, it's not a valid prefix match
        return 1
    else
        return 1
    fi
}

# Main script
main() {
    # Check if expected version prefix is provided
    if [[ $# -ne 1 ]]; then
        echo "ERROR: Expected version prefix is required" >&2
        usage
    fi
    
    local expected_prefix="$1"
    
    # Validate that expected prefix contains only digits and dots
    if [[ ! "$expected_prefix" =~ ^[0-9]+(\.[0-9]+)*$ ]]; then
        echo "ERROR: Invalid version prefix format. Use format like '5' or '5.32'" >&2
        exit 1
    fi
    
    echo "Checking Perl version..."
    
    # Get the actual Perl version
    local actual_version
    actual_version=$(get_perl_version)
    
    if [[ -z "$actual_version" ]]; then
        echo "ERROR: Could not determine Perl version" >&2
        exit 1
    fi
    
    echo "Installed Perl version: $actual_version"
    echo "Expected version prefix: $expected_prefix"
    
    # Validate the version
    if validate_version_prefix "$actual_version" "$expected_prefix"; then
        echo "SUCCESS: Perl version $actual_version matches expected prefix $expected_prefix"
        exit 0
    else
        echo "FAILURE: Perl version $actual_version does not match expected prefix $expected_prefix" >&2
        exit 1
    fi
}

# Run main function with all arguments
main "$@"
