#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Script to verify that a program is cmake and matches a specified version prefix
# Usage: verify-cmake-version.sh <program_path> <version_prefix>
# 
# Exit codes:
#   0 - Success (program is cmake and version matches prefix)
#   1 - Program is not cmake
#   2 - Version does not match prefix
#   3 - Invalid arguments or program not found

set -euo pipefail

# Function to display usage information
usage() {
    echo "Usage: $0 <program_path> <version_prefix>"
    echo ""
    echo "Verifies that the specified program is cmake and its version matches the given prefix."
    echo ""
    echo "Arguments:"
    echo "  program_path    Path to the program to verify"
    echo "  version_prefix  Version prefix to match (e.g., '3', '3.4', '3.4.2')"
    echo ""
    echo "Examples:"
    echo "  $0 /usr/bin/cmake 3"
    echo "  $0 cmake 3.4"
    echo ""
    echo "Exit codes:"
    echo "  0 - Success (program is cmake and version matches prefix)"
    echo "  1 - Program is not cmake"
    echo "  2 - Version does not match prefix"
    echo "  3 - Invalid arguments or program not found"
}

# Function to extract version number from cmake --version output
extract_version() {
    local version_output="$1"
    # Extract version using regex - looks specifically for "version" keyword followed by version number
    # This avoids matching digits in binary name (e.g., cmake3) by targeting the "version X.Y.Z" pattern
    # Using space+ instead of \s+ for compatibility with older bash/grep versions
    echo "$version_output" | grep -oE 'version +[0-9]+(\.[0-9]+)*' | grep -oE '[0-9]+(\.[0-9]+)*'
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
    if [ $# -ne 2 ]; then
        echo "Error: Invalid number of arguments." >&2
        echo "" >&2
        usage >&2
        exit 3
    fi
    
    local program_path="$1"
    local version_prefix="$2"
    
    # Validate version prefix format (should contain only digits and dots)
    if ! [[ "$version_prefix" =~ ^[0-9]+(\.[0-9]+)*$ ]]; then
        echo "Error: Invalid version prefix format. Must contain only digits and dots (e.g., '3', '3.4', '3.4.2')." >&2
        exit 3
    fi
    
    # Check if program exists and is executable
    if ! command -v "$program_path" >/dev/null 2>&1; then
        echo "Error: Program '$program_path' not found or not executable." >&2
        exit 3
    fi
    
    # Get version output from the program
    local version_output
    if ! version_output=$("$program_path" --version 2>&1); then
        echo "Error: Failed to execute '$program_path --version'." >&2
        exit 3
    fi
    
    # Check if output contains "cmake" (case-insensitive)
    if ! echo "$version_output" | grep -qi "cmake"; then
        echo "Error: Program '$program_path' is not cmake. Version output:" >&2
        echo "$version_output" >&2
        exit 1
    fi
    
    # Extract version number from output
    local actual_version
    actual_version=$(extract_version "$version_output")
    
    if [ -z "$actual_version" ]; then
        echo "Error: Could not extract version number from cmake output:" >&2
        echo "$version_output" >&2
        exit 1
    fi
    
    # Check if version matches prefix
    if version_matches_prefix "$actual_version" "$version_prefix"; then
        echo "Success: '$program_path' is cmake version $actual_version, which matches prefix '$version_prefix'."
        exit 0
    else
        echo "Error: cmake version $actual_version does not match expected prefix '$version_prefix'." >&2
        exit 2
    fi
}

# Run main function with all arguments
main "$@"
