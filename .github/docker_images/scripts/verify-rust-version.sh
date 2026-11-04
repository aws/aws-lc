#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Script to verify that a Rust toolchain program exists and, optionally, that it
# matches a specified version prefix
# Usage: verify-rust-version.sh <program_path> [version_prefix]
#
# Most images track the current stable Rust, so the version prefix is optional:
# with one argument the script only confirms the program is present and working
# and reports its version. Pass a prefix for images pinned to a specific
# release (e.g. Ubuntu 10.04, which is pinned to 1.63).
#
# Exit codes:
#   0 - Success (program is a Rust tool and, if given, version matches prefix)
#   1 - Program is not the expected Rust tool
#   2 - Version does not match prefix
#   3 - Invalid arguments or program not found

set -euo pipefail

# Function to display usage information
usage() {
    echo "Usage: $0 <program_path> [version_prefix]"
    echo ""
    echo "Verifies that the specified program is a Rust toolchain program and, when a"
    echo "version prefix is given, that its version matches that prefix."
    echo ""
    echo "Arguments:"
    echo "  program_path    Path to the program to verify (e.g., 'rustc', 'cargo', 'rustfmt')"
    echo "  version_prefix  Optional version prefix to match (e.g., '1', '1.63', '1.63.0')."
    echo "                  Omit it on images that track the current stable release."
    echo ""
    echo "Examples:"
    echo "  $0 rustc"
    echo "  $0 cargo"
    echo "  $0 rustc 1.63"
    echo ""
    echo "Exit codes:"
    echo "  0 - Success (program is a Rust tool and, if given, version matches prefix)"
    echo "  1 - Program is not the expected Rust tool"
    echo "  2 - Version does not match prefix"
    echo "  3 - Invalid arguments or program not found"
}

# Function to extract version number from "<name> --version" output
extract_version() {
    local version_output="$1"
    # Handles formats like "rustc 1.97.1 (8bab26f4f 2026-07-14)" and
    # "cargo 1.97.1 (c980f4866 2026-06-30)" by taking the first version-looking
    # token, which avoids matching the date in the trailing parenthetical.
    echo "$version_output" | grep -oE '[0-9]+(\.[0-9]+)+' | head -1
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
    if [ $# -lt 1 ] || [ $# -gt 2 ]; then
        echo "Error: Invalid number of arguments." >&2
        echo "" >&2
        usage >&2
        exit 3
    fi

    local program_path="$1"
    local version_prefix="${2:-}"

    # Validate version prefix format (should contain only digits and dots)
    if [ -n "$version_prefix" ] && ! [[ "$version_prefix" =~ ^[0-9]+(\.[0-9]+)*$ ]]; then
        echo "Error: Invalid version prefix format. Must contain only digits and dots (e.g., '1', '1.63', '1.63.0')." >&2
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

    # Check that the output identifies the expected program. Compare against the
    # basename so absolute paths are accepted too.
    local program_name
    program_name="$(basename "$program_path")"
    if ! echo "$version_output" | grep -qi "$program_name"; then
        echo "Error: Program '$program_path' does not appear to be $program_name. Version output:" >&2
        echo "$version_output" >&2
        exit 1
    fi

    # Extract version number from output
    local actual_version
    actual_version=$(extract_version "$version_output")

    if [ -z "$actual_version" ]; then
        echo "Error: Could not extract version number from $program_name output:" >&2
        echo "$version_output" >&2
        exit 1
    fi

    # With no prefix requested, presence and a parseable version are enough
    if [ -z "$version_prefix" ]; then
        echo "Success: '$program_path' is $program_name version $actual_version."
        exit 0
    fi

    # Check if version matches prefix
    if version_matches_prefix "$actual_version" "$version_prefix"; then
        echo "Success: '$program_path' is $program_name version $actual_version, which matches prefix '$version_prefix'."
        exit 0
    else
        echo "Error: $program_name version $actual_version does not match expected prefix '$version_prefix'." >&2
        exit 2
    fi
}

# Run main function with all arguments
main "$@"
