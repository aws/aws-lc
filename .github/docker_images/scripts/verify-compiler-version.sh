#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

# Function to display usage
usage() {
    echo "Usage: $0 <compiler_path> <expected_compiler_type> <expected_version_prefix>"
    echo "  compiler_path: Path to GCC or Clang compiler executable, or command name"
    echo "  expected_compiler_type: Expected compiler type ('gcc', 'g++', or 'clang')"
    echo "  expected_version_prefix: Version prefix to match (e.g., '4.2', '11')"
    echo ""
    echo "Examples:"
    echo "  $0 /usr/bin/gcc gcc 4.2"
    echo "  $0 /usr/bin/g++ g++ 4.2"
    echo "  $0 /usr/bin/clang clang 11"
    echo "  $0 gcc gcc 9"
    echo "  $0 g++ g++ 9"
    echo "  $0 clang clang 11"
    echo "  $0 \$CC gcc 9"
    exit 1
}

# Function to extract version from compiler output
extract_version() {
    local compiler="$1"
    local expected_type="$2"
    local version_output
    
    # Get version output from compiler
    if ! version_output=$("$compiler" --version 2>/dev/null); then
        echo "Error: Failed to get version from compiler: $compiler" >&2
        return 1
    fi
    
    # Extract version number based on compiler type
    local version=""
    
    # Check if it's G++ (g++ specifically) - check this first since g++ output contains both "g++" and "gcc"
    if echo "$version_output" | grep -q "^g++"; then
        if [[ "$expected_type" != "g++" ]]; then
            echo "Error: Expected $expected_type compiler, but found g++" >&2
            return 1
        fi
        # G++ format: "g++ (GCC) 4.8.5" or "g++ version 4.8.5"
        version=$(echo "$version_output" | head -n1 | grep -oE '[0-9]+\.[0-9]+(\.[0-9]+)?' | head -n1)
    # Check if it's GCC (gcc specifically)
    elif echo "$version_output" | grep -q "^gcc"; then
        if [[ "$expected_type" != "gcc" ]]; then
            echo "Error: Expected $expected_type compiler, but found gcc" >&2
            return 1
        fi
        # GCC format: "gcc (GCC) 4.8.5" or "gcc version 4.8.5"
        version=$(echo "$version_output" | head -n1 | grep -oE '[0-9]+\.[0-9]+(\.[0-9]+)?' | head -n1)
    # Check if it's Clang
    elif echo "$version_output" | grep -q "clang"; then
        if [[ "$expected_type" != "clang" ]]; then
            echo "Error: Expected $expected_type compiler, but found Clang" >&2
            return 1
        fi
        # Clang format: "clang version 11.0.0" or "Apple clang version 12.0.0"
        version=$(echo "$version_output" | head -n1 | grep -oE '[0-9]+\.[0-9]+(\.[0-9]+)?' | head -n1)
    else
        echo "Error: Unsupported compiler type. Only GCC and Clang are supported." >&2
        return 1
    fi
    
    if [[ -z "$version" ]]; then
        echo "Error: Could not extract version from compiler output" >&2
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
    if [[ $# -ne 3 ]]; then
        echo "Error: Exactly 3 arguments required" >&2
        usage
    fi
    
    local compiler_path="$1"
    local expected_compiler_type="$2"
    local expected_prefix="$3"
    
    # Check if compiler_path is a direct file path or a command name
    if [[ ! -f "$compiler_path" ]]; then
        # Try to find the compiler using command -v
        local resolved_path
        if resolved_path=$(command -v "$compiler_path" 2>/dev/null); then
            compiler_path="$resolved_path"
            echo "Resolved compiler command '$1' to: $compiler_path"
        else
            echo "Error: Compiler not found: $compiler_path" >&2
            echo "Tried both as direct path and command name in PATH" >&2
            exit 1
        fi
    fi
    
    if [[ ! -x "$compiler_path" ]]; then
        echo "Error: Compiler is not executable: $compiler_path" >&2
        exit 1
    fi
    
    # Validate expected compiler type
    if [[ "$expected_compiler_type" != "gcc" && "$expected_compiler_type" != "g++" && "$expected_compiler_type" != "clang" ]]; then
        echo "Error: Invalid compiler type: $expected_compiler_type" >&2
        echo "Expected: 'gcc', 'g++', or 'clang'" >&2
        exit 1
    fi
    
    # Validate expected prefix format
    if ! echo "$expected_prefix" | grep -qE '^[0-9]+(\.[0-9]+)*$'; then
        echo "Error: Invalid version prefix format: $expected_prefix" >&2
        echo "Expected format: number or number.number (e.g., '4', '4.2', '11.0')" >&2
        exit 1
    fi
    
    # Extract actual version (this also validates compiler type)
    local actual_version
    if ! actual_version=$(extract_version "$compiler_path" "$expected_compiler_type"); then
        exit 1
    fi
    
    echo "Compiler: $compiler_path"
    echo "Expected type: $expected_compiler_type"
    echo "Actual version: $actual_version"
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
