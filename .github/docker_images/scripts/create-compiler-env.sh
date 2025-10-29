#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -euo pipefail

COMPILER_ENV_DIR="${COMPILER_ENV_DIR:-/opt/compiler-env}"

# Standard paths to search for compilers
SEARCH_PATHS=("/usr/bin" "/usr/local/bin" "/bin")

# Function to check if a command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Function to extract major version from compiler output
extract_major_version() {
    local compiler="$1"
    local version_output
    
    # Try different version flags
    if version_output=$("$compiler" --version 2>/dev/null); then
        # Extract version number from output (handles various formats)
        echo "$version_output" | head -n1 | grep -oE '[0-9]+\.[0-9]+(\.[0-9]+)?' | head -n1 | cut -d. -f1
    elif version_output=$("$compiler" -dumpversion 2>/dev/null); then
        echo "$version_output" | cut -d. -f1
    else
        return 1
    fi
}

# Function to discover versioned compilers from filesystem
discover_versioned_compilers() {
    local compiler_base="$1"  # e.g., "gcc" or "clang"
    local cxx_base="$2"       # e.g., "g++" or "clang++"
    local versions=()
    
    # Search for versioned compilers in standard paths
    for search_path in "${SEARCH_PATHS[@]}"; do
        if [[ -d "$search_path" ]]; then
            # Find all versioned compilers (e.g., gcc-11, clang-14)
            while IFS= read -r -d '' compiler_path; do
                local basename_comp
                basename_comp=$(basename "$compiler_path")
                # Extract version from filename (e.g., gcc-11 -> 11, gcc-4.1 -> 4.1)
                if [[ "$basename_comp" =~ ^${compiler_base}-([0-9]+(\.[0-9]+)?)$ ]]; then
                    local version="${BASH_REMATCH[1]}"
                    local cxx_path="${search_path}/${cxx_base}-${version}"
                    
                    # Check if corresponding C++ compiler exists
                    if [[ -x "$cxx_path" ]]; then
                        versions+=("$version")
                    fi
                fi
            done < <(find "$search_path" -maxdepth 1 -name "${compiler_base}-[0-9]*" \( -type f -o -type l \) \
                -executable -print0 2>/dev/null)
        fi
    done
    
    # Remove duplicates and sort (only if versions array is not empty)
    if [[ ${#versions[@]} -gt 0 ]]; then
        printf '%s\n' "${versions[@]}" | sort -uV
    fi
}

# Function to create a compiler setup script
create_compiler_script() {
    local script_name="$1"
    local cc_compiler="$2"
    local cxx_compiler="$3"
    local display_name="$4"
    
    local script_path="${COMPILER_ENV_DIR}/${script_name}"
    
    echo "Creating compiler setup script: ${script_path}"
    
    cat > "${script_path}" << EOF
# Compiler environment setup for ${display_name}
export CC=${cc_compiler}
export CXX=${cxx_compiler}
echo "Compiler environment set to ${display_name}"
echo "CC=\$CC"
echo "CXX=\$CXX"
EOF
    
    echo "Created ${script_path}"
}

# Function to detect and create GCC compiler scripts
detect_gcc_compilers() {
    echo "Detecting GCC compilers..."
    
    # Discover versioned GCC compilers
    local versions
    mapfile -t versions < <(discover_versioned_compilers "gcc" "g++")
    
    if [[ ${#versions[@]} -gt 0 ]]; then
        for version in "${versions[@]}"; do
            if [[ -n "$version" ]]; then
                create_compiler_script "setup-gcc-${version}.sh" "gcc-${version}" "g++-${version}" "GCC ${version}"
            fi
        done
    fi
    
    # Handle base GCC compiler
    if command_exists "gcc" && command_exists "g++"; then
        local major_version
        if major_version=$(extract_major_version "gcc"); then
            echo "Detected base GCC version: ${major_version}"
            
            # Create generic setup script
            create_compiler_script "setup-gcc.sh" "gcc" "g++" "GCC"
            
            # Create version-specific script if it doesn't already exist
            local versioned_script="setup-gcc-${major_version}.sh"
            if [[ ! -f "${COMPILER_ENV_DIR}/${versioned_script}" ]]; then
                create_compiler_script "${versioned_script}" "gcc" "g++" "GCC ${major_version}"
            fi
        else
            echo "Warning: Could not determine GCC version, creating generic script only"
            create_compiler_script "setup-gcc.sh" "gcc" "g++" "GCC"
        fi
    fi
}

# Function to detect and create Clang compiler scripts
detect_clang_compilers() {
    echo "Detecting Clang compilers..."
    
    # Discover versioned Clang compilers
    local versions
    mapfile -t versions < <(discover_versioned_compilers "clang" "clang++")
    
    if [[ ${#versions[@]} -gt 0 ]]; then
        for version in "${versions[@]}"; do
            if [[ -n "$version" ]]; then
                create_compiler_script "setup-clang-${version}.sh" "clang-${version}" "clang++-${version}" "Clang ${version}"
            fi
        done
    fi
    
    # Handle base Clang compiler
    if command_exists "clang" && command_exists "clang++"; then
        local major_version
        if major_version=$(extract_major_version "clang"); then
            echo "Detected base Clang version: ${major_version}"
            
            # Create generic setup script
            create_compiler_script "setup-clang.sh" "clang" "clang++" "Clang"
            
            # Create version-specific script if it doesn't already exist
            local versioned_script="setup-clang-${major_version}.sh"
            if [[ ! -f "${COMPILER_ENV_DIR}/${versioned_script}" ]]; then
                create_compiler_script "${versioned_script}" "clang" "clang++" "Clang ${major_version}"
            fi
        else
            echo "Warning: Could not determine Clang version, creating generic script only"
            create_compiler_script "setup-clang.sh" "clang" "clang++" "Clang"
        fi
    fi
}

# Main function
main() {
    echo "Starting compiler environment setup script creation..."
    
    # Create the compiler environment directory
    mkdir -p "${COMPILER_ENV_DIR}"
    echo "Created directory: ${COMPILER_ENV_DIR}"
    
    # Detect and create compiler scripts
    detect_gcc_compilers
    detect_clang_compilers
    
    # List created scripts
    echo "Compiler environment setup complete!"
    echo "Created scripts:"
    for script in "${COMPILER_ENV_DIR}"/*.sh; do
        if [[ -f "$script" ]]; then
            echo "  $(basename "$script")"
        fi
    done
    
    echo "Usage: source ${COMPILER_ENV_DIR}/setup-<compiler>.sh"
}

# Run main function if script is executed directly
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
