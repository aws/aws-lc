#!/usr/bin/env bash
set -ex
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC


RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

usage() {
    echo "Usage: $0 [-c|--check] [-f|--fix] [-h|--help]
     -c, --check    Check formatting without making changes
     -f, --fix      Fix formatting issues
     -h, --help     Show this help message"
    exit 1
}

# Find all relevant source files, excluding build and third party directories
find_sources() {
    find include \( -name "*.c" -o -name "*.cc" -o -name "*.cpp" -o -name "*.h" \) \
        -not -path "./third_party/*" \
        -not -path "./generated-src/*" \
        -not -path "*/CMakeFiles/*" \
        -not -name "crypto_test_data.cc" \
        -not -name "err_data.c" \
        -type f
}

check_clang_format() {
    if ! command -v clang-format &> /dev/null; then
        echo -e "${RED}Error: clang-format is not installed${NC}"
        exit 1
    fi
}

check_format() {
    echo -e "${YELLOW}Checking format...${NC}"
    local issues=0
    local files=$(find_sources)
    set +x
    for file in $files; do
        local diff=$(clang-format -style=file "$file" | diff "$file" -)
        if [ -n "$diff" ]; then
            echo -e "${RED}Format issues in:${NC} $file, diff:"
            echo "$diff"
            issues=1
        fi
    done
    set -x

    if [ $issues -eq 0 ]; then
        echo -e "${GREEN}No formatting issues found!${NC}"
        return 0
    else
        echo -e "${RED}Formatting issues found!${NC}"
        echo "Run '$0 --fix' to fix these issues, double check clang-format versions agree:"
        clang-format --version
        return 1
    fi
}

fix_format() {
    echo -e "${YELLOW}Fixing format...${NC}"
    local files=$(find_sources)

    if [ -z "$files" ]; then
        echo -e "${YELLOW}No files found to format${NC}"
        exit 0
    fi

    echo "$files" | xargs clang-format -i -style=file
    echo -e "${GREEN}Formatting complete!${NC}"
}

if [ $# -eq 0 ]; then
    usage
fi

check_clang_format

while [ "$1" != "" ]; do
    case $1 in
        -c | --check )    check_format
                         exit $?
                         ;;
        -f | --fix )     fix_format
                         exit 0
                         ;;
        -h | --help )    usage
                         exit
                         ;;
        * )              usage
                         exit 1
    esac
    shift
done