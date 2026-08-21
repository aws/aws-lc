#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Shared assertions for the installed pkg-config metadata. With the OpenSSL
# shim enabled and suffixed libraries, AWS-LC installs two interfaces:
#
#   native cohabitant:  libcrypto-<product>.pc  libssl-<product>.pc  aws-lc.pc
#   OpenSSL shim:       libcrypto.pc            libssl.pc            openssl.pc
#
# The native modules stay suffixed; every shim-facing module must describe the
# unsuffixed OpenSSL interface. See INCORPORATING.md for why.
#
# Sourcing scripts must define a fail() function before calling these.

# Detect library directory (lib or lib64)
function get_lib_dir() {
    local INSTALL_DIR=$1
    if [[ -d "${INSTALL_DIR}/lib64" ]]; then
        echo "lib64"
    else
        echo "lib"
    fi
}

# Derive the product suffix (e.g. "-awslc") from the installed native filenames
# rather than hardcoding it, so these assertions still hold if SOFTWARE_NAME
# changes. Prints the empty string when the native modules are unsuffixed.
function get_product_suffix() {
    local PC_DIR=$1
    local NATIVE_PC
    for NATIVE_PC in "${PC_DIR}"/libcrypto-*.pc; do
        if [[ -f "${NATIVE_PC}" ]]; then
            NATIVE_PC=$(basename "${NATIVE_PC}" .pc)
            echo "${NATIVE_PC#libcrypto}"
            return 0
        fi
    done
    echo ""
}

# Print every whitespace-delimited token of a .pc file's Requires,
# Requires.private, Libs and Libs.private fields, one per line. Deliberately
# skips includedir, -L paths, Name and Cflags, which legitimately mention the
# product name.
function pc_dependency_tokens() {
    local PC_PATH=$1
    awk '
        /^[[:space:]]*(Requires|Libs)(\.private)?[[:space:]]*:/ {
            sub(/^[^:]*:/, "")
            n = split($0, tokens, /[[:space:]]+/)
            for (i = 1; i <= n; i++) {
                if (tokens[i] != "") print tokens[i]
            }
        }
    ' "${PC_PATH}"
}

# Exact whitespace-delimited token match: unlike a substring test, this does
# not accept "-lcrypto-awslc" when looking for "-lcrypto".
function has_exact_token() {
    local HAYSTACK=$1
    local NEEDLE=$2
    local -a TOKENS
    local TOKEN
    # read -ra splits on whitespace without pathname expansion.
    read -ra TOKENS <<< "${HAYSTACK}"
    for TOKEN in "${TOKENS[@]}"; do
        if [[ "${TOKEN}" == "${NEEDLE}" ]]; then
            return 0
        fi
    done
    return 1
}

function assert_exact_token() {
    local HAYSTACK=$1
    local NEEDLE=$2
    local DESCRIPTION=$3
    if ! has_exact_token "${HAYSTACK}" "${NEEDLE}"; then
        fail "${DESCRIPTION}: expected exact token '${NEEDLE}' in '${HAYSTACK}'"
    fi
}

function assert_no_exact_token() {
    local HAYSTACK=$1
    local NEEDLE=$2
    local DESCRIPTION=$3
    if has_exact_token "${HAYSTACK}" "${NEEDLE}"; then
        fail "${DESCRIPTION}: unexpected exact token '${NEEDLE}' in '${HAYSTACK}'"
    fi
}

# No dependency field of a shim-facing .pc file may name a suffixed crypto/ssl
# module or library. Suffix-agnostic on purpose: this also catches a product
# suffix other than -awslc, and a failure to derive the suffix at all.
function assert_no_suffixed_openssl_tokens() {
    local PC_PATH=$1
    local TOKEN
    while read -r TOKEN; do
        case "${TOKEN}" in
            -lcrypto-*|-lssl-*|libcrypto-*|libssl-*)
                fail "$(basename "${PC_PATH}") names suffixed OpenSSL token '${TOKEN}' in a Requires/Libs field"
                ;;
        esac
    done < <(pc_dependency_tokens "${PC_PATH}")
}

# Assert a pkg-config query emits an exact token. FLAG is a pkg-config option
# such as --libs, --print-requires or --print-requires-private. The caller must
# set PKG_CONFIG_PATH.
function assert_pkgconfig_token() {
    local PC_NAME=$1
    local FLAG=$2
    local EXPECTED=$3
    local OUTPUT
    OUTPUT=$(pkg-config ${FLAG} "${PC_NAME}")
    assert_exact_token "${OUTPUT}" "${EXPECTED}" "pkg-config ${FLAG} ${PC_NAME}"
}

function assert_no_pkgconfig_token() {
    local PC_NAME=$1
    local FLAG=$2
    local UNEXPECTED=$3
    local OUTPUT
    OUTPUT=$(pkg-config ${FLAG} "${PC_NAME}")
    assert_no_exact_token "${OUTPUT}" "${UNEXPECTED}" "pkg-config ${FLAG} ${PC_NAME}"
}
