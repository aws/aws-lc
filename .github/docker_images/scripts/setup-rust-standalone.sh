#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Installs a Rust toolchain from a pre-downloaded standalone distribution
# tarball, for images too old to use rustup (see setup-rust.sh).
#
# Two constraints drive this script:
#   1. rustup-init requires glibc 2.17, and Rust 1.64.0 raised the tier-1
#      *-unknown-linux-gnu baseline to glibc 2.17 as well. Rust 1.63.0 is the
#      last release that still runs against older glibc (its binaries need only
#      GLIBC_2.10), which is what makes it usable on Ubuntu 10.04's glibc 2.11.
#   2. These images have a TLS stack too old to reach static.rust-lang.org, so
#      the tarball cannot be fetched here. The workflow downloads it on the
#      runner and passes it in through the "dependencies" build context, the
#      same way Dockerfile.1004 already sources its CMake tarball.
#
# Usage: setup-rust-standalone.sh <path-to-rust-tarball>

set -euo pipefail

if [ $# -ne 1 ]; then
    echo "Usage: $0 <path-to-rust-tarball>" >&2
    exit 1
fi

rust_tarball="$1"
CARGO_HOME="${CARGO_HOME:-/.cargo}"
RUST_PREFIX="${RUST_PREFIX:-/usr/local}"
# Component names come from the "components" manifest inside the tarball. The
# docs and the various -preview analysis tools are skipped to limit image size.
RUST_COMPONENTS="${RUST_COMPONENTS:-rustc,rust-std-x86_64-unknown-linux-gnu,cargo,clippy-preview,rustfmt-preview}"

if [ ! -f "${rust_tarball}" ]; then
    echo "Error: Rust tarball '${rust_tarball}' not found." >&2
    exit 1
fi

extract_dir="$(mktemp -d)"
tar -xzf "${rust_tarball}" -C "${extract_dir}" --strip-components=1

"${extract_dir}/install.sh" \
    --prefix="${RUST_PREFIX}" \
    --components="${RUST_COMPONENTS}"

rm -rf "${extract_dir}"

# rustc shells out to "cc" as its default linker driver. These images install
# only versioned compilers (e.g. gcc-4.1), so provide the unversioned name that
# rustc expects, without disturbing the existing gcc-* binaries.
if ! command -v cc >/dev/null 2>&1; then
    # "|| true" keeps set -e/pipefail from aborting the lookups themselves, so
    # an image with no gcc at all reaches the explicit error message below.
    gcc_path="$(command -v gcc || true)"
    if [ -z "${gcc_path}" ]; then
        gcc_path="$(ls /usr/bin/gcc-* 2>/dev/null | sort -V | tail -1 || true)"
    fi
    if [ -z "${gcc_path}" ]; then
        echo "Error: no gcc found to back the 'cc' linker driver rustc requires." >&2
        exit 1
    fi
    ln -s "${gcc_path}" /usr/bin/cc
fi

# Match setup-rust.sh: a shared, world-writable CARGO_HOME so non-root CI jobs
# can populate cargo's registry/git caches.
mkdir -p "${CARGO_HOME}"
chmod -R a+w "${CARGO_HOME}"
