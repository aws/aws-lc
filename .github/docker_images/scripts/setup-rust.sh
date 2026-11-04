#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Installs a Rust toolchain via rustup. Defaults to the current stable release;
# set RUST_VERSION to pin a specific one.
#
# This requires glibc 2.17 or newer, because that is the floor for both
# rustup-init and Rust's tier-1 *-unknown-linux-gnu targets. Images older than
# that (Ubuntu 10.04) use setup-rust-standalone.sh instead.

set -euo pipefail

RUSTUP_HOME="${RUSTUP_HOME:-/.rustup}"
CARGO_HOME="${CARGO_HOME:-/.cargo}"
RUST_VERSION=${RUST_VERSION:-stable}
RUST_COMPONENTS=${RUST_COMPONENTS:-clippy,rustfmt}

# The canonical install line from https://rustup.rs passes "--tlsv1.2" to curl,
# but that option was only added in curl 7.34 and CentOS 7 ships 7.29, so it is
# deliberately omitted. Not every image has curl (Ubuntu 16.04 has only wget),
# so fall back to whichever downloader is present. rustup-init.sh does the same
# curl-or-wget detection internally when it fetches the rustup-init binary.
rustup_init="/tmp/rustup-init.sh"
if command -v curl >/dev/null 2>&1; then
    curl --proto '=https' -sSf https://sh.rustup.rs -o "${rustup_init}"
elif command -v wget >/dev/null 2>&1; then
    wget -q https://sh.rustup.rs -O "${rustup_init}"
else
    echo "Error: neither curl nor wget is available to download rustup." >&2
    exit 1
fi

# --no-modify-path because PATH is set via ENV in the Dockerfile rather than by
# appending to a shell profile that non-login CI shells would never read.
sh "${rustup_init}" -y \
    --no-modify-path \
    --profile minimal \
    --default-toolchain "${RUST_VERSION}" \
    --component "${RUST_COMPONENTS}"

rm -f "${rustup_init}"

# CI jobs can run as a non-root user (see codebuild/common/run_nonroot_target.yml)
# and cargo writes to CARGO_HOME for its registry/git caches, so the shared
# toolchain must be world-writable. The official rust image does the same.
chmod -R a+w "${RUSTUP_HOME}" "${CARGO_HOME}"
