#!/bin/sh
# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# rust-phase1 CI probe (not for merge): installs rustup's stable toolchain if
# the job has none, adds each Rust target given, and on Windows adds the
# llvm-tools the Windows fold uses. A failure only warns, and the job then
# builds without Rust.
#
# Usage: install_rust.sh [<rust-target>...]

CARGO_HOME="${CARGO_HOME:-${HOME}/.cargo}"
PATH="${CARGO_HOME}/bin:${PATH}"
export CARGO_HOME PATH

warn() {
  echo "::warning title=ENABLE_RUST::install_rust.sh: $*"
  exit 0
}

if ! command -v rustup >/dev/null 2>&1; then
  if command -v curl >/dev/null 2>&1; then
    curl --proto '=https' -sSf https://sh.rustup.rs -o /tmp/rustup-init.sh || warn "can't download rustup"
  elif command -v wget >/dev/null 2>&1; then
    wget -q https://sh.rustup.rs -O /tmp/rustup-init.sh || warn "can't download rustup"
  else
    warn "no curl or wget to download rustup"
  fi
  sh /tmp/rustup-init.sh -y --no-modify-path --profile minimal --default-toolchain stable \
    || warn "rustup-init failed"
  rm -f /tmp/rustup-init.sh
fi

if [ "$#" -gt 0 ]; then
  rustup target add "$@" || warn "can't add Rust targets $*"
fi
case "$(uname -s)" in
  MINGW* | MSYS* | CYGWIN*) rustup component add llvm-tools || warn "can't add llvm-tools" ;;
esac

# Later steps of a GitHub Actions job read their PATH from GITHUB_PATH.
if [ -n "${GITHUB_PATH:-}" ]; then
  echo "${CARGO_HOME}/bin" >> "${GITHUB_PATH}"
fi
rustc --version
