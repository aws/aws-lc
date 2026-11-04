#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# retry runs its arguments, re-attempting up to a fixed number of times with an
# escalating backoff. It exists so that transient package-mirror/CDN errors
# during BSD VM setup -- for example an HTTP 503 from cdn.NetBSD.org, or a reset
# connection to a FreeBSD/OpenBSD pkg mirror -- do not fail the whole nightly BSD
# CI run. Wrap network-dependent setup commands with it (pkg install, pkg_add,
# curl). Commands wrapped with it must be safe to re-run.
retry() {
  local n=1
  local max=5
  until "$@"; do
    if [ "${n}" -ge "${max}" ]; then
      echo "retry: command failed after ${n} attempts: $*" >&2
      return 1
    fi
    echo "retry: attempt ${n}/${max} failed: $* -- retrying in $((n * 15))s" >&2
    sleep "$((n * 15))"
    n=$((n + 1))
  done
}
