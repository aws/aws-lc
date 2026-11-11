#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# retry_with_backoff runs its arguments, re-attempting up to a fixed number of
# times with an escalating (linear) backoff. Use it to wrap commands that can
# fail transiently -- for example package installs or downloads that depend on a
# remote mirror/CDN -- so that a single transient error does not fail the whole
# job. The wrapped command must be safe to re-run. If every attempt fails, the
# last non-zero exit status is returned so a genuinely persistent failure is not
# masked.
retry_with_backoff() {
  local n=1
  local max=5
  local rc=0
  until "$@"; do
    rc=$?
    if [ "${n}" -ge "${max}" ]; then
      echo "retry_with_backoff: command failed (exit ${rc}) after ${n} attempts: $*" >&2
      return "${rc}"
    fi
    echo "retry_with_backoff: attempt ${n}/${max} failed (exit ${rc}): $* -- retrying in $((n * 15))s" >&2
    sleep "$((n * 15))"
    n=$((n + 1))
  done
}
