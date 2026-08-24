#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

# Runs "go vet" over the Go code in this repository. Among other things this
# catches malformed struct tags, which compile fine but silently change how
# encoding/json maps fields.
#
# "go vet ./..." cannot be used directly, for two reasons.
#
# 1. The util/fipstools directory holds test_fips.c (compiled by CMake, not by
#    cgo) alongside Go files, so the Go toolchain cannot load it as a package.
#    Note that plain "go list ./..." prints nothing at all in that situation, so
#    "go list -e" is required to enumerate the packages that do load.
#
# 2. Two packages have pre-existing findings that are out of scope to fix here.
#    Rather than skipping them entirely, only the specific analyzers that fire
#    are disabled, so every other analyzer (including structtag) still runs:
#      - ssl/test/runner: the test harness copies testCase/Config values, which
#        embed a sync.Once (copylocks), and RecordingConn.WriteTo intentionally
#        does not match io.WriterTo (stdmethods).
#      - util/fipstools/delocate: unreachable code in the generated
#        delocate.peg.go, which is marked DO NOT EDIT.

EXPECTED_UNLOADABLE="github.com/aws/aws-lc/util/fipstools"
RUNNER_PKG="github.com/aws/aws-lc/ssl/test/runner"
DELOCATE_PKG="github.com/aws/aws-lc/util/fipstools/delocate"

# Guard the exemption above: a newly broken package should fail loudly here
# rather than being silently dropped from the vet run.
UNLOADABLE=$(go list -e -f '{{if .Error}}{{.ImportPath}}{{end}}' ./...)
if [[ "${UNLOADABLE}" != "${EXPECTED_UNLOADABLE}" ]]; then
  echo "The set of packages that fail to load has changed."
  echo "Expected: ${EXPECTED_UNLOADABLE}"
  echo "Found:    ${UNLOADABLE}"
  echo "Fix the package, or update EXPECTED_UNLOADABLE in $0."
  exit 1
fi

# Full analyzer set on every package that loads, except the two below.
go list -e -f '{{if not .Error}}{{.ImportPath}}{{end}}' ./... \
  | grep -vxF -e "${RUNNER_PKG}" -e "${DELOCATE_PKG}" \
  | xargs go vet

# Reduced analyzer set on the two packages with pre-existing findings.
go vet -copylocks=false -stdmethods=false "${RUNNER_PKG}"
go vet -unreachable=false "${DELOCATE_PKG}"

echo "go vet reported no problems."
