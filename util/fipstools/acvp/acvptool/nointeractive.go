// Copyright (c) 2020, Google Inc.
// SPDX-License-Identifier: ISC

//go:build !interactive
// +build !interactive

package main

import (
	"github.com/aws/aws-lc/util/fipstools/acvp/acvptool/acvp"
)

const interactiveModeSupported = false

func runInteractive(*acvp.Server, Config) {
	panic("not supported")
}
