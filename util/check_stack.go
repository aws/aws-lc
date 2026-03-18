// Copyright (c) 2022, Google Inc.
// SPDX-License-Identifier: ISC

//go:build ignore

// check_stack.go checks that each of its arguments has a non-executable stack.
// See https://www.airs.com/blog/archives/518 for details.
package main

import (
	"debug/elf"
	"fmt"
	"os"
)

func checkStack(path string) {
	file, err := elf.Open(path)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error opening %s: %s\n", path, err)
		os.Exit(1)
	}
	defer file.Close()

	for _, prog := range file.Progs {
		if prog.Type == elf.PT_GNU_STACK && prog.Flags&elf.PF_X != 0 {
			fmt.Fprintf(os.Stderr, "%s has an executable stack.\n", path)
			os.Exit(1)
		}
	}
}

func main() {
	for _, path := range os.Args[1:] {
		checkStack(path)
	}
}
