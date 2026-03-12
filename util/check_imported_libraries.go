// Copyright (c) 2017, Google Inc.
// SPDX-License-Identifier: ISC

//go:build ignore

// check_imported_libraries.go checks that each of its arguments only imports
// allowed libraries. This is used to avoid accidental dependencies on
// libstdc++.so.
package main

import (
	"debug/elf"
	"fmt"
	"os"
)

func checkImportedLibraries(path string) {
	file, err := elf.Open(path)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error opening %s: %s\n", path, err)
		os.Exit(1)
	}
	defer file.Close()

	libs, err := file.ImportedLibraries()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error reading %s: %s\n", path, err)
		os.Exit(1)
	}

	for _, lib := range libs {
		if lib != "libc.so.6" && lib != "libcrypto.so" && lib != "libpthread.so.0" {
			fmt.Printf("Invalid dependency for %s: %s\n", path, lib)
			fmt.Printf("All dependencies:\n")
			for _, lib := range libs {
				fmt.Printf("    %s\n", lib)
			}
			os.Exit(1)
		}
	}
}

func main() {
	for _, path := range os.Args[1:] {
		checkImportedLibraries(path)
	}
}
