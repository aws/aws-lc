// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package main

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
)

func main() {
	license_regex, _ := regexp.Compile("(?i)(SPDX-License-Identifier: Apache-2.0 OR ISC" +
		"|Brian Smith" +
		"|CloudFlare Ltd." +
		"|Eric Young" +
		"|Google" +
		"|Intel" +
		"|Marc Bevand" +
		"|OpenSSL license|OpenSSL Project)")
	filematcher, _ := regexp.Compile("(Dockerfile|\\.(ASM|c|cc|h|sh|go|pl|ps1|yml|s|S))$")

	var files []string
	var unlicensed_files []string

	excludes := []string{
		".github",
		".peg", // exlude all .peg.go files
		"build",
		"third_party",
		"crypto", // boringssl source code files
		"ssl",
		"util",
		"sources.cmake",
	}

	// Collect all non-excluded source files into |files|
	err := filepath.Walk(".", func(path string, info os.FileInfo, err error) error {
		if !info.IsDir() && filematcher.MatchString(path) && !excludeDirectory(path, excludes) {
			files = append(files, path)
		}
		return nil
	})

	if err != nil {
		panic(err)
	}

	// Check that every file contains one of the known copyright headers,
	// otherwise add it to |unlicensed_files|
	for _, file := range files {
		content, _ := os.ReadFile(file)
		if license_regex.MatchString(string(content)) != true {
			unlicensed_files = append(unlicensed_files, file)
		}
	}

	if len(unlicensed_files) > 0 {
		for _, failure := range unlicensed_files {
			fmt.Println(fmt.Sprintf("%s is missing a copyright header", failure))
		}

		panic("FAILED Copyright Check")
	} else {
		fmt.Println("PASSED Copyright Check")
	}
}

func excludeDirectory(path string, list []string) bool {
	for _, exclude := range list {
		// If filepath is within one of the excluded directories
		if strings.Contains(path, exclude) {
			return true
		}
	}

	// Don't want to exclude filepath
	return false
}
