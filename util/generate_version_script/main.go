// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// generate_version_script reads a symbol registry file where each line is
// "<symbol_name> <version_node> [visibility]" and generates a GNU ld version
// script with proper version inheritance.
//
// Symbols are grouped by version node. Versions are sorted numerically
// (AWS_LC_1.0 < AWS_LC_1.1 < AWS_LC_2.0), and each version
// automatically inherits from its immediate predecessor. The oldest (base)
// version includes "local: *;" to hide all unlisted symbols.
//
// The optional third field is the visibility (see the visibility type below):
// PUBLIC, PRIVATE, PRIVATE_CXX, PRIVATE_CXX_CLASS, PUBLIC_CXX, or
// PUBLIC_CXX_CLASS. All symbols are included in the version script regardless of
// visibility. C++ symbols are emitted in an "extern C++" block with glob
// patterns so the linker matches their demangled C++ names.
//
// Usage:
//
//	go run ./util/generate_version_script -in crypto/libcrypto.txt -out crypto/libcrypto.map
package main

import (
	"bufio"
	"flag"
	"fmt"
	"io"
	"os"
	"sort"
	"strconv"
	"strings"
)

var inFile string
var outFile string

func init() {
	flag.StringVar(&inFile, "in", "", "Symbol registry file (one '<symbol> <version> [visibility]' per line)")
	flag.StringVar(&outFile, "out", "", "Output GNU ld version script (.map)")
}

// visibility classifies a symbol's linkage and export status. It is the third
// field of a registry line. Go has no native enum; the idiom is a defined
// string type with typed constants, which keeps parsing trivial (the on-disk
// value is the constant itself) while giving the compiler a named type to
// reason about.
type visibility string

const (
	visPublic         visibility = "PUBLIC"            // public C API from include/openssl/*.h
	visPrivate        visibility = "PRIVATE"           // internal C-linkage API
	visPrivateCxx     visibility = "PRIVATE_CXX"       // internal C++ function
	visPrivateCxxClas visibility = "PRIVATE_CXX_CLASS" // internal C++ class (all members)
	visPublicCxx      visibility = "PUBLIC_CXX"        // public C++ function
	visPublicCxxClass visibility = "PUBLIC_CXX_CLASS"  // public C++ class (all members)
)

// symbolInfo holds a symbol name and its visibility classification.
type symbolInfo struct {
	name       string
	visibility visibility
}

func main() {
	flag.Parse()

	if inFile == "" {
		fmt.Fprintf(os.Stderr, "Error: -in is required\n")
		flag.Usage()
		os.Exit(1)
	}
	if outFile == "" {
		fmt.Fprintf(os.Stderr, "Error: -out is required\n")
		flag.Usage()
		os.Exit(1)
	}

	versionSymbols, versions, err := readRegistry(inFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error reading registry %s: %v\n", inFile, err)
		os.Exit(1)
	}

	if err := writeVersionScript(outFile, versions, versionSymbols); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing version script: %v\n", err)
		os.Exit(1)
	}

	total := 0
	for _, syms := range versionSymbols {
		total += len(syms)
	}
	fmt.Fprintf(os.Stderr, "Generated %s (%d symbols across %d version(s))\n",
		outFile, total, len(versions))
}

// readRegistry opens a symbol registry file and parses it.
func readRegistry(filename string) (map[string][]symbolInfo, []string, error) {
	f, err := os.Open(filename)
	if err != nil {
		return nil, nil, err
	}
	defer f.Close()
	return readRegistryFrom(f)
}

// readRegistryFrom parses the symbol registry from a reader and returns a map
// of version to its symbols, plus the versions sorted oldest-first.
// Each line is "<symbol> <version>" or "<symbol> <version> <visibility>".
func readRegistryFrom(r io.Reader) (map[string][]symbolInfo, []string, error) {
	versionSymbols := make(map[string][]symbolInfo)
	scanner := bufio.NewScanner(r)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		fields := strings.Fields(line)
		if len(fields) < 2 || len(fields) > 3 {
			return nil, nil, fmt.Errorf("malformed line (expected 'symbol version [visibility]'): %q", line)
		}
		symbol, version := fields[0], fields[1]
		vis := visPublic
		if len(fields) == 3 {
			vis = visibility(fields[2])
		}
		versionSymbols[version] = append(versionSymbols[version], symbolInfo{
			name:       symbol,
			visibility: vis,
		})
	}
	if err := scanner.Err(); err != nil {
		return nil, nil, err
	}

	versions := make([]string, 0, len(versionSymbols))
	for v := range versionSymbols {
		versions = append(versions, v)
	}
	sort.Slice(versions, func(i, j int) bool {
		return versionLess(versions[i], versions[j])
	})

	return versionSymbols, versions, nil
}

// versionLess compares two version strings of the form "AWS_LC_X_Y".
func versionLess(a, b string) bool {
	ma, na := parseVersion(a)
	mb, nb := parseVersion(b)
	if ma != mb {
		return ma < mb
	}
	return na < nb
}

// parseVersion extracts (major, minor) from "AWS_LC_X.Y".
func parseVersion(v string) (int, int) {
	s := strings.TrimPrefix(v, "AWS_LC_")
	parts := strings.SplitN(s, ".", 2)
	if len(parts) != 2 {
		return 0, 0
	}
	major, _ := strconv.Atoi(parts[0])
	minor, _ := strconv.Atoi(parts[1])
	return major, minor
}

// writeVersionScript creates a file and writes the GNU ld version script to it.
func writeVersionScript(filename string, versions []string, versionSymbols map[string][]symbolInfo) error {
	f, err := os.Create(filename)
	if err != nil {
		return err
	}
	defer f.Close()
	return writeVersionScriptTo(f, versions, versionSymbols)
}

// writeVersionScriptTo emits the GNU ld version script to a writer.
// C and PRIVATE symbols are emitted as plain symbol names.
// PRIVATE_CXX symbols are emitted in an "extern C++" block with glob patterns
// that match the demangled name (function_name followed by parameter list).
func writeVersionScriptTo(w io.Writer, versions []string, versionSymbols map[string][]symbolInfo) error {
	bw := bufio.NewWriter(w)

	fmt.Fprintf(bw, "# GNU ld version script for AWS-LC\n")
	fmt.Fprintf(bw, "# Auto-generated from symbol registry. Do not edit manually.\n")
	fmt.Fprintf(bw, "# To add new symbols: util/update_symbol_version.sh <new_version>\n")
	fmt.Fprintf(bw, "# To regenerate:      util/generate_initial_version_scripts.sh\n")
	fmt.Fprintf(bw, "\n")

	for i, version := range versions {
		syms := make([]symbolInfo, len(versionSymbols[version]))
		copy(syms, versionSymbols[version])
		sort.Slice(syms, func(a, b int) bool {
			return syms[a].name < syms[b].name
		})

		// Separate C-linkage symbols from C++ function/class symbols.
		var cSymbols []string
		var cxxFuncSymbols []string
		var cxxClassSymbols []string
		for _, sym := range syms {
			switch sym.visibility {
			case visPrivateCxx, visPublicCxx:
				cxxFuncSymbols = append(cxxFuncSymbols, sym.name)
			case visPrivateCxxClas, visPublicCxxClass:
				cxxClassSymbols = append(cxxClassSymbols, sym.name)
			default:
				cSymbols = append(cSymbols, sym.name)
			}
		}

		fmt.Fprintf(bw, "%s {\n", version)
		fmt.Fprintf(bw, "  global:\n")
		for _, sym := range cSymbols {
			fmt.Fprintf(bw, "    %s;\n", sym)
		}
		if len(cxxFuncSymbols) > 0 || len(cxxClassSymbols) > 0 {
			fmt.Fprintf(bw, "    extern \"C++\" {\n")
			for _, sym := range cxxFuncSymbols {
				// Glob pattern matches the demangled name. The symbol name
				// already includes the namespace (e.g., "bssl::func_name")
				// if it was declared inside a namespace block.
				fmt.Fprintf(bw, "      %s*;\n", sym)
			}
			for _, sym := range cxxClassSymbols {
				// "ns::ClassName::*" matches all member functions.
				fmt.Fprintf(bw, "      %s::*;\n", sym)
			}
			fmt.Fprintf(bw, "    };\n")
		}

		// local: *; hides all unlisted symbols. Only the oldest (base) version
		// needs it; derived versions inherit the local scope automatically.
		if i == 0 {
			fmt.Fprintf(bw, "  local:\n")
			fmt.Fprintf(bw, "    *;\n")
			fmt.Fprintf(bw, "};\n")
		} else {
			fmt.Fprintf(bw, "} %s;\n", versions[i-1])
		}

		if i < len(versions)-1 {
			fmt.Fprintf(bw, "\n")
		}
	}

	return bw.Flush()
}
