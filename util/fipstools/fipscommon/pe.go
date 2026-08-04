// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package fipscommon

import (
	"bytes"
	"debug/pe"
	"errors"
	"fmt"
	"os"
	"strconv"
	"strings"
)

// PEInfo holds parsed PE file information needed for symbol resolution.
type PEInfo struct {
	File      *pe.File
	ImageBase uint64
}

// ParseMapFile reads a Windows linker map file and returns a map of
// BORINGSSL_bcm_* symbol names to their Rva+Base addresses.
//
// MSVC-style map files (also produced by lld-link with /MAP:) contain several
// sections. Symbol addresses we care about live under a column-header line of
// the form:
//
//	 Address         Publics by Value              Rva+Base               Lib:Object
//
// followed by rows of the form:
//
//	 SSSS:OOOOOOOO  name  RRRRRRRRRRRRRRRR  [f]  Lib:Object
//
// A later "Static symbols" heading begins a section that reuses the row format,
// so anchoring parsing to the Publics header avoids accidentally picking up a
// same-named static symbol from some other translation unit. The
// BORINGSSL_bcm_* markers are `extern` and therefore only ever appear in
// Publics by Value in practice, but the anchor makes the intent explicit and
// the parser less fragile.
func ParseMapFile(mapPath string) (map[string]uint64, error) {
	data, err := os.ReadFile(mapPath)
	if err != nil {
		return nil, fmt.Errorf("failed to read map file: %s", err.Error())
	}

	symbols := make(map[string]uint64)
	inPublics := false
	sawPublicsHeading := false
	for _, line := range strings.Split(string(data), "\n") {
		trimmed := strings.TrimSpace(line)
		// Section headings are column-header / label lines with no leading
		// address column. Detect the Publics by Value column-header line
		// (which also contains the word "Address") and the Static symbols
		// label that terminates the public section.
		if strings.Contains(trimmed, "Publics by Value") {
			inPublics = true
			sawPublicsHeading = true
			continue
		}
		if trimmed == "Static symbols" {
			inPublics = false
			continue
		}
		if !inPublics {
			continue
		}
		fields := strings.Fields(line)
		if len(fields) < 3 || !strings.Contains(fields[0], ":") {
			continue
		}
		name := fields[1]
		if !strings.HasPrefix(name, "BORINGSSL_bcm_") {
			continue
		}
		rvaBase, err := strconv.ParseUint(fields[2], 16, 64)
		if err != nil {
			return nil, fmt.Errorf("failed to parse Rva+Base for symbol %q: %s", name, err.Error())
		}
		if _, exists := symbols[name]; exists {
			return nil, fmt.Errorf("duplicate symbol %q in map file", name)
		}
		symbols[name] = rvaBase
	}

	// Guard against silently-malformed map files: if we never saw the
	// expected heading the caller will get confusing "symbol not found"
	// errors downstream. Surface the real problem here instead.
	if !sawPublicsHeading {
		return nil, fmt.Errorf("map file %q does not contain a \"Publics by Value\" section; is this an MSVC-style linker map?", mapPath)
	}

	return symbols, nil
}

// ParsePE parses a PE file from raw bytes and extracts the image base.
func ParsePE(objectBytes []byte) (*PEInfo, error) {
	peFile, err := pe.NewFile(bytes.NewReader(objectBytes))
	if err != nil {
		return nil, fmt.Errorf("failed to parse PE: %s", err.Error())
	}

	var imageBase uint64
	switch oh := peFile.OptionalHeader.(type) {
	case *pe.OptionalHeader64:
		imageBase = oh.ImageBase
	case *pe.OptionalHeader32:
		imageBase = uint64(oh.ImageBase)
	default:
		return nil, errors.New("unsupported PE optional header type")
	}

	return &PEInfo{File: peFile, ImageBase: imageBase}, nil
}

// ResolveSymbolFileOffset converts a symbol's Rva+Base address (from a linker
// map file) to a file offset within the PE binary.
func (p *PEInfo) ResolveSymbolFileOffset(symbolAddrs map[string]uint64, name string) (uint64, error) {
	addr, ok := symbolAddrs[name]
	if !ok {
		return 0, fmt.Errorf("symbol %q not found in map file", name)
	}
	if addr < p.ImageBase {
		return 0, fmt.Errorf("symbol %q address 0x%x is below image base 0x%x", name, addr, p.ImageBase)
	}
	rva := addr - p.ImageBase
	for _, s := range p.File.Sections {
		start := uint64(s.VirtualAddress)
		if rva >= start && rva < start+uint64(s.VirtualSize) {
			offsetInSection := rva - start
			if offsetInSection >= uint64(s.Size) {
				return 0, fmt.Errorf("RVA 0x%x for %q is in zero-fill/BSS region of section %s (offset 0x%x exceeds raw data size 0x%x)", rva, name, s.Name, offsetInSection, s.Size)
			}
			return offsetInSection + uint64(s.Offset), nil
		}
	}
	return 0, fmt.Errorf("RVA 0x%x for %q not found in any PE section", rva, name)
}
