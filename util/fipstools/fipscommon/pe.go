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
func ParseMapFile(mapPath string) (map[string]uint64, error) {
	data, err := os.ReadFile(mapPath)
	if err != nil {
		return nil, fmt.Errorf("failed to read map file: %s", err.Error())
	}

	symbols := make(map[string]uint64)
	// Symbol lines have format: SSSS:OOOOOOOO  name  RRRRRRRRRRRRRRRR  Lib:Object
	for _, line := range strings.Split(string(data), "\n") {
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
			return rva - start + uint64(s.Offset), nil
		}
	}
	return 0, fmt.Errorf("RVA 0x%x for %q not found in any PE section", rva, name)
}