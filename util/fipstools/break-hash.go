// Copyright (c) 2017, Google Inc.
// SPDX-License-Identifier: ISC

//go:build ignore

// break-hash parses an ELF or PE binary containing the FIPS module and corrupts
// the first byte of the module. This should cause the integrity check to fail.
package main

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha512"
	"debug/elf"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"os"

	"github.com/aws/aws-lc/util/fipstools/fipscommon"
)

func doELF(objectBytes []byte) (int, []byte, error) {
	object, err := elf.NewFile(bytes.NewReader(objectBytes))
	if err != nil {
		return 0, nil, errors.New("failed to parse object: " + err.Error())
	}

	// Find the .text section.
	var textSection *elf.Section
	var textSectionIndex elf.SectionIndex
	for i, section := range object.Sections {
		if section.Name == ".text" {
			textSectionIndex = elf.SectionIndex(i)
			textSection = section
			break
		}
	}

	if textSection == nil {
		return 0, nil, errors.New("failed to find .text section in object")
	}

	symbols, err := object.Symbols()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%s\nTrying dynamic symbols\n", err)
		symbols, err = object.DynamicSymbols()
	}
	if err != nil {
		return 0, nil, errors.New("failed to parse symbols: " + err.Error())
	}

	// Find the start and end markers of the module.
	var startSeen, endSeen bool
	var start, end uint64

	for _, symbol := range symbols {
		if symbol.Section != textSectionIndex {
			continue
		}

		switch symbol.Name {
		case "BORINGSSL_bcm_text_start":
			if startSeen {
				return 0, nil, errors.New("duplicate start symbol found")
			}
			startSeen = true
			start = symbol.Value
		case "BORINGSSL_bcm_text_end":
			if endSeen {
				return 0, nil, errors.New("duplicate end symbol found")
			}
			endSeen = true
			end = symbol.Value
		default:
			continue
		}
	}

	if !startSeen || !endSeen {
		return 0, nil, errors.New("could not find module in object")
	}

	moduleText := make([]byte, end-start)
	if n, err := textSection.ReadAt(moduleText, int64(start-textSection.Addr)); err != nil {
		return 0, nil, fmt.Errorf("failed to read from module start (at %d of %d) in .text: %s", start, textSection.Size, err)
	} else if n != len(moduleText) {
		return 0, nil, fmt.Errorf("short read from .text: wanted %d, got %d", len(moduleText), n)
	}

	// In order to match up the module start with the raw ELF contents,
	// search for the first 256 bytes and assume that will be unique.
	fileOffset := bytes.Index(objectBytes, moduleText[:256])
	if fileOffset < 0 {
		return 0, nil, errors.New("did not find module prefix in object file")
	}

	if bytes.Index(objectBytes[fileOffset+1:], moduleText[:256]) >= 0 {
		return 0, nil, errors.New("found two occurrences of prefix in object file")
	}

	return fileOffset, moduleText, nil
}

func doPE(objectBytes []byte, mapPath string) (int, []byte, error) {
	symbolAddrs, err := fipscommon.ParseMapFile(mapPath)
	if err != nil {
		return 0, nil, err
	}

	peInfo, err := fipscommon.ParsePE(objectBytes)
	if err != nil {
		return 0, nil, err
	}

	startOffset, err := peInfo.ResolveSymbolFileOffset(symbolAddrs, "BORINGSSL_bcm_text_start")
	if err != nil {
		return 0, nil, err
	}
	endOffset, err := peInfo.ResolveSymbolFileOffset(symbolAddrs, "BORINGSSL_bcm_text_end")
	if err != nil {
		return 0, nil, err
	}

	if startOffset >= endOffset || endOffset > uint64(len(objectBytes)) {
		return 0, nil, fmt.Errorf("invalid boundaries: start=0x%x end=0x%x filesize=%d", startOffset, endOffset, len(objectBytes))
	}

	moduleText := make([]byte, endOffset-startOffset)
	copy(moduleText, objectBytes[startOffset:endOffset])

	return int(startOffset), moduleText, nil
}

func do(outPath, inPath, mapPath string) error {
	objectBytes, err := os.ReadFile(inPath)
	if err != nil {
		return err
	}

	var fileOffset int
	var moduleText []byte

	if mapPath != "" {
		fileOffset, moduleText, err = doPE(objectBytes, mapPath)
	} else {
		fileOffset, moduleText, err = doELF(objectBytes)
	}
	if err != nil {
		return err
	}

	// Calculate the before hash of the module.
	var zeroKey [64]byte
	mac := hmac.New(sha512.New, zeroKey[:])
	mac.Write(moduleText)
	hashWas := mac.Sum(nil)

	// Corrupt the module in the binary.
	objectBytes[fileOffset] ^= 1

	// Calculate the after hash of the module.
	moduleText[0] ^= 1
	mac.Reset()
	mac.Write(moduleText)
	newHash := mac.Sum(nil)

	fmt.Printf("Found start of module at file offset 0x%x:\n", fileOffset)
	fmt.Println(hex.Dump(moduleText[:128]))
	fmt.Printf("\nHash of module was:          %x\n", hashWas)
	fmt.Printf("Hash of corrupted module is: %x\n", newHash)

	return os.WriteFile(outPath, objectBytes, 0755)
}

func main() {
	mapPath := flag.String("map", "", "Path to linker .map file (required for Windows PE/DLL)")
	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: %s [-map mapfile] <input binary> <output path>\n", os.Args[0])
		flag.PrintDefaults()
	}
	flag.Parse()

	args := flag.Args()
	if len(args) != 2 {
		flag.Usage()
		os.Exit(1)
	}

	if err := do(args[1], args[0], *mapPath); err != nil {
		fmt.Fprintf(os.Stderr, "%s\n", err)
		os.Exit(1)
	}
}
