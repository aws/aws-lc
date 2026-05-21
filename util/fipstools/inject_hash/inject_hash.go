// Copyright (c) 2017, Google Inc.
// SPDX-License-Identifier: ISC

// inject_hash parses an archive containing a file object file. It finds a FIPS
// module inside that object, calculates its hash and replaces the default hash
// value in the object with the calculated value.
package main

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"
	"debug/elf"
	"debug/macho"
	"debug/pe"
	"encoding/binary"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"strings"

	"github.com/aws/aws-lc/util/ar"
	"github.com/aws/aws-lc/util/fipstools/fipscommon"
)

func doLinux(objectBytes []byte, isStatic bool) ([]byte, []byte, error) {

	object, err := elf.NewFile(bytes.NewReader(objectBytes))
	if err != nil {
		return nil, nil, errors.New("failed to parse object: " + err.Error())
	}

	// Find the .text and, optionally, .data sections.

	var textSection, rodataSection *elf.Section
	var textSectionIndex, rodataSectionIndex elf.SectionIndex
	for i, section := range object.Sections {
		switch section.Name {
		case ".text":
			textSectionIndex = elf.SectionIndex(i)
			textSection = section
		case ".rodata":
			rodataSectionIndex = elf.SectionIndex(i)
			rodataSection = section
		}
	}

	if textSection == nil {
		return nil, nil, errors.New("failed to find .text section in object")
	}

	// Find the starting and ending symbols for the module.

	var textStart, textEnd, rodataStart, rodataEnd *uint64

	symbols, err := object.Symbols()
	if err != nil {
		return nil, nil, errors.New("failed to parse symbols: " + err.Error())
	}

	for _, symbol := range symbols {
		var base uint64
		switch symbol.Section {
		case textSectionIndex:
			base = textSection.Addr
		case rodataSectionIndex:
			if rodataSection == nil {
				continue
			}
			base = rodataSection.Addr
		default:
			continue
		}

		if isStatic {
			// Static objects appear to have different semantics about whether symbol
			// values are relative to their section or not.
			base = 0
		} else if symbol.Value < base {
			return nil, nil, fmt.Errorf("symbol %q at %x, which is below base of %x", symbol.Name, symbol.Value, base)
		}

		value := symbol.Value - base
		switch symbol.Name {
		case "BORINGSSL_bcm_text_start":
			if textStart != nil {
				return nil, nil, errors.New("duplicate start symbol found")
			}
			textStart = &value
		case "BORINGSSL_bcm_text_end":
			if textEnd != nil {
				return nil, nil, errors.New("duplicate end symbol found")
			}
			textEnd = &value
		case "BORINGSSL_bcm_rodata_start":
			if rodataStart != nil {
				return nil, nil, errors.New("duplicate rodata start symbol found")
			}
			rodataStart = &value
		case "BORINGSSL_bcm_rodata_end":
			if rodataEnd != nil {
				return nil, nil, errors.New("duplicate rodata end symbol found")
			}
			rodataEnd = &value
		default:
			continue
		}
	}

	if textStart == nil || textEnd == nil {
		return nil, nil, errors.New("could not find .text module boundaries in object")
	}

	if (rodataStart == nil) != (rodataSection == nil) {
		return nil, nil, errors.New("rodata start marker inconsistent with rodata section presence")
	}

	if (rodataStart != nil) != (rodataEnd != nil) {
		return nil, nil, errors.New("rodata marker presence inconsistent")
	}

	if max := textSection.Size; *textStart > max || *textStart > *textEnd || *textEnd > max {
		return nil, nil, fmt.Errorf("invalid module .text boundaries: start: %x, end: %x, max: %x", *textStart, *textEnd, max)
	}

	if rodataSection != nil {
		if max := rodataSection.Size; *rodataStart > max || *rodataStart > *rodataEnd || *rodataEnd > max {
			return nil, nil, fmt.Errorf("invalid module .rodata boundaries: start: %x, end: %x, max: %x", *rodataStart, *rodataEnd, max)
		}
	}

	// Extract the module from the .text section and hash it.

	text := textSection.Open()
	if _, err := text.Seek(int64(*textStart), 0); err != nil {
		return nil, nil, errors.New("failed to seek to module start in .text: " + err.Error())
	}
	moduleText := make([]byte, *textEnd-*textStart)
	if _, err := io.ReadFull(text, moduleText); err != nil {
		return nil, nil, errors.New("failed to read .text: " + err.Error())
	}

	// Maybe extract the module's read-only data too
	var moduleROData []byte
	if rodataSection != nil {
		rodata := rodataSection.Open()
		if _, err := rodata.Seek(int64(*rodataStart), 0); err != nil {
			return nil, nil, errors.New("failed to seek to module start in .rodata: " + err.Error())
		}
		moduleROData = make([]byte, *rodataEnd-*rodataStart)
		if _, err := io.ReadFull(rodata, moduleROData); err != nil {
			return nil, nil, errors.New("failed to read .rodata: " + err.Error())
		}
	}

	return moduleText, moduleROData, nil
}

func doAppleOS(objectBytes []byte) ([]byte, []byte, error) {

	object, err := macho.NewFile(bytes.NewReader(objectBytes))
	if err != nil {
		return nil, nil, errors.New("failed to parse object: " + err.Error())
	}

	// Find the __text and, optionally, __const sections.
	// They are both in __TEXT segment and are unique.
	var textSection, rodataSection *macho.Section
	var textSectionIndex, rodataSectionIndex int
	for i, section := range object.Sections {
		if section.Seg == "__TEXT" && section.Name == "__text" {
			textSection = section
			textSectionIndex = i + 1
		}
		if section.Seg == "__TEXT" && section.Name == "__const" {
			rodataSection = section
			rodataSectionIndex = i + 1
		}
	}

	if textSection == nil {
		return nil, nil, errors.New("failed to find __text section in object")
	}

	// Find the starting and ending symbols for the module.
	var textStart, textEnd, rodataStart, rodataEnd *uint64

	symbols := object.Symtab.Syms
	if symbols == nil {
		return nil, nil, errors.New("failed to parse symbols: " + err.Error())
	}

	for _, symbol := range symbols {
		var base uint64
		switch int(symbol.Sect) {
		case textSectionIndex:
			base = textSection.Addr
		case rodataSectionIndex:
			if rodataSection == nil {
				continue
			}
			base = rodataSection.Addr
		default:
			continue
		}

		if symbol.Name != "" && symbol.Name != " " && symbol.Value < base {
			return nil, nil, fmt.Errorf("symbol %q at %x, which is below base of %x\n", symbol.Name, symbol.Value, base)
		}

		// Skip debugging symbols
		//
		// #define	N_STAB	0xe0  /* if any of these bits set, a symbolic debugging entry */
		//
		// "Only symbolic debugging entries have some of the N_STAB bits set and if any of these bits are set then it is
		// a symbolic debugging entry (a stab).  In which case then the values of the n_type field (the entire field)
		// are given in <mach-o/stab.h>"
		//
		// https://github.com/apple-oss-distributions/xnu/blob/main/EXTERNAL_HEADERS/mach-o/nlist.h
		if symbol.Type&0xe0 != 0 {
			continue
		}

		value := symbol.Value - base
		switch symbol.Name {
		case "_BORINGSSL_bcm_text_start":
			if textStart != nil {
				return nil, nil, errors.New("duplicate start symbol found")
			}
			textStart = &value
		case "_BORINGSSL_bcm_text_end":
			if textEnd != nil {
				return nil, nil, errors.New("duplicate end symbol found")
			}
			textEnd = &value
		case "_BORINGSSL_bcm_rodata_start":
			if rodataStart != nil {
				return nil, nil, errors.New("duplicate rodata start symbol found")
			}
			rodataStart = &value
		case "_BORINGSSL_bcm_rodata_end":
			if rodataEnd != nil {
				return nil, nil, errors.New("duplicate rodata end symbol found")
			}
			rodataEnd = &value
		default:
			continue
		}
	}

	if textStart == nil || textEnd == nil {
		return nil, nil, errors.New("could not find .text module boundaries in object")
	}

	if (rodataStart == nil) != (rodataSection == nil) {
		return nil, nil, errors.New("rodata start marker inconsistent with rodata section presence")
	}

	if (rodataStart != nil) != (rodataEnd != nil) {
		return nil, nil, errors.New("rodata marker presence inconsistent")
	}

	if max := textSection.Size; *textStart > max || *textStart > *textEnd || *textEnd > max {
		return nil, nil, fmt.Errorf("invalid module __text boundaries: start: %x, end: %x, max: %x", *textStart, *textEnd, max)
	}

	if rodataSection != nil {
		if max := rodataSection.Size; *rodataStart > max || *rodataStart > *rodataEnd || *rodataEnd > max {
			return nil, nil, fmt.Errorf("invalid module __const boundaries: start: %x, end: %x, max: %x", *rodataStart, *rodataEnd, max)
		}
	}

	// Extract the module from the __text section.
	text := textSection.Open()
	if _, err := text.Seek(int64(*textStart), 0); err != nil {
		return nil, nil, errors.New("failed to seek to module start in __text: " + err.Error())
	}
	moduleText := make([]byte, *textEnd-*textStart)
	if _, err := io.ReadFull(text, moduleText); err != nil {
		return nil, nil, errors.New("failed to read __text: " + err.Error())
	}

	// Maybe extract the module's read-only data too
	var moduleROData []byte
	if rodataSection != nil {
		rodata := rodataSection.Open()
		if _, err := rodata.Seek(int64(*rodataStart), 0); err != nil {
			return nil, nil, errors.New("failed to seek to module start in __const: " + err.Error())
		}
		moduleROData = make([]byte, *rodataEnd-*rodataStart)
		if _, err := io.ReadFull(rodata, moduleROData); err != nil {
			return nil, nil, errors.New("failed to read __const: " + err.Error())
		}
	}

	return moduleText, moduleROData, nil
}

func doWindows(objectBytes []byte, mapPath string) ([]byte, []byte, error) {
	symbolAddrs, err := fipscommon.ParseMapFile(mapPath)
	if err != nil {
		return nil, nil, err
	}

	peInfo, err := fipscommon.ParsePE(objectBytes)
	if err != nil {
		return nil, nil, err
	}

	extractRegion := func(startSym, endSym string) ([]byte, error) {
		startOff, err := peInfo.ResolveSymbolFileOffset(symbolAddrs, startSym)
		if err != nil {
			return nil, err
		}
		endOff, err := peInfo.ResolveSymbolFileOffset(symbolAddrs, endSym)
		if err != nil {
			return nil, err
		}
		if startOff >= endOff || endOff > uint64(len(objectBytes)) {
			return nil, fmt.Errorf("invalid boundaries: start=0x%x end=0x%x filesize=%d", startOff, endOff, len(objectBytes))
		}
		buf := make([]byte, endOff-startOff)
		copy(buf, objectBytes[startOff:endOff])
		return buf, nil
	}

	moduleText, err := extractRegion("BORINGSSL_bcm_text_start", "BORINGSSL_bcm_text_end")
	if err != nil {
		return nil, nil, err
	}

	// The Windows FIPS build is always a shared library (see the `windowsOS`
	// branch of `do` below, which rejects static inputs). In shared builds the
	// runtime integrity check in bcm.c hashes the rodata region in addition
	// to the text region, so the map file must contain both rodata markers.
	// Silently skipping rodata here would produce a hash that disagrees with
	// what the runtime computes and the DLL would fail the power-on self-test.
	_, hasRodataStart := symbolAddrs["BORINGSSL_bcm_rodata_start"]
	_, hasRodataEnd := symbolAddrs["BORINGSSL_bcm_rodata_end"]
	if !hasRodataStart || !hasRodataEnd {
		return nil, nil, errors.New("rodata markers missing from map file; Windows FIPS shared build requires both BORINGSSL_bcm_rodata_start and BORINGSSL_bcm_rodata_end")
	}
	moduleROData, err := extractRegion("BORINGSSL_bcm_rodata_start", "BORINGSSL_bcm_rodata_end")
	if err != nil {
		return nil, nil, err
	}

	return moduleText, moduleROData, nil
}

func doMingw(objectBytes []byte) ([]byte, []byte, error) {
	object, err := pe.NewFile(bytes.NewReader(objectBytes))
	if err != nil {
		return nil, nil, errors.New("failed to parse object: " + err.Error())
	}

	// Find .text and .rdata sections. Windows uses .rdata for read-only data.
	var textSection, rodataSection *pe.Section
	var textSectionIndex, rodataSectionIndex int

	for i, section := range object.Sections {
		switch section.Name {
		case ".text":
			textSection = section
			textSectionIndex = i + 1
		case ".rdata":
			rodataSection = section
			rodataSectionIndex = i + 1
		}
	}

	if textSection == nil {
		return nil, nil, errors.New("failed to find .text section in object")
	}

	var textStart, textEnd, rodataStart, rodataEnd *uint64

	symbols := object.Symbols
	if symbols == nil {
		return nil, nil, errors.New("no symbol table found in object")
	}

	for _, symbol := range symbols {
		switch int(symbol.SectionNumber) {
		case textSectionIndex:
		case rodataSectionIndex:
			// rodataSectionIndex is 0 if no .rdata section was found,
			// which would match undefined symbols (COFF section number 0) — skip those.
			if rodataSection == nil {
				continue
			}
		default:
			continue
		}

		// In COFF, symbol.Value is the offset from the start of the section,
		// not an RVA.
		offset := uint64(symbol.Value)

		switch symbol.Name {
		case "BORINGSSL_bcm_text_start":
			if textStart != nil {
				return nil, nil, errors.New("duplicate start symbol found")
			}
			textStart = &offset
		case "BORINGSSL_bcm_text_end":
			if textEnd != nil {
				return nil, nil, errors.New("duplicate end symbol found")
			}
			textEnd = &offset
		case "BORINGSSL_bcm_rodata_start":
			if rodataStart != nil {
				return nil, nil, errors.New("duplicate rodata start symbol found")
			}
			rodataStart = &offset
		case "BORINGSSL_bcm_rodata_end":
			if rodataEnd != nil {
				return nil, nil, errors.New("duplicate rodata end symbol found")
			}
			rodataEnd = &offset
		}
	}

	if textStart == nil || textEnd == nil {
		return nil, nil, errors.New("could not find .text module boundaries in object")
	}

	if rodataStart != nil && rodataSection == nil {
		return nil, nil, errors.New("rodata start marker found but no .rdata section present")
	}

	if (rodataStart != nil) != (rodataEnd != nil) {
		return nil, nil, errors.New("rodata marker presence inconsistent")
	}

	if max := uint64(textSection.Size); *textStart > max || *textStart > *textEnd || *textEnd > max {
		return nil, nil, fmt.Errorf("invalid module .text boundaries: start: %x, end: %x, max: %x", *textStart, *textEnd, max)
	}

	if rodataStart != nil {
		if max := uint64(rodataSection.Size); *rodataStart > max || *rodataStart > *rodataEnd || *rodataEnd > max {
			return nil, nil, fmt.Errorf("invalid module .rdata boundaries: start: %x, end: %x, max: %x", *rodataStart, *rodataEnd, max)
		}
	}

	text, err := textSection.Data()
	if err != nil {
		return nil, nil, errors.New("failed to read .text data: " + err.Error())
	}
	moduleText := text[*textStart:*textEnd]

	var moduleROData []byte
	if rodataStart != nil {
		rodata, err := rodataSection.Data()
		if err != nil {
			return nil, nil, errors.New("failed to read .rdata data: " + err.Error())
		}
		moduleROData = rodata[*rodataStart:*rodataEnd]
	}

	return moduleText, moduleROData, nil
}

func do(outPath, oInput string, arInput string, appleOS bool, windowsOS bool, mapFile string, mingw bool) error {
	var objectBytes []byte
	var isStatic bool
	var perm os.FileMode

	if appleOS && windowsOS {
		return fmt.Errorf("-apple and -windows are mutually exclusive")
	}

	if windowsOS && len(mapFile) == 0 {
		return fmt.Errorf("-map is required when -windows is set")
	}

	if len(arInput) > 0 {
		isStatic = true

		if len(oInput) > 0 {
			return fmt.Errorf("-in-archive and -in-object are mutually exclusive")
		}

		if appleOS {
			return fmt.Errorf("only shared libraries can be handled on macOS/iOS")
		}

		if windowsOS {
			return fmt.Errorf("only shared libraries can be handled on Windows")
		}

		fi, err := os.Stat(arInput)
		if err != nil {
			return err
		}
		perm = fi.Mode()

		arFile, err := os.Open(arInput)
		if err != nil {
			return err
		}
		defer arFile.Close()

		ar, err := ar.ParseAR(arFile)
		if err != nil {
			return err
		}

		if len(ar) != 1 {
			return fmt.Errorf("expected one file in archive, but found %d", len(ar))
		}

		for _, contents := range ar {
			objectBytes = contents
		}
	} else if len(oInput) > 0 {
		fi, err := os.Stat(oInput)
		if err != nil {
			return err
		}
		perm = fi.Mode()

		if objectBytes, err = os.ReadFile(oInput); err != nil {
			return err
		}
		isStatic = strings.HasSuffix(oInput, ".o")
	} else {
		return fmt.Errorf("exactly one of -in-archive or -in-object is required")
	}

	var moduleText, moduleROData []byte
	var err error
	if windowsOS {
		moduleText, moduleROData, err = doWindows(objectBytes, mapFile)
	} else if appleOS {
		moduleText, moduleROData, err = doAppleOS(objectBytes)
	} else if mingw == true {
		moduleText, moduleROData, err = doMingw(objectBytes)
	} else {
		moduleText, moduleROData, err = doLinux(objectBytes, isStatic)
	}

	if err != nil {
		return err
	}

	var zeroKey [64]byte
	mac := hmac.New(sha256.New, zeroKey[:])

	if moduleROData != nil {
		var lengthBytes [8]byte
		binary.LittleEndian.PutUint64(lengthBytes[:], uint64(len(moduleText)))
		mac.Write(lengthBytes[:])
		mac.Write(moduleText)

		binary.LittleEndian.PutUint64(lengthBytes[:], uint64(len(moduleROData)))
		mac.Write(lengthBytes[:])
		mac.Write(moduleROData)
	} else {
		mac.Write(moduleText)
	}
	calculated := mac.Sum(nil)

	// Replace the default hash value in the object with the calculated
	// value and write it out.

	offset := bytes.Index(objectBytes, fipscommon.UninitHashValue[:])
	if offset < 0 {
		return errors.New("did not find uninitialised hash value in object file")
	}

	if bytes.Index(objectBytes[offset+1:], fipscommon.UninitHashValue[:]) >= 0 {
		return errors.New("found two occurrences of uninitialised hash value in object file")
	}

	copy(objectBytes[offset:], calculated)

	return os.WriteFile(outPath, objectBytes, perm&0777)
}

func main() {
	arInput := flag.String("in-archive", "", "Path to a .a file")
	oInput := flag.String("in-object", "", "Path to a .o file")
	outPath := flag.String("o", "", "Path to output object")
	appleOS := flag.Bool("apple", false, "Whether the FIPS module is built for macOS/iOS or not.")
	windowsOS := flag.Bool("windows", false, "Whether the FIPS module is built for Windows or not.")
	mapFile := flag.String("map", "", "Path to linker .map file (required for Windows)")
	mingw := flag.Bool("mingw", false, "Whether the FIPS module is built for a Windows MinGW toolchain or not.")

	flag.Parse()

	if err := do(*outPath, *oInput, *arInput, *appleOS, *windowsOS, *mapFile, *mingw); err != nil {
		fmt.Fprintf(os.Stderr, "%s\n", err)
		os.Exit(1)
	}
}
