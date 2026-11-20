// Copyright (c) 2017, Google Inc.
// SPDX-License-Identifier: ISC

// inject_hash parses an archive containing a file object file. It finds a FIPS
// module inside that object, calculates its hash and replaces the default hash
// value in the object with the calculated value. With -rust, it does the same
// for the module region of bcm-rust.o, bcm.o's Rust counterpart: in static
// FIPS builds in bcm-rust.o, after applying the relocations in the region
// (relocateModule), and in shared ones in the final library, as for bcm.o.
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

// rustUninitHashValue is bcm-rust.o's placeholder for its hash
// (crypto/rust/fipsmodule/src/fips.rs). It differs from bcm.o's, so each
// appears once in a shared library that holds both modules.
var rustUninitHashValue = [32]byte{
	0xeb, 0xa0, 0xdc, 0x87, 0x3f, 0x90, 0x5a, 0x73, 0xae, 0x32, 0xd8, 0xb2, 0x74, 0xd9, 0x4c, 0x7c, 0x50, 0x48, 0x00, 0xe1, 0xb2, 0xee, 0x1c, 0x96, 0x64, 0x35, 0x99, 0x82, 0xae, 0xfc, 0x2d, 0xd8,
}

func doLinux(objectBytes []byte, isStatic bool, rust bool) ([]byte, []byte, error) {

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
			// bcm-rust.o's region holds its constants too, in .text.
			if !rust {
				rodataSectionIndex = elf.SectionIndex(i)
				rodataSection = section
			}
		}
	}

	if textSection == nil {
		return nil, nil, errors.New("failed to find .text section in object")
	}

	// Find the starting and ending symbols for the module. bcm-rust.o's are
	// defined by crypto/rust/fipsmodule/bcm-rust.lds.

	var textStart, textEnd, rodataStart, rodataEnd *uint64
	markers := "BORINGSSL_bcm"
	if rust {
		markers = "BORINGSSL_bcm_rust"
	}

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
		case markers + "_text_start":
			if textStart != nil {
				return nil, nil, errors.New("duplicate start symbol found")
			}
			textStart = &value
		case markers + "_text_end":
			if textEnd != nil {
				return nil, nil, errors.New("duplicate end symbol found")
			}
			textEnd = &value
		case markers + "_rodata_start":
			if rodataStart != nil {
				return nil, nil, errors.New("duplicate rodata start symbol found")
			}
			rodataStart = &value
		case markers + "_rodata_end":
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
	// A shared library's final link has applied every relocation already.
	if rust && isStatic {
		if err := relocateModule(object, textSectionIndex, *textStart, *textEnd, moduleText); err != nil {
			return nil, nil, err
		}
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

// relocateModule applies the relocations inside bcm-rust.o's module region,
// [start, end) of its text section, to text, the region's bytes, as the
// consumer's final link will.
//
// bcm.o needs no such step: delocate's assembly leaves no relocation in its
// region. bcm-rust.o is rustc output that a partial link merged into one
// section (crypto/rust/fipsmodule/bcm-rust.lds), and a partial link keeps
// every relocation. A PC-relative relocation whose target is in the same
// section has the same value wherever the final link puts that section, so
// those are applied here. Any other relocation, such as a call out of the
// module, a GOT reference or aarch64's page-relative adrp, would make the
// final link write bytes that differ from the ones hashed here, so it fails
// the build. crypto/rust/fipsmodule/src/fips.rs lists the module code rules
// that avoid them.
func relocateModule(object *elf.File, textIndex elf.SectionIndex, start, end uint64, text []byte) error {
	if object.Class != elf.ELFCLASS64 {
		return errors.New("-rust supports only 64-bit ELF objects")
	}
	symbols, err := object.Symbols()
	if err != nil {
		return errors.New("failed to parse symbols: " + err.Error())
	}
	for _, section := range object.Sections {
		if elf.SectionIndex(section.Info) != textIndex || (section.Type != elf.SHT_RELA && section.Type != elf.SHT_REL) {
			continue
		}
		if section.Type == elf.SHT_REL {
			return fmt.Errorf("%s: relocations without addends aren't supported", section.Name)
		}
		data, err := section.Data()
		if err != nil {
			return fmt.Errorf("failed to read %s: %s", section.Name, err)
		}
		for ; len(data) >= 24; data = data[24:] {
			off := object.ByteOrder.Uint64(data[0:8])
			info := object.ByteOrder.Uint64(data[8:16])
			addend := int64(object.ByteOrder.Uint64(data[16:24]))
			if off < start || off >= end {
				continue
			}
			symIndex := elf.R_SYM64(info)
			if symIndex == 0 || int(symIndex) > len(symbols) {
				return fmt.Errorf("relocation at .text+%#x has symbol index %d", off, symIndex)
			}
			// Symbols omits the null symbol at index 0.
			sym := symbols[symIndex-1]
			name := sym.Name
			if elf.ST_TYPE(sym.Info) == elf.STT_SECTION && int(sym.Section) < len(object.Sections) {
				name = object.Sections[sym.Section].Name
			}
			if sym.Section != textIndex {
				return fmt.Errorf("module code at .text+%#x refers to %q, outside the module", off, name)
			}
			value := int64(sym.Value) + addend - int64(off)
			if err := applyRelocation(object, elf.R_TYPE64(info), value, text[off-start:]); err != nil {
				return fmt.Errorf("module code at .text+%#x, referring to %q: %s", off, name, err)
			}
		}
	}
	return nil
}

// applyRelocation writes value, the distance from a relocation's place to its
// target, into field, the bytes at that place, for the relocation types rustc
// emits for references inside the module.
func applyRelocation(object *elf.File, typ uint32, value int64, field []byte) error {
	order := object.ByteOrder
	put32 := func(v uint32) error {
		if len(field) < 4 {
			return errors.New("relocation runs past the module")
		}
		order.PutUint32(field, v)
		return nil
	}
	// insn sets the bits-wide immediate at bit lsb of an aarch64 instruction
	// to value >> shift.
	insn := func(shift, bits, lsb uint) error {
		if value&(1<<shift-1) != 0 {
			return errors.New("misaligned target")
		}
		imm := value >> shift
		if imm < -(1<<(bits-1)) || imm >= 1<<(bits-1) {
			return fmt.Errorf("target out of range (%d bytes away)", value)
		}
		if len(field) < 4 {
			return errors.New("relocation runs past the module")
		}
		mask := uint32(1<<bits-1) << lsb
		order.PutUint32(field, order.Uint32(field)&^mask|uint32(imm)<<lsb&mask)
		return nil
	}

	switch object.Machine {
	case elf.EM_X86_64:
		switch r := elf.R_X86_64(typ); r {
		case elf.R_X86_64_PC32, elf.R_X86_64_PLT32:
			if value != int64(int32(value)) {
				return errors.New("target out of range")
			}
			return put32(uint32(value))
		default:
			return fmt.Errorf("%v isn't PC-relative within the module", r)
		}
	case elf.EM_AARCH64:
		switch r := elf.R_AARCH64(typ); r {
		case elf.R_AARCH64_CALL26, elf.R_AARCH64_JUMP26:
			return insn(2, 26, 0)
		case elf.R_AARCH64_CONDBR19, elf.R_AARCH64_LD_PREL_LO19:
			return insn(2, 19, 5)
		case elf.R_AARCH64_ADR_PREL_LO21:
			// adr reaches 1 MiB, which limits the whole module on aarch64,
			// as delocate's adr limits bcm.o.
			if value < -(1<<20) || value >= 1<<20 {
				return fmt.Errorf("target out of adr's 1 MiB range (%d bytes away)", value)
			}
			if len(field) < 4 {
				return errors.New("relocation runs past the module")
			}
			const mask = 3<<29 | 0x7ffff<<5
			imm := uint32(value)
			order.PutUint32(field, order.Uint32(field)&^mask|(imm&3)<<29|(imm>>2&0x7ffff)<<5)
			return nil
		case elf.R_AARCH64_ADR_PREL_PG_HI21, elf.R_AARCH64_ADD_ABS_LO12_NC:
			return fmt.Errorf("%v is page-relative, and lld can rewrite adrp: build with -Ccode-model=tiny", r)
		default:
			return fmt.Errorf("%v isn't PC-relative within the module", r)
		}
	default:
		return fmt.Errorf("-rust doesn't support %v", object.Machine)
	}
}

func doAppleOS(objectBytes []byte, rust bool) ([]byte, []byte, error) {

	object, err := macho.NewFile(bytes.NewReader(objectBytes))
	if err != nil {
		return nil, nil, errors.New("failed to parse object: " + err.Error())
	}

	// bcm-rust.o's module region is a section of its own, which its partial
	// link makes from its code and constants (cmake/cargo.cmake).
	if rust {
		section := object.Section("__bcm_rust")
		if section == nil || section.Seg != "__TEXT" {
			return nil, nil, errors.New("failed to find __TEXT,__bcm_rust section in object")
		}
		moduleText, err := section.Data()
		if err != nil {
			return nil, nil, errors.New("failed to read __bcm_rust: " + err.Error())
		}
		return moduleText, nil, nil
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

// doWindowsRust finds bcm-rust.o's module region in a DLL, from its markers in
// the linker map file (cmake/rust_crate_object_fold.cmake). The module has no
// separate rodata region: its constants are in the region too.
func doWindowsRust(objectBytes []byte, mapPath string) ([]byte, error) {
	symbolAddrs, err := fipscommon.ParseMapFile(mapPath)
	if err != nil {
		return nil, err
	}
	peInfo, err := fipscommon.ParsePE(objectBytes)
	if err != nil {
		return nil, err
	}
	const startSym, endSym = "BORINGSSL_bcm_rust_text_start", "BORINGSSL_bcm_rust_text_end"
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
	if err := checkNoBaseRelocations(peInfo, symbolAddrs[startSym]-peInfo.ImageBase, symbolAddrs[endSym]-peInfo.ImageBase); err != nil {
		return nil, err
	}
	return objectBytes[startOff:endOff], nil
}

// checkNoBaseRelocations fails if the loader would patch any byte from RVA
// start to end, which happens to an absolute address in a DLL that doesn't
// load at its preferred base. COFF has no .data.rel.ro, so a constant that
// holds a pointer stays in the module region, and only this catches it.
func checkNoBaseRelocations(peInfo *fipscommon.PEInfo, start, end uint64) error {
	var dir pe.DataDirectory
	switch oh := peInfo.File.OptionalHeader.(type) {
	case *pe.OptionalHeader64:
		if len(oh.DataDirectory) > pe.IMAGE_DIRECTORY_ENTRY_BASERELOC {
			dir = oh.DataDirectory[pe.IMAGE_DIRECTORY_ENTRY_BASERELOC]
		}
	case *pe.OptionalHeader32:
		if len(oh.DataDirectory) > pe.IMAGE_DIRECTORY_ENTRY_BASERELOC {
			dir = oh.DataDirectory[pe.IMAGE_DIRECTORY_ENTRY_BASERELOC]
		}
	}
	if dir.Size == 0 {
		return nil
	}
	var relocs []byte
	for _, section := range peInfo.File.Sections {
		if dir.VirtualAddress >= section.VirtualAddress && dir.VirtualAddress < section.VirtualAddress+section.VirtualSize {
			data, err := section.Data()
			if err != nil {
				return err
			}
			offset := dir.VirtualAddress - section.VirtualAddress
			if uint64(offset)+uint64(dir.Size) > uint64(len(data)) {
				return errors.New("base relocation table runs past its section")
			}
			relocs = data[offset : offset+dir.Size]
			break
		}
	}
	if relocs == nil {
		return errors.New("base relocation table not found in any section")
	}
	for len(relocs) >= 8 {
		page := uint64(binary.LittleEndian.Uint32(relocs))
		size := binary.LittleEndian.Uint32(relocs[4:])
		if size < 8 || uint64(size) > uint64(len(relocs)) {
			return errors.New("malformed base relocation block")
		}
		for entries := relocs[8:size]; len(entries) >= 2; entries = entries[2:] {
			entry := binary.LittleEndian.Uint16(entries)
			if entry>>12 == 0 { // IMAGE_REL_BASED_ABSOLUTE, padding
				continue
			}
			rva := page + uint64(entry&0xfff)
			// The widest field a base relocation patches is 8 bytes.
			if rva+8 > start && rva < end {
				return fmt.Errorf("the loader patches RVA 0x%x, in bcm-rust.o's module region 0x%x-0x%x", rva, start, end)
			}
		}
		relocs = relocs[size:]
	}
	return nil
}

func do(outPath, oInput string, arInput string, appleOS bool, windowsOS bool, mapFile string, rust bool) error {
	var objectBytes []byte
	var isStatic bool
	var perm os.FileMode

	if appleOS && windowsOS {
		return fmt.Errorf("-apple and -windows are mutually exclusive")
	}

	if windowsOS && len(mapFile) == 0 {
		return fmt.Errorf("-map is required when -windows is set")
	}

	if rust && len(oInput) == 0 {
		return fmt.Errorf("-rust takes an object with -in-object")
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
	if windowsOS && rust {
		moduleText, err = doWindowsRust(objectBytes, mapFile)
	} else if windowsOS {
		moduleText, moduleROData, err = doWindows(objectBytes, mapFile)
	} else if appleOS {
		moduleText, moduleROData, err = doAppleOS(objectBytes, rust)
	} else {
		moduleText, moduleROData, err = doLinux(objectBytes, isStatic, rust)
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

	uninitHashValue := fipscommon.UninitHashValue
	if rust {
		uninitHashValue = rustUninitHashValue
	}
	offset := bytes.Index(objectBytes, uninitHashValue[:])
	if offset < 0 {
		return errors.New("did not find uninitialised hash value in object file")
	}

	if bytes.Index(objectBytes[offset+1:], uninitHashValue[:]) >= 0 {
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
	rust := flag.Bool("rust", false, "Whether the object is bcm-rust.o, the Rust FIPS module.")

	flag.Parse()

	if err := do(*outPath, *oInput, *arInput, *appleOS, *windowsOS, *mapFile, *rust); err != nil {
		fmt.Fprintf(os.Stderr, "%s\n", err)
		os.Exit(1)
	}
}
