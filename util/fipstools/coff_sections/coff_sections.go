// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// coff_sections renames sections of a COFF object file. bcm-rust.o's fold
// uses it in Windows FIPS builds, where there's no partial link and
// llvm-objcopy can't rename COFF sections, to put the module's code and
// constants in one group of sections (cmake/rust_crate_object_fold.cmake).
//
// Usage: coff_sections -o <out.obj> <in.obj> <old>=<new>[,code]...
//
// Each rule renames the sections named <old>, or starting with <old> if it
// ends in "*". The first rule that matches a section applies. ",code" also
// makes a section of constants read-only code, so that the linker merges it
// with code sections of the same name: lld-link keeps sections with different
// characteristics apart. A section that was writable stops being writable:
// AWS-LC's assembly declares .rodata without flags, which COFF makes
// writable. Alignment and COMDAT selection don't change. New names fit in the
// 8-byte section header, so the string table doesn't change.
package main

import (
	"debug/pe"
	"encoding/binary"
	"errors"
	"flag"
	"fmt"
	"os"
	"strconv"
	"strings"
)

type rule struct {
	old, new string
	prefix   bool
	code     bool
}

func parseRule(arg string) (rule, error) {
	old, new, ok := strings.Cut(arg, "=")
	if !ok || old == "" {
		return rule{}, fmt.Errorf("rule %q isn't <old>=<new>[,code]", arg)
	}
	r := rule{old: old, new: new}
	r.new, r.code = strings.CutSuffix(r.new, ",code")
	r.old, r.prefix = strings.CutSuffix(r.old, "*")
	if r.new == "" || len(r.new) > 8 {
		return rule{}, fmt.Errorf("rule %q: the new name has to be 1 to 8 bytes", arg)
	}
	return r, nil
}

func (r rule) matches(name string) bool {
	if r.prefix {
		return strings.HasPrefix(name, r.old)
	}
	return name == r.old
}

func rename(obj []byte, rules []rule) error {
	le := binary.LittleEndian
	if len(obj) < 20 {
		return errors.New("not a COFF object")
	}
	if le.Uint16(obj[0:]) == 0 && le.Uint16(obj[2:]) == 0xffff {
		return errors.New("bigobj COFF files aren't supported")
	}
	numSections := int(le.Uint16(obj[2:]))
	symbolTable := int(le.Uint32(obj[8:]))
	numSymbols := int(le.Uint32(obj[12:]))
	if le.Uint16(obj[16:]) != 0 {
		return errors.New("not a COFF object: it has an optional header")
	}
	stringTable := symbolTable + numSymbols*18
	if len(obj) < 20+numSections*40 || len(obj) < stringTable+4 {
		return errors.New("truncated COFF object")
	}
	for i := 0; i < numSections; i++ {
		header := obj[20+i*40:][:40]
		name := strings.TrimRight(string(header[:8]), "\x00")
		if strings.HasPrefix(name, "/") {
			offset, err := strconv.Atoi(name[1:])
			if err != nil || stringTable+offset >= len(obj) {
				return fmt.Errorf("section %d has a bad long name %q", i, name)
			}
			long := obj[stringTable+offset:]
			end := strings.IndexByte(string(long), 0)
			if end < 0 {
				return fmt.Errorf("section %d's long name isn't terminated", i)
			}
			name = string(long[:end])
		}
		for _, r := range rules {
			if !r.matches(name) {
				continue
			}
			copy(header[:8], make([]byte, 8))
			copy(header[:8], r.new)
			if r.code {
				chars := le.Uint32(header[36:])
				if chars&pe.IMAGE_SCN_CNT_UNINITIALIZED_DATA != 0 {
					return fmt.Errorf("section %s has no contents, so it can't become code", name)
				}
				chars &^= pe.IMAGE_SCN_CNT_INITIALIZED_DATA | pe.IMAGE_SCN_MEM_WRITE
				chars |= pe.IMAGE_SCN_CNT_CODE | pe.IMAGE_SCN_MEM_EXECUTE | pe.IMAGE_SCN_MEM_READ
				le.PutUint32(header[36:], chars)
			}
			break
		}
	}
	return nil
}

func main() {
	out := flag.String("o", "", "output object file")
	flag.Parse()
	if *out == "" || flag.NArg() < 2 {
		fmt.Fprintln(os.Stderr, "usage: coff_sections -o <out.obj> <in.obj> <old>=<new>[,code]...")
		os.Exit(2)
	}
	var rules []rule
	for _, arg := range flag.Args()[1:] {
		r, err := parseRule(arg)
		if err != nil {
			fmt.Fprintln(os.Stderr, "coff_sections:", err)
			os.Exit(1)
		}
		rules = append(rules, r)
	}
	obj, err := os.ReadFile(flag.Arg(0))
	if err == nil {
		err = rename(obj, rules)
	}
	if err == nil {
		err = os.WriteFile(*out, obj, 0644)
	}
	if err != nil {
		fmt.Fprintf(os.Stderr, "coff_sections: %s: %s\n", flag.Arg(0), err)
		os.Exit(1)
	}
}
