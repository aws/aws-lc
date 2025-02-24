package main

import (
	"debug/elf"
	"encoding/hex"
	"flag"
	"fmt"
	"os"
	"path/filepath"
)

const usageTemplate = `
Compare the fipsmodule hash of two shared libraries or two binaries statically linked AWS-LC:
%s <fileLeft> <fileRight>

Print the fipsmodule hash of a shared library or a binary statically linked AWS-LC:
%s <file>

`

var usageStr string

func init() {
	programName := filepath.Base(os.Args[0])
	usageStr = fmt.Sprintf(usageTemplate, programName, programName)
}

func printErrorAndExit(message string, args ...interface{}) {
	_, _ = fmt.Fprintf(os.Stderr, message, args...)
	os.Exit(1)
}

func printMessage(message string, args ...interface{}) {
	_, _ = fmt.Fprintf(os.Stdout, message, args...)
}

func main() {
	flag.Parse()

	switch {
	case len(flag.Args()) == 1:
		printModuleHash(flag.Arg(0))
	case len(flag.Args()) == 2:
		diffModules(flag.Arg(0), flag.Arg(1))
	default:
		printErrorAndExit(usageStr)
	}
}

func printModuleHash(filepath string) {
	hashBytes, err := getFIPSModuleHashSymbol(filepath)
	if err != nil {
		printErrorAndExit("Error: %v\n", err)
	}

	hexStr := hex.EncodeToString(hashBytes)

	printMessage("%s\n", hexStr)
}

func diffModules(left, right string) {
	leftHashBytes, err := getFIPSModuleHashSymbol(left)
	if err != nil {
		printErrorAndExit("Error: %v\n", err)
	}

	rightHashBytes, err := getFIPSModuleHashSymbol(right)
	if err != nil {
		printErrorAndExit("Error: %v\n", err)
	}

	leftHexStr := hex.EncodeToString(leftHashBytes)
	rightHexStr := hex.EncodeToString(rightHashBytes)

	if leftHexStr != rightHexStr {
		printErrorAndExit("MISMATCH: (%s != %s)\n", leftHexStr, rightHexStr)
	}

	printMessage("MATCH: (%s)\n", leftHexStr)
}

func getFIPSModuleHashSymbol(filepath string) ([]byte, error) {
	const fipsModuleHashSymbol = "BORINGSSL_bcm_text_hash"

	elfFile, err := elf.Open(filepath)
	if err != nil {
		return nil, fmt.Errorf("failed to open file: %w", err)
	}
	defer elfFile.Close()

	symbols, err := elfFile.Symbols()
	if err != nil {
		return nil, fmt.Errorf("error reading symbols: %w", err)
	}

	var hashSymbol elf.Symbol
	found := false
	for _, symbol := range symbols {
		if symbol.Name == fipsModuleHashSymbol {
			hashSymbol = symbol
			found = true
			break
		}
	}

	if !found {
		return nil, fmt.Errorf("failed to find fipsmodule hash symbol")
	}

	hashSymbolSection := elfFile.Sections[hashSymbol.Section]
	if hashSymbolSection == nil {
		return nil, fmt.Errorf("fipsmodule hash symbol's section not found")
	}

	hashSymbolOffset := hashSymbol.Value - hashSymbolSection.Addr
	const expectedSize = 32
	if hashSymbol.Size != expectedSize {
		return nil, fmt.Errorf("the fipsmodule hash symbol does not match the expected size, expect %v got %v", expectedSize, hashSymbol.Size)
	}

	hashSymbolSectionData, err := hashSymbolSection.Data()
	if err != nil {
		return nil, fmt.Errorf("error reading section containing fipsmodule hash symbol: %w", err)
	}

	if int(hashSymbolOffset+hashSymbol.Size) > len(hashSymbolSectionData) {
		return nil, fmt.Errorf("the fipsmodule hash extends out of bounds of the section?")
	}

	return hashSymbolSectionData[hashSymbolOffset : hashSymbolOffset+hashSymbol.Size], nil
}
