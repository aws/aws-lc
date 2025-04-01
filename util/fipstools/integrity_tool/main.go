package main

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"
	"debug/elf"
	"encoding/binary"
	"encoding/hex"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
)

const usageTemplate = `
Compare the fipsmodule hash of two shared libraries or two binaries statically linked AWS-LC:

%s <fileLeft> <fileRight>

Print the fipsmodule hash of a shared library or a binary statically linked AWS-LC.
Options:
-verify used to verify that the contents of the module match the recorded hash.
-extract used to extract the BCM .text and .rodata sections explicitly for inspection. This will dump in binary and hex.

%s [-verify] [-extract] <file>

`

const (
	fipsModuleHashSymbol      = "BORINGSSL_bcm_text_hash"
	fipsModuleTextSection     = "BORINGSSL_bcm_text"
	fipsModuleReadOnlySection = "BORINGSSL_bcm_rodata"
)

var (
	usageStr string
	verify   bool
	extract  bool
)

func init() {
	programName := filepath.Base(os.Args[0])
	usageStr = fmt.Sprintf(usageTemplate, programName, programName)
	flag.BoolVar(&verify, "verify", false, "Verify the recorded fipsmodule hash of a shared library or a binary statically linked AWS-LC to it's contents")
	flag.BoolVar(&extract, "extract", false, "Extract the BCM sections to output files")
	flag.CommandLine.Usage = func() {
		_, _ = fmt.Fprint(os.Stderr, usageStr)
		// Exit handled by flag package
	}
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
	module, err := loadFIPSModule(filepath)
	if err != nil {
		printErrorAndExit("Error: %v\n", err)
	}
	defer module.Close()

	hashBytes, err := getFIPSModuleIntegrityHash(&module)
	if err != nil {
		printErrorAndExit("Error: %v\n", err)
	}

	hexStr := hex.EncodeToString(hashBytes)
	printMessage("%s\n", hexStr)

	if verify {
		computed, err := computeFIPSModuleIntegrityHash(&module)
		if err != nil {
			printErrorAndExit("Error Verifying Integrity Hash: %v\n", err)
		}
		if bytes.Equal(hashBytes, computed) {
			printMessage("Integrity Hash: VERIFIED\n")
		} else {
			printErrorAndExit("Integrity Hash: MISMATCH\nComputed: %v\n", hex.EncodeToString(computed))
		}
	}

	if extract {
		textBinary, textHex, rodataBinary, rodataHex, err := extractModuleSections(&module)
		if err != nil {
			printErrorAndExit("Error: %v\n", err)
		}
		printMessage("Extracted %s: %s\n", fipsModuleTextSection, textBinary)
		printMessage("Extracted %s: %s\n", fipsModuleTextSection, textHex)
		if rodataBinary != "" && rodataHex != "" {
			printMessage("Extracted %s: %s\n", fipsModuleReadOnlySection, rodataBinary)
			printMessage("Extracted %s: %s\n", fipsModuleReadOnlySection, rodataHex)
		}
	}
}

func diffModules(left, right string) {
	leftModule, err := loadFIPSModule(left)
	if err != nil {
		printErrorAndExit("Error: %v\n", err)
	}
	defer leftModule.Close()

	leftHashBytes, err := getFIPSModuleIntegrityHash(&leftModule)
	if err != nil {
		printErrorAndExit("Error: %v\n", err)
	}

	rightModule, err := loadFIPSModule(right)
	if err != nil {
		printErrorAndExit("Error: %v\n", err)
	}
	defer rightModule.Close()

	rightHashBytes, err := getFIPSModuleIntegrityHash(&rightModule)
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

type FIPSModule struct {
	file        *elf.File
	hash        *elf.Symbol
	textStart   *elf.Symbol
	textEnd     *elf.Symbol
	rodataStart *elf.Symbol
	rodataEnd   *elf.Symbol
}

func (m *FIPSModule) Close() error {
	m.hash = nil
	m.textStart = nil
	m.textEnd = nil
	m.rodataStart = nil
	m.rodataEnd = nil
	return m.file.Close()
}

func (m *FIPSModule) HasROData() bool {
	return m.rodataStart != nil && m.rodataEnd != nil
}

func loadFIPSModule(filepath string) (FIPSModule, error) {
	file, err := elf.Open(filepath)
	if err != nil {
		return FIPSModule{}, fmt.Errorf("failed to open file: %w", err)
	}

	symbols, err := file.Symbols()
	if err != nil {
		return FIPSModule{}, fmt.Errorf("error reading symbols: %w", err)
	}

	var hashSymbol, textStart, textEnd, rodataStart, rodataEnd *elf.Symbol

	for _, symbol := range symbols {
		symbol := symbol
		if symbol.Name == fipsModuleHashSymbol {
			hashSymbol = &symbol
		} else if strings.HasPrefix(symbol.Name, fipsModuleTextSection) {
			if strings.HasSuffix(symbol.Name, "_start") {
				textStart = &symbol
			} else if strings.HasSuffix(symbol.Name, "_end") {
				textEnd = &symbol
			} else {
				return FIPSModule{}, fmt.Errorf("unexpected symbol name: %s", symbol.Name)
			}
		} else if strings.HasPrefix(symbol.Name, fipsModuleReadOnlySection) {
			if strings.HasSuffix(symbol.Name, "_start") {
				rodataStart = &symbol
			} else if strings.HasSuffix(symbol.Name, "_end") {
				rodataEnd = &symbol
			} else {
				return FIPSModule{}, fmt.Errorf("unexpected symbol name: %s", symbol.Name)
			}
		}
	}

	if hashSymbol == nil {
		return FIPSModule{}, fmt.Errorf("failed to find fipsmodule hash symbol")
	}

	// We should always find the the .text section start and end markers. The .rodata section markers will only
	// be present for shared library builds.
	if textStart == nil || textEnd == nil {
		return FIPSModule{}, fmt.Errorf("failed to find fipsmodule .text start and end markers")
	}

	if (rodataStart != nil) != (rodataEnd != nil) {
		return FIPSModule{}, fmt.Errorf("inconsistent fipsmodule .rodata start and end markers")
	}

	return FIPSModule{
		file:        file,
		hash:        hashSymbol,
		textStart:   textStart,
		textEnd:     textEnd,
		rodataStart: rodataStart,
		rodataEnd:   rodataEnd,
	}, nil
}

func getFIPSModuleIntegrityHash(module *FIPSModule) ([]byte, error) {
	hashSymbolSection := module.file.Sections[module.hash.Section]
	if hashSymbolSection == nil {
		return nil, fmt.Errorf("fipsmodule hash symbol's section not found")
	}

	hashSymbolOffset := module.hash.Value - hashSymbolSection.Addr
	const expectedSize = 32
	if module.hash.Size != expectedSize {
		return nil, fmt.Errorf("the fipsmodule hash symbol does not match the expected size, expect %v got %v", expectedSize, module.hash.Size)
	}

	hashSymbolSectionData, err := hashSymbolSection.Data()
	if err != nil {
		return nil, fmt.Errorf("error reading section containing fipsmodule hash symbol: %w", err)
	}

	if int(hashSymbolOffset+module.hash.Size) > len(hashSymbolSectionData) {
		return nil, fmt.Errorf("the fipsmodule hash extends out of bounds of the section?")
	}

	return hashSymbolSectionData[hashSymbolOffset : hashSymbolOffset+module.hash.Size], nil
}

func computeFIPSModuleIntegrityHash(module *FIPSModule) ([]byte, error) {
	length, subReader, err := getSubSectionReader(module.file, module.textStart, module.textEnd)
	if err != nil {
		return nil, fmt.Errorf("failed to extract .text section: %w", err)
	}

	var lengthBytes [8]byte
	var zeroKey [64]byte
	hmacHash := hmac.New(sha256.New, zeroKey[:])
	binary.LittleEndian.PutUint64(lengthBytes[:], uint64(length))
	if _, err := hmacHash.Write(lengthBytes[:]); err != nil {
		return nil, err
	}
	if _, err := io.Copy(hmacHash, subReader); err != nil {
		return nil, err
	}

	if module.HasROData() {
		length, subReader, err := getSubSectionReader(module.file, module.rodataStart, module.rodataEnd)
		if err != nil {
			return nil, fmt.Errorf("failed to extract .rodata section: %w", err)
		}
		binary.LittleEndian.PutUint64(lengthBytes[:], uint64(length))
		if _, err := hmacHash.Write(lengthBytes[:]); err != nil {
			return nil, err
		}
		if _, err := io.Copy(hmacHash, subReader); err != nil {
			return nil, err
		}
	}

	return hmacHash.Sum(nil), nil
}

func extractModuleSections(module *FIPSModule) (textBinary, textHex, rodataBinary, rodataHex string, err error) {
	textBinary, err = dumpSubSectionBinaryToFile(module.file, fipsModuleTextSection, module.textStart, module.textEnd)
	if err != nil {
		return "", "", "", "", fmt.Errorf("failed to dump %s binary to file: %w", fipsModuleTextSection, err)
	}

	textHex, err = dumpSubSectionHexToFile(module.file, fipsModuleTextSection, module.textStart, module.textEnd)
	if err != nil {
		return "", "", "", "", fmt.Errorf("failed to dump %s hex to file: %w", fipsModuleTextSection, err)
	}

	if module.HasROData() {
		rodataBinary, err = dumpSubSectionBinaryToFile(module.file, fipsModuleReadOnlySection, module.rodataStart, module.rodataEnd)
		if err != nil {
			return "", "", "", "", fmt.Errorf("failed to dump %s binary to file: %w", fipsModuleReadOnlySection, err)
		}

		rodataHex, err = dumpSubSectionHexToFile(module.file, fipsModuleReadOnlySection, module.rodataStart, module.rodataEnd)
		if err != nil {
			return "", "", "", "", fmt.Errorf("failed to dump %s hex to file: %w", fipsModuleReadOnlySection, err)
		}
	}

	return textBinary, textHex, rodataBinary, rodataHex, nil
}

func dumpSubSectionBinaryToFile(file *elf.File, name string, start, end *elf.Symbol) (string, error) {
	_, subReader, err := getSubSectionReader(file, start, end)
	if err != nil {
		return "", fmt.Errorf("failed to extract %s section: %w", name, err)
	}
	fileName, err := writeContentsToTempFile(subReader, name+".bin")
	if err != nil {
		return "", fmt.Errorf("failed to write %s binary to file: %w", name, err)
	}
	return fileName, nil
}

func dumpSubSectionHexToFile(file *elf.File, name string, start, end *elf.Symbol) (string, error) {
	_, subReader, err := getSubSectionReader(file, start, end)
	if err != nil {
		return "", fmt.Errorf("failed to extract %s section: %w", name, err)
	}

	tempFile, err := getTempFile(name + ".hex")
	if err != nil {
		return "", err
	}

	hexDumper := hex.Dumper(tempFile)
	if _, err := io.Copy(hexDumper, subReader); err != nil {
		return "", fmt.Errorf("failed to write %s hex to file: %w", name, err)
	}
	if err := hexDumper.Close(); err != nil {
		return "", fmt.Errorf("failed to close hex dumper: %w", err)
	}

	if err := tempFile.Close(); err != nil {
		return "", fmt.Errorf("failed to close file: %w", err)
	}

	return tempFile.Name(), nil
}

func getSubSectionReader(file *elf.File, start, end *elf.Symbol) (int64, io.Reader, error) {
	symbolSection := file.Sections[start.Section]
	if symbolSection == nil {
		return 0, nil, fmt.Errorf("section not found")
	}

	if start.Section != end.Section {
		return 0, nil, fmt.Errorf("start and end symbols are in different sections")
	}

	startOffset := start.Value - symbolSection.Addr
	if start.Size != 0 {
		return 0, nil, fmt.Errorf("start symbol does not match the expected size, expect 0 got %v", start.Size)
	}

	endOffset := end.Value - symbolSection.Addr
	if end.Size != 0 {
		return 0, nil, fmt.Errorf("end symbol does not match the expected size, expect 0 got %v", end.Size)
	}

	sectionReader := symbolSection.Open()
	if _, err := sectionReader.Seek(int64(startOffset), 0); err != nil {
		return 0, nil, err
	}

	length := int64(endOffset - startOffset)

	return length, io.LimitReader(sectionReader, length), nil
}

func writeContentsToTempFile(reader io.Reader, filename string) (string, error) {
	file, err := getTempFile(filename)
	if err != nil {
		return "", err
	}
	if _, err := io.Copy(file, reader); err != nil {
		return "", fmt.Errorf("failed to write file: %w", err)
	}
	if err := file.Close(); err != nil {
		return "", fmt.Errorf("failed to close file: %w", err)
	}
	return file.Name(), nil
}

func getTempFile(filename string) (*os.File, error) {
	file, err := os.CreateTemp("", fmt.Sprintf("*.%s", filename))
	if err != nil {
		return nil, fmt.Errorf("failed to create file: %w", err)
	}
	return file, nil
}
