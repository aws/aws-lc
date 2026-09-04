// Copyright (c) 2021, Google Inc.
// SPDX-License-Identifier: ISC

//go:build ignore

package main

import (
	"bytes"
	"compress/bzip2"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"os/exec"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
)

var (
	toolPath       *string = flag.String("tool", "", "Path to acvptool binary")
	moduleWrappers *string = flag.String("module-wrappers", "", "Comma-separated list of name:path pairs for known module wrappers")
	testsPath      *string = flag.String("tests", "", "Path to JSON file listing tests")
	update         *bool   = flag.Bool("update", false, "If true then write updated outputs")
)

type invocation struct {
	toolPath           string
	wrapperPath        string
	inPath             string
	expectedPath       string
	expectedVectorSets []vectorSetDescriptor
}

type vectorSetDescriptor struct {
	Algorithm string `json:"algorithm"`
	Mode      string `json:"mode"`
	Revision  string `json:"revision"`
}

func main() {
	flag.Parse()

	if len(*toolPath) == 0 {
		log.Fatal("-tool must be given")
	}

	if len(*moduleWrappers) == 0 {
		log.Fatal("-module-wrappers must be given")
	}

	wrappers := make(map[string]string)
	pairs := strings.Split(*moduleWrappers, ",")
	for _, pair := range pairs {
		parts := strings.SplitN(pair, ":", 2)
		if _, ok := wrappers[parts[0]]; ok {
			log.Fatalf("wrapper %q defined twice", parts[0])
		}
		wrappers[parts[0]] = parts[1]
	}

	if len(*testsPath) == 0 {
		log.Fatal("-tests must be given")
	}

	testsFile, err := os.Open(*testsPath)
	if err != nil {
		log.Fatal(err)
	}
	defer testsFile.Close()

	decoder := json.NewDecoder(testsFile)
	var tests []struct {
		Wrapper            string
		In                 string
		Out                string // Optional, may be empty.
		ExpectedVectorSets []vectorSetDescriptor
	}
	if err := decoder.Decode(&tests); err != nil {
		log.Fatal(err)
	}

	work := make(chan invocation, runtime.NumCPU())
	var numFailed uint32

	var wg sync.WaitGroup
	for i := 0; i < runtime.NumCPU(); i++ {
		wg.Add(1)
		go worker(&wg, work, &numFailed)
	}

	for _, test := range tests {
		wrapper, ok := wrappers[test.Wrapper]
		if !ok {
			log.Fatalf("wrapper %q not specified on command line", test.Wrapper)
		}
		work <- invocation{
			toolPath:           *toolPath,
			wrapperPath:        wrapper,
			inPath:             test.In,
			expectedPath:       test.Out,
			expectedVectorSets: test.ExpectedVectorSets,
		}
	}

	close(work)
	wg.Wait()

	n := atomic.LoadUint32(&numFailed)
	if n > 0 {
		log.Printf("Failed %d tests", n)
		os.Exit(1)
	} else {
		log.Printf("%d ACVP tests matched expectations", len(tests))
	}
}

func worker(wg *sync.WaitGroup, work <-chan invocation, numFailed *uint32) {
	defer wg.Done()

	for test := range work {
		if err := doTest(test); err != nil {
			log.Printf("Test failed for %q: %s", test.inPath, err)
			atomic.AddUint32(numFailed, 1)
		}
	}
}

func doTest(test invocation) error {
	input, err := os.Open(test.inPath)
	if err != nil {
		return fmt.Errorf("Failed to open %q: %s", test.inPath, err)
	}
	defer input.Close()

	tempFile, err := os.CreateTemp("", "boringssl-check_expected-")
	if err != nil {
		return fmt.Errorf("Failed to create temp file: %s", err)
	}
	defer os.Remove(tempFile.Name())
	defer tempFile.Close()

	testInputFile := test.inPath
	if strings.HasSuffix(test.inPath, ".bz2") {
		// Decompress the input file when it is compressed.
		decompressor := bzip2.NewReader(input)
		if _, err := io.Copy(tempFile, decompressor); err != nil {
			return fmt.Errorf("Failed to decompress %q: %s", test.inPath, err)
		}
		testInputFile = tempFile.Name()
	}
	if err := checkExpectedVectorSets(testInputFile, test.expectedVectorSets); err != nil {
		return fmt.Errorf("Invalid vector-set inventory in %q: %s", test.inPath, err)
	}
	cmd := exec.Command(test.toolPath, "-wrapper", test.wrapperPath, "-json", testInputFile)
	result, err := cmd.CombinedOutput()
	if err != nil {
		os.Stderr.Write(result)
		return fmt.Errorf("Failed to process %q: %s", test.inPath, err)
	}

	if len(test.expectedPath) == 0 {
		// This test has variable output and thus cannot be compared against a fixed
		// result.
		return nil
	}

	expected, err := os.Open(test.expectedPath)
	if err != nil {
		if *update {
			writeUpdate(test.expectedPath, result)
		}
		return fmt.Errorf("Failed to open %q: %s", test.expectedPath, err)
	}
	defer expected.Close()

	var expectedBytes []byte
	if strings.HasSuffix(test.expectedPath, ".bz2") {
		decompressor := bzip2.NewReader(expected)
		var expectedBuf bytes.Buffer
		if _, err := io.Copy(&expectedBuf, decompressor); err != nil {
			return fmt.Errorf("Failed to decompress %q: %s", test.expectedPath, err)
		}
		expectedBytes = expectedBuf.Bytes()
	} else {
		// Avoid decompression if it's not compressed
		expectedBytes, _ = os.ReadFile(test.expectedPath)
	}

	if !bytes.Equal(expectedBytes, result) {
		if *update {
			writeUpdate(test.expectedPath, result)
		}
		return fmt.Errorf("Mismatch for %q", test.expectedPath)
	}

	return nil
}

func checkExpectedVectorSets(path string, expected []vectorSetDescriptor) error {
	if len(expected) == 0 {
		return nil
	}

	input, err := os.Open(path)
	if err != nil {
		return err
	}
	defer input.Close()

	var elements []json.RawMessage
	if err := json.NewDecoder(input).Decode(&elements); err != nil {
		return err
	}
	if len(elements) < 2 {
		return fmt.Errorf("input has fewer than two elements")
	}

	actual := make([]vectorSetDescriptor, 0, len(elements)-1)
	for i, element := range elements[1:] {
		var descriptor vectorSetDescriptor
		if err := json.Unmarshal(element, &descriptor); err != nil {
			return fmt.Errorf("failed to parse vector set %d: %s", i+1, err)
		}
		if len(descriptor.Algorithm) == 0 || len(descriptor.Mode) == 0 || len(descriptor.Revision) == 0 {
			return fmt.Errorf("vector set %d has incomplete descriptor: %+v", i+1, descriptor)
		}
		actual = append(actual, descriptor)
	}

	counts := make(map[vectorSetDescriptor]int)
	for i, descriptor := range expected {
		if len(descriptor.Algorithm) == 0 || len(descriptor.Mode) == 0 || len(descriptor.Revision) == 0 {
			return fmt.Errorf("expected vector set %d has incomplete descriptor: %+v", i+1, descriptor)
		}
		counts[descriptor]++
	}
	for _, descriptor := range actual {
		counts[descriptor]--
	}
	for _, count := range counts {
		if count != 0 {
			return fmt.Errorf("got %+v, expected %+v", actual, expected)
		}
	}
	if len(actual) != len(expected) {
		return fmt.Errorf("got %+v, expected %+v", actual, expected)
	}

	return nil
}

func writeUpdate(path string, contents []byte) {
	path = strings.TrimSuffix(path, ".bz2")
	if err := os.WriteFile(path, contents, 0644); err != nil {
		log.Printf("Failed to create missing file %q: %s", path, err)
	} else {
		log.Printf("Wrote %q", path)
	}
}
