// Copyright (c) 2017, Google Inc.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

package main

import (
	"bytes"
	"flag"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

var (
	testDataDir = flag.String("testdata", "testdata", "The path to the test data directory.")
	update      = flag.Bool("update", false, "If true, update output files rather than compare them.")
)

type delocateTest struct {
	name                    string
	includes                []string
	inputs                  []string
	out                     string
	startEndDebugDirectives bool
}

func (test *delocateTest) Path(file string) string {
	return filepath.Join(*testDataDir, test.name, file)
}

var delocateTests = []delocateTest{
	{"generic-FileDirectives", nil, []string{"in.s"}, "out.s", true},
	{"generic-FileDirectives-no-start-end", nil, []string{"in.s"}, "out.s", false},
	{"generic-Includes", []string{"/some/include/path/openssl/foo.h", "/some/include/path/openssl/bar.h"}, []string{"in.s"}, "out.s", true},
	{"ppc64le-GlobalEntry", nil, []string{"in.s"}, "out.s", true},
	{"ppc64le-LoadToR0", nil, []string{"in.s"}, "out.s", true},
	{"ppc64le-Sample2", nil, []string{"in.s"}, "out.s", true},
	{"ppc64le-Sample", nil, []string{"in.s"}, "out.s", true},
	{"ppc64le-TOCWithOffset", nil, []string{"in.s"}, "out.s", true},
	{"x86_64-Basic", nil, []string{"in.s"}, "out.s", true},
	{"x86_64-BSS", nil, []string{"in.s"}, "out.s", true},
	{"x86_64-GOTRewrite", nil, []string{"in.s"}, "out.s", true},
	{"x86_64-LargeMemory", nil, []string{"in.s"}, "out.s", true},
	{"x86_64-LabelRewrite", nil, []string{"in1.s", "in2.s"}, "out.s", true},
	{"x86_64-Sections", nil, []string{"in.s"}, "out.s", true},
	{"x86_64-ThreeArg", nil, []string{"in.s"}, "out.s", true},
	{"x86_64-FourArg", nil, []string{"in.s"}, "out.s", true},
	{"aarch64-Basic", nil, []string{"in.s"}, "out.s", true},
}

func TestDelocate(t *testing.T) {
	for _, test := range delocateTests {
		t.Run(test.name, func(t *testing.T) {
			var inputs []inputFile
			for i, in := range test.inputs {
				inputs = append(inputs, inputFile{
					index: i,
					path:  test.Path(in),
				})
			}

			if err := parseInputs(inputs, nil); err != nil {
				t.Fatalf("parseInputs failed: %s", err)
			}

			var buf bytes.Buffer
			if err := transform(&buf, test.includes, inputs, test.startEndDebugDirectives); err != nil {
				t.Fatalf("transform failed: %s", err)
			}

			if *update {
				os.WriteFile(test.Path(test.out), buf.Bytes(), 0666)
			} else {
				expected, err := os.ReadFile(test.Path(test.out))
				if err != nil {
					t.Fatalf("could not read %q: %s", test.Path(test.out), err)
				}

				got := buf.Bytes()
				if !bytes.Equal(got, expected) {
					t.Errorf("delocated output differed.\nWanted:\n%s\nGot:\n%s\n", expected, got)

					expectedLines := strings.Split(string(expected), "\n")
					gotLines := strings.Split(string(got), "\n")

					for i := 0; i < len(expectedLines) && i < len(gotLines); i++ {
						if expectedLines[i] != gotLines[i] {
							t.Errorf("\nFirst difference at line %d:\nExpected:\t%q\nGot:\t%q\n", i+1, expectedLines[i], gotLines[i])
							break
						}
					}
				}
			}
		})
	}
}
