// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package main

import (
	"bytes"
	"strings"
	"testing"
)

func TestParseVersion(t *testing.T) {
	tests := []struct {
		input     string
		wantMajor int
		wantMinor int
	}{
		{"AWS_LC_0_0", 0, 0},
		{"AWS_LC_1_0", 1, 0},
		{"AWS_LC_1_1", 1, 1},
		{"AWS_LC_2_0", 2, 0},
		{"AWS_LC_10_3", 10, 3},
		{"bad", 0, 0},
		{"AWS_LC_", 0, 0},
	}
	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			major, minor := parseVersion(tt.input)
			if major != tt.wantMajor || minor != tt.wantMinor {
				t.Errorf("parseVersion(%q) = (%d, %d), want (%d, %d)",
					tt.input, major, minor, tt.wantMajor, tt.wantMinor)
			}
		})
	}
}

func TestVersionLess(t *testing.T) {
	tests := []struct {
		a, b string
		want bool
	}{
		{"AWS_LC_0_0", "AWS_LC_1_0", true},
		{"AWS_LC_1_0", "AWS_LC_0_0", false},
		{"AWS_LC_1_0", "AWS_LC_1_1", true},
		{"AWS_LC_1_1", "AWS_LC_2_0", true},
		{"AWS_LC_0_0", "AWS_LC_0_0", false},
		{"AWS_LC_2_0", "AWS_LC_1_1", false},
	}
	for _, tt := range tests {
		t.Run(tt.a+"_vs_"+tt.b, func(t *testing.T) {
			got := versionLess(tt.a, tt.b)
			if got != tt.want {
				t.Errorf("versionLess(%q, %q) = %v, want %v", tt.a, tt.b, got, tt.want)
			}
		})
	}
}

func TestReadRegistryFrom(t *testing.T) {
	tests := []struct {
		name         string
		input        string
		wantVersions []string
		wantCounts   map[string]int
		wantErr      bool
	}{
		{
			name:         "empty input",
			input:        "",
			wantVersions: nil,
			wantCounts:   map[string]int{},
		},
		{
			name:         "comments and blank lines",
			input:        "# comment\n\n# another comment\n",
			wantVersions: nil,
			wantCounts:   map[string]int{},
		},
		{
			name:         "single version two fields",
			input:        "AES_encrypt AWS_LC_0_0\nAES_decrypt AWS_LC_0_0\n",
			wantVersions: []string{"AWS_LC_0_0"},
			wantCounts:   map[string]int{"AWS_LC_0_0": 2},
		},
		{
			name:         "single version three fields",
			input:        "AES_encrypt AWS_LC_0_0 PUBLIC\nCRYPTO_once AWS_LC_0_0 PRIVATE\n",
			wantVersions: []string{"AWS_LC_0_0"},
			wantCounts:   map[string]int{"AWS_LC_0_0": 2},
		},
		{
			name: "multiple versions sorted correctly",
			input: "AES_encrypt AWS_LC_0_0 PUBLIC\n" +
				"SSL_read AWS_LC_0_0 PUBLIC\n" +
				"new_func AWS_LC_1_0 PUBLIC\n" +
				"newer_func AWS_LC_2_0 PRIVATE\n",
			wantVersions: []string{"AWS_LC_0_0", "AWS_LC_1_0", "AWS_LC_2_0"},
			wantCounts:   map[string]int{"AWS_LC_0_0": 2, "AWS_LC_1_0": 1, "AWS_LC_2_0": 1},
		},
		{
			name:    "malformed line too few fields",
			input:   "AES_encrypt\n",
			wantErr: true,
		},
		{
			name:    "malformed line too many fields",
			input:   "AES_encrypt AWS_LC_0_0 PUBLIC EXTRA\n",
			wantErr: true,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			versionSymbols, versions, err := readRegistryFrom(strings.NewReader(tt.input))
			if tt.wantErr {
				if err == nil {
					t.Fatal("expected error, got nil")
				}
				return
			}
			if err != nil {
				t.Fatalf("unexpected error: %v", err)
			}
			if len(versions) != len(tt.wantVersions) {
				t.Fatalf("versions = %v, want %v", versions, tt.wantVersions)
			}
			for i, v := range versions {
				if v != tt.wantVersions[i] {
					t.Errorf("version[%d] = %q, want %q", i, v, tt.wantVersions[i])
				}
			}
			for v, wantCount := range tt.wantCounts {
				if got := len(versionSymbols[v]); got != wantCount {
					t.Errorf("len(versionSymbols[%q]) = %d, want %d", v, got, wantCount)
				}
			}
		})
	}
}

func TestReadRegistryFromVisibility(t *testing.T) {
	input := "foo AWS_LC_0_0\nbar AWS_LC_0_0 PRIVATE\nbaz AWS_LC_0_0 PRIVATE_CXX\n"
	versionSymbols, _, err := readRegistryFrom(strings.NewReader(input))
	if err != nil {
		t.Fatal(err)
	}
	syms := versionSymbols["AWS_LC_0_0"]
	want := map[string]string{
		"foo": "PUBLIC",
		"bar": "PRIVATE",
		"baz": "PRIVATE_CXX",
	}
	for _, s := range syms {
		if expected, ok := want[s.name]; ok {
			if s.visibility != expected {
				t.Errorf("symbol %q visibility = %q, want %q", s.name, s.visibility, expected)
			}
		}
	}
}

func TestWriteVersionScriptTo_SingleVersion(t *testing.T) {
	versions := []string{"AWS_LC_0_0"}
	versionSymbols := map[string][]symbolInfo{
		"AWS_LC_0_0": {
			{name: "AES_encrypt", visibility: "PUBLIC"},
			{name: "AES_decrypt", visibility: "PUBLIC"},
		},
	}

	var buf bytes.Buffer
	if err := writeVersionScriptTo(&buf, versions, versionSymbols); err != nil {
		t.Fatal(err)
	}
	output := buf.String()

	// Check header comment.
	if !strings.Contains(output, "# GNU ld version script for AWS-LC") {
		t.Error("missing header comment")
	}
	// Check version block.
	if !strings.Contains(output, "AWS_LC_0_0 {") {
		t.Error("missing version block")
	}
	// Check symbols are present and sorted.
	if !strings.Contains(output, "    AES_decrypt;") {
		t.Error("missing AES_decrypt symbol")
	}
	if !strings.Contains(output, "    AES_encrypt;") {
		t.Error("missing AES_encrypt symbol")
	}
	// Base version must have local: *.
	if !strings.Contains(output, "  local:") {
		t.Error("base version missing local: *")
	}
}

func TestWriteVersionScriptTo_MultipleVersions(t *testing.T) {
	versions := []string{"AWS_LC_0_0", "AWS_LC_1_0"}
	versionSymbols := map[string][]symbolInfo{
		"AWS_LC_0_0": {
			{name: "AES_encrypt", visibility: "PUBLIC"},
		},
		"AWS_LC_1_0": {
			{name: "new_func", visibility: "PUBLIC"},
		},
	}

	var buf bytes.Buffer
	if err := writeVersionScriptTo(&buf, versions, versionSymbols); err != nil {
		t.Fatal(err)
	}
	output := buf.String()

	// Base version has local: *.
	if !strings.Contains(output, "  local:\n    *;\n};") {
		t.Error("base version missing local: *;")
	}
	// Derived version inherits from base.
	if !strings.Contains(output, "} AWS_LC_0_0;") {
		t.Error("derived version missing inheritance from AWS_LC_0_0")
	}
	// Derived version should NOT have local: *.
	// Count occurrences of "local:" — should be exactly 1.
	if strings.Count(output, "local:") != 1 {
		t.Error("only base version should have local:")
	}
}

func TestWriteVersionScriptTo_CxxSymbols(t *testing.T) {
	versions := []string{"AWS_LC_0_0"}
	versionSymbols := map[string][]symbolInfo{
		"AWS_LC_0_0": {
			{name: "AES_encrypt", visibility: "PUBLIC"},
			{name: "bssl::func1", visibility: "PRIVATE_CXX"},
			{name: "bssl::SSLKeyShare", visibility: "PRIVATE_CXX_CLASS"},
		},
	}

	var buf bytes.Buffer
	if err := writeVersionScriptTo(&buf, versions, versionSymbols); err != nil {
		t.Fatal(err)
	}
	output := buf.String()

	// C symbol in global section.
	if !strings.Contains(output, "    AES_encrypt;") {
		t.Error("missing C symbol")
	}
	// C++ block.
	if !strings.Contains(output, `    extern "C++" {`) {
		t.Error("missing extern C++ block")
	}
	// C++ function glob pattern.
	if !strings.Contains(output, "      bssl::func1*;") {
		t.Error("missing C++ function glob pattern")
	}
	// C++ class glob pattern.
	if !strings.Contains(output, "      bssl::SSLKeyShare::*;") {
		t.Error("missing C++ class glob pattern")
	}
}

func TestWriteVersionScriptTo_Empty(t *testing.T) {
	var buf bytes.Buffer
	if err := writeVersionScriptTo(&buf, nil, nil); err != nil {
		t.Fatal(err)
	}
	output := buf.String()
	// Should have just the header comment.
	if !strings.Contains(output, "# GNU ld version script") {
		t.Error("missing header comment in empty output")
	}
	if strings.Contains(output, "global:") {
		t.Error("empty output should not contain version blocks")
	}
}

func TestEndToEnd(t *testing.T) {
	registry := `# Symbol registry for testing
AES_encrypt AWS_LC_0_0 PUBLIC
AES_decrypt AWS_LC_0_0 PUBLIC
bssl::ssl_func AWS_LC_0_0 PRIVATE_CXX
new_api AWS_LC_1_0 PUBLIC
bssl::SSLKeyShare AWS_LC_1_0 PRIVATE_CXX_CLASS
`
	versionSymbols, versions, err := readRegistryFrom(strings.NewReader(registry))
	if err != nil {
		t.Fatal(err)
	}

	if len(versions) != 2 {
		t.Fatalf("expected 2 versions, got %d", len(versions))
	}
	if versions[0] != "AWS_LC_0_0" || versions[1] != "AWS_LC_1_0" {
		t.Fatalf("unexpected version order: %v", versions)
	}

	var buf bytes.Buffer
	if err := writeVersionScriptTo(&buf, versions, versionSymbols); err != nil {
		t.Fatal(err)
	}
	output := buf.String()

	// Verify structure: header, base version with local:*, derived version with inheritance.
	lines := strings.Split(output, "\n")
	var foundBase, foundDerived, foundLocal, foundInherit bool
	for _, line := range lines {
		if strings.HasPrefix(line, "AWS_LC_0_0 {") {
			foundBase = true
		}
		if strings.HasPrefix(line, "AWS_LC_1_0 {") {
			foundDerived = true
		}
		if strings.TrimSpace(line) == "*;" {
			foundLocal = true
		}
		if strings.TrimSpace(line) == "} AWS_LC_0_0;" {
			foundInherit = true
		}
	}
	if !foundBase {
		t.Error("missing base version block")
	}
	if !foundDerived {
		t.Error("missing derived version block")
	}
	if !foundLocal {
		t.Error("missing local: * in base version")
	}
	if !foundInherit {
		t.Error("derived version missing inheritance from AWS_LC_0_0")
	}
}
