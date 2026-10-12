// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

package main

import (
	"bytes"
	"sort"
	"strings"
	"testing"
	"testing/fstest"
)

// ---------------------------------------------------------------------------
// makeSet
// ---------------------------------------------------------------------------

func TestMakeSet(t *testing.T) {
	tests := []struct {
		name string
		csv  string
		want map[string]struct{}
	}{
		{"empty", "", map[string]struct{}{}},
		{"single", "foo", map[string]struct{}{"foo": {}}},
		{"multiple", "a,b,c", map[string]struct{}{"a": {}, "b": {}, "c": {}}},
		{"whitespace", " a , b , c ", map[string]struct{}{"a": {}, "b": {}, "c": {}}},
		{"trailing comma", "a,b,", map[string]struct{}{"a": {}, "b": {}}},
		{"duplicates", "a,b,a", map[string]struct{}{"a": {}, "b": {}}},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := makeSet(tt.csv)
			if len(got) != len(tt.want) {
				t.Fatalf("makeSet(%q) returned %d elements, want %d", tt.csv, len(got), len(tt.want))
			}
			for k := range tt.want {
				if _, ok := got[k]; !ok {
					t.Errorf("makeSet(%q) missing key %q", tt.csv, k)
				}
			}
		})
	}
}

// ---------------------------------------------------------------------------
// lastIdent
// ---------------------------------------------------------------------------

func TestLastIdent(t *testing.T) {
	tests := []struct {
		input string
		want  string
	}{
		{"int foo", "foo"},
		{"const char *bar", "bar"},
		{"void **baz", "baz"},
		{"unsigned long long count", "count"},
		{"", ""},
		{"***", ""},
		{"int *(*complex_thing", "int"},
	}
	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			got := lastIdent(tt.input)
			if got != tt.want {
				t.Errorf("lastIdent(%q) = %q, want %q", tt.input, got, tt.want)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// stripAttributes
// ---------------------------------------------------------------------------

func TestStripAttributes(t *testing.T) {
	tests := []struct {
		name  string
		input string
		want  string
	}{
		{
			"no attributes",
			"int foo(void)",
			"int foo(void)",
		},
		{
			"single attribute",
			`int __attribute__((deprecated)) foo(void)`,
			"int  foo(void)",
		},
		{
			"nested parens",
			`int __attribute__((deprecated("use bar"))) foo(void)`,
			"int  foo(void)",
		},
		{
			"multiple attributes",
			`__attribute__((visibility("default"))) int __attribute__((deprecated)) foo(void)`,
			" int  foo(void)",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := stripAttributes(tt.input)
			if got != tt.want {
				t.Errorf("stripAttributes(%q) = %q, want %q", tt.input, got, tt.want)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// symbolFromDecl
// ---------------------------------------------------------------------------

func TestSymbolFromDecl(t *testing.T) {
	tests := []struct {
		name    string
		decl    string
		want    string
		isClass bool
	}{
		{
			"simple function",
			" int SSL_read(SSL *ssl, void *buf, int num);",
			"SSL_read",
			false,
		},
		{
			"void function",
			" void AES_encrypt(const unsigned char *in, unsigned char *out, const AES_KEY *key);",
			"AES_encrypt",
			false,
		},
		{
			"data symbol",
			" const ASN1_ITEM RSA_PSS_PARAMS_it;",
			"RSA_PSS_PARAMS_it",
			false,
		},
		{
			"pointer return",
			" RSA *RSA_new(void);",
			"RSA_new",
			false,
		},
		{
			"function returning function pointer",
			" int (*SSL_get_verify_callback(const SSL *ssl))(int, X509_STORE_CTX *);",
			"SSL_get_verify_callback",
			false,
		},
		{
			"function returning function pointer with space",
			" int ( *SSL_CTX_get_verify_callback(const SSL_CTX *ctx))(int, X509_STORE_CTX *);",
			"SSL_CTX_get_verify_callback",
			false,
		},
		{
			"typedef skipped",
			"typedef int (*verify_cb)(int ok, X509_STORE_CTX *ctx);",
			"",
			false,
		},
		{
			"no semicolon",
			" int incomplete_decl(void)",
			"",
			false,
		},
		{
			"class export",
			" SSLKeyShare { public: static SSLKeyShare *Create();",
			"SSLKeyShare",
			true,
		},
		{
			"class with inheritance",
			" MyClass : public Base { void foo();",
			"MyClass",
			true,
		},
		{
			"static member skipped",
			"static int internal_func(void);",
			"",
			false,
		},
		{
			"with deprecated attribute",
			` __attribute__((deprecated)) int OLD_func(void);`,
			"OLD_func",
			false,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := symbolFromDecl(tt.decl)
			if got.name != tt.want {
				t.Errorf("symbolFromDecl(%q).name = %q, want %q", tt.decl, got.name, tt.want)
			}
			if got.isClass != tt.isClass {
				t.Errorf("symbolFromDecl(%q).isClass = %v, want %v", tt.decl, got.isClass, tt.isClass)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// extractedSymbol.qualifiedName
// ---------------------------------------------------------------------------

func TestQualifiedName(t *testing.T) {
	tests := []struct {
		sym  extractedSymbol
		want string
	}{
		{extractedSymbol{name: "foo", namespace: ""}, "foo"},
		{extractedSymbol{name: "foo", namespace: "bssl"}, "bssl::foo"},
		{extractedSymbol{name: "bar", namespace: "bssl::internal"}, "bssl::internal::bar"},
	}
	for _, tt := range tests {
		t.Run(tt.want, func(t *testing.T) {
			got := tt.sym.qualifiedName()
			if got != tt.want {
				t.Errorf("qualifiedName() = %q, want %q", got, tt.want)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// buildNamespaceRanges / namespaceAt
// ---------------------------------------------------------------------------

func TestBuildNamespaceRanges(t *testing.T) {
	tests := []struct {
		name      string
		text      string
		wantNames []string
		wantCount int
	}{
		{
			"no namespaces",
			"int foo; int bar;",
			nil,
			0,
		},
		{
			"single namespace",
			"namespace bssl { int foo; }",
			[]string{"bssl"},
			1,
		},
		{
			"nested namespaces",
			"namespace outer { namespace inner { int foo; } }",
			[]string{"outer", "outer::inner"},
			2,
		},
		{
			"anonymous namespace skipped",
			"namespace { int foo; }",
			nil,
			0,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			ranges := buildNamespaceRanges(tt.text)
			if len(ranges) != tt.wantCount {
				t.Fatalf("buildNamespaceRanges returned %d ranges, want %d", len(ranges), tt.wantCount)
			}
			for i, r := range ranges {
				if i < len(tt.wantNames) && r.name != tt.wantNames[i] {
					t.Errorf("range[%d].name = %q, want %q", i, r.name, tt.wantNames[i])
				}
				if r.start >= r.end {
					t.Errorf("range[%d] has start=%d >= end=%d", i, r.start, r.end)
				}
			}
		})
	}
}

func TestNamespaceAt(t *testing.T) {
	text := "namespace bssl { int foo; }"
	ranges := buildNamespaceRanges(text)

	// Position 0 is before the namespace opening brace — global scope.
	if ns := namespaceAt(0, ranges); ns != "" {
		t.Errorf("position 0 should be global, got %q", ns)
	}
	// Find a position inside the braces.
	bracePos := strings.IndexByte(text, '{')
	innerPos := bracePos + 2 // safely inside the namespace body
	if ns := namespaceAt(innerPos, ranges); ns != "bssl" {
		t.Errorf("position %d should be bssl, got %q", innerPos, ns)
	}
}

func TestNamespaceAt_Nested(t *testing.T) {
	text := "namespace outer { namespace inner { int foo; } }"
	ranges := buildNamespaceRanges(text)

	// Find inner namespace opening brace.
	innerStart := strings.Index(text, "inner {") + len("inner {") + 1
	if ns := namespaceAt(innerStart, ranges); ns != "outer::inner" {
		t.Errorf("inner position should be outer::inner, got %q", ns)
	}
}

// ---------------------------------------------------------------------------
// extractSymbols
// ---------------------------------------------------------------------------

func TestExtractSymbols(t *testing.T) {
	tests := []struct {
		name      string
		text      string
		wantNames []string
	}{
		{
			"single function",
			marker + " int SSL_read(SSL *ssl, void *buf, int num);",
			[]string{"SSL_read"},
		},
		{
			"multiple symbols",
			marker + " int foo(void); " + marker + " void bar(int x);",
			[]string{"bar", "foo"},
		},
		{
			"no markers",
			"int foo(void); void bar(int x);",
			nil,
		},
		{
			"with namespace",
			"namespace bssl { " + marker + " int func1(void); }",
			[]string{"func1"},
		},
		{
			"deduplication",
			marker + " int foo(void); " + marker + " int foo(int x);",
			[]string{"foo"},
		},
		{
			"class with exported members",
			"namespace bssl { class SSLKeyShare { " + marker + " static SSLKeyShare *Create(void); }; }",
			[]string{"SSLKeyShare"},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			syms := extractSymbols(tt.text)
			var names []string
			for _, s := range syms {
				names = append(names, s.name)
			}
			sort.Strings(names)
			sort.Strings(tt.wantNames)
			if len(names) != len(tt.wantNames) {
				t.Fatalf("extractSymbols returned %v, want %v", names, tt.wantNames)
			}
			for i := range names {
				if names[i] != tt.wantNames[i] {
					t.Errorf("symbol[%d] = %q, want %q", i, names[i], tt.wantNames[i])
				}
			}
		})
	}
}

func TestExtractSymbolsNamespace(t *testing.T) {
	text := "namespace bssl { " + marker + " int func1(void); }"
	syms := extractSymbols(text)
	if len(syms) != 1 {
		t.Fatalf("expected 1 symbol, got %d", len(syms))
	}
	if syms[0].namespace != "bssl" {
		t.Errorf("namespace = %q, want %q", syms[0].namespace, "bssl")
	}
	if syms[0].qualifiedName() != "bssl::func1" {
		t.Errorf("qualifiedName = %q, want %q", syms[0].qualifiedName(), "bssl::func1")
	}
}

// ---------------------------------------------------------------------------
// findClassesWithExportedMembers
// ---------------------------------------------------------------------------

func TestFindClassesWithExportedMembers(t *testing.T) {
	tests := []struct {
		name string
		text string
		want []string
	}{
		{
			"no classes",
			"int foo; int bar;",
			nil,
		},
		{
			"class with marker",
			"class MyClass { " + marker + " static void Create(void); };",
			[]string{"MyClass"},
		},
		{
			"class without marker",
			"class MyClass { int x; };",
			nil,
		},
		{
			"enum class skipped",
			"enum class Direction { kLeft, kRight };",
			nil,
		},
		{
			"class with inheritance",
			"class Derived : public Base { " + marker + " static Derived *Create(void); };",
			[]string{"Derived"},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := findClassesWithExportedMembers(tt.text)
			if len(got) != len(tt.want) {
				t.Fatalf("findClassesWithExportedMembers returned %v, want %v", got, tt.want)
			}
			for i := range got {
				if got[i] != tt.want[i] {
					t.Errorf("[%d] = %q, want %q", i, got[i], tt.want[i])
				}
			}
		})
	}
}

// ---------------------------------------------------------------------------
// uniqueDirs
// ---------------------------------------------------------------------------

func TestUniqueDirs(t *testing.T) {
	tests := []struct {
		name  string
		files []string
		want  []string
	}{
		{"empty", nil, nil},
		{"single", []string{"/a/b/c.h"}, []string{"/a/b"}},
		{"dedup", []string{"/a/b/c.h", "/a/b/d.h", "/a/e/f.h"}, []string{"/a/b", "/a/e"}},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := uniqueDirs(tt.files)
			if len(got) != len(tt.want) {
				t.Fatalf("uniqueDirs(%v) = %v, want %v", tt.files, got, tt.want)
			}
			for i := range got {
				if got[i] != tt.want[i] {
					t.Errorf("[%d] = %q, want %q", i, got[i], tt.want[i])
				}
			}
		})
	}
}

// ---------------------------------------------------------------------------
// findHeadersFS / findHeadersWithExportFS (using fstest.MapFS)
// ---------------------------------------------------------------------------

func TestFindHeadersFS(t *testing.T) {
	fsys := fstest.MapFS{
		"openssl/ssl.h":      &fstest.MapFile{Data: []byte("// ssl")},
		"openssl/crypto.h":   &fstest.MapFile{Data: []byte("// crypto")},
		"openssl/base.h":     &fstest.MapFile{Data: []byte("// base")},
		"openssl/internal.c": &fstest.MapFile{Data: []byte("// not a header")},
		"sub/dir/deep.h":     &fstest.MapFile{Data: []byte("// deep")},
	}

	headers, err := findHeadersFS(fsys)
	if err != nil {
		t.Fatal(err)
	}

	want := []string{
		"openssl/base.h",
		"openssl/crypto.h",
		"openssl/ssl.h",
		"sub/dir/deep.h",
	}
	if len(headers) != len(want) {
		t.Fatalf("findHeadersFS returned %v, want %v", headers, want)
	}
	for i := range headers {
		if headers[i] != want[i] {
			t.Errorf("[%d] = %q, want %q", i, headers[i], want[i])
		}
	}
}

func TestFindHeadersFS_Empty(t *testing.T) {
	fsys := fstest.MapFS{
		"readme.txt": &fstest.MapFile{Data: []byte("no headers here")},
	}
	headers, err := findHeadersFS(fsys)
	if err != nil {
		t.Fatal(err)
	}
	if len(headers) != 0 {
		t.Errorf("expected no headers, got %v", headers)
	}
}

func TestFindHeadersWithExportFS(t *testing.T) {
	fsys := fstest.MapFS{
		"exported.h": &fstest.MapFile{Data: []byte("OPENSSL_EXPORT int foo(void);")},
		"internal.h": &fstest.MapFile{Data: []byte("int bar(void);")},
		"jent.h":     &fstest.MapFile{Data: []byte("JENT_PRIVATE_STATIC int jent_func(void);")},
		"plain.c":    &fstest.MapFile{Data: []byte("OPENSSL_EXPORT but not a header")},
	}

	headers, err := findHeadersWithExportFS(fsys)
	if err != nil {
		t.Fatal(err)
	}

	want := []string{"exported.h", "jent.h"}
	if len(headers) != len(want) {
		t.Fatalf("findHeadersWithExportFS returned %v, want %v", headers, want)
	}
	for i := range headers {
		if headers[i] != want[i] {
			t.Errorf("[%d] = %q, want %q", i, headers[i], want[i])
		}
	}
}

// ---------------------------------------------------------------------------
// buildPublicWrapper
// ---------------------------------------------------------------------------

func TestBuildPublicWrapper_NoTargetNoExclude(t *testing.T) {
	headers := []string{"openssl/base.h", "openssl/crypto.h", "openssl/ssl.h"}
	wrapper := buildPublicWrapper(headers, nil, nil)

	// Should start with base.h include and marker definition.
	if !strings.Contains(wrapper, "#include <openssl/base.h>") {
		t.Error("missing base.h include")
	}
	if !strings.Contains(wrapper, "#define OPENSSL_EXPORT "+marker) {
		t.Error("missing marker definition")
	}
	// All headers should be included.
	for _, h := range headers {
		if !strings.Contains(wrapper, "#include <"+h+">") {
			t.Errorf("missing include for %s", h)
		}
	}
}

func TestBuildPublicWrapper_WithExclude(t *testing.T) {
	headers := []string{"openssl/base.h", "openssl/crypto.h", "openssl/ssl.h"}
	excluded := map[string]struct{}{"ssl.h": {}}
	wrapper := buildPublicWrapper(headers, nil, excluded)

	if strings.Contains(wrapper, "#include <openssl/ssl.h>") {
		t.Error("excluded header ssl.h should not be included")
	}
	if !strings.Contains(wrapper, "#include <openssl/crypto.h>") {
		t.Error("non-excluded header crypto.h should be included")
	}
}

func TestBuildPublicWrapper_WithTargeted(t *testing.T) {
	headers := []string{"openssl/base.h", "openssl/crypto.h", "openssl/ssl.h"}
	targeted := map[string]struct{}{"ssl.h": {}}
	wrapper := buildPublicWrapper(headers, targeted, nil)

	// Two-pass approach: non-targeted included first with empty OPENSSL_EXPORT,
	// then targeted included with marker OPENSSL_EXPORT.
	// Check that the wrapper defines OPENSSL_EXPORT empty first.
	emptyDefIdx := strings.Index(wrapper, "#define OPENSSL_EXPORT\n")
	markerDefIdx := strings.Index(wrapper, "#define OPENSSL_EXPORT "+marker)

	if emptyDefIdx < 0 {
		t.Fatal("missing empty OPENSSL_EXPORT define (pass 1)")
	}
	if markerDefIdx < 0 {
		t.Fatal("missing marker OPENSSL_EXPORT define (pass 2)")
	}
	if emptyDefIdx >= markerDefIdx {
		t.Error("empty define should come before marker define")
	}

	// ssl.h should appear only after the marker define.
	sslIdx := strings.LastIndex(wrapper, "#include <openssl/ssl.h>")
	if sslIdx < markerDefIdx {
		t.Error("targeted header should appear after marker definition")
	}

	// Non-targeted headers should appear before the marker define.
	cryptoIdx := strings.Index(wrapper, "#include <openssl/crypto.h>")
	if cryptoIdx < 0 {
		t.Fatal("missing crypto.h include")
	}
	if cryptoIdx > markerDefIdx {
		t.Error("non-targeted header should appear before marker definition")
	}
}

// ---------------------------------------------------------------------------
// buildInternalWrapper
// ---------------------------------------------------------------------------

func TestBuildInternalWrapper(t *testing.T) {
	publicHeaders := []string{"openssl/base.h", "openssl/crypto.h"}
	otherHeaders := []string{"crypto/internal.h"}
	internalHeaders := []string{"ssl/internal.h"}

	wrapper := buildInternalWrapper(publicHeaders, otherHeaders, internalHeaders)

	// Public headers should be included with angle brackets.
	if !strings.Contains(wrapper, "#include <openssl/base.h>") {
		t.Error("missing public header include")
	}
	if !strings.Contains(wrapper, "#include <openssl/crypto.h>") {
		t.Error("missing public header include")
	}

	// Other internal headers should be included with quotes (suppressed).
	if !strings.Contains(wrapper, `#include "crypto/internal.h"`) {
		t.Error("missing suppressed internal header include")
	}

	// Target internal headers should appear after the marker define.
	markerIdx := strings.LastIndex(wrapper, "#define OPENSSL_EXPORT "+marker)
	targetIdx := strings.Index(wrapper, `#include "ssl/internal.h"`)
	if markerIdx < 0 || targetIdx < 0 {
		t.Fatal("missing marker define or target include")
	}
	if targetIdx < markerIdx {
		t.Error("target internal header should appear after marker definition")
	}

	// Extra export macros should be handled.
	for _, m := range extraExportMacros {
		if !strings.Contains(wrapper, "#define "+m+" "+marker) {
			t.Errorf("missing marker redefinition for %s", m)
		}
	}
}

// ---------------------------------------------------------------------------
// scanExtraExportMacrosContent
// ---------------------------------------------------------------------------

func TestScanExtraExportMacrosContent(t *testing.T) {
	content := `#ifndef JENT_H
#define JENT_H
JENT_PRIVATE_STATIC unsigned int jent_read_entropy(void *buf, unsigned int len);
JENT_PRIVATE_STATIC int jent_entropy_init(void);
#endif
`
	syms := scanExtraExportMacrosContent(content)
	var names []string
	for _, s := range syms {
		names = append(names, s.name)
	}
	sort.Strings(names)

	want := []string{"jent_entropy_init", "jent_read_entropy"}
	if len(names) != len(want) {
		t.Fatalf("scanExtraExportMacrosContent returned %v, want %v", names, want)
	}
	for i := range names {
		if names[i] != want[i] {
			t.Errorf("[%d] = %q, want %q", i, names[i], want[i])
		}
	}
}

func TestScanExtraExportMacrosContent_NoMatch(t *testing.T) {
	content := "int regular_func(void);\nvoid another(int x);\n"
	syms := scanExtraExportMacrosContent(content)
	if len(syms) != 0 {
		t.Errorf("expected no symbols, got %v", syms)
	}
}

// ---------------------------------------------------------------------------
// sortEntries
// ---------------------------------------------------------------------------

func TestSortEntries(t *testing.T) {
	symbolMap := map[string]symbolEntry{
		"zebra": {name: "zebra", visibility: "PUBLIC"},
		"alpha": {name: "alpha", visibility: "PRIVATE"},
		"mid":   {name: "mid", visibility: "PUBLIC"},
	}
	entries := sortEntries(symbolMap)
	if len(entries) != 3 {
		t.Fatalf("expected 3 entries, got %d", len(entries))
	}
	if entries[0].name != "alpha" || entries[1].name != "mid" || entries[2].name != "zebra" {
		t.Errorf("entries not sorted: %v", entries)
	}
}

// ---------------------------------------------------------------------------
// formatOutput
// ---------------------------------------------------------------------------

func TestFormatOutput_NamesOnly(t *testing.T) {
	entries := []symbolEntry{
		{name: "AES_decrypt", visibility: "PUBLIC"},
		{name: "AES_encrypt", visibility: "PUBLIC"},
	}
	var buf bytes.Buffer
	if err := formatOutput(&buf, entries, false); err != nil {
		t.Fatal(err)
	}
	got := buf.String()
	want := "AES_decrypt\nAES_encrypt\n"
	if got != want {
		t.Errorf("formatOutput (names only):\ngot:  %q\nwant: %q", got, want)
	}
}

func TestFormatOutput_WithVisibility(t *testing.T) {
	entries := []symbolEntry{
		{name: "AES_encrypt", visibility: "PUBLIC"},
		{name: "bssl::func1", visibility: "PRIVATE_CXX"},
	}
	var buf bytes.Buffer
	if err := formatOutput(&buf, entries, true); err != nil {
		t.Fatal(err)
	}
	got := buf.String()
	want := "AES_encrypt PUBLIC\nbssl::func1 PRIVATE_CXX\n"
	if got != want {
		t.Errorf("formatOutput (with visibility):\ngot:  %q\nwant: %q", got, want)
	}
}

func TestFormatOutput_Empty(t *testing.T) {
	var buf bytes.Buffer
	if err := formatOutput(&buf, nil, false); err != nil {
		t.Fatal(err)
	}
	if buf.Len() != 0 {
		t.Errorf("expected empty output, got %q", buf.String())
	}
}

// ---------------------------------------------------------------------------
// mockDeps helper
// ---------------------------------------------------------------------------

// mockPreprocessor returns a deps.preprocess function that returns canned
// output for C and C++ modes.
func mockPreprocessor(cOutput, cxxOutput string) func([]string, string, map[string]struct{}, map[string]struct{}, []string, string) (string, error) {
	return func(_ []string, _ string, _, _ map[string]struct{}, _ []string, lang string) (string, error) {
		if lang == "c++" {
			return cxxOutput, nil
		}
		return cOutput, nil
	}
}

func testDeps(cOutput, cxxOutput string) deps {
	return deps{
		findHeaders: func(dir string) ([]string, error) {
			return []string{dir + "/dummy.h"}, nil
		},
		findHeadersWithExport: func(dir string) ([]string, error) {
			return nil, nil
		},
		preprocess:         mockPreprocessor(cOutput, cxxOutput),
		preprocessInternal: func(_, _, _ []string, _, _ string, _ bool, _ []string) (string, error) { return "", nil },
		loadDynSyms:        func(_ string) (map[string]struct{}, error) { return nil, nil },
		scanExtraMacros:    func(_ string) []extractedSymbol { return nil },
		stderr:             &bytes.Buffer{},
	}
}

// ---------------------------------------------------------------------------
// parseTargetSets / splitTrimmed
// ---------------------------------------------------------------------------

func TestParseTargetSets(t *testing.T) {
	sets := parseTargetSets("A,B;C")
	if len(sets) != 2 {
		t.Fatalf("expected 2 sets, got %d: %v", len(sets), sets)
	}
	if len(sets[0]) != 2 || sets[0][0] != "A" || sets[0][1] != "B" {
		t.Errorf("set[0] = %v, want [A B]", sets[0])
	}
	if len(sets[1]) != 1 || sets[1][0] != "C" {
		t.Errorf("set[1] = %v, want [C]", sets[1])
	}
}

func TestParseTargetSets_Empty(t *testing.T) {
	sets := parseTargetSets("")
	// Empty input should produce a single nil-defines run.
	if len(sets) != 1 || sets[0] != nil {
		t.Errorf("expected [[]], got %v", sets)
	}
}

func TestSplitTrimmed(t *testing.T) {
	got := splitTrimmed(" a , b , , c ", ",")
	want := []string{"a", "b", "c"}
	if len(got) != len(want) {
		t.Fatalf("splitTrimmed = %v, want %v", got, want)
	}
	for i := range got {
		if got[i] != want[i] {
			t.Errorf("[%d] = %q, want %q", i, got[i], want[i])
		}
	}
}

// ---------------------------------------------------------------------------
// run()
// ---------------------------------------------------------------------------

func TestRun_PublicSymbols(t *testing.T) {
	cOutput := marker + " int foo(void); " + marker + " void bar(int x);"
	d := testDeps(cOutput, cOutput)

	cfg := config{
		includeDir: "/fake/include",
		targetSets: [][]string{nil},
	}

	entries, err := run(cfg, d)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 2 {
		t.Fatalf("expected 2 entries, got %d: %v", len(entries), entries)
	}
	if entries[0].name != "bar" || entries[0].visibility != "PUBLIC" {
		t.Errorf("entries[0] = %+v, want bar/PUBLIC", entries[0])
	}
	if entries[1].name != "foo" || entries[1].visibility != "PUBLIC" {
		t.Errorf("entries[1] = %+v, want foo/PUBLIC", entries[1])
	}
}

func TestRun_CxxOnlySymbols(t *testing.T) {
	cOutput := marker + " int c_func(void);"
	cxxOutput := marker + " int c_func(void); namespace bssl { " + marker + " int cxx_func(void); }"

	d := testDeps(cOutput, cxxOutput)
	cfg := config{
		includeDir: "/fake/include",
		targetSets: [][]string{nil},
	}

	entries, err := run(cfg, d)
	if err != nil {
		t.Fatal(err)
	}

	entryMap := make(map[string]symbolEntry)
	for _, e := range entries {
		entryMap[e.name] = e
	}

	if e, ok := entryMap["c_func"]; !ok || e.visibility != "PUBLIC" {
		t.Errorf("c_func should be PUBLIC, got %+v", e)
	}
	if e, ok := entryMap["bssl::cxx_func"]; !ok || e.visibility != "PUBLIC_CXX" {
		t.Errorf("bssl::cxx_func should be PUBLIC_CXX, got %+v (map=%v)", e, entryMap)
	}
}

func TestRun_NoHeaders(t *testing.T) {
	d := testDeps("", "")
	d.findHeaders = func(dir string) ([]string, error) {
		return nil, nil
	}

	cfg := config{
		includeDir: "/fake/include",
		targetSets: [][]string{nil},
	}

	_, err := run(cfg, d)
	if err == nil {
		t.Fatal("expected error for no headers")
	}
	if !strings.Contains(err.Error(), "no .h files") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestRun_Validation(t *testing.T) {
	cOutput := marker + " int present(void); " + marker + " int missing(void);"
	d := testDeps(cOutput, cOutput)
	d.loadDynSyms = func(path string) (map[string]struct{}, error) {
		return map[string]struct{}{"present": {}}, nil
	}
	var stderrBuf bytes.Buffer
	d.stderr = &stderrBuf

	cfg := config{
		includeDir:    "/fake/include",
		targetSets:    [][]string{nil},
		validatePaths: []string{"/fake/lib.so"},
	}

	entries, err := run(cfg, d)
	if err != nil {
		t.Fatal(err)
	}
	// Should still return both symbols.
	if len(entries) != 2 {
		t.Fatalf("expected 2 entries, got %d", len(entries))
	}
	// Stderr should contain warning about missing symbol.
	if !strings.Contains(stderrBuf.String(), "WARNING") {
		t.Error("expected validation warning on stderr")
	}
	if !strings.Contains(stderrBuf.String(), "missing") {
		t.Error("expected 'missing' symbol in warning")
	}
}

func TestRun_ExcludedHeaders(t *testing.T) {
	// The preprocessor mock ignores headers, but we verify that
	// excluded headers flow through to the preprocess call.
	var capturedExcluded map[string]struct{}
	d := testDeps("", "")
	d.preprocess = func(_ []string, _ string, _, excluded map[string]struct{}, _ []string, _ string) (string, error) {
		capturedExcluded = excluded
		return marker + " int only_func(void);", nil
	}

	cfg := config{
		includeDir: "/fake/include",
		targetSets: [][]string{nil},
		excluded:   map[string]struct{}{"ssl.h": {}},
	}

	entries, err := run(cfg, d)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 1 || entries[0].name != "only_func" {
		t.Errorf("unexpected entries: %v", entries)
	}
	if _, ok := capturedExcluded["ssl.h"]; !ok {
		t.Error("excluded set should contain ssl.h")
	}
}

func TestRun_InternalDirs(t *testing.T) {
	cOutput := marker + " int public_func(void);"
	d := testDeps(cOutput, cOutput)

	// Mock internal directory processing.
	d.findHeadersWithExport = func(dir string) ([]string, error) {
		if strings.Contains(dir, "crypto") {
			return []string{dir + "/internal.h"}, nil
		}
		return nil, nil
	}
	d.preprocessInternal = func(_, _, _ []string, _, _ string, _ bool, _ []string) (string, error) {
		return marker + " int private_func(void);", nil
	}

	cfg := config{
		includeDir:   "/fake/include",
		targetSets:   [][]string{nil},
		internalDirs: []string{"crypto"},
		sourceRoot:   "/fake",
	}

	entries, err := run(cfg, d)
	if err != nil {
		t.Fatal(err)
	}

	entryMap := make(map[string]symbolEntry)
	for _, e := range entries {
		entryMap[e.name] = e
	}

	if e, ok := entryMap["public_func"]; !ok || e.visibility != "PUBLIC" {
		t.Errorf("public_func should be PUBLIC, got %+v", e)
	}
	if e, ok := entryMap["private_func"]; !ok || e.visibility != "PRIVATE" {
		t.Errorf("private_func should be PRIVATE, got %+v", e)
	}
}

func TestRun_InternalDirsCxx(t *testing.T) {
	cOutput := marker + " int public_func(void);"
	d := testDeps(cOutput, cOutput)

	d.findHeadersWithExport = func(dir string) ([]string, error) {
		if strings.Contains(dir, "ssl") {
			return []string{dir + "/internal.h"}, nil
		}
		return nil, nil
	}
	d.preprocessInternal = func(_, _, _ []string, _, _ string, _ bool, _ []string) (string, error) {
		return "namespace bssl { " + marker + " int ssl_internal(void); }", nil
	}

	cfg := config{
		includeDir:   "/fake/include",
		targetSets:   [][]string{nil},
		internalDirs: []string{"ssl"},
		sourceRoot:   "/fake",
	}

	entries, err := run(cfg, d)
	if err != nil {
		t.Fatal(err)
	}

	entryMap := make(map[string]symbolEntry)
	for _, e := range entries {
		entryMap[e.name] = e
	}

	if e, ok := entryMap["bssl::ssl_internal"]; !ok || e.visibility != "PRIVATE_CXX" {
		t.Errorf("bssl::ssl_internal should be PRIVATE_CXX, got %+v", e)
	}
}
