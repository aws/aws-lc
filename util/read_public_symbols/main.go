// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// read_public_symbols extracts the set of public API symbols from the AWS-LC
// public headers located in the given include directory. It uses the C
// preprocessor to fully expand all macros (including DEFINE_STACK_OF,
// DECLARE_ASN1_ITEM, etc.), then parses the expanded output to find every
// symbol declared with OPENSSL_EXPORT.
//
// Optionally, internal headers (under crypto/ and ssl/) can also be scanned
// for OPENSSL_EXPORT symbols. These are classified as PRIVATE (C linkage) or
// PRIVATE_CXX (C++ linkage) while public header symbols are PUBLIC.
//
// Optionally, the extracted symbols can be validated against one or more built
// shared libraries to catch parser errors or missing implementations. Any
// symbol found in the headers but absent from all provided libraries is
// reported as a warning.
//
// Usage:
//
//	# All public headers (for libcrypto baseline, excluding ssl.h):
//	go run ./util/read_public_symbols -include-dir include \
//	  -exclude ssl.h -out tests/ci/baselines/symbols/libcrypto-1.0.txt
//
//	# Only ssl.h (for libssl baseline):
//	go run ./util/read_public_symbols -include-dir include \
//	  -include ssl.h -out tests/ci/baselines/symbols/libssl-1.0.txt
//
//	# With internal headers and visibility output:
//	go run ./util/read_public_symbols -include-dir include \
//	  -exclude ssl.h -internal-dirs crypto -emit-visibility \
//	  -out crypto/libcrypto_symbols.txt
//
//	# With validation against both shared libraries:
//	go run ./util/read_public_symbols -include-dir include \
//	  -validate-against build/crypto/libcrypto-awslc.so,build/ssl/libssl-awslc.so \
//	  -out public_symbols.txt
package main

import (
	"bufio"
	"debug/elf"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
)

var includeDir string
var outputFile string
var ccFlag string
var validateAgainst string
var includeHeaders string
var excludeHeaders string
var targets string
var internalDirsFlag string
var suppressDirsFlag string
var emitVisibility bool
var sourceRoot string

func init() {
	flag.StringVar(&includeDir, "include-dir", "include", "Directory containing public headers (e.g. include/)")
	flag.StringVar(&outputFile, "out", "", "Output file for public symbol list (default: stdout)")
	flag.StringVar(&ccFlag, "cc", "cc", "C compiler to use for preprocessing")
	flag.StringVar(&validateAgainst, "validate-against", "", "Comma-separated paths to shared libraries to validate extracted symbols against")
	flag.StringVar(&includeHeaders, "include", "", "If set, only extract symbols from these comma-separated header basenames (e.g. ssl.h). All other headers are included first with OPENSSL_EXPORT suppressed to establish include guards, preventing transitive re-inclusion.")
	flag.StringVar(&excludeHeaders, "exclude", "", "Comma-separated header basenames to omit entirely (e.g. ssl.h)")
	flag.StringVar(&targets, "targets",
		"OPENSSL_X86_64,OPENSSL_LINUX;OPENSSL_AARCH64,OPENSSL_LINUX;OPENSSL_ARM,OPENSSL_LINUX",
		"Semicolon-separated list of OPENSSL_* define sets to run the preprocessor with. Each set is comma-separated (e.g. OPENSSL_X86_64,OPENSSL_LINUX). The preprocessor is run once per set and results are unioned to cover all platform-specific #ifdef guards.")
	flag.StringVar(&internalDirsFlag, "internal-dirs", "", "Comma-separated directories (relative to -source-root) to scan for internal headers with OPENSSL_EXPORT (e.g. crypto,ssl). Symbols found only in these headers are classified as PRIVATE or PRIVATE_CXX.")
	flag.StringVar(&suppressDirsFlag, "suppress-internal-dirs", "", "Comma-separated directories whose internal headers should be suppressed (included with OPENSSL_EXPORT empty) during internal header processing, without extracting their symbols. Use to prevent transitive includes from leaking symbols (e.g. ssl/internal.h includes crypto/internal.h — suppress crypto when extracting ssl).")
	flag.BoolVar(&emitVisibility, "emit-visibility", false, "Output 'SYMBOL VISIBILITY' instead of just 'SYMBOL'. Visibility is PUBLIC, PRIVATE, or PRIVATE_CXX.")
	flag.StringVar(&sourceRoot, "source-root", ".", "Project source root directory (for resolving internal header includes)")
}

// marker is substituted for OPENSSL_EXPORT so we can locate each exported
// declaration in the preprocessed output.
const marker = "AWSLC_PUBLIC_SYMBOL"

// extraExportMacros lists additional macros (beyond OPENSSL_EXPORT) that mark
// exported symbols in third-party code compiled into the libraries.
// These are redefined to our marker alongside OPENSSL_EXPORT.
var extraExportMacros = []string{
	"JENT_PRIVATE_STATIC", // third_party/jitterentropy
}

// identRE matches a valid C identifier.
var identRE = regexp.MustCompile(`^[A-Za-z_][A-Za-z0-9_]*$`)

// cxxInternalDirs lists directory basenames whose headers use C++ linkage.
var cxxInternalDirs = map[string]struct{}{
	"ssl": {},
}

// symbolEntry holds a symbol name and its visibility classification.
type symbolEntry struct {
	name       string
	visibility string // "PUBLIC", "PRIVATE", "PRIVATE_CXX", or "PRIVATE_CXX_CLASS"
}

// extractedSymbol holds a symbol name extracted from the preprocessed output,
// along with whether it represents a C++ class export and its namespace.
type extractedSymbol struct {
	name      string
	isClass   bool
	namespace string // e.g., "bssl" for symbols inside namespace bssl { }
}

// qualifiedName returns the namespace-qualified symbol name (e.g., "bssl::name")
// or just the bare name if there is no namespace.
func (s extractedSymbol) qualifiedName() string {
	if s.namespace != "" {
		return s.namespace + "::" + s.name
	}
	return s.name
}

// nsRange represents a character range in the preprocessed text that is inside
// a particular namespace block.
type nsRange struct {
	name       string
	start, end int
}

func makeSet(csv string) map[string]struct{} {
	s := make(map[string]struct{})
	for _, name := range strings.Split(csv, ",") {
		name = strings.TrimSpace(name)
		if name != "" {
			s[name] = struct{}{}
		}
	}
	return s
}

// config holds all parsed CLI options for the symbol extraction pipeline.
type config struct {
	includeDir     string
	targeted       map[string]struct{}
	excluded       map[string]struct{}
	targetSets     [][]string
	emitVisibility bool
	validatePaths  []string // from -validate-against, pre-split
	internalDirs   []string // directory names relative to sourceRoot
	suppressDirs   []string // directory names for suppression
	sourceRoot     string
}

// deps holds injectable dependencies. Use prodDeps() for real execution;
// override individual fields in tests.
type deps struct {
	findHeaders           func(dir string) ([]string, error)
	findHeadersWithExport func(dir string) ([]string, error)
	preprocess            func(headers []string, includeDir string, targeted, excluded map[string]struct{}, extraDefines []string, lang string) (string, error)
	preprocessInternal    func(publicHeaders, otherInternalHeaders, internalHeaders []string, includeDir, sourceRoot string, isCxx bool, extraDefines []string) (string, error)
	loadDynSyms           func(path string) (map[string]struct{}, error)
	scanExtraMacros       func(headerPath string) []extractedSymbol
	stderr                io.Writer
}

func prodDeps() deps {
	return deps{
		findHeaders:           findHeaders,
		findHeadersWithExport: findHeadersWithExport,
		preprocess:            runPreprocessor,
		preprocessInternal:    runInternalPreprocessor,
		loadDynSyms:           loadDynSyms,
		scanExtraMacros:       scanExtraExportMacros,
		stderr:                os.Stderr,
	}
}

// parseTargetSets parses the semicolon-separated target define sets.
func parseTargetSets(targets string) [][]string {
	var targetSets [][]string
	for _, target := range strings.Split(targets, ";") {
		target = strings.TrimSpace(target)
		if target == "" {
			continue
		}
		var defines []string
		for _, def := range strings.Split(target, ",") {
			def = strings.TrimSpace(def)
			if def != "" {
				defines = append(defines, def)
			}
		}
		if len(defines) > 0 {
			targetSets = append(targetSets, defines)
		}
	}
	if len(targetSets) == 0 {
		targetSets = [][]string{nil}
	}
	return targetSets
}

// splitTrimmed splits s by sep, trims whitespace, and drops empty strings.
func splitTrimmed(s, sep string) []string {
	var result []string
	for _, part := range strings.Split(s, sep) {
		part = strings.TrimSpace(part)
		if part != "" {
			result = append(result, part)
		}
	}
	return result
}

func main() {
	flag.Parse()

	cfg := config{
		includeDir:     includeDir,
		targeted:       makeSet(includeHeaders),
		excluded:       makeSet(excludeHeaders),
		targetSets:     parseTargetSets(targets),
		emitVisibility: emitVisibility,
		validatePaths:  splitTrimmed(validateAgainst, ","),
		internalDirs:   splitTrimmed(internalDirsFlag, ","),
		suppressDirs:   splitTrimmed(suppressDirsFlag, ","),
		sourceRoot:     sourceRoot,
	}

	entries, err := run(cfg, prodDeps())
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	var out io.Writer = os.Stdout
	if outputFile != "" {
		f, err := os.Create(outputFile)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error creating output file: %v\n", err)
			os.Exit(1)
		}
		defer f.Close()
		out = f
	}

	if err := formatOutput(out, entries, cfg.emitVisibility); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing output: %v\n", err)
		os.Exit(1)
	}

	if outputFile != "" {
		fmt.Fprintf(os.Stderr, "Extracted %d symbols from headers\n", len(entries))
	}
}

// run executes the core symbol extraction pipeline and returns sorted entries.
func run(cfg config, d deps) ([]symbolEntry, error) {
	headers, err := d.findHeaders(cfg.includeDir)
	if err != nil {
		return nil, fmt.Errorf("finding headers in %s: %w", cfg.includeDir, err)
	}
	if len(headers) == 0 {
		return nil, fmt.Errorf("no .h files found under %s", cfg.includeDir)
	}

	// First pass: C mode (captures all C-linkage symbols).
	publicSeen := make(map[string]struct{})
	for _, defines := range cfg.targetSets {
		preprocessed, err := d.preprocess(headers, cfg.includeDir, cfg.targeted, cfg.excluded, defines, "c")
		if err != nil {
			return nil, fmt.Errorf("preprocessor error (defines=%v): %w", defines, err)
		}
		for _, sym := range extractSymbols(preprocessed) {
			publicSeen[sym.name] = struct{}{}
		}
	}

	// Second pass: C++ mode captures symbols inside #if defined(__cplusplus)
	// blocks. Symbols found only in C++ mode are classified as PUBLIC_CXX.
	publicCxxSeen := make(map[string]extractedSymbol)
	for _, defines := range cfg.targetSets {
		preprocessed, err := d.preprocess(headers, cfg.includeDir, cfg.targeted, cfg.excluded, defines, "c++")
		if err != nil {
			return nil, fmt.Errorf("C++ preprocessor error (defines=%v): %w", defines, err)
		}
		for _, sym := range extractSymbols(preprocessed) {
			if _, inC := publicSeen[sym.name]; !inC {
				publicCxxSeen[sym.name] = sym
			}
		}
	}

	// Build symbol map from public symbols.
	symbolMap := make(map[string]symbolEntry)
	for s := range publicSeen {
		symbolMap[s] = symbolEntry{name: s, visibility: "PUBLIC"}
	}
	for _, sym := range publicCxxSeen {
		vis := "PUBLIC_CXX"
		if sym.isClass {
			vis = "PUBLIC_CXX_CLASS"
		}
		qname := sym.qualifiedName()
		symbolMap[qname] = symbolEntry{name: qname, visibility: vis}
	}

	// Validate against shared libraries if requested.
	if len(cfg.validatePaths) > 0 {
		publicSymbols := make([]string, 0, len(publicSeen))
		for s := range publicSeen {
			publicSymbols = append(publicSymbols, s)
		}
		sort.Strings(publicSymbols)
		if err := validateSymbolsWith(publicSymbols, cfg.validatePaths, d.loadDynSyms, d.stderr); err != nil {
			return nil, fmt.Errorf("validation error: %w", err)
		}
	}

	// Process internal directories if specified.
	if len(cfg.internalDirs) > 0 {
		absSourceRoot, err := filepath.Abs(cfg.sourceRoot)
		if err != nil {
			return nil, fmt.Errorf("resolving source root: %w", err)
		}
		absIncludeDir, err := filepath.Abs(cfg.includeDir)
		if err != nil {
			return nil, fmt.Errorf("resolving include dir: %w", err)
		}

		allPublicHeaders, err := d.findHeaders(absIncludeDir)
		if err != nil {
			return nil, fmt.Errorf("finding public headers: %w", err)
		}

		// Discover internal headers per directory.
		type internalDir struct {
			name       string
			isCxx      bool
			visibility string
			headers    []string
		}
		var dirs []internalDir
		for _, dir := range cfg.internalDirs {
			_, isCxx := cxxInternalDirs[dir]
			visibility := "PRIVATE"
			if isCxx {
				visibility = "PRIVATE_CXX"
			}
			dirPath := filepath.Join(absSourceRoot, dir)
			intHeaders, err := d.findHeadersWithExport(dirPath)
			if err != nil {
				return nil, fmt.Errorf("finding headers in %s: %w", dirPath, err)
			}
			if len(intHeaders) == 0 {
				fmt.Fprintf(d.stderr, "No .h files with OPENSSL_EXPORT found under %s\n", dirPath)
				continue
			}
			dirs = append(dirs, internalDir{dir, isCxx, visibility, intHeaders})
		}

		// Collect headers from suppress directories.
		var suppressHeaders []string
		for _, dir := range cfg.suppressDirs {
			dirPath := filepath.Join(absSourceRoot, dir)
			hdrs, err := d.findHeadersWithExport(dirPath)
			if err != nil {
				return nil, fmt.Errorf("finding headers in %s: %w", dirPath, err)
			}
			suppressHeaders = append(suppressHeaders, hdrs...)
		}

		// Process each internal directory with cross-suppression.
		for _, intDir := range dirs {
			var otherInternalHeaders []string
			otherInternalHeaders = append(otherInternalHeaders, suppressHeaders...)
			for _, other := range dirs {
				if other.name != intDir.name && (intDir.isCxx || !other.isCxx) {
					otherInternalHeaders = append(otherInternalHeaders, other.headers...)
				}
			}

			internalSeen := make(map[string]extractedSymbol)
			for _, defines := range cfg.targetSets {
				preprocessed, err := d.preprocessInternal(
					allPublicHeaders, otherInternalHeaders, intDir.headers,
					absIncludeDir, absSourceRoot,
					intDir.isCxx, defines,
				)
				if err != nil {
					return nil, fmt.Errorf("internal preprocessor error (dir=%s, defines=%v): %w", intDir.name, defines, err)
				}
				for _, sym := range extractSymbols(preprocessed) {
					internalSeen[sym.name] = sym
				}
			}

			// Regex fallback for third-party headers.
			for _, h := range intDir.headers {
				for _, sym := range d.scanExtraMacros(h) {
					if _, exists := internalSeen[sym.name]; !exists {
						internalSeen[sym.name] = sym
					}
				}
			}

			// Only add symbols not already in the public set.
			newCount := 0
			for _, sym := range internalSeen {
				qname := sym.qualifiedName()
				if _, isPublic := publicSeen[sym.name]; !isPublic {
					if _, exists := symbolMap[qname]; !exists {
						vis := intDir.visibility
						if sym.isClass && vis == "PRIVATE_CXX" {
							vis = "PRIVATE_CXX_CLASS"
						}
						symbolMap[qname] = symbolEntry{name: qname, visibility: vis}
						newCount++
					}
				}
			}
			fmt.Fprintf(d.stderr, "Found %d internal symbols from %s/ (%d headers, %s)\n",
				newCount, intDir.name, len(intDir.headers), intDir.visibility)
		}
	}

	return sortEntries(symbolMap), nil
}

// sortEntries collects symbol entries from a map and returns them sorted by name.
func sortEntries(symbolMap map[string]symbolEntry) []symbolEntry {
	entries := make([]symbolEntry, 0, len(symbolMap))
	for _, e := range symbolMap {
		entries = append(entries, e)
	}
	sort.Slice(entries, func(i, j int) bool {
		return entries[i].name < entries[j].name
	})
	return entries
}

// formatOutput writes sorted symbol entries to the writer. When emitVisibility
// is true, each line is "SYMBOL VISIBILITY"; otherwise just "SYMBOL".
func formatOutput(w io.Writer, entries []symbolEntry, emitVisibility bool) error {
	bw := bufio.NewWriter(w)
	for _, entry := range entries {
		if emitVisibility {
			fmt.Fprintf(bw, "%s %s\n", entry.name, entry.visibility)
		} else {
			fmt.Fprintln(bw, entry.name)
		}
	}
	return bw.Flush()
}

// validateSymbolsWith checks that every symbol in the header-extracted list is
// present as a dynamic symbol in at least one of the given ELF shared
// libraries. Missing symbols are printed to w as warnings.
func validateSymbolsWith(symbols []string, libPaths []string, loadSyms func(string) (map[string]struct{}, error), w io.Writer) error {
	dynSyms := make(map[string]struct{})
	for _, path := range libPaths {
		path = strings.TrimSpace(path)
		if path == "" {
			continue
		}
		syms, err := loadSyms(path)
		if err != nil {
			return fmt.Errorf("reading %s: %w", path, err)
		}
		for s := range syms {
			dynSyms[s] = struct{}{}
		}
	}

	var missing []string
	for _, sym := range symbols {
		if _, ok := dynSyms[sym]; !ok {
			missing = append(missing, sym)
		}
	}

	if len(missing) > 0 {
		fmt.Fprintf(w, "WARNING: %d symbol(s) from public headers not found in any provided library.\n", len(missing))
		fmt.Fprintf(w, "These may be parser errors or platform-specific symbols:\n")
		for _, sym := range missing {
			fmt.Fprintf(w, "  %s\n", sym)
		}
	} else {
		fmt.Fprintf(w, "Validation OK: all %d symbols found in provided libraries.\n", len(symbols))
	}

	return nil
}

// loadDynSyms reads the ELF dynamic symbol table of a shared library and
// returns a set of defined global symbol names.
func loadDynSyms(path string) (map[string]struct{}, error) {
	f, err := elf.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	syms, err := f.DynamicSymbols()
	if err != nil {
		return nil, err
	}

	result := make(map[string]struct{}, len(syms))
	for _, sym := range syms {
		// Only include defined symbols with global or weak binding.
		if elf.ST_BIND(sym.Info) != elf.STB_GLOBAL && elf.ST_BIND(sym.Info) != elf.STB_WEAK {
			continue
		}
		if sym.Section == elf.SHN_UNDEF {
			continue
		}
		name := sym.Name
		// Strip version suffix if present (e.g., "func@@AWS_LC_1_0" → "func")
		if idx := strings.IndexByte(name, '@'); idx >= 0 {
			name = name[:idx]
		}
		if name != "" {
			result[name] = struct{}{}
		}
	}
	return result, nil
}

// scanExtraExportMacros does a regex scan of a raw header file for function
// declarations using extraExportMacros (e.g., JENT_PRIVATE_STATIC). This is a
// fallback for third-party headers that redefine their export macro internally,
// which defeats the preprocessor marker substitution approach. The declarations
// in these headers are simple enough for direct regex extraction.
func scanExtraExportMacros(headerPath string) []extractedSymbol {
	data, err := os.ReadFile(headerPath)
	if err != nil {
		return nil
	}
	return scanExtraExportMacrosContent(string(data))
}

// scanExtraExportMacrosContent scans raw header content for function
// declarations using extraExportMacros and returns extracted symbols.
func scanExtraExportMacrosContent(content string) []extractedSymbol {
	var results []extractedSymbol
	for _, macro := range extraExportMacros {
		if !strings.Contains(content, macro) {
			continue
		}
		// Collapse whitespace and scan for "MACRO type name(" patterns.
		// We join each MACRO-prefixed declaration into a single line, then
		// reuse symbolFromDecl by substituting the macro with our marker.
		flat := strings.Join(strings.Fields(content), " ")
		for _, chunk := range strings.Split(flat, macro)[1:] {
			sym := symbolFromDecl(chunk)
			if sym.name != "" {
				results = append(results, sym)
			}
		}
	}
	return results
}

// findHeadersFS returns all .h files under the root of fsys, sorted.
// Paths are relative to the FS root using forward slashes.
func findHeadersFS(fsys fs.FS) ([]string, error) {
	var headers []string
	err := fs.WalkDir(fsys, ".", func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !d.IsDir() && strings.HasSuffix(path, ".h") {
			headers = append(headers, path)
		}
		return nil
	})
	sort.Strings(headers)
	return headers, err
}

// findHeaders returns all .h files under dir, sorted (absolute paths).
func findHeaders(dir string) ([]string, error) {
	relPaths, err := findHeadersFS(os.DirFS(dir))
	if err != nil {
		return nil, err
	}
	absPaths := make([]string, len(relPaths))
	for i, p := range relPaths {
		absPaths[i] = filepath.Join(dir, filepath.FromSlash(p))
	}
	return absPaths, nil
}

// findHeadersWithExportFS returns all .h files under the root of fsys that
// contain "OPENSSL_EXPORT" or an extra export macro, sorted. Paths are
// relative to the FS root.
func findHeadersWithExportFS(fsys fs.FS) ([]string, error) {
	all, err := findHeadersFS(fsys)
	if err != nil {
		return nil, err
	}
	var filtered []string
	for _, h := range all {
		data, err := fs.ReadFile(fsys, h)
		if err != nil {
			continue
		}
		content := string(data)
		if strings.Contains(content, "OPENSSL_EXPORT") {
			filtered = append(filtered, h)
			continue
		}
		for _, macro := range extraExportMacros {
			if strings.Contains(content, macro) {
				filtered = append(filtered, h)
				break
			}
		}
	}
	return filtered, nil
}

// findHeadersWithExport returns all .h files under dir that contain the string
// "OPENSSL_EXPORT" or an extra export macro, sorted (absolute paths).
func findHeadersWithExport(dir string) ([]string, error) {
	relPaths, err := findHeadersWithExportFS(os.DirFS(dir))
	if err != nil {
		return nil, err
	}
	absPaths := make([]string, len(relPaths))
	for i, p := range relPaths {
		absPaths[i] = filepath.Join(dir, filepath.FromSlash(p))
	}
	return absPaths, nil
}

// buildPublicWrapper builds the C preprocessor wrapper source for public headers.
// headers are relative include paths (e.g., "openssl/ssl.h") using forward slashes.
//
// targeted: if non-empty, only extract symbols from these header basenames.
//
//	All other headers are included first with OPENSSL_EXPORT suppressed to
//	set include guards. The targeted headers are then included with the
//	marker active.
//
// excluded: headers to omit entirely from all passes.
func buildPublicWrapper(headers []string, targeted, excluded map[string]struct{}) string {
	var sb strings.Builder

	include := func(h string) {
		sb.WriteString("#include <" + h + ">\n")
	}

	if len(targeted) > 0 {
		// Two-pass approach:
		// Pass 1 — include everything (except targeted and excluded) with OPENSSL_EXPORT
		// suppressed to set include guards.
		// Pass 2 — redefine as marker and include only the targeted headers.
		// Their transitive #includes are already guarded so won't re-process.
		sb.WriteString("#include <openssl/base.h>\n")
		sb.WriteString("#undef OPENSSL_EXPORT\n")
		sb.WriteString("#define OPENSSL_EXPORT\n")
		for _, h := range headers {
			base := filepath.Base(h)
			_, isTargeted := targeted[base]
			_, isExcluded := excluded[base]
			if !isTargeted && !isExcluded {
				include(h)
			}
		}
		sb.WriteString("#undef OPENSSL_EXPORT\n")
		sb.WriteString("#define OPENSSL_EXPORT " + marker + "\n")
		for _, h := range headers {
			if _, ok := targeted[filepath.Base(h)]; ok {
				include(h)
			}
		}
	} else {
		// Default: mark all non-excluded headers.
		sb.WriteString("#include <openssl/base.h>\n")
		sb.WriteString("#undef OPENSSL_EXPORT\n")
		sb.WriteString("#define OPENSSL_EXPORT " + marker + "\n")
		for _, h := range headers {
			if _, ok := excluded[filepath.Base(h)]; !ok {
				include(h)
			}
		}
	}

	return sb.String()
}

// runPreprocessor builds a wrapper C file that includes public headers with
// OPENSSL_EXPORT replaced by our marker, runs the C preprocessor, and returns
// the output as a single flat string with all whitespace normalized.
//
// A wrapper is used (rather than a simple -D flag) because base.h redefines
// OPENSSL_EXPORT internally. The wrapper includes base.h first, then overrides
// OPENSSL_EXPORT as needed.
func runPreprocessor(headers []string, includeDir string, targeted, excluded map[string]struct{}, extraDefines []string, lang string) (string, error) {
	// Convert absolute paths to include-relative paths for the wrapper.
	relHeaders := make([]string, 0, len(headers))
	for _, h := range headers {
		rel, err := filepath.Rel(includeDir, h)
		if err != nil {
			continue
		}
		relHeaders = append(relHeaders, filepath.ToSlash(rel))
	}

	wrapper := buildPublicWrapper(relHeaders, targeted, excluded)
	return runCC(wrapper, []string{includeDir}, extraDefines, lang)
}

// buildInternalWrapper builds a C preprocessor wrapper that first includes all
// public headers with OPENSSL_EXPORT suppressed (to set include guards and
// prevent re-extraction), then includes internal headers with OPENSSL_EXPORT
// replaced by the marker.
//
// publicHeaders are include-relative paths (e.g., "openssl/base.h").
// otherInternalHeaders and internalHeaders are source-root-relative paths.
func buildInternalWrapper(publicHeaders, otherInternalHeaders, internalHeaders []string) string {
	var sb strings.Builder

	// Pass 1: include base.h and suppress OPENSSL_EXPORT, then include all
	// public headers AND other internal directory headers to set their include
	// guards. This prevents public symbols from being re-extracted and stops
	// transitive internal includes from leaking symbols between libraries
	// (e.g., ssl/internal.h includes crypto/internal.h).
	sb.WriteString("#include <openssl/base.h>\n")
	sb.WriteString("#undef OPENSSL_EXPORT\n")
	sb.WriteString("#define OPENSSL_EXPORT\n")
	for _, m := range extraExportMacros {
		sb.WriteString("#undef " + m + "\n")
		sb.WriteString("#define " + m + "\n")
	}

	for _, h := range publicHeaders {
		sb.WriteString("#include <" + h + ">\n")
	}
	for _, h := range otherInternalHeaders {
		sb.WriteString("#include \"" + h + "\"\n")
	}

	// Pass 2: enable marker and include target internal headers.
	sb.WriteString("#undef OPENSSL_EXPORT\n")
	sb.WriteString("#define OPENSSL_EXPORT " + marker + "\n")
	for _, m := range extraExportMacros {
		sb.WriteString("#undef " + m + "\n")
		sb.WriteString("#define " + m + " " + marker + "\n")
	}

	for _, h := range internalHeaders {
		sb.WriteString("#include \"" + h + "\"\n")
	}

	return sb.String()
}

// runInternalPreprocessor builds a wrapper and runs the preprocessor for
// internal header scanning.
func runInternalPreprocessor(publicHeaders, otherInternalHeaders, internalHeaders []string, includeDir, sourceRoot string, isCxx bool, extraDefines []string) (string, error) {
	// Convert absolute paths to relative paths for the wrapper.
	relPublicHeaders := make([]string, 0, len(publicHeaders))
	for _, h := range publicHeaders {
		rel, err := filepath.Rel(includeDir, h)
		if err != nil {
			continue
		}
		relPublicHeaders = append(relPublicHeaders, filepath.ToSlash(rel))
	}

	relOtherHeaders := make([]string, 0, len(otherInternalHeaders))
	for _, h := range otherInternalHeaders {
		rel, err := filepath.Rel(sourceRoot, h)
		if err != nil {
			continue
		}
		relOtherHeaders = append(relOtherHeaders, filepath.ToSlash(rel))
	}

	relInternalHeaders := make([]string, 0, len(internalHeaders))
	for _, h := range internalHeaders {
		rel, err := filepath.Rel(sourceRoot, h)
		if err != nil {
			continue
		}
		relInternalHeaders = append(relInternalHeaders, filepath.ToSlash(rel))
	}

	wrapper := buildInternalWrapper(relPublicHeaders, relOtherHeaders, relInternalHeaders)

	lang := "c"
	if isCxx {
		lang = "c++"
	}

	includeDirs := []string{sourceRoot, includeDir}
	for _, d := range uniqueDirs(append(internalHeaders, otherInternalHeaders...)) {
		includeDirs = append(includeDirs, d)
	}

	allDefines := make([]string, len(extraDefines), len(extraDefines)+1)
	copy(allDefines, extraDefines)
	allDefines = append(allDefines, "BORINGSSL_IMPLEMENTATION")

	return runCC(wrapper, includeDirs, allDefines, lang)
}

// runCC executes the C preprocessor on a wrapper source string and returns the
// output as a single flat string with all whitespace normalized.
func runCC(wrapper string, includeDirs []string, extraDefines []string, lang string) (string, error) {
	args := []string{"-E", "-P"}
	for _, dir := range includeDirs {
		args = append(args, "-I", dir)
	}
	for _, def := range extraDefines {
		args = append(args, "-D"+def)
	}
	args = append(args, "-x", lang, "-")

	cmd := exec.Command(ccFlag, args...)
	cmd.Stdin = strings.NewReader(wrapper)

	output, err := cmd.Output()
	if err != nil {
		if ee, ok := err.(*exec.ExitError); ok {
			return "", fmt.Errorf("%w\n%s", err, ee.Stderr)
		}
		return "", err
	}

	return strings.Join(strings.Fields(string(output)), " "), nil
}

// uniqueDirs returns a sorted list of unique directory paths from the given
// file list.
func uniqueDirs(files []string) []string {
	dirs := make(map[string]struct{})
	for _, f := range files {
		dirs[filepath.Dir(f)] = struct{}{}
	}
	result := make([]string, 0, len(dirs))
	for d := range dirs {
		result = append(result, d)
	}
	sort.Strings(result)
	return result
}

// buildNamespaceRanges scans the flattened preprocessed text for all
// "namespace IDENT {" blocks and returns their character ranges with names.
// Nested namespaces produce joined names (e.g., "outer::inner").
func buildNamespaceRanges(text string) []nsRange {
	var ranges []nsRange
	type frame struct {
		name  string
		depth int
	}
	var stack []frame
	braceDepth := 0

	i := 0
	for i < len(text) {
		if i+10 < len(text) && text[i:i+10] == "namespace " {
			rest := text[i+10:]
			braceIdx := strings.IndexByte(rest, '{')
			if braceIdx >= 0 && braceIdx < 100 {
				name := strings.TrimSpace(rest[:braceIdx])
				if identRE.MatchString(name) {
					stack = append(stack, frame{name: name, depth: braceDepth})
					braceDepth++
					var parts []string
					for _, f := range stack {
						parts = append(parts, f.name)
					}
					fullName := strings.Join(parts, "::")
					ranges = append(ranges, nsRange{
						name:  fullName,
						start: i + 10 + braceIdx + 1,
					})
					i += 10 + braceIdx + 1
					continue
				}
			}
		}

		if text[i] == '{' {
			braceDepth++
		} else if text[i] == '}' {
			braceDepth--
			if len(stack) > 0 && braceDepth == stack[len(stack)-1].depth {
				for j := len(ranges) - 1; j >= 0; j-- {
					if ranges[j].end == 0 {
						ranges[j].end = i
						break
					}
				}
				stack = stack[:len(stack)-1]
			}
		}
		i++
	}
	return ranges
}

// namespaceAt returns the namespace enclosing the given character position,
// or "" if the position is in the global namespace.
func namespaceAt(pos int, ranges []nsRange) string {
	best := ""
	for _, r := range ranges {
		if pos >= r.start && pos < r.end {
			if len(r.name) > len(best) {
				best = r.name
			}
		}
	}
	return best
}

// extractSymbols parses the flat preprocessed text and returns a deduplicated
// list of symbols declared with OPENSSL_EXPORT, with namespace context.
func extractSymbols(text string) []extractedSymbol {
	nsRanges := buildNamespaceRanges(text)

	seen := make(map[string]extractedSymbol)
	parts := strings.Split(text, marker)

	pos := len(parts[0])
	for i := 1; i < len(parts); i++ {
		sym := symbolFromDecl(parts[i])
		if sym.name != "" {
			sym.namespace = namespaceAt(pos, nsRanges)
			seen[sym.name] = sym
		}
		pos += len(marker) + len(parts[i])
	}

	for _, name := range findClassesWithExportedMembers(text) {
		if _, exists := seen[name]; !exists {
			ns := ""
			classIdx := strings.Index(text, "class "+name+" ")
			if classIdx < 0 {
				classIdx = strings.Index(text, "class "+name+"{")
			}
			if classIdx >= 0 {
				ns = namespaceAt(classIdx, nsRanges)
			}
			seen[name] = extractedSymbol{name: name, isClass: true, namespace: ns}
		}
	}

	symbols := make([]extractedSymbol, 0, len(seen))
	for _, s := range seen {
		symbols = append(symbols, s)
	}
	return symbols
}

// findClassesWithExportedMembers scans the flattened preprocessed text for
// class definitions whose body contains our OPENSSL_EXPORT marker.
func findClassesWithExportedMembers(text string) []string {
	var classes []string
	search := text
	for {
		idx := strings.Index(search, "class ")
		if idx < 0 {
			break
		}
		if idx >= 5 && strings.TrimRight(search[idx-5:idx], " ") == "enum" {
			search = search[idx+6:]
			continue
		}
		after := search[idx+6:]
		fields := strings.Fields(after)
		if len(fields) == 0 {
			break
		}
		name := fields[0]
		if !identRE.MatchString(name) {
			search = after
			continue
		}
		braceIdx := strings.IndexByte(after, '{')
		if braceIdx < 0 {
			break
		}
		depth := 1
		pos := braceIdx + 1
		for pos < len(after) && depth > 0 {
			if after[pos] == '{' {
				depth++
			} else if after[pos] == '}' {
				depth--
			}
			pos++
		}
		if depth != 0 {
			break
		}
		classBody := after[braceIdx+1 : pos-1]
		if strings.Contains(classBody, marker) {
			classes = append(classes, name)
		}
		search = after[pos:]
	}
	return classes
}

// stripAttributes removes all __attribute__((...)) sequences from s.
func stripAttributes(s string) string {
	const attr = "__attribute__"
	for {
		idx := strings.Index(s, attr)
		if idx < 0 {
			break
		}
		i := idx + len(attr)
		for i < len(s) && (s[i] == ' ' || s[i] == '\t') {
			i++
		}
		if i >= len(s) || s[i] != '(' {
			break
		}
		depth, end := 0, i
		for end < len(s) {
			if s[end] == '(' {
				depth++
			} else if s[end] == ')' {
				depth--
				if depth == 0 {
					break
				}
			}
			end++
		}
		s = s[:idx] + s[end+1:]
	}
	return s
}

// symbolFromDecl extracts the exported symbol name from the declaration text
// immediately following an OPENSSL_EXPORT marker.
func symbolFromDecl(decl string) extractedSymbol {
	semi := strings.IndexByte(decl, ';')
	if semi < 0 {
		return extractedSymbol{}
	}
	decl = decl[:semi]

	trimmed := strings.TrimSpace(decl)

	if strings.HasPrefix(trimmed, "typedef") {
		return extractedSymbol{}
	}

	if strings.ContainsRune(decl, '{') {
		brace := strings.IndexByte(decl, '{')
		beforeBrace := strings.TrimSpace(decl[:brace])
		fields := strings.Fields(beforeBrace)
		if len(fields) > 0 {
			candidate := fields[0]
			if identRE.MatchString(candidate) {
				return extractedSymbol{name: candidate, isClass: true}
			}
		}
		return extractedSymbol{}
	}

	if strings.HasPrefix(trimmed, "static") {
		return extractedSymbol{}
	}

	decl = stripAttributes(decl)

	openParen := strings.IndexByte(decl, '(')

	var candidate string
	if openParen >= 0 {
		afterParen := openParen + 1
		for afterParen < len(decl) && decl[afterParen] == ' ' {
			afterParen++
		}
		if afterParen < len(decl) && decl[afterParen] == '*' {
			inner := decl[afterParen+1:]
			if nextParen := strings.IndexByte(inner, '('); nextParen >= 0 {
				candidate = lastIdent(inner[:nextParen])
			}
		} else {
			candidate = lastIdent(decl[:openParen])
		}
	} else {
		candidate = lastIdent(decl)
	}

	if !identRE.MatchString(candidate) {
		return extractedSymbol{}
	}
	return extractedSymbol{name: candidate}
}

// lastIdent returns the last token from s that is a valid C identifier,
// stripping any leading '*' pointer markers.
func lastIdent(s string) string {
	fields := strings.Fields(s)
	for i := len(fields) - 1; i >= 0; i-- {
		tok := strings.TrimLeft(fields[i], "*")
		if identRE.MatchString(tok) {
			return tok
		}
	}
	return ""
}
