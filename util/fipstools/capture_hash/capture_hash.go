// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// capture_hash runs another executable that has been linked with libcrypto. It
// expects the libcrypto to run the power-on self-tests and fail due to a
// fingerprint mismatch. capture_hash parses the output to extract the correct
// fingerprint value.
//
// The -patch-dll flag (required for the Windows FIPS build) specifies a DLL to
// binary-patch: the tool reads the DLL, finds the placeholder hash value,
// replaces it with the captured hash, and writes the patched DLL back. This
// single-DLL approach avoids building two separate DLLs whose linker output
// may differ — e.g. mandatory ASLR on ARM64 causes ADRP immediate differences,
// and lld-link (clang-cl) is not guaranteed to produce byte-identical output
// across two independent link operations.
//
// Without -patch-dll, the tool writes a C source file to stdout containing the
// correct hash. This mode is retained for debugging but is no longer used by
// the build system.

package main

import (
	"bytes"
	"encoding/hex"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/aws/aws-lc/util/fipstools/fipscommon"
)

const expectedFailureMsg = "FIPS integrity test failed."

// This must match what is in crypto/fipsmodule/fips_shared_support.c
const expectedHashLine = "Expected:   ae2cea2abda6f3ec977f9bf6949afc836827cba0a09f6b6fde52cde2cdff3180"
const calculatedPrefix = "Calculated: "
const hashHexLen = 64

func main() {
	executable := flag.String("in-executable", "", "Path to the executable file")
	patchDll := flag.String("patch-dll", "", "Path to a DLL to binary-patch with the captured hash (single-DLL mode)")
	flag.Parse()

	if *executable == "" {
		fmt.Fprintf(os.Stderr, "capture_hash: -in-executable is required\n")
		os.Exit(1)
	}

	// When -patch-dll is specified, check whether the DLL still contains the
	// placeholder hash. If it has already been patched (e.g. by a previous
	// build invocation in the same output directory), there is nothing to do.
	// Running the executable against an already-patched DLL would cause the
	// FIPS self-test to pass, and capture_hash would fail because it expects
	// the self-test to report a mismatch.
	if *patchDll != "" {
		dllBytes, err := os.ReadFile(*patchDll)
		if err != nil {
			fmt.Fprintf(os.Stderr, "capture_hash: failed to read DLL: %v\n", err)
			os.Exit(1)
		}
		if bytes.Index(dllBytes, fipscommon.UninitHashValue[:]) < 0 {
			fmt.Fprintf(os.Stderr, "capture_hash: %s already patched (placeholder not found), skipping\n", *patchDll)
			return
		}
	}

	cmd := exec.Command(*executable)

	// When -patch-dll is specified, the executable links against a DLL that
	// may reside in a different directory. Under Wine binfmt (cross-compiling
	// from Linux), Wine needs WINEPATH to locate the DLL. We replace any
	// existing WINEPATH rather than appending, because a stale WINEPATH
	// (e.g. from a previous build) could cause Wine to load an already-
	// patched copy of the DLL instead of the one we need to patch.
	if *patchDll != "" {
		dllDir := filepath.Dir(*patchDll)
		env := os.Environ()
		found := false
		for i, e := range env {
			if strings.HasPrefix(e, "WINEPATH=") {
				env[i] = "WINEPATH=" + dllDir
				found = true
				break
			}
		}
		if !found {
			env = append(env, "WINEPATH="+dllDir)
		}
		cmd.Env = env
	}

	out, err := cmd.CombinedOutput()
	if err == nil {
		fmt.Fprintf(os.Stderr, "%s", out)
		fmt.Fprintf(os.Stderr, "capture_hash: executable did not fail as expected\n")
		os.Exit(1)
	}

	// Search for the expected lines by content rather than by strict line
	// numbers. This makes the parser tolerant of additional diagnostic output
	// that may be printed before or between the FIPS integrity test messages.
	lines := strings.Split(string(out), "\r\n")

	foundFailureMsg := false
	foundExpectedHash := false
	hashHex := ""

	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == expectedFailureMsg {
			foundFailureMsg = true
		}
		if line == expectedHashLine {
			foundExpectedHash = true
		}
		if strings.HasPrefix(line, calculatedPrefix) {
			parts := strings.Fields(line)
			if len(parts) >= 2 {
				hashHex = parts[1]
			}
		}
	}

	if !foundFailureMsg {
		fmt.Fprintf(os.Stderr, "%s", out)
		fmt.Fprintf(os.Stderr, "capture_hash: did not find %q in output\n", expectedFailureMsg)
		os.Exit(1)
	}

	if !foundExpectedHash {
		fmt.Fprintf(os.Stderr, "%s", out)
		fmt.Fprintf(os.Stderr, "capture_hash: did not find %q in output\n", expectedHashLine)
		os.Exit(1)
	}

	if hashHex == "" {
		fmt.Fprintf(os.Stderr, "%s", out)
		fmt.Fprintf(os.Stderr, "capture_hash: did not find %q line in output\n", calculatedPrefix)
		os.Exit(1)
	}

	if len(hashHex) != hashHexLen {
		fmt.Fprintf(os.Stderr, "%s", out)
		fmt.Fprintf(os.Stderr, "capture_hash: hash %q is %d chars, expected %d\n", hashHex, len(hashHex), hashHexLen)
		os.Exit(1)
	}

	fmt.Fprintf(os.Stderr, "capture_hash: captured hash = %s\n", hashHex)

	if *patchDll != "" {
		// Single-DLL mode: binary-patch the placeholder hash in the DLL.
		hashBytes, err := hex.DecodeString(hashHex)
		if err != nil {
			fmt.Fprintf(os.Stderr, "capture_hash: failed to decode hash hex: %v\n", err)
			os.Exit(1)
		}

		fi, err := os.Stat(*patchDll)
		if err != nil {
			fmt.Fprintf(os.Stderr, "capture_hash: %v\n", err)
			os.Exit(1)
		}
		perm := fi.Mode() & 0777

		dllBytes, err := os.ReadFile(*patchDll)
		if err != nil {
			fmt.Fprintf(os.Stderr, "capture_hash: failed to read DLL: %v\n", err)
			os.Exit(1)
		}

		offset := bytes.Index(dllBytes, fipscommon.UninitHashValue[:])
		if offset < 0 {
			fmt.Fprintf(os.Stderr, "capture_hash: placeholder hash not found in %s\n", *patchDll)
			os.Exit(1)
		}

		// Verify uniqueness — the placeholder must appear exactly once.
		if bytes.Index(dllBytes[offset+len(fipscommon.UninitHashValue):], fipscommon.UninitHashValue[:]) >= 0 {
			fmt.Fprintf(os.Stderr, "capture_hash: found multiple occurrences of placeholder hash in %s\n", *patchDll)
			os.Exit(1)
		}

		copy(dllBytes[offset:], hashBytes)

		if err := os.WriteFile(*patchDll, dllBytes, perm); err != nil {
			fmt.Fprintf(os.Stderr, "capture_hash: failed to write patched DLL: %v\n", err)
			os.Exit(1)
		}

		fmt.Fprintf(os.Stderr, "capture_hash: patched %s at offset 0x%x\n", *patchDll, offset)
	} else {
		// Stdout mode (not used by the build system): generate a C source file.
		fmt.Printf(`// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
// This file is generated by: 'go run util/fipstools/capture_hash/capture_hash.go -in-executable %s'
#include <stdint.h>
const uint8_t BORINGSSL_bcm_text_hash[32] = {
`, *executable)
		for i := 0; i < len(hashHex); i += 2 {
			fmt.Printf("0x%s, ", hashHex[i:i+2])
		}
		fmt.Printf(`
};
`)
	}
}
