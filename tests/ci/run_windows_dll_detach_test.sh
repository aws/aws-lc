#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Regression test for https://github.com/aws/aws-lc/issues/3540: a static
# libcrypto embedded in a DLL runs its randomness shutdown handler on
# |DLL_PROCESS_DETACH|, where reaching |CRYPTO_sysrand| faults. Builds that
# configuration and exits; a non-zero status means the teardown faulted.
#
# Usage: run_windows_dll_detach_test.sh <build-dir> [c-compiler]

set -eu

BUILD_DIR="${1:-}"
CC_BIN="${2:-clang}"

if [ -z "${BUILD_DIR}" ]; then
    echo "Usage: $(basename "$0") <build-dir> [c-compiler]" >&2
    exit 1
fi

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SRC_ROOT="$( cd -- "${SCRIPT_DIR}/../.." &> /dev/null && pwd )"

# MSYS2 and Git Bash mangle POSIX paths passed to native programs. `cygpath -m`
# gives forward-slash Windows paths, which both Clang drivers accept.
to_native() {
    if command -v cygpath > /dev/null 2>&1; then
        cygpath -m "$1"
    else
        printf '%s' "$1"
    fi
}

# libcrypto.a under a MinGW ABI, crypto.lib under an MSVC one.
CRYPTO_LIB=""
for candidate in "${BUILD_DIR}/crypto/libcrypto.a" "${BUILD_DIR}/crypto/crypto.lib"; do
    if [ -f "${candidate}" ]; then
        CRYPTO_LIB="${candidate}"
        break
    fi
done

if [ -z "${CRYPTO_LIB}" ]; then
    echo "No static libcrypto in ${BUILD_DIR}/crypto. This test needs a static" >&2
    echo "build (BUILD_SHARED_LIBS=OFF); a shared build is already covered by" >&2
    echo "the existing guard." >&2
    exit 1
fi

SCRATCH="$(mktemp -d)"
trap 'rm -rf "${SCRATCH}"' EXIT

cat > "${SCRATCH}/probe_dll.c" <<'EOF'
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// A third-party DLL embedding a static libcrypto.

#include <openssl/rand.h>

__declspec(dllexport) int probe_init(void) {
  unsigned char buf[32];
  // Initializes the tree-DRBG and registers the thread-local state that the
  // shutdown handler walks.
  return RAND_bytes(buf, sizeof(buf));
}
EOF

cat > "${SCRATCH}/probe_main.c" <<'EOF'
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// The application loading that DLL. Must not link libcrypto itself: a second
// copy in the image registers its own shutdown handler and changes the teardown
// under test.

#include <windows.h>
#include <stdio.h>

typedef int (*probe_init_t)(void);

int main(void) {
  // A fault must fail the runner, not hang it on a WER dialog.
  SetErrorMode(SEM_FAILCRITICALERRORS | SEM_NOGPFAULTERRORBOX);

  HMODULE dll = LoadLibraryA("./probe.dll");
  if (dll == NULL) {
    fprintf(stderr, "LoadLibraryA(probe.dll) failed: %lu\n", GetLastError());
    return 1;
  }

  probe_init_t probe_init = (probe_init_t)(void (*)(void))GetProcAddress(dll, "probe_init");
  if (probe_init == NULL) {
    fprintf(stderr, "GetProcAddress(probe_init) failed: %lu\n", GetLastError());
    return 1;
  }

  if (probe_init() != 1) {
    fprintf(stderr, "probe_init failed\n");
    return 1;
  }

  // libcrypto holds the only reference to bcryptprimitives.dll, which it
  // |LoadLibraryW|'d on demand. Drop it so the module is unmapped while
  // probe.dll and its cached |ProcessPrng| pointer stay alive. Otherwise the
  // test depends on the loader unmapping bcryptprimitives.dll before probe.dll
  // detaches. This what was reported in
  // but ordering is not stable.
  HMODULE bcryptprimitives = GetModuleHandleW(L"bcryptprimitives.dll");
  if (bcryptprimitives != NULL) {
    FreeLibrary(bcryptprimitives);
  } else {
    fprintf(stderr, "note: bcryptprimitives.dll not loaded; this build may not "
                    "use the ProcessPrng path\n");
  }

  // Returning runs probe.dll's |DLL_PROCESS_DETACH|, and libcrypto's shutdown
  // handler with it.
  return 0;
}
EOF

PROBE_DLL="$(to_native "${SCRATCH}")/probe.dll"
PROBE_EXE="$(to_native "${SCRATCH}")/probe_main.exe"

# Clang maps `-lfoo` to foo.lib for MSVC targets, so one spelling covers both.
"${CC_BIN}" -shared -o "${PROBE_DLL}" \
    "$(to_native "${SCRATCH}/probe_dll.c")" \
    -I "$(to_native "${SRC_ROOT}/include")" \
    "$(to_native "${CRYPTO_LIB}")" \
    -lws2_32 -lbcrypt -ladvapi32

"${CC_BIN}" -o "${PROBE_EXE}" "$(to_native "${SCRATCH}/probe_main.c")"

echo "Running static-libcrypto-in-a-DLL shutdown probe"
set +e
( cd "${SCRATCH}" && ./probe_main.exe )
PROBE_STATUS=$?
set -e

if [ "${PROBE_STATUS}" -ne 0 ]; then
    echo "FAIL: probe exited ${PROBE_STATUS}. A static libcrypto embedded in a" >&2
    echo "DLL faulted or errored during process teardown. See" >&2
    echo "https://github.com/aws/aws-lc/issues/3540." >&2
    exit 1
fi

echo "PASS"
