#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

# Cross-compiles a FIPS *shared* (DLL) build of AWS-LC for Windows using the
# mingw-w64 toolchain, then exercises the FIPS integrity self-test under Wine.
# This is the cross-compilation analogue of the native clang-cl FIPS shared
# coverage, and validates the PE/COFF hash-injection path in inject_hash.go as
# well as the MinGW-specific CMake plumbing (bcm marker objects, statically
# linked winpthread).

TARGET_CPU="${1}"
TARGET_PLATFORM="${2}"
BUILD_OPTIONS=("${@:3:5}")
# MinGW FIPS shared requires a reasonably recent binutils (>= ~2.41, as shipped
# by Ubuntu 24.04 / mingw-w64 gcc-13). Older linkers (e.g. binutils 2.38 on
# Ubuntu 22.04) drop the dllexport directives (.drectve) for the FIPS module's
# symbols during the bcm.o partial link, leaving libcrypto.dll under-exported.
# This is a new build target with no existing consumers, so we set the floor
# here rather than fall back to -Wl,--export-all-symbols.
GCC_VERSION="13"
THREAD_MODEL="posix"

if [ "${#BUILD_OPTIONS[@]}" -lt 1 ]; then
    echo "Must pass build parameters"
    exit 1
fi

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
SCRIPT_DIR="$(readlink -f "${SCRIPT_DIR}")"

source "${SCRIPT_DIR}/common_posix_setup.sh"
source "${SCRIPT_DIR}/gtest_util.sh"

# Assumes script is executed from the root of aws-lc directory
SCRATCH_FOLDER="${SYS_ROOT}/SCRATCH_${TARGET_CPU}_FIPS"

if [ -e "${SCRATCH_FOLDER}" ]; then
    # Some directories in the archive lack write permission, preventing deletion of files
    chmod +w -R "${SCRATCH_FOLDER}"
    rm -rf "${SCRATCH_FOLDER:?}"
fi
mkdir -p "${SCRATCH_FOLDER}"

pushd "${SCRATCH_FOLDER}"

# Note: unlike the static cross-mingw build, we do NOT set
# CMAKE_EXE_LINKER_FLAGS=--static here. A FIPS shared build links the test
# executables against the crypto DLL, so the executables (and the DLL) must be
# able to locate their runtime dependencies at load time. winpthread is pulled
# statically into the crypto DLL itself (see the MINGW AND FIPS branch in the
# top-level CMakeLists.txt); the remaining mingw runtime DLLs are made
# discoverable through WINEPATH below.
cat <<EOF > ${TARGET_CPU}-${TARGET_PLATFORM}.cmake
# Specify the target system
set(CMAKE_SYSTEM_NAME Windows)
set(CMAKE_SYSTEM_PROCESSOR ${TARGET_CPU})

# Specify the cross-compiler
set(CMAKE_C_COMPILER /usr/bin/${TARGET_CPU}-${TARGET_PLATFORM}-gcc-${THREAD_MODEL})
set(CMAKE_CXX_COMPILER /usr/bin/${TARGET_CPU}-${TARGET_PLATFORM}-g++-${THREAD_MODEL})

# Specify the sysroot for the target system
set(CMAKE_SYSROOT /usr/lib/gcc/${TARGET_CPU}-${TARGET_PLATFORM}/${GCC_VERSION}-${THREAD_MODEL}/)
set(CMAKE_SYSTEM_INCLUDE_PATH /usr/lib/gcc/${TARGET_CPU}-${TARGET_PLATFORM}/${GCC_VERSION}-${THREAD_MODEL}/include)

set(CMAKE_FIND_ROOT_PATH /usr/lib/gcc/${TARGET_CPU}-${TARGET_PLATFORM}/${GCC_VERSION}-${THREAD_MODEL}/)
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)

set(CMAKE_GENERATOR Ninja)
EOF

cat ${TARGET_CPU}-${TARGET_PLATFORM}.cmake

function wine_z_path {
  local unix_path="${1%/}"
  printf 'Z:%s' "${unix_path//\//\\}"
}

# Make the cross-compiled crypto/ssl DLLs, generated test DLLs, and the mingw
# runtime DLLs (libstdc++, libgcc_s, libwinpthread) discoverable by Wine when it
# loads the test executables. WINEPATH is a semicolon-separated list of
# Windows-style paths.
export WINEPATH="$(wine_z_path "${BUILD_ROOT}")"
WINEPATH+=";$(wine_z_path "${BUILD_ROOT}/crypto")"
WINEPATH+=";$(wine_z_path "${BUILD_ROOT}/ssl")"
WINEPATH+=";$(wine_z_path "/usr/lib/gcc/${TARGET_CPU}-${TARGET_PLATFORM}/${GCC_VERSION}-${THREAD_MODEL}")"
WINEPATH+=";$(wine_z_path "/usr/${TARGET_CPU}-${TARGET_PLATFORM}/lib")"
# Keep Wine quiet and non-interactive in CI.
export WINEDEBUG="-all"

echo "Testing AWS-LC FIPS shared library for ${TARGET_CPU}."

for BO in "${BUILD_OPTIONS[@]}"; do
  run_build \
    -DCMAKE_TOOLCHAIN_FILE="${SCRATCH_FOLDER}/${TARGET_CPU}-${TARGET_PLATFORM}.cmake" \
    -DFIPS=1 \
    -DBUILD_SHARED_LIBS=1 \
    ${BO}

  # The module's FIPS status can be verified by 'tool/bssl isfips'. This must
  # report FIPS mode is enabled for a successful shared FIPS build.
  module_status=$(${BUILD_ROOT}/tool/bssl.exe isfips)
  [[ "${module_status}" == "1" ]] || { echo >&2 "FIPS Mode validation failed."; exit 1; }

  # Positive test: test_fips exercises the power-on self-test, including the
  # runtime integrity check that recomputes the module hash. This validates that
  # inject_hash.go wrote a correct hash into the PE/COFF DLL.
  ${BUILD_ROOT}/util/fipstools/test_fips.exe

  # Negative test: corrupt the FIPS module inside the crypto DLL and confirm the
  # runtime integrity check detects it (test_fips must now FAIL). This proves the
  # integrity check actually runs and has teeth on the MinGW PE/COFF DLL, rather
  # than merely being self-consistent with inject_hash.go (both measure the same
  # window, so a passing positive test alone cannot distinguish a working check
  # from a no-op one). break-hash.go -mingw locates the module via the PE/COFF
  # symbol table (no .map file) and flips a byte inside
  # [BORINGSSL_bcm_text_start, BORINGSSL_bcm_text_end].
  crypto_dll="${BUILD_ROOT}/crypto/libcrypto.dll"
  if [ ! -f "${crypto_dll}" ]; then
    echo >&2 "Expected crypto DLL not found at ${crypto_dll}"; exit 1
  fi
  cp "${crypto_dll}" "${crypto_dll}.bak"
  (cd "${SRC_ROOT}" && go run util/fipstools/break-hash.go -mingw "${crypto_dll}" "${crypto_dll}.corrupted")
  cp "${crypto_dll}.corrupted" "${crypto_dll}"
  # test_fips is expected to fail here; disable errexit so we can capture its
  # exit code instead of aborting the script.
  set +e
  ${BUILD_ROOT}/util/fipstools/test_fips.exe
  fips_negative_rc=$?
  set -e
  # Restore the pristine DLL before asserting, so a failure does not leave a
  # corrupted DLL behind for the gtest runs below or for local re-runs.
  cp "${crypto_dll}.bak" "${crypto_dll}"
  rm -f "${crypto_dll}.bak" "${crypto_dll}.corrupted"
  if [ "${fips_negative_rc}" -eq 0 ]; then
    echo >&2 "FIPS integrity negative test failed: test_fips should have failed with a corrupted crypto DLL."
    exit 1
  fi

  # Confirm the module loads and basic functionality works through the DLL.
  shard_gtest "${BUILD_ROOT}/crypto/crypto_test.exe --gtest_also_run_disabled_tests"
  shard_gtest ${BUILD_ROOT}/ssl/ssl_test.exe
done
popd
