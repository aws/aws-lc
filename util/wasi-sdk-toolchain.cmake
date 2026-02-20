# AWS-LC WASI SDK Toolchain File
#
# This is a wrapper toolchain file for building AWS-LC with the WASI SDK.
# It includes the WASI SDK P2 toolchain and configures settings for
# building AWS-LC for the wasm32-wasip2 target.
#
# Usage:
#   cmake -DCMAKE_TOOLCHAIN_FILE=util/wasi-sdk-toolchain.cmake ...
#
# Prerequisites:
#   - WASI SDK must be installed (https://github.com/WebAssembly/wasi-sdk)
#   - WASI_SDK_PREFIX environment variable should point to WASI SDK root,
#     or the SDK should be installed at /opt/wasi-sdk
#   - A WASI runtime (wasmtime, wasmer, etc.) for running the compiled binaries
#
# Environment Variables:
#   WASI_SDK_PREFIX - Path to the WASI SDK (defaults to /opt/wasi-sdk)
#
# Supported targets:
#   - wasm32-wasip2 (WASI Preview 2 - default)
#   - wasm32-wasip1 (WASI Preview 1, set -DWASI_TARGET=wasm32-wasip1)
#
# Note: WASI does not currently support pthreads. AWS-LC will be built
# in single-threaded mode. The wasm32-wasip1-threads target exists but
# requires runtime support that is still experimental.

# Find the WASI SDK
if(DEFINED ENV{WASI_SDK_PREFIX})
    set(WASI_SDK_PREFIX "$ENV{WASI_SDK_PREFIX}")
elseif(NOT DEFINED WASI_SDK_PREFIX)
    # Default installation paths
    if(EXISTS "/opt/wasi-sdk")
        set(WASI_SDK_PREFIX "/opt/wasi-sdk")
    elseif(EXISTS "$ENV{HOME}/wasi-sdk")
        set(WASI_SDK_PREFIX "$ENV{HOME}/wasi-sdk")
    else()
        message(FATAL_ERROR
            "WASI SDK not found. Please either:\n"
            "  1. Set WASI_SDK_PREFIX environment variable to your WASI SDK location\n"
            "  2. Install WASI SDK to /opt/wasi-sdk\n"
            "Download from: https://github.com/WebAssembly/wasi-sdk/releases")
    endif()
endif()

if(NOT EXISTS "${WASI_SDK_PREFIX}")
    message(FATAL_ERROR "WASI SDK not found at: ${WASI_SDK_PREFIX}")
endif()

message(STATUS "Using WASI SDK at: ${WASI_SDK_PREFIX}")

# Select WASI target (default to wasip2)
if(NOT DEFINED WASI_TARGET)
    set(WASI_TARGET "wasm32-wasip2")
endif()

# Validate the target
set(VALID_WASI_TARGETS "wasm32-wasi" "wasm32-wasip1" "wasm32-wasip2")
if(NOT WASI_TARGET IN_LIST VALID_WASI_TARGETS)
    message(FATAL_ERROR
        "Invalid WASI_TARGET: ${WASI_TARGET}\n"
        "Valid targets are: ${VALID_WASI_TARGETS}")
endif()

message(STATUS "WASI target: ${WASI_TARGET}")

# Platform executable suffix
if(WIN32)
    set(WASI_HOST_EXE_SUFFIX ".exe")
else()
    set(WASI_HOST_EXE_SUFFIX "")
endif()

# Set system information
# Using "Generic" allows AWS-LC to skip pthread requirements check
# since WASI doesn't support traditional pthreads
set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_VERSION 1)
set(CMAKE_SYSTEM_PROCESSOR wasm32)

# Mark as cross-compiling
set(CMAKE_CROSSCOMPILING TRUE)

# Set compilers
set(CMAKE_C_COMPILER "${WASI_SDK_PREFIX}/bin/clang${WASI_HOST_EXE_SUFFIX}")
set(CMAKE_CXX_COMPILER "${WASI_SDK_PREFIX}/bin/clang++${WASI_HOST_EXE_SUFFIX}")
set(CMAKE_ASM_COMPILER "${WASI_SDK_PREFIX}/bin/clang${WASI_HOST_EXE_SUFFIX}")
set(CMAKE_AR "${WASI_SDK_PREFIX}/bin/llvm-ar${WASI_HOST_EXE_SUFFIX}")
set(CMAKE_RANLIB "${WASI_SDK_PREFIX}/bin/llvm-ranlib${WASI_HOST_EXE_SUFFIX}")
set(CMAKE_NM "${WASI_SDK_PREFIX}/bin/llvm-nm${WASI_HOST_EXE_SUFFIX}")
set(CMAKE_STRIP "${WASI_SDK_PREFIX}/bin/llvm-strip${WASI_HOST_EXE_SUFFIX}")
set(CMAKE_OBJCOPY "${WASI_SDK_PREFIX}/bin/llvm-objcopy${WASI_HOST_EXE_SUFFIX}")
set(CMAKE_OBJDUMP "${WASI_SDK_PREFIX}/bin/llvm-objdump${WASI_HOST_EXE_SUFFIX}")

# Set compiler targets
set(CMAKE_C_COMPILER_TARGET ${WASI_TARGET})
set(CMAKE_CXX_COMPILER_TARGET ${WASI_TARGET})
set(CMAKE_ASM_COMPILER_TARGET ${WASI_TARGET})

# Set sysroot
set(CMAKE_SYSROOT "${WASI_SDK_PREFIX}/share/wasi-sysroot")

# Search paths configuration
# Don't look in the sysroot for executables to run during the build
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
# Only look in the sysroot (not in host paths) for libraries and headers
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_PACKAGE ONLY)

# WASI-specific compiler flags
# -D_WASI_EMULATED_SIGNAL: Enable signal emulation (limited)
# -D_WASI_EMULATED_PROCESS_CLOCKS: Enable clock_gettime for process clocks
set(WASI_COMPILE_FLAGS "-D_WASI_EMULATED_SIGNAL -D_WASI_EMULATED_PROCESS_CLOCKS")

# WASI-specific linker flags
# -lwasi-emulated-signal: Link signal emulation library
# -lwasi-emulated-process-clocks: Link process clocks emulation
# Memory configuration flags:
# -Wl,-z,stack-size=1048576: Set stack size to 1MB (default is typically 64KB).
#   Some crypto tests allocate large buffers on the stack (e.g., 128KB for digest tests).
# -Wl,--initial-memory=134217728: Set initial linear memory to 128MB.
#   Large test binaries need sufficient memory for test data and operations.
# -Wl,--max-memory=268435456: Set maximum linear memory to 256MB.
#   Allows memory to grow for tests that process large amounts of data.
set(WASI_LINK_FLAGS "-lwasi-emulated-signal -lwasi-emulated-process-clocks -Wl,-z,stack-size=1048576 -Wl,--initial-memory=134217728 -Wl,--max-memory=268435456")

# Apply flags
set(CMAKE_C_FLAGS_INIT "${WASI_COMPILE_FLAGS}")
set(CMAKE_CXX_FLAGS_INIT "${WASI_COMPILE_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS_INIT "${WASI_LINK_FLAGS}")
set(CMAKE_SHARED_LINKER_FLAGS_INIT "${WASI_LINK_FLAGS}")
set(CMAKE_MODULE_LINKER_FLAGS_INIT "${WASI_LINK_FLAGS}")

# WASI doesn't support shared libraries in the traditional sense
set(BUILD_SHARED_LIBS OFF CACHE BOOL "Build shared libraries" FORCE)

# Disable Google Test death tests for WASI
# WASI does not support fork() or process exit code detection required by
# death tests. We must define this before gtest headers are included to
# prevent gtest-port.h from auto-detecting based on the host OS (e.g., __APPLE__).
add_compile_definitions(GTEST_HAS_DEATH_TEST=0)

# Disable Google Test stream redirection for WASI
# WASI does not support dup(), dup2(), or mkstemp() which are required for
# capturing stdout/stderr during tests.
add_compile_definitions(GTEST_HAS_STREAM_REDIRECTION=0)

# Output helpful message
message(STATUS "AWS-LC WASI SDK toolchain configured:")
message(STATUS "  SDK Path: ${WASI_SDK_PREFIX}")
message(STATUS "  Target: ${WASI_TARGET}")
message(STATUS "  Sysroot: ${CMAKE_SYSROOT}")
message(STATUS "  C Compiler: ${CMAKE_C_COMPILER}")
