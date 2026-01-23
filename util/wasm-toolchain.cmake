# AWS-LC WASM Toolchain File
#
# This is a wrapper toolchain file for building AWS-LC with Emscripten.
# It includes the standard Emscripten toolchain and configures pthread support
# for multithreaded WASM builds.
#
# Usage:
#   cmake -DCMAKE_TOOLCHAIN_FILE=util/wasm-toolchain.cmake ...
#
# Prerequisites:
#   - EMSDK environment must be sourced before running cmake
#   - EMSDK_PATH environment variable should point to Emscripten SDK root
#   - Node.js 16+ (for pthread/SharedArrayBuffer support)

# Find the Emscripten toolchain file
if(DEFINED ENV{EMSDK})
    set(EMSCRIPTEN_ROOT_PATH "$ENV{EMSDK}/upstream/emscripten")
elseif(DEFINED EMSDK_PATH)
    set(EMSCRIPTEN_ROOT_PATH "${EMSDK_PATH}/upstream/emscripten")
else()
    message(FATAL_ERROR "EMSDK environment variable or EMSDK_PATH must be set")
endif()

set(EMSCRIPTEN_TOOLCHAIN_FILE "${EMSCRIPTEN_ROOT_PATH}/cmake/Modules/Platform/Emscripten.cmake")

if(NOT EXISTS "${EMSCRIPTEN_TOOLCHAIN_FILE}")
    message(FATAL_ERROR "Emscripten toolchain file not found at: ${EMSCRIPTEN_TOOLCHAIN_FILE}")
endif()

# Include the standard Emscripten toolchain file
include("${EMSCRIPTEN_TOOLCHAIN_FILE}")

# Override CMAKE_SYSTEM_NAME to "Generic" so AWS-LC treats this as an embedded
# target and skips the pthread requirement check in its CMakeLists.txt.
# The Emscripten toolchain sets this to "Emscripten" but AWS-LC's CMakeLists.txt
# only recognizes "Generic" and "Android" as systems that don't require pthreads
# validation (we handle pthreads via Emscripten's own implementation).
set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR wasm32)

# Ensure cross-compiling is still set
set(CMAKE_CROSSCOMPILING TRUE)

# Enable pthread support for multithreaded WASM builds.
# Emscripten implements pthreads using Web Workers and SharedArrayBuffer.
# This requires:
#   - Compilation with -pthread flag
#   - Node.js 16+ or a browser with SharedArrayBuffer support
#   - COOP/COEP headers when running in browsers (not needed for Node.js)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -pthread")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pthread")

# Configure Emscripten to generate Node.js-compatible output with pthread support.
# Emscripten generates a JS wrapper file (no extension) and a .wasm binary.
# The JS wrapper loads and executes the .wasm file.
#
# Runtime environment flags:
# -sENVIRONMENT=node,worker: Target Node.js environment and web workers (for pthreads)
# -sNODERAWFS=1: Use Node.js raw filesystem for file I/O
# -sEXIT_RUNTIME=1: Exit the runtime when main() returns (needed for test runners)
#
# Memory flags:
# -sALLOW_MEMORY_GROWTH=1: Allow WASM memory to grow dynamically
# -sINITIAL_MEMORY=134217728: Set initial memory to 128MB. With pthreads enabled,
#   SharedArrayBuffer is used which requires memory to be allocated upfront.
#   Large test binaries (like integration_test) need ~113MB, so 128MB gives headroom.
# -sSTACK_SIZE=1048576: Increase stack size to 1MB (default is 64KB) for large tests
# -sASSERTIONS=1: Enable runtime assertions for better error messages during testing
#
# Warning suppression:
# -Wno-pthreads-mem-growth: Suppress warning about -pthread + ALLOW_MEMORY_GROWTH.
#   This combination may cause JS code accessing WASM memory to be slower, but WASM
#   code itself runs at full speed. This is acceptable for our use case.
#   See: https://github.com/WebAssembly/design/issues/1271
#
# Pthread flags:
# -pthread: Enable pthread support (must be on both compile and link)
# -sPTHREAD_POOL_SIZE=8: Pre-create 8 web workers at startup. This is important
#   because creating workers is asynchronous, and having a pool available means
#   pthread_create() can return synchronously without waiting for worker creation.
# -sPROXY_TO_PTHREAD: Run main() on a pthread instead of the main browser thread.
#   This is recommended because:
#   - The main browser thread cannot block (Atomics.wait doesn't work there)
#   - Moving main() to a worker allows proper blocking on mutexes, joins, etc.
#   - The main thread remains responsive for handling proxied operations
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -sENVIRONMENT=node,worker -sNODERAWFS=1 -sEXIT_RUNTIME=1 -sALLOW_MEMORY_GROWTH=1 -sINITIAL_MEMORY=134217728 -sASSERTIONS=1 -sSTACK_SIZE=1048576 -pthread -sPTHREAD_POOL_SIZE=8 -sPROXY_TO_PTHREAD -Wno-pthreads-mem-growth")