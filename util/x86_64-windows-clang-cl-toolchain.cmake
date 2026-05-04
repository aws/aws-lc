# AWS-LC Cross-compile Toolchain: Linux → x86_64-pc-windows-msvc
#
# This toolchain configures clang-cl + lld-link + LLVM tools to cross-compile
# AWS-LC from a Linux host to a Windows MSVC target, using MSVC SDK headers
# and libraries supplied by xwin (https://github.com/Jake-Shadle/xwin).
#
# Usage:
#   cmake -DCMAKE_TOOLCHAIN_FILE=util/x86_64-windows-clang-cl-toolchain.cmake \
#         -G Ninja -DCMAKE_BUILD_TYPE=Release ...
#
# Prerequisites:
#   - clang-cl, lld-link, llvm-lib, llvm-rc, llvm-mt on PATH (Clang >= 19)
#   - An xwin-splatted MSVC SDK. The layout is expected to be:
#       ${XWIN_SDK_ROOT}/crt/{include,lib/x86_64}
#       ${XWIN_SDK_ROOT}/sdk/include/{ucrt,um,shared}
#       ${XWIN_SDK_ROOT}/sdk/lib/{ucrt,um}/x86_64
#     Override the root via the XWIN_SDK_ROOT cache variable or environment
#     variable; defaults to /tmp/xwin.

set(CMAKE_SYSTEM_NAME Windows)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

set(CMAKE_C_COMPILER clang-cl)
set(CMAKE_CXX_COMPILER clang-cl)
set(CMAKE_C_COMPILER_TARGET x86_64-pc-windows-msvc)
set(CMAKE_CXX_COMPILER_TARGET x86_64-pc-windows-msvc)
set(CMAKE_RC_COMPILER llvm-rc)
set(CMAKE_MT llvm-mt)

# Force the MSVC release dynamic runtime (/MD) everywhere, including inside
# CMake's initial try_compile probe. xwin does not splat the debug CRT import
# libraries by default, so without this CMake's probe fails to link against
# msvcrtd.lib. Requires CMP0091 NEW, which AWS-LC's top-level CMakeLists sets.
set(CMAKE_MSVC_RUNTIME_LIBRARY MultiThreadedDLL)

# Locate the xwin SDK. Prefer an explicit cache variable, then the environment,
# then fall back to the conventional /tmp/xwin used by the CI job.
if(NOT DEFINED XWIN_SDK_ROOT)
  if(DEFINED ENV{XWIN_SDK_ROOT})
    set(XWIN_SDK_ROOT "$ENV{XWIN_SDK_ROOT}" CACHE PATH "xwin MSVC SDK root")
  else()
    set(XWIN_SDK_ROOT "/tmp/xwin" CACHE PATH "xwin MSVC SDK root")
  endif()
endif()

# Include paths use /imsvc so clang-cl treats them as system headers and does
# not emit warnings from within them.
string(APPEND CMAKE_C_FLAGS_INIT
  " /imsvc ${XWIN_SDK_ROOT}/crt/include"
  " /imsvc ${XWIN_SDK_ROOT}/sdk/include/ucrt"
  " /imsvc ${XWIN_SDK_ROOT}/sdk/include/um"
  " /imsvc ${XWIN_SDK_ROOT}/sdk/include/shared")
set(CMAKE_CXX_FLAGS_INIT "${CMAKE_C_FLAGS_INIT}")

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT
  " /LIBPATH:${XWIN_SDK_ROOT}/crt/lib/x86_64"
  " /LIBPATH:${XWIN_SDK_ROOT}/sdk/lib/um/x86_64"
  " /LIBPATH:${XWIN_SDK_ROOT}/sdk/lib/ucrt/x86_64")
set(CMAKE_SHARED_LINKER_FLAGS_INIT "${CMAKE_EXE_LINKER_FLAGS_INIT}")
