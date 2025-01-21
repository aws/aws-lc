cmake_minimum_required(VERSION 3.0)

if(POLICY CMP0091)
cmake_policy(SET CMP0091 NEW)
endif()

# Defer enabling C and CXX languages.
project(AWSLC NONE)

if(MSVC)
  # On Windows, prefer cl over gcc if both are available. By default most of
  # the CMake generators prefer gcc, even on Windows.
  set(CMAKE_GENERATOR_CC cl)
endif()

if(ARCH STREQUAL "aarch64" AND CMAKE_GENERATOR MATCHES "Visual Studio" AND NOT "${CMAKE_VS_PLATFORM_TOOLSET}" MATCHES "ClangCL")
  message(FATAL_ERROR "AWS-LC Windows/ARM64 assembly code requires ClangCL. Current toolset: ${CMAKE_VS_PLATFORM_TOOLSET}")
endif()

include(sources.cmake)
include(TestBigEndian)

if(POLICY CMP0077)
  cmake_policy(SET CMP0077 NEW) #option does nothing when a normal variable of the same name exists.
endif()

option(BUILD_TESTING "Build all test targets for AWS-LC" ON)
option(BUILD_LIBSSL "Build libssl for AWS-LC" ON)
option(BUILD_TOOL "Build bssl tool for AWS-LC" ON)
option(ENABLE_DILITHIUM "Enable Dilithium signatures in the EVP API" OFF)
option(DISABLE_PERL "Disable Perl for AWS-LC" OFF)
option(DISABLE_GO "Disable Go for AWS-LC" OFF)
option(ENABLE_FIPS_ENTROPY_CPU_JITTER "Enable FIPS entropy source: CPU Jitter" OFF)
option(ENABLE_DATA_INDEPENDENT_TIMING "Enable automatic setting/resetting Data-Independent Timing
(DIT) flag in cryptographic functions. Currently only applicable to Arm64 (except on Windows)" OFF)
include(cmake/go.cmake)

enable_language(C)

# Configure entropy source in case of FIPS build
if(FIPS)
  message(STATUS "FIPS build mode configured")

  if(ENABLE_FIPS_ENTROPY_CPU_JITTER)
    add_definitions(-DFIPS_ENTROPY_SOURCE_JITTER_CPU)
    add_subdirectory(third_party/jitterentropy)
    message(STATUS "FIPS entropy source method configured: CPU Jitter")
  else()
    add_definitions(-DFIPS_ENTROPY_SOURCE_PASSIVE)
    message(STATUS "FIPS entropy source method configured: Passive")
  endif()
endif()

if(${CMAKE_SYSTEM_NAME} STREQUAL "OpenBSD")
  # OpenBSD by defaults links with --execute-only this is problematic for two reasons:
  # 1. The FIPS shared and static builds need to compute the module signature hash by reading the .text section
  # 2. s2n-bignum x86 assembly sources still have references to static data in the .text section
  if(NOT BUILD_SHARED_LIBS)
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--no-execute-only")
  else()
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--no-execute-only")
  endif()
endif()

if(CMAKE_HOST_SYSTEM_NAME STREQUAL "SunOS" AND NOT CMAKE_CROSSCOMPILING)
  # Determine if the host is running an illumos distribution:
  execute_process(COMMAND /usr/bin/uname -o OUTPUT_VARIABLE UNAME_O
    OUTPUT_STRIP_TRAILING_WHITESPACE)

  if (UNAME_O STREQUAL "illumos")
    set(HOST_ILLUMOS 1)
  endif()

  if (UNAME_O STREQUAL "Solaris")
    set(HOST_SOLARIS 1)
  endif()

  if (HOST_ILLUMOS)
    #
    # illumos systems require linking libsocket and libnsl to get various
    # networking routines sometimes found in libc on other platforms:
    #
    if(NOT BUILD_SHARED_LIBS)
      set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -lsocket -lnsl")
    else()
      set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -lsocket -lnsl")
    endif()
  endif()
endif()

# Tests and libssl both require the CXX language to be enabled. If a consumer
# chooses to disable building the tests and libssl, do not enable CXX
if(BUILD_TESTING OR BUILD_LIBSSL)
  enable_language(CXX)
endif()

if (NOT DEFINED CMAKE_CXX_STANDARD)
  set(CMAKE_CXX_STANDARD 11)
endif()
set(CMAKE_CXX_STANDARD_REQUIRED ON)
if (NOT DEFINED CMAKE_C_STANDARD)
  try_compile(
          RESULT
          ${PROJECT_BINARY_DIR}
          SOURCES "${CMAKE_CURRENT_LIST_DIR}/tests/compiler_features_tests/c11.c"
          COMPILE_DEFINITIONS -c -std=c11)
  if(RESULT)
    set(CMAKE_C_STANDARD 11)
  else()
    set(CMAKE_C_STANDARD 99)
  endif()
endif ()
set(CMAKE_C_STANDARD_REQUIRED ON)

if(CMAKE_C_COMPILER_ID MATCHES "Clang")
  set(CLANG 1)
elseif(CMAKE_C_COMPILER_ID MATCHES "GNU")
  set(GCC 1)
endif()

if (NOT WIN32 AND NOT APPLE)
  include(GNUInstallDirs)
elseif(NOT DEFINED CMAKE_INSTALL_LIBDIR)
  set(CMAKE_INSTALL_LIBDIR "lib")
  set(CMAKE_INSTALL_INCLUDEDIR "include")
  set(CMAKE_INSTALL_BINDIR "bin")
endif()

install(DIRECTORY include/openssl
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
        COMPONENT Development
        PATTERN boringssl_prefix_symbols.h EXCLUDE
        PATTERN boringssl_prefix_symbols_asm.h EXCLUDE
        PATTERN boringssl_prefix_symbols_nasm.inc EXCLUDE
)

if (TEST_SYSGENID_PATH)
  message(STATUS "Setting AWSLC_SNAPSAFE_TESTING=1")
  add_definitions(-DAWSLC_SNAPSAFE_TESTING=1)
  message(STATUS "Setting AWSLC_SYSGENID_PATH=${TEST_SYSGENID_PATH}")
  add_definitions(-DAWSLC_SYSGENID_PATH=\"${TEST_SYSGENID_PATH}\")
endif()

if(NOT DISABLE_PERL)
  find_package(Perl REQUIRED)
endif()

if("${CMAKE_SYSTEM_NAME}" STREQUAL "Linux" AND BUILD_TESTING AND NOT CMAKE_CROSSCOMPILING)
  find_package(PkgConfig QUIET)
  if (PkgConfig_FOUND)
    pkg_check_modules(LIBUNWIND libunwind-generic)
    if(LIBUNWIND_FOUND)
      add_definitions(-DBORINGSSL_HAVE_LIBUNWIND)
    else()
      message("libunwind not found. Disabling unwind tests.")
    endif()
  else()
    message("pkgconfig not found. Disabling unwind tests.")
  endif()
endif()

if(NOT GO_EXECUTABLE)
  message(STATUS "Go not found. Disabling some code generation and using pre-generated code in generated-src/")
endif()
if (NOT PERL_EXECUTABLE)
  message(STATUS "Perl not found. Disabling some code generation and using pre-generated code in generated-src/")
endif()

if(NOT PERL_EXECUTABLE OR NOT GO_EXECUTABLE)
  set(GENERATE_CODE_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/generated-src")
endif()


if(ENABLE_DILITHIUM)
  add_definitions(-DENABLE_DILITHIUM)
endif()

if(USE_CUSTOM_LIBCXX)
  set(BORINGSSL_ALLOW_CXX_RUNTIME 1)
endif()

if(BORINGSSL_ALLOW_CXX_RUNTIME)
  add_definitions(-DBORINGSSL_ALLOW_CXX_RUNTIME)
endif()

string(TOLOWER "${CMAKE_BUILD_TYPE}" CMAKE_BUILD_TYPE_LOWER)
if(NOT FIPS)
  if("${CMAKE_BUILD_TYPE_LOWER}" STREQUAL "relwithassert" OR
     NOT CMAKE_BUILD_TYPE_LOWER MATCHES "rel")
    add_definitions(-DBORINGSSL_DISPATCH_TEST)
    # CMake automatically connects include_directories to the NASM
    # command-line, but not add_definitions.
    set(CMAKE_ASM_NASM_FLAGS "${CMAKE_ASM_NASM_FLAGS} -DBORINGSSL_DISPATCH_TEST")
  elseif(CMAKE_BUILD_TYPE_LOWER MATCHES "rel")
    add_definitions(-DBORINGSSL_RELEASE_BUILD)
  endif()
endif()

# Add a RelWithAsserts build configuration. It is the same as Release, except it
# does not define NDEBUG, so asserts run.
foreach(VAR CMAKE_C_FLAGS CMAKE_CXX_FLAGS CMAKE_ASM_FLAGS)
  string(REGEX REPLACE "(^| )[/-]DNDEBUG( |$)" " " "${VAR}_RELWITHASSERTS"
         "${${VAR}_RELEASE}")
endforeach()

if(BORINGSSL_PREFIX AND BORINGSSL_PREFIX_SYMBOLS AND GO_EXECUTABLE)

  message(STATUS "Prefix build configured: building headers using prefix \"${BORINGSSL_PREFIX}\" and symbols file \"${BORINGSSL_PREFIX_SYMBOLS}\"")

  if(IS_ABSOLUTE ${BORINGSSL_PREFIX_SYMBOLS})
    set(BORINGSSL_PREFIX_SYMBOLS_PATH ${BORINGSSL_PREFIX_SYMBOLS})
  else()
    set(BORINGSSL_PREFIX_SYMBOLS_PATH ${PROJECT_BINARY_DIR}/${BORINGSSL_PREFIX_SYMBOLS})
  endif()

  add_custom_command(
    OUTPUT symbol_prefix_include/openssl/boringssl_prefix_symbols.h
           symbol_prefix_include/openssl/boringssl_prefix_symbols_asm.h
           symbol_prefix_include/openssl/boringssl_prefix_symbols_nasm.inc
    COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl
    COMMAND ${GO_EXECUTABLE} run ${CMAKE_CURRENT_SOURCE_DIR}/util/make_prefix_headers.go -out ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl -prefix ${BORINGSSL_PREFIX} ${BORINGSSL_PREFIX_SYMBOLS_PATH}
    COMMAND ${CMAKE_COMMAND} -E remove
          ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl/boringssl_prefix_symbols.h.bak
          ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl/boringssl_prefix_symbols_asm.h.bak
          ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl/boringssl_prefix_symbols_nasm.inc.bak
    DEPENDS util/make_prefix_headers.go
            ${BORINGSSL_PREFIX_SYMBOLS_PATH})
  # add_dependencies needs a target, not a file, so we add an intermediate
  # target.
  add_custom_target(
    boringssl_prefix_symbols
    DEPENDS symbol_prefix_include/openssl/boringssl_prefix_symbols.h
            symbol_prefix_include/openssl/boringssl_prefix_symbols_asm.h
            symbol_prefix_include/openssl/boringssl_prefix_symbols_nasm.inc)

  install(DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl
          DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
          COMPONENT Development
  )
elseif(BORINGSSL_PREFIX AND BORINGSSL_PREFIX_HEADERS)

  message(STATUS "Prefix build configured: performing build using prefix \"${BORINGSSL_PREFIX}\" and headers path \"${BORINGSSL_PREFIX_HEADERS}\"")

  if(IS_ABSOLUTE ${BORINGSSL_PREFIX_HEADERS})
    set(BORINGSSL_PREFIX_HEADERS_PATH ${BORINGSSL_PREFIX_HEADERS})
  else()
    set(BORINGSSL_PREFIX_HEADERS_PATH ${PROJECT_BINARY_DIR}/${BORINGSSL_PREFIX_HEADERS})
  endif()

  file(COPY ${BORINGSSL_PREFIX_HEADERS_PATH}/openssl/boringssl_prefix_symbols.h DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl)
  file(COPY ${BORINGSSL_PREFIX_HEADERS_PATH}/openssl/boringssl_prefix_symbols_asm.h DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl)
  file(COPY ${BORINGSSL_PREFIX_HEADERS_PATH}/openssl/boringssl_prefix_symbols_nasm.inc DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl)

  add_custom_target(boringssl_prefix_symbols)

  install(DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/symbol_prefix_include/openssl
          DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
          COMPONENT Development
  )
elseif(BORINGSSL_PREFIX OR BORINGSSL_PREFIX_SYMBOLS)
  message(FATAL_ERROR "Must specify both or neither of BORINGSSL_PREFIX and BORINGSSL_PREFIX_SYMBOLS")
elseif((BORINGSSL_PREFIX AND BORINGSSL_PREFIX_SYMBOLS) AND NOT GO_EXECUTABLE)
  message(FATAL_ERROR "Must have Go installed when using BORINGSSL_PREFIX and BORINGSSL_PREFIX_SYMBOLS")
else()
  add_custom_target(boringssl_prefix_symbols)

  install(DIRECTORY include/openssl
          DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
          COMPONENT Development
          PATTERN boringssl_prefix_symbols.h
          PATTERN boringssl_prefix_symbols_asm.h
          PATTERN boringssl_prefix_symbols_nasm.inc
  )
endif()

if("${CMAKE_SYSTEM_NAME}" STREQUAL "Emscripten")
  set(EMSCRIPTEN 1)
endif()

macro(check_compiler file_to_test flag_to_set)
  try_compile(
          RESULT
          ${PROJECT_BINARY_DIR}
          SOURCES "${CMAKE_CURRENT_LIST_DIR}/tests/compiler_features_tests/${file_to_test}"
          COMPILE_DEFINITIONS "-Werror"
          OUTPUT_VARIABLE ERROR_MESSAGE)
  if(RESULT)
    set(COMPILER_CHECK_FLAGS "${COMPILER_CHECK_FLAGS} -D${flag_to_set}")
    message(STATUS "${file_to_test} probe is positive, enabling ${flag_to_set}")
  else()
    message(STATUS "${file_to_test} probe is negative, NOT enabling ${flag_to_set}:")
    # Some build applications use regexes on build output to highlight build
    # errors. Below, we modify a compiler error message to avoid that a negative
    # probe is considered an error in such build applications.
    string(REPLACE ": error:"
      ": compiler_error:" ERROR_MESSAGE_PROCESSED
      ${ERROR_MESSAGE})
    message(STATUS "    ${ERROR_MESSAGE_PROCESSED}")
  endif()
endmacro()

macro(check_run file_to_test flag_to_set compile_flags)
  message(STATUS "Run check_run file_to_test '${file_to_test}', "
          "flag_to_set '${flag_to_set}', "
          "and compile_flags '${compile_flags}'.")
  try_run(
          ${flag_to_set}
          COMPILE_RESULT
          "${CMAKE_CURRENT_BINARY_DIR}"
          "${CMAKE_CURRENT_LIST_DIR}/tests/compiler_features_tests/${file_to_test}"
          COMPILE_DEFINITIONS "${compile_flags}"
          OUTPUT_VARIABLE COMPILE_AND_RUN_OUTPUT)
  if (NOT COMPILE_RESULT)
    message(WARNING "COMPILE_AND_RUN_OUTPUT ${COMPILE_AND_RUN_OUTPUT}")
  endif()
endmacro()

# Some ancient assemblers don't know about AVX instructions, which is an
# assumption we make for some of the assembly implementations. This flag
# can be set to handle such cases.
option(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX "Exclude AVX code from the build" OFF)

# Some assemblers know about AVX but not ADX, AVX2 or AVX512 instructions, e.g. gcc 4.8.2.
# This flag can be set to handle such cases.
# Note:
# * Although this flag name implies an effect on AVX512 instructions, it's also
#   intended to avoid generating ADX and AVX2 instructions.
# * This flag name has "512AVX" instead of "AVX512" so that it doesn't
#   include the entire flag -DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX and match
#   to it in the Perl files checks.
option(MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX "Exclude AVX512 code from the build" OFF)

if(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
  add_definitions(-DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
  add_definitions(-DMY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX)
  set(MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX ON)
  message(STATUS "MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX selected, removing all AVX optimisations")
endif()

if(MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX)
  add_definitions(-DMY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX)
  message(STATUS "MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX selected, removing ADX, AVX2 and AVX512 optimisations")
endif()

if (GCC)
  # All versions of GCC that AWS-LC supports has this warning
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wredundant-decls")

  # Detect if memcmp is wrongly stripped like strcmp.
  # If exists, let CMake generate a warning.
  # memcmp bug link https://gcc.gnu.org/bugzilla/show_bug.cgi?id=95189.
  # CMake try_run requires these variables must be preset.
  # https://cmake.org/cmake/help/latest/command/try_run.html
  set(MEMCMP_INVALID_STRIPPED "")
  set(MEMCMP_INVALID_STRIPPED__TRYRUN_OUTPUT "")

  # See https://gitlab.kitware.com/cmake/cmake/-/issues/16920 for why we set this to 2
  # During the `try_run` commands invoked by `check_run` a test program is run for the threading library.
  # This test is run expecting two threads, and this variable isn't set, for some systems
  # (particularly for systems using cross-compilation) causing our test to run without 2 threads and fail.
  # We set this variable here to allow these builds to succeed and keep these tests around to make sure
  # that we properly detect the compiler bugs that we are trying to test for with these `try_run` calls.

  set(THREADS_PTHREAD_ARG "2" CACHE STRING "Forcibly set by CMakeLists.txt." FORCE)

  if (CMAKE_BUILD_TYPE_LOWER MATCHES "release")
    # CMAKE_C_FLAGS_RELEASE enables `-O3`.
    check_run(memcmp_invalid_stripped_check.c MEMCMP_INVALID_STRIPPED "${CMAKE_C_FLAGS_RELEASE}")
  elseif(CMAKE_BUILD_TYPE_LOWER MATCHES "relwithdebinfo")
    # CMAKE_C_FLAGS_RELEASE enables `-O2`.
    check_run(memcmp_invalid_stripped_check.c MEMCMP_INVALID_STRIPPED "${CMAKE_C_FLAGS_RELWITHDEBINFO}")
  endif()

  if (MEMCMP_INVALID_STRIPPED)
    message(WARNING "Currently, GCC ${CMAKE_C_COMPILER_VERSION} is not supported due to a memcmp related bug reported in "
            "https://gcc.gnu.org/bugzilla/show_bug.cgi?id=95189.\n"
            "We strongly recommend against using the GCC ${CMAKE_C_COMPILER_VERSION} compiler.")
  endif ()
endif ()

if(GCC OR CLANG)
  # Note clang-cl is odd and sets both CLANG and MSVC. We base our configuration
  # primarily on our normal Clang one.
  if (NOT CMAKE_VERSION VERSION_GREATER "3.1.0")
    message(STATUS "Adding CMAKE_C_FLAGS -std=c${CMAKE_C_STANDARD}")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -std=c${CMAKE_C_STANDARD}")
  else()
    message(STATUS "Setting CMAKE_C_STANDARD=${CMAKE_C_STANDARD}")
  endif()

  # TODO(CryptoAlg-759): enable '-Wpedantic' if awslc has to follow c99 spec.
  if(CLANG OR (GCC AND CMAKE_C_COMPILER_VERSION VERSION_GREATER "4.1.3"))
    # GCC 4.1.3 and below do not support all of these flags or they raise false positives.
    if (MSVC)
      # clang-cl sets different default warnings than clang. It also treats -Wall
      # as -Weverything, to match MSVC. Instead -W3 is the alias for -Wall.
      # See http://llvm.org/viewvc/llvm-project?view=revision&revision=319116
      set(C_CXX_FLAGS "${C_CXX_FLAGS} -W3 -fmsc-version=1900")
      set(C_CXX_FLAGS "${C_CXX_FLAGS} -Wno-deprecated-declarations")
    else()
      set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wextra")
      set(C_CXX_FLAGS "${C_CXX_FLAGS} -Wall -fvisibility=hidden -fno-common")
      set(CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS} -Wno-newline-eof")
    endif()
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wunused -Wcomment -Wchar-subscripts -Wuninitialized -Wshadow")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wwrite-strings -Wformat-security -Wunused-result -Wno-overlength-strings")
    set(C_CXX_FLAGS "${C_CXX_FLAGS} -Wno-c11-extensions -Wvla -Wtype-limits -Wno-unused-parameter")
  endif()
  set(C_CXX_FLAGS "${C_CXX_FLAGS} -Werror -Wformat=2 -Wsign-compare -Wmissing-field-initializers -Wwrite-strings")

  if((GCC AND CMAKE_C_COMPILER_VERSION VERSION_GREATER "8") OR
     (CMAKE_C_COMPILER_ID MATCHES "Clang" AND NOT CMAKE_C_COMPILER_VERSION VERSION_LESS "13"))
    # GCC 8.x added a warning called -Wcast-function-type to the -Wextra umbrella.
    # Also suppress for all clang versions supporting this warning.
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wno-cast-function-type")
  endif()

  if(CMAKE_BUILD_TYPE_LOWER STREQUAL "debug" OR CMAKE_BUILD_TYPE_LOWER STREQUAL "relwithdebinfo")
    if (MSVC)
      set(C_CXX_FLAGS "${C_CXX_FLAGS} /Zi")
    else()
      if(EMSCRIPTEN)
        # emscripten's emcc/clang does not accept the "-ggdb" flag.
        set(C_CXX_FLAGS "${C_CXX_FLAGS} -g")
      else()
        set(C_CXX_FLAGS "${C_CXX_FLAGS} -ggdb")
      endif()
    endif()
  endif()

  if(MINGW)
    # Some MinGW compilers set _WIN32_WINNT to an older version (Windows Server 2003)
    # See: https://learn.microsoft.com/en-us/cpp/porting/modifying-winver-and-win32-winnt?view=msvc-170
    # Support Windows 7 and later.
    add_definitions(-D_WIN32_WINNT=_WIN32_WINNT_WIN7)
  endif()

  if(CLANG)
    set(C_CXX_FLAGS "${C_CXX_FLAGS} -Wnewline-eof -fcolor-diagnostics")
  elseif(CMAKE_C_COMPILER_VERSION VERSION_GREATER "4.1.3")
    # GCC (at least 4.8.4) has a bug where it'll find unreachable free() calls
    # and declare that the code is trying to free a stack pointer. GCC 4.1.3 and lower
    # doesn't support this flag and can't use it.
    set(C_CXX_FLAGS "${C_CXX_FLAGS} -Wno-free-nonheap-object")
    # GCC (from at least 4.8) does not include -Wmissing-braces in -Wall due to Bug 25137.
    # This warning is turned on everywhere internally however, so we have to define it here
    # to check that our changes don't break the build.
    # See https://gcc.gnu.org/bugzilla/show_bug.cgi?id=25137
    set(C_CXX_FLAGS "${C_CXX_FLAGS} -Wmissing-braces")
  endif()

  # -Wstring-concatenation was added in Clang 12.0.0, which corresponds to
  # AppleClang 13.0.0 per the table in
  # https://en.wikipedia.org/wiki/Xcode#Toolchain_versions
  if((CMAKE_C_COMPILER_ID STREQUAL "Clang" AND
          NOT(CMAKE_C_COMPILER_VERSION VERSION_LESS "12.0.0")) OR
  (CMAKE_C_COMPILER_ID STREQUAL "AppleClang" AND
          NOT(CMAKE_C_COMPILER_VERSION VERSION_LESS "13.0.0")))
    set(C_CXX_FLAGS "${C_CXX_FLAGS} -Wstring-concatenation")
  endif()

  if(CLANG OR NOT "7.0.0" VERSION_GREATER CMAKE_C_COMPILER_VERSION)
    set(C_CXX_FLAGS "${C_CXX_FLAGS} -Wimplicit-fallthrough")
  endif()

  if(CMAKE_COMPILER_IS_GNUCXX AND CMAKE_CXX_COMPILER_VERSION VERSION_GREATER "5")
    set(C_CXX_FLAGS "${C_CXX_FLAGS} -Wformat-signedness")
  endif()

  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${C_CXX_FLAGS} -Wmissing-prototypes -Wold-style-definition -Wstrict-prototypes")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${C_CXX_FLAGS} -Wmissing-declarations")

  if(NOT MSVC)
    if (NOT CMAKE_CXX_STANDARD)
      set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
    endif ()
    if(APPLE)
      set(CMAKE_MACOSX_RPATH 1)
    endif()
    if(NOT BORINGSSL_ALLOW_CXX_RUNTIME)
      set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-exceptions -fno-rtti")
    endif()
  endif()

  # In GCC, -Wmissing-declarations is the C++ spelling of -Wmissing-prototypes
  # and using the wrong one is an error. In Clang, -Wmissing-prototypes is the
  # spelling for both and -Wmissing-declarations is some other warning.
  #
  # https://gcc.gnu.org/onlinedocs/gcc-7.1.0/gcc/Warning-Options.html#Warning-Options
  # https://clang.llvm.org/docs/DiagnosticsReference.html#wmissing-prototypes
  # https://clang.llvm.org/docs/DiagnosticsReference.html#wmissing-declarations
  if(CLANG)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wmissing-prototypes")
  endif()

  if(GCC AND "4.8" VERSION_GREATER CMAKE_C_COMPILER_VERSION AND CMAKE_C_COMPILER_VERSION VERSION_GREATER "4.1.3")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wno-array-bounds")
  endif()

  check_compiler("stdalign_check.c" AWS_LC_STDALIGN_AVAILABLE)
  check_compiler("builtin_swap_check.c" AWS_LC_BUILTIN_SWAP_SUPPORTED)
  if(FIPS AND CMAKE_SYSTEM_NAME STREQUAL "Linux")
    check_compiler("linux_u32.c" AWS_LC_URANDOM_U32)
  endif()

  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${COMPILER_CHECK_FLAGS}")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${COMPILER_CHECK_FLAGS}")

elseif(MSVC)
  set(MSVC_DISABLED_WARNINGS_LIST
      "C4061" # enumerator 'identifier' in switch of enum 'enumeration' is not
              # explicitly handled by a case label
              # Disable this because it flags even when there is a default.
      "C4100" # 'exarg' : unreferenced formal parameter
      "C4127" # conditional expression is constant
      "C4146" # unary minus operator applied to unsigned type, result still unsigned
      "C4200" # nonstandard extension used : zero-sized array in
              # struct/union.
      "C4204" # nonstandard extension used: non-constant aggregate initializer
      "C4221" # nonstandard extension used : 'identifier' : cannot be
              # initialized using address of automatic variable
      "C4242" # 'function' : conversion from 'int' to 'uint8_t',
              # possible loss of data
      "C4244" # 'function' : conversion from 'int' to 'uint8_t',
              # possible loss of data
      "C4267" # conversion from 'size_t' to 'int', possible loss of data
      "C4371" # layout of class may have changed from a previous version of the
              # compiler due to better packing of member '...'
      "C4388" # signed/unsigned mismatch
      "C4296" # '>=' : expression is always true
      "C4350" # behavior change: 'std::_Wrap_alloc...'
      "C4365" # '=' : conversion from 'size_t' to 'int',
              # signed/unsigned mismatch
      "C4389" # '!=' : signed/unsigned mismatch
      "C4464" # relative include path contains '..'
      "C4510" # 'argument' : default constructor could not be generated
      "C4512" # 'argument' : assignment operator could not be generated
      "C4514" # 'function': unreferenced inline function has been removed
      "C4548" # expression before comma has no effect; expected expression with
              # side-effect" caused by FD_* macros.
      "C4610" # struct 'argument' can never be instantiated - user defined
              # constructor required.
      "C4623" # default constructor was implicitly defined as deleted
      "C4625" # copy constructor could not be generated because a base class
              # copy constructor is inaccessible or deleted
      "C4626" # assignment operator could not be generated because a base class
              # assignment operator is inaccessible or deleted
      "C4628" # digraphs not supported with -Ze
      "C4668" # 'symbol' is not defined as a preprocessor macro, replacing with
              # '0' for 'directives'
              # Disable this because GTest uses it everywhere.
      "C4706" # assignment within conditional expression
      "C4710" # 'function': function not inlined
      "C4711" # function 'function' selected for inline expansion
      "C4800" # 'int' : forcing value to bool 'true' or 'false'
              # (performance warning)
      "C4820" # 'bytes' bytes padding added after construct 'member_name'
      "C5026" # move constructor was implicitly defined as deleted
      "C5027" # move assignment operator was implicitly defined as deleted
      "C5045" # Compiler will insert Spectre mitigation for memory load if
              # /Qspectre switch specified
      "C4255" # no function prototype given: converting '()' to '(void)'
      "C4152" # non standard extension, function/data ptr conversion in expression
              # used in bcm.c to check functions are inside the FIPS module memory region
      "C4295" # array is too small to include a terminating null character
      "C4701" # potentially uninitialized local
      "C4505" # unreferenced local function has been removed
      "C4702" # unreachable code in bcm.c power on tests
      "C4191" # unsafe conversion from 'type of expression' to 'type required'
              # TODO remove once https://github.com/openssl/openssl/issues/18957 is resolved
      "C4996" # deprecated warnings using low level functions in OpenSSL 3.0
      "C4746" # consider using __iso_volatile_load/store intrinsic functions
      "C5264" # 'variable-name': 'const' variable is not used
      "C5266" # 'const' qualifier on return type has no effect
      "C5267" # definition of implicit copy constructor for '...' is deprecated because it has a user-provided destructor
          )
  set(MSVC_LEVEL4_WARNINGS_LIST
      # See https://connect.microsoft.com/VisualStudio/feedback/details/1217660/warning-c4265-when-using-functional-header
      "C4265" # class has virtual functions, but destructor is not virtual
      )
  string(REPLACE "C" " -wd" MSVC_DISABLED_WARNINGS_STR
                            ${MSVC_DISABLED_WARNINGS_LIST})
  string(REPLACE "C" " -w4" MSVC_LEVEL4_WARNINGS_STR
                            ${MSVC_LEVEL4_WARNINGS_LIST})
  set(CMAKE_C_FLAGS   "-utf-8 -Wall -WX ${MSVC_DISABLED_WARNINGS_STR} ${MSVC_LEVEL4_WARNINGS_STR}")
  set(CMAKE_CXX_FLAGS "-utf-8 -Wall -WX ${MSVC_DISABLED_WARNINGS_STR} ${MSVC_LEVEL4_WARNINGS_STR}")

  # If we're using MSVC on Windows in FIPS mode with RelWithDebInfo then we want to override some of the default RelWithDebInfo flags.
  # This fixes the problem we run into with RelWithDebInfo and FIPS mode on Windows where the FIPS module wouldn't span the expected symbol.
  if(CMAKE_BUILD_TYPE_LOWER MATCHES "relwithdebinfo" AND FIPS)
    # /Zi requires the /debug flag for executables/libraries that we want .pdb files for.
    # We want to replace the default /debug flag with /DEBUG:FULL, to explicitly make sure that the .pdb files can be used on machines other than one on which it's built.
    string(REPLACE "/debug" "/DEBUG:FULL" CMAKE_SHARED_LINKER_FLAGS_RELWITHDEBINFO "${CMAKE_SHARED_LINKER_FLAGS_RELWITHDEBINFO}")
    string(REPLACE "/debug" "/DEBUG:FULL" CMAKE_EXE_LINKER_FLAGS_RELWITHDEBINFO "${CMAKE_EXE_LINKER_FLAGS_RELWITHDEBINFO}")

    # The /debug flag also turns off the /OPT linker flag so we want to turn them back on across the board.
    set(CMAKE_SHARED_LINKER_FLAGS_RELWITHDEBINFO "${CMAKE_SHARED_LINKER_FLAGS_RELWITHDEBINFO} /OPT:REF,ICF,LBR")
    set(CMAKE_EXE_LINKER_FLAGS_RELWITHDEBINFO "${CMAKE_EXE_LINKER_FLAGS_RELWITHDEBINFO} /OPT:REF,ICF,LBR")
  endif()
endif()

if(WIN32)
  add_definitions(-D_HAS_EXCEPTIONS=0)
  add_definitions(-DWIN32_LEAN_AND_MEAN)
  add_definitions(-DNOMINMAX)
  # Allow use of fopen.
  add_definitions(-D_CRT_SECURE_NO_WARNINGS)
  # VS 2017 and higher supports STL-only warning suppressions.
  # A bug in CMake < 3.13.0 may cause the space in this value to
  # cause issues when building with NASM. In that case, update CMake.
  add_definitions("-D_STL_EXTRA_DISABLED_WARNINGS=4774 4987")
endif()

if((GCC AND CMAKE_C_COMPILER_VERSION VERSION_GREATER "4.9.99") OR
   CLANG)
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wshadow")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wshadow")
endif()

# pthread_rwlock_t on Linux requires a feature flag. We limit this to Linux
# because, on Apple platforms, it instead disables APIs we use. See compat(5)
# and sys/cdefs.h. Reportedly, FreeBSD also breaks when this is set. See
# https://crbug.com/boringssl/471.
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -D_XOPEN_SOURCE=700")
endif()

if(FUZZ)
  if(NOT CLANG)
    message(FATAL_ERROR "You need to build with Clang for fuzzing to work")
  endif()

  if(CMAKE_C_COMPILER_VERSION VERSION_LESS "6.0.0")
    message(FATAL_ERROR "You need Clang ≥ 6.0.0")
  endif()

  add_definitions(-DBORINGSSL_UNSAFE_DETERMINISTIC_MODE)
  set(RUNNER_ARGS "-deterministic")

  if(NOT NO_FUZZER_MODE)
    add_definitions(-DBORINGSSL_UNSAFE_FUZZER_MODE)
    set(RUNNER_ARGS ${RUNNER_ARGS} "-fuzzer" "-shim-config" "fuzzer_mode.json")
  endif()

  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=address,fuzzer-no-link -fsanitize-coverage=edge,indirect-calls")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address,fuzzer-no-link -fsanitize-coverage=edge,indirect-calls")
endif()

if(BUILD_SHARED_LIBS)
  add_definitions(-DBORINGSSL_SHARED_LIBRARY)
  # Enable position-independent code globally. This is needed because
  # some library targets are OBJECT libraries.
  set(CMAKE_POSITION_INDEPENDENT_CODE TRUE)
elseif(NOT DEFINED CMAKE_POSITION_INDEPENDENT_CODE)
  set(CMAKE_POSITION_INDEPENDENT_CODE TRUE)
endif()

if(MSAN)
  if(NOT CLANG)
    message(FATAL_ERROR "Cannot enable MSAN unless using Clang")
  endif()

  if(ASAN)
    message(FATAL_ERROR "ASAN and MSAN are mutually exclusive")
  endif()

  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=memory -fsanitize-memory-track-origins -fno-omit-frame-pointer")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=memory -fsanitize-memory-track-origins -fno-omit-frame-pointer")
  set(CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS} -fsanitize=memory -fsanitize-memory-track-origins -fno-omit-frame-pointer")
endif()

if(ASAN)
  if(NOT CLANG)
    message(FATAL_ERROR "Cannot enable ASAN unless using Clang")
  endif()

  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=address -fsanitize-address-use-after-scope -fno-omit-frame-pointer")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address -fsanitize-address-use-after-scope -fno-omit-frame-pointer")
endif()

if(CFI)
  if(NOT CLANG)
    message(FATAL_ERROR "Cannot enable CFI unless using Clang")
  endif()

  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=cfi -fno-sanitize-trap=cfi -flto=thin")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=cfi -fno-sanitize-trap=cfi -flto=thin")
  # We use Chromium's copy of clang, which requires -fuse-ld=lld if building
  # with -flto. That, in turn, can't handle -ggdb.
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fuse-ld=lld")
  string(REPLACE "-ggdb" "-g" CMAKE_C_FLAGS "${CMAKE_C_FLAGS}")
  string(REPLACE "-ggdb" "-g" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
  # -flto causes object files to contain LLVM bitcode. Mixing those with
  # assembly output in the same static library breaks the linker.
  set(OPENSSL_NO_ASM "1")
endif()

if(TSAN)
  if(NOT CLANG)
    message(FATAL_ERROR "Cannot enable TSAN unless using Clang")
  endif()

  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=thread")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=thread")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=thread")
endif()

if(UBSAN)
  if(NOT CLANG)
    message(FATAL_ERROR "Cannot enable UBSAN unless using Clang")
  endif()

  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=undefined")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=undefined")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=undefined")

  if(NOT UBSAN_RECOVER)
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fno-sanitize-recover=undefined")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-sanitize-recover=undefined")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fno-sanitize-recover=undefined")
  endif()
endif()

if(GCOV)
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} --coverage -O0")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} --coverage -O0")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} --coverage")
endif()

if(KEEP_ASM_LOCAL_SYMBOLS)
  set(CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS} -Wa,-L")
endif()

if(FIPS)

  if(NOT GO_EXECUTABLE OR NOT PERL_EXECUTABLE)
    message(FATAL_ERROR "Building AWS-LC for FIPS requires Go and Perl")
  endif()

  if(NOT BUILD_SHARED_LIBS AND NOT (NOT WIN32 AND NOT APPLE))
    message(FATAL_ERROR "Static FIPS build of AWS-LC is suported only on Linux")
  endif()

  if(WIN32 AND CMAKE_BUILD_TYPE_LOWER STREQUAL "debug")
    message(FATAL_ERROR "Windows Debug build is not supported with FIPS, use Release or RelWithDebInfo")
  endif()

  add_definitions(-DBORINGSSL_FIPS)
  if(FIPS_BREAK_TEST)
    add_definitions("-DBORINGSSL_FIPS_BREAK_${FIPS_BREAK_TEST}=1")
  endif()
  # The FIPS integrity check does not work for ASan and MSan builds.
  if(NOT ASAN AND NOT MSAN)
    if(BUILD_SHARED_LIBS)
      set(FIPS_SHARED "1")
    else()
      set(FIPS_DELOCATE "1")
    endif()
  endif()
  if(FIPS_SHARED AND ANDROID)
    # The Android CMake files set -ffunction-sections and -fdata-sections,
    # which is incompatible with FIPS_SHARED.
    set(CMAKE_C_FLAGS
        "${CMAKE_C_FLAGS} -fno-function-sections -fno-data-sections")
    set(CMAKE_CXX_FLAGS
        "${CMAKE_CXX_FLAGS} -fno-function-sections -fno-data-sections")
  endif()
endif()

if(OPENSSL_SMALL)
  add_definitions(-DOPENSSL_SMALL)
endif()

if(CONSTANT_TIME_VALIDATION)
  add_definitions(-DBORINGSSL_CONSTANT_TIME_VALIDATION)
endif()

# CMake's iOS support uses Apple's multiple-architecture toolchain. It takes an
# architecture list from CMAKE_OSX_ARCHITECTURES, leaves CMAKE_SYSTEM_PROCESSOR
# alone, and expects all architecture-specific logic to be conditioned within
# the source files rather than the build. This does not work for our assembly
# files, so we fix CMAKE_SYSTEM_PROCESSOR and only support single-architecture
# builds.
if(NOT OPENSSL_NO_ASM AND CMAKE_OSX_ARCHITECTURES)
  list(LENGTH CMAKE_OSX_ARCHITECTURES NUM_ARCHES)
  if(NOT NUM_ARCHES EQUAL 1)
    message(FATAL_ERROR "Universal binaries not supported.")
  endif()
  list(GET CMAKE_OSX_ARCHITECTURES 0 CMAKE_SYSTEM_PROCESSOR)
endif()

if(MALLOC_FAILURE_TESTING)
  add_definitions(-DBORINGSSL_MALLOC_FAILURE_TESTING)
endif()

TEST_BIG_ENDIAN(BIG_ENDIAN)

if(OPENSSL_NO_SSE2_FOR_TESTING)
  add_definitions(-DOPENSSL_NO_SSE2_FOR_TESTING)
endif()

if(HOST_ILLUMOS OR HOST_SOLARIS)
  #
  # CMAKE_SYSTEM_PROCESSOR unfortunately comes from the output of "uname -p",
  # which on illumos systems emits "i386".  Instead, use the value from
  # "isainfo -n", which prints "the name of the native instruction set used by
  # portable applications"; e.g., "amd64".
  #
  execute_process(COMMAND /usr/bin/isainfo -n OUTPUT_VARIABLE
    CMAKE_SYSTEM_PROCESSOR_LOWER OUTPUT_STRIP_TRAILING_WHITESPACE)
else()
  # Some consumers might use upper-case (e.g.) "X86" or "X86_64".
  # Matching below is based on lower-case.
  string(TOLOWER "${CMAKE_SYSTEM_PROCESSOR}" CMAKE_SYSTEM_PROCESSOR_LOWER)
endif()

if(OPENSSL_NO_ASM)
  add_definitions(-DOPENSSL_NO_ASM)
  set(ARCH "generic")
elseif(CMAKE_SYSTEM_PROCESSOR_LOWER MATCHES "x86_64|amd64")
  # If ARCH is originally detected as 64-bit, perform an additional check
  # to determine whether to build as 32-bit or 64-bit. This happens in some
  # cases such as when building in Docker, where the host-level architecture is 64-bit
  # but the Docker image should result in building for a 32-bit architecture.
  if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    set(ARCH "x86_64")
  else()
    set(ARCH "x86")
  endif()
elseif(CMAKE_SYSTEM_PROCESSOR_LOWER MATCHES "x86|i386|i686")
  set(ARCH "x86")
elseif(CMAKE_SYSTEM_PROCESSOR_LOWER MATCHES "arm64.*|aarch64")
  # If ARCH is originally detected as 64-bit, perform an additional check
  # to determine whether to build as 32-bit or 64-bit. This happens in some
  # cases such as when building on an 64-bit CPU where the OS is 32-bit.
  if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    set(ARCH "aarch64")
  else()
    set(ARCH "arm")
  endif()
elseif(CMAKE_SYSTEM_PROCESSOR_LOWER MATCHES "^arm*")
  set(ARCH "arm")
elseif(CMAKE_SYSTEM_PROCESSOR_LOWER MATCHES "powerpc64le|ppc64le")
  set(ARCH "ppc64le")
elseif (${CMAKE_SYSTEM_PROCESSOR_LOWER} STREQUAL "riscv64")
  set(ARCH "riscv64")
elseif (${CMAKE_SYSTEM_PROCESSOR_LOWER} STREQUAL "s390x")
  set(ARCH "s390x")
elseif (${CMAKE_SYSTEM_PROCESSOR_LOWER} STREQUAL "loongarch64")
  set(ARCH "loongarch64")
else()
  message(STATUS "Unknown processor found. Using generic implementations. Processor: " ${CMAKE_SYSTEM_PROCESSOR})
  set(ARCH "generic")
endif()

# If target ARCH is 32-bit x86, ensure SSE2 is enabled since it's used by the optimized assembly.
# To build for targets that do not support SSE2, use the `OPENSSL_NO_ASM` flag.
if(ARCH STREQUAL "x86" AND NOT OPENSSL_NO_SSE2_FOR_TESTING)
  # Most compilers enable SSE2 in 32-bit x86 by default, but in some cases GCC and Clang don't.
  # See: https://github.com/aws/aws-lc/commit/6fe8dcbe96e580ea85233fdb98a142e42951b70b
  if(GCC OR CLANG)
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -msse2")
  endif()
endif()

if(ENABLE_DATA_INDEPENDENT_TIMING)
  add_definitions(-DENABLE_AUTO_SET_RESET_DIT)
endif()

if(USE_CUSTOM_LIBCXX)
  if(NOT CLANG)
    message(FATAL_ERROR "USE_CUSTOM_LIBCXX only supported with Clang")
  endif()

  # The docker images set an environment variable to the llvm project directory which the sandbox builds will use,
  # you can also pass in the llvm project path as a CMake parameter which takes precedence over the environment variable
  if(DEFINED ENV{LLVM_PROJECT_HOME} AND NOT LLVM_PROJECT_HOME)
    set(LLVM_PROJECT_HOME $ENV{LLVM_PROJECT_HOME})
  endif()

  if(NOT LLVM_PROJECT_HOME)
    message(FATAL "Could not find path to LLVM project, must set LLVM_PROJECT_HOME environment variable or pass in -DLLVM_PROJECT_HOME")
  endif()

  # CMAKE_CXX_FLAGS ends up in the linker flags as well, so use
  # add_compile_options. There does not appear to be a way to set
  # language-specific compile-only flags.
  add_compile_options("-nostdinc++")
  set(CMAKE_CXX_LINK_FLAGS "${CMAKE_CXX_LINK_FLAGS} -nostdlib++")
  include_directories(
    SYSTEM
    util/bot/libcxx-config
    ${LLVM_PROJECT_HOME}/libcxx/include
    ${LLVM_PROJECT_HOME}/libcxxabi/include
  )

  # This is patterned after buildtools/third_party/libc++/BUILD.gn and
  # buildtools/third_party/libc++abi/BUILD.gn in Chromium.

  file(GLOB LIBCXX_SOURCES "${LLVM_PROJECT_HOME}/libcxx/src/*.cpp" "${LLVM_PROJECT_HOME}/libcxx/src/ryu/*.cpp")
  file(GLOB LIBCXXABI_SOURCES "${LLVM_PROJECT_HOME}/libcxxabi/src/*.cpp")

  # This file is meant for exception-less builds.
  list(REMOVE_ITEM LIBCXXABI_SOURCES "${LLVM_PROJECT_HOME}/libcxxabi/src/cxa_noexception.cpp")

  # libc++ also defines new and delete.
  list(REMOVE_ITEM LIBCXXABI_SOURCES "${LLVM_PROJECT_HOME}/libcxxabi/src/stdlib_new_delete.cpp")
  if(TSAN)
    # ThreadSanitizer tries to intercept these symbols. Skip them to avoid
    # symbol conflicts.
    list(REMOVE_ITEM LIBCXXABI_SOURCES "${LLVM_PROJECT_HOME}/libcxxabi/src/cxa_guard.cpp")
  endif()

  add_library(libcxxabi ${LIBCXXABI_SOURCES})
  target_compile_definitions(
    libcxxabi PRIVATE
    -D_LIBCPP_ENABLE_CXX17_REMOVED_UNEXPECTED_FUNCTIONS
  )

  add_library(libcxx ${LIBCXX_SOURCES})
  if(ASAN OR MSAN OR TSAN)
    # Sanitizers try to intercept new and delete.
    target_compile_definitions(
      libcxx PRIVATE
      -D_LIBCPP_DISABLE_NEW_DELETE_DEFINITIONS
    )
  endif()
  target_compile_definitions(
    libcxx PRIVATE
    -D_LIBCPP_BUILDING_LIBRARY
    -DLIBCXX_BUILDING_LIBCXXABI
  )
  set_target_properties(
    libcxx libcxxabi PROPERTIES
    COMPILE_FLAGS "-Wno-missing-prototypes -Wno-implicit-fallthrough"
    # libc++ and libc++abi must be built in C++20 mode.
    CXX_STANDARD 20
    CXX_STANDARD_REQUIRED TRUE
  )
  # libc++abi depends on libc++ internal headers.
  set_property(TARGET libcxx libcxxabi APPEND PROPERTY INCLUDE_DIRECTORIES "${LLVM_PROJECT_HOME}/libcxx/src")
  target_link_libraries(libcxx libcxxabi)
endif()

if(BUILD_TESTING)
  # Add minimal googletest targets. The provided one has many side-effects, and
  # googletest has a very straightforward build.
  add_library(boringssl_gtest third_party/googletest/src/gtest-all.cc)
  if(USE_CUSTOM_LIBCXX)
    target_link_libraries(boringssl_gtest libcxx)
  endif()
  if(BUILD_SHARED_LIBS)
    # This is needed for the Windows build to correctly annotate GTest's API with __declspec(dllexport)
    target_compile_options(boringssl_gtest PRIVATE -DGTEST_CREATE_SHARED_LIBRARY=1)
  endif()
  target_include_directories(
    boringssl_gtest
    PUBLIC third_party/googletest/include
    PRIVATE third_party/googletest
  )

  # Declare a dummy target to build all unit tests. Test targets should inject
  # themselves as dependencies next to the target definition.
  add_custom_target(all_tests)

  # On Windows, CRYPTO_TEST_DATA is too long to fit in command-line limits.
  # TODO(davidben): CMake 3.12 has a list(JOIN) command. Use that when we've
  # updated the minimum version.
  set(EMBED_TEST_DATA_ARGS "")
  foreach(arg ${CRYPTO_TEST_DATA})
    set(EMBED_TEST_DATA_ARGS "${EMBED_TEST_DATA_ARGS}${arg}\n")
  endforeach()
  file(WRITE "${CMAKE_CURRENT_BINARY_DIR}/embed_test_data_args.txt"
      "${EMBED_TEST_DATA_ARGS}")

  if(GO_EXECUTABLE)
    add_custom_command(
        OUTPUT crypto_test_data.cc
        COMMAND ${GO_EXECUTABLE} run util/embed_test_data.go -file-list
        "${CMAKE_CURRENT_BINARY_DIR}/embed_test_data_args.txt" >
        "${CMAKE_CURRENT_BINARY_DIR}/crypto_test_data.cc"
        DEPENDS util/embed_test_data.go ${CRYPTO_TEST_DATA}
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
  else()
    add_custom_command(
        OUTPUT crypto_test_data.cc
        COMMAND ${CMAKE_COMMAND} -E tar "jxvf" ${GENERATE_CODE_ROOT}/crypto_test_data.cc.tar.bz2
        DEPENDS  ${GENERATE_CODE_ROOT}/crypto_test_data.cc.tar.bz2
        WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}")
  endif()
  add_library(crypto_test_data OBJECT crypto_test_data.cc)

  # sets tests to compile an so executable file for testing in our Android app CI.
  if(ANDROIDTESTRUNNER)
    set(CRYPTO_TEST_EXEC crypto_test.so)
    set(RANDOM_TEST_EXEC urandom_test.so)
    set(SSL_TEST_EXEC ssl_test.so)
    set(MEM_TEST_EXEC mem_test.so)
    set(MEM_SET_TEST_EXEC mem_set_test.so)
    set(INTEGRATION_TEST_EXEC integration_test.so)
    set(DYNAMIC_LOADING_TEST_EXEC dynamic_loading_test.so)
    set(RWLOCK_STATIC_INIT_TEST_EXEC rwlock_static_init.so)
  else()
    set(CRYPTO_TEST_EXEC crypto_test)
    set(RANDOM_TEST_EXEC urandom_test)
    set(SSL_TEST_EXEC ssl_test)
    set(MEM_TEST_EXEC mem_test)
    set(MEM_SET_TEST_EXEC mem_set_test)
    set(INTEGRATION_TEST_EXEC integration_test)
    set(DYNAMIC_LOADING_TEST_EXEC dynamic_loading_test)
    set(RWLOCK_STATIC_INIT_TEST_EXEC rwlock_static_init)
  endif()

  add_subdirectory(util/fipstools/acvp/modulewrapper)

  macro(set_test_location executable_name)
    if(CMAKE_GENERATOR MATCHES "Visual Studio")
      message(NOTICE "Location  for ${executable_name} is: ${CMAKE_CURRENT_BINARY_DIR}")
      # Set the output directory for the executable
      set_target_properties(${executable_name} PROPERTIES
        RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
        RUNTIME_OUTPUT_DIRECTORY_DEBUG "${CMAKE_CURRENT_BINARY_DIR}"
        RUNTIME_OUTPUT_DIRECTORY_RELEASE "${CMAKE_CURRENT_BINARY_DIR}"
        RUNTIME_OUTPUT_DIRECTORY_RELWITHDEBINFO "${CMAKE_CURRENT_BINARY_DIR}"
        RUNTIME_OUTPUT_DIRECTORY_MINSIZEREL "${CMAKE_CURRENT_BINARY_DIR}"
      )
    endif()
  endmacro()
endif()

add_subdirectory(crypto)
if(BUILD_LIBSSL)
  add_subdirectory(ssl)
  if(BUILD_TOOL)
    add_subdirectory(tool)
    add_subdirectory(tool-openssl)
  endif()
endif()
add_subdirectory(util/fipstools)

if(FUZZ)
  if(LIBFUZZER_FROM_DEPS)
    file(GLOB LIBFUZZER_SOURCES "util/bot/libFuzzer/*.cpp")
    add_library(Fuzzer STATIC ${LIBFUZZER_SOURCES})
    # libFuzzer does not pass our aggressive warnings. It also must be built
    # without -fsanitize-coverage options or clang crashes.
    set_target_properties(Fuzzer PROPERTIES COMPILE_FLAGS "-Wno-shadow -Wno-format-nonliteral -Wno-missing-prototypes -fsanitize-coverage=0")
  endif()

  add_subdirectory(fuzz)
endif()


if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  set(HANDSHAKER_ARGS "-handshaker-path" $<TARGET_FILE:handshaker>)
  set(SSL_TRANSFER_ARGS "-ssl-transfer-test-file" ${PROJECT_SOURCE_DIR}/ssl/test/runner/ssl_transfer/test_case_names.txt)
  if(DEFINED ENV{AWS_LC_SSL_RUNNER_START_INDEX})
    set(AWS_LC_SSL_RUNNER_INDEX_FILTER "-test-case-start-index" $ENV{AWS_LC_SSL_RUNNER_START_INDEX})
  endif()
  if(DEFINED ENV{AWS_LC_SSL_RUNNER_END_INDEX})
    set(AWS_LC_SSL_RUNNER_INDEX_FILTER "${AWS_LC_SSL_RUNNER_INDEX_FILTER}" "-test-case-end-index" $ENV{AWS_LC_SSL_RUNNER_END_INDEX})
  endif()
endif()

# Define GO_TEST_TIMEOUT based on env variable.
# This is needed because sanitizer test in aarch64 takes 45 mins, which exceeds `go test` default timeout(10m).
# https://golang.org/pkg/cmd/go/internal/test/
if(DEFINED ENV{AWS_LC_GO_TEST_TIMEOUT})
  set(GO_TEST_TIMEOUT "$ENV{AWS_LC_GO_TEST_TIMEOUT}")
else()
  set(GO_TEST_TIMEOUT "10m")
endif()

if (NOT ${CMAKE_VERSION} VERSION_LESS "3.2")
  # USES_TERMINAL is only available in CMake 3.2 or later.
  set(MAYBE_USES_TERMINAL USES_TERMINAL)
endif()

if(BUILD_TESTING)
  if(GO_EXECUTABLE)
    if(FIPS)
      if(MSVC)
        set(ACVP_TOOL ${PROJECT_BINARY_DIR}/acvptool.exe)
        set(TEST_WRAPPER ${PROJECT_BINARY_DIR}/testmodulewrapper.exe)
      else()
        set(ACVP_TOOL ${PROJECT_BINARY_DIR}/acvptool)
        set(TEST_WRAPPER ${PROJECT_BINARY_DIR}/testmodulewrapper)
      endif()

      # Read util/go_fips_tests.txt into a CMake variable.
      file(READ util/go_fips_tests.txt GO_FIPS_TESTS)
      string(REPLACE "\n" ";" GO_FIPS_TESTS "${GO_FIPS_TESTS}")
      list(REMOVE_ITEM GO_FIPS_TESTS "")
      set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS
        util/go_fips_tests.txt)

      if(MSVC)
        # Delocator doesn't support Windows. So, this test would fail.
        string(REGEX REPLACE "./util/fipstools/delocate" "" GO_FIPS_TESTS "${GO_FIPS_TESTS}")
      endif()

      # We want to run the SHA tests iteratively because they contain Large Data Tests, which make
      # us hash anywhere from 1-8 gigabytes of memory, so running multiple at the same time cause a
      # failure on most machines due to a lack of memory.
      set(acvp_sha_test_commands)
      file(GLOB acvp_sha_tests "${PROJECT_SOURCE_DIR}/util/fipstools/acvp/acvptool/test/sha-tests/*.json")
      foreach(test_path ${acvp_sha_tests})
        get_filename_component(test_name ${test_path} NAME)
        list(APPEND acvp_sha_test_commands
              COMMAND ${GO_EXECUTABLE} run check_expected.go
                        -tool ${ACVP_TOOL}
                        -module-wrappers modulewrapper:$<TARGET_FILE:modulewrapper>,testmodulewrapper:${TEST_WRAPPER}
                        -tests "sha-tests/${test_name}")
      endforeach()

      add_custom_target(
        build_acvp_tool
        COMMAND ${GO_EXECUTABLE} build -o ${ACVP_TOOL}
                boringssl.googlesource.com/boringssl/util/fipstools/acvp/acvptool
        COMMAND ${GO_EXECUTABLE} build -o ${TEST_WRAPPER}
                boringssl.googlesource.com/boringssl/util/fipstools/acvp/acvptool/testmodulewrapper
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        DEPENDS modulewrapper
        ${MAYBE_USES_TERMINAL})

      add_custom_target(
        acvp_tests
        COMMAND ${CMAKE_COMMAND} -E echo
        COMMAND ${CMAKE_COMMAND} -E echo "Running ACVP tests"
        COMMAND ${GO_EXECUTABLE} run check_expected.go
                  -tool ${ACVP_TOOL}
                  -module-wrappers modulewrapper:$<TARGET_FILE:modulewrapper>,testmodulewrapper:${TEST_WRAPPER}
                  -tests tests.json
        ${acvp_sha_test_commands}
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/util/fipstools/acvp/acvptool/test
        DEPENDS build_acvp_tool
        ${MAYBE_USES_TERMINAL})

      add_custom_target(
        fips_specific_tests_if_any
        DEPENDS acvp_tests
      )
    else()
      add_custom_target(fips_specific_tests_if_any)
    endif()

    # Add macho parser tests if FIPS and on MacOS
    if(FIPS AND APPLE)
      add_custom_target(
        macho_parser_tests
        COMMAND ./util/fipstools/inject_hash/macho_parser/tests/test_macho_parser
        WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
        DEPENDS test_macho_parser
      )
      add_dependencies(fips_specific_tests_if_any macho_parser_tests)
    endif()

    # Read util/go_tests.txt into a CMake variable.
    file(READ util/go_tests.txt GO_TESTS)
    foreach(fips_specific_test ${GO_FIPS_TESTS})
      set(GO_TESTS "${GO_TESTS}\n${fips_specific_test}")
    endforeach()
    string(REPLACE "\n" ";" GO_TESTS "${GO_TESTS}")
    list(REMOVE_ITEM GO_TESTS "")
    set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS
      util/go_tests.txt)

    if(BUILD_LIBSSL)
      add_custom_target(
          run_ssl_runner_tests
          COMMAND ${CMAKE_COMMAND} -E echo "Running SSL tests"
          COMMAND cd ssl/test/runner &&
                  ${GO_EXECUTABLE} test -timeout ${GO_TEST_TIMEOUT} -shim-path $<TARGET_FILE:bssl_shim>
                    ${HANDSHAKER_ARGS} ${RUNNER_ARGS} ${AWS_LC_SSL_RUNNER_INDEX_FILTER} ${SSL_TRANSFER_ARGS}
          WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
          DEPENDS bssl_shim handshaker fips_specific_tests_if_any
          ${MAYBE_USES_TERMINAL})

      add_custom_target(
          run_ssl_runner_tests_valgrind
          COMMAND ${CMAKE_COMMAND} -E echo "Running SSL tests"
          COMMAND cd ssl/test/runner &&
          ${GO_EXECUTABLE} test -timeout ${GO_TEST_TIMEOUT} -shim-path $<TARGET_FILE:bssl_shim> -valgrind
          ${HANDSHAKER_ARGS} ${RUNNER_ARGS} ${AWS_LC_SSL_RUNNER_INDEX_FILTER} ${SSL_TRANSFER_ARGS}
          WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
          DEPENDS bssl_shim handshaker fips_specific_tests_if_any
          ${MAYBE_USES_TERMINAL})

      add_custom_target(
          run_tests
          COMMAND ${CMAKE_COMMAND} -E echo
          COMMAND ${CMAKE_COMMAND} -E echo "Running Go tests"
          COMMAND ${GO_EXECUTABLE} test ${GO_TESTS}
          COMMAND ${CMAKE_COMMAND} -E echo
          COMMAND ${CMAKE_COMMAND} -E echo "Running unit tests"
          COMMAND ${GO_EXECUTABLE} run util/all_tests.go -build-dir
                 ${PROJECT_BINARY_DIR}
          WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
          DEPENDS all_tests run_ssl_runner_tests
          ${MAYBE_USES_TERMINAL})
    else()
      add_custom_target(
          run_tests
          COMMAND ${CMAKE_COMMAND} -E echo "Running Go tests"
          COMMAND ${GO_EXECUTABLE} test ${GO_TESTS}
          COMMAND ${CMAKE_COMMAND} -E echo
          COMMAND ${CMAKE_COMMAND} -E echo "Running unit tests"
          COMMAND ${GO_EXECUTABLE} run util/all_tests.go -build-dir
                  ${PROJECT_BINARY_DIR} -ssl-tests=false
          WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
          DEPENDS all_tests fips_specific_tests_if_any
          ${MAYBE_USES_TERMINAL}
      )
    endif()

    add_custom_target(
        run_tests_valgrind
        COMMAND ${GO_EXECUTABLE} run util/all_tests.go -build-dir
                ${PROJECT_BINARY_DIR} -valgrind=true -valgrind-supp-dir="tests/ci"
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        DEPENDS all_tests
        ${MAYBE_USES_TERMINAL})

    add_custom_target(
        run_tests_with_sde
        COMMAND ${GO_EXECUTABLE} run util/all_tests.go -build-dir
                ${PROJECT_BINARY_DIR} -sde=true -sde-path="$ENV{SDEROOT}/sde"
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        DEPENDS all_tests
        ${MAYBE_USES_TERMINAL})
  else()
    if(BUILD_LIBSSL)
      add_custom_target(
          run_minimal_tests
          COMMAND crypto_test
          COMMAND urandom_test
          COMMAND ssl_test
          WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
          DEPENDS all_tests
          ${MAYBE_USES_TERMINAL})
    else()
      add_custom_command(
          run_minimal_tests
          COMMAND crypto_test
          COMMAND urandom_test
          WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
          DEPENDS all_tests
          ${MAYBE_USES_TERMINAL}
      )
    endif()
  endif()
endif()

if(NOT MSVC AND NOT CLANG AND NOT GCC)
  message(STATUS "Alternative compiler '${CMAKE_C_COMPILER_ID}' detected. Not all flags may be set, check final options with 'cmake --build . -- VERBOSE=1'")
endif()

# Parse |OPENSSL_VERSION_NUMBER| in both files and make sure they match.
# |OPENSSL_VERSION_NUMBER| exists in `opensslv.h` only to support
# MySQL's CMake build.
FILE(STRINGS "include/openssl/base.h"
      BASE_VERSION_NUMBER
      REGEX "^#[ ]*define[\t ]+OPENSSL_VERSION_NUMBER[\t ]+0x[0-9].*"
      )
FILE(STRINGS "include/openssl/opensslv.h"
      OPENSSLV_VERSION_NUMBER
      REGEX "^#[ ]*define[\t ]+OPENSSL_VERSION_NUMBER[\t ]+0x[0-9].*"
      )
if(NOT ${BASE_VERSION_NUMBER} MATCHES ${OPENSSLV_VERSION_NUMBER})
  message( FATAL_ERROR "OPENSSL_VERSION_NUMBER in base.h and opensslv.h should match.")
endif()

# TODO: Find a way to make this automatically align with OPENSSL_VERSION_NUMBER in base.h.
set(VERSION 1.1.1)

# AWS-LC may be installed in a non-standard prefix. If OpenSSL exists in the standard path,
# the downstream integration may build with the system's OpenSSL version instead.
# Consider adjusting the PKG_CONFIG_PATH environment to get around this.
file(GLOB OPENSSL_PKGCONFIGS "pkgconfig/*.pc.in")

include(cmake/JoinPaths.cmake)
join_paths(libdir_for_pc_file "\${prefix}" "${CMAKE_INSTALL_LIBDIR}")
join_paths(includedir_for_pc_file "\${prefix}" "${CMAKE_INSTALL_INCLUDEDIR}")

foreach(in_file ${OPENSSL_PKGCONFIGS})
  file(RELATIVE_PATH in_file ${PROJECT_SOURCE_DIR} ${in_file})
  string(REPLACE ".in" "" pc_file ${in_file})
  configure_file(${in_file} ${CMAKE_CURRENT_BINARY_DIR}/${pc_file} @ONLY)
  install(FILES ${CMAKE_CURRENT_BINARY_DIR}/${pc_file} DESTINATION ${CMAKE_INSTALL_LIBDIR}/pkgconfig)
endforeach()
