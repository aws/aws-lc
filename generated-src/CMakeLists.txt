# Copyright (c) 2019 The Chromium Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

# This file is created by generate_build_files.py. Do not edit manually.

cmake_minimum_required(VERSION 3.0)

project(AWSLC LANGUAGES C CXX)

if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  set(CLANG 1)
endif()

if(CMAKE_COMPILER_IS_GNUCXX OR CLANG)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -fvisibility=hidden -fno-common -fno-exceptions -fno-rtti")
  if(APPLE)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
  endif()

  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fvisibility=hidden -fno-common")
  if((CMAKE_C_COMPILER_VERSION VERSION_GREATER "4.8.99") OR CLANG)
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -std=c11")
  else()
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -std=c99")
  endif()
endif()

# pthread_rwlock_t requires a feature flag.
if(NOT WIN32)
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -D_XOPEN_SOURCE=700")
endif()

if(UNIX AND NOT APPLE)
  include(GNUInstallDirs)
elseif(NOT DEFINED CMAKE_INSTALL_LIBDIR)
  set(CMAKE_INSTALL_LIBDIR "lib")
  set(CMAKE_INSTALL_INCLUDEDIR "include")
  set(CMAKE_INSTALL_BINDIR "bin")
endif()

install(DIRECTORY /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/include/openssl
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
        COMPONENT Development
)

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

add_definitions(-DBORINGSSL_IMPLEMENTATION)

# CMake's iOS support uses Apple's multiple-architecture toolchain. It takes an
# architecture list from CMAKE_OSX_ARCHITECTURES, leaves CMAKE_SYSTEM_PROCESSOR
# alone, and expects all architecture-specific logic to be conditioned within
# the source files rather than the build. This does not work for our assembly
# files, so we fix CMAKE_SYSTEM_PROCESSOR and only support single-architecture
# builds.
if(NOT OPENSSL_NO_ASM AND CMAKE_OSX_ARCHITECTURES)
  list(LENGTH CMAKE_OSX_ARCHITECTURES NUM_ARCHES)
  if(NOT ${NUM_ARCHES} EQUAL 1)
    message(FATAL_ERROR "Universal binaries not supported.")
  endif()
  list(GET CMAKE_OSX_ARCHITECTURES 0 CMAKE_SYSTEM_PROCESSOR)
endif()

if(OPENSSL_NO_ASM)
  add_definitions(-DOPENSSL_NO_ASM)
  set(ARCH "generic")
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "x86_64")
  set(ARCH "x86_64")
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "amd64")
  set(ARCH "x86_64")
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "AMD64")
  # cmake reports AMD64 on Windows, but we might be building for 32-bit.
  if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    set(ARCH "x86_64")
  else()
    set(ARCH "x86")
  endif()
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "x86")
  set(ARCH "x86")
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "i386")
  set(ARCH "x86")
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "i686")
  set(ARCH "x86")
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "aarch64")
  set(ARCH "aarch64")
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "arm64")
  set(ARCH "aarch64")
# Apple A12 Bionic chipset which is added in iPhone XS/XS Max/XR uses arm64e architecture.
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "arm64e")
  set(ARCH "aarch64")
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "^arm*")
  set(ARCH "arm")
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "mips")
  # Just to avoid the “unknown processor” error.
  set(ARCH "generic")
elseif(${CMAKE_SYSTEM_PROCESSOR} STREQUAL "ppc64le")
  set(ARCH "ppc64le")
else()
  message(FATAL_ERROR "Unknown processor:" ${CMAKE_SYSTEM_PROCESSOR})
endif()

if(NOT OPENSSL_NO_ASM)
  if(UNIX)
    enable_language(ASM)

    # Clang's integerated assembler does not support debug symbols.
    if(NOT CMAKE_ASM_COMPILER_ID MATCHES "Clang")
      set(CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS} -Wa,-g")
    endif()

    # CMake does not add -isysroot and -arch flags to assembly.
    if(APPLE)
      if(CMAKE_OSX_SYSROOT)
        set(CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS} -isysroot \"${CMAKE_OSX_SYSROOT}\"")
      endif()
      foreach(arch ${CMAKE_OSX_ARCHITECTURES})
        set(CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS} -arch ${arch}")
      endforeach()
    endif()
  else()
    set(CMAKE_ASM_NASM_FLAGS "${CMAKE_ASM_NASM_FLAGS} -gcv8")
    enable_language(ASM_NASM)
  endif()
endif()

if(BUILD_SHARED_LIBS)
  add_definitions(-DBORINGSSL_SHARED_LIBRARY)
  # Enable position-independent code globally. This is needed because
  # some library targets are OBJECT libraries.
  set(CMAKE_POSITION_INDEPENDENT_CODE TRUE)
endif()

include_directories(/home/ANT.AMAZON.COM/kauand/Sync/aws-lc/include)

set(
  CRYPTO_ios_aarch64_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/chacha/chacha-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/aesv8-armx64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/armv8-mont.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/ghash-neon-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/ghashv8-armx64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/p256-armv8-asm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/p256_beeu-armv8-asm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/sha1-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/sha256-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/sha512-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/fipsmodule/vpaes-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-aarch64/crypto/test/trampoline-armv8.S
)

set(
  CRYPTO_ios_arm_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/chacha/chacha-armv4.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/fipsmodule/aesv8-armx32.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/fipsmodule/armv4-mont.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/fipsmodule/bsaes-armv7.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/fipsmodule/ghash-armv4.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/fipsmodule/ghashv8-armx32.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/fipsmodule/sha1-armv4-large.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/fipsmodule/sha256-armv4.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/fipsmodule/sha512-armv4.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/fipsmodule/vpaes-armv7.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/ios-arm/crypto/test/trampoline-armv4.S
)

set(
  CRYPTO_linux_aarch64_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/chacha/chacha-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/aesv8-armx64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/armv8-mont.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/ghash-neon-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/ghashv8-armx64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/p256-armv8-asm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/p256_beeu-armv8-asm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/sha1-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/sha256-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/sha512-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/fipsmodule/vpaes-armv8.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-aarch64/crypto/test/trampoline-armv8.S
)

set(
  CRYPTO_linux_arm_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/curve25519/asm/x25519-asm-arm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/poly1305/asm/poly1305_asm_arm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/chacha/chacha-armv4.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/fipsmodule/aesv8-armx32.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/fipsmodule/armv4-mont.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/fipsmodule/bsaes-armv7.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/fipsmodule/ghash-armv4.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/fipsmodule/ghashv8-armx32.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/fipsmodule/sha1-armv4-large.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/fipsmodule/sha256-armv4.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/fipsmodule/sha512-armv4.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/fipsmodule/vpaes-armv7.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-arm/crypto/test/trampoline-armv4.S
)

set(
  CRYPTO_linux_ppc64le_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-ppc64le/crypto/fipsmodule/aesp8-ppc.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-ppc64le/crypto/fipsmodule/ghashp8-ppc.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-ppc64le/crypto/test/trampoline-ppc.S
)

set(
  CRYPTO_linux_x86_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/chacha/chacha-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/aesni-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/bn-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/co-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/ghash-ssse3-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/ghash-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/md5-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/sha1-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/sha256-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/sha512-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/vpaes-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/fipsmodule/x86-mont.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86/crypto/test/trampoline-x86.S
)

set(
  CRYPTO_linux_x86_64_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/hrss/asm/poly_rq_mul.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/chacha/chacha-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/cipher_extra/aes128gcmsiv-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/cipher_extra/chacha20_poly1305_x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/aesni-gcm-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/aesni-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/ghash-ssse3-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/ghash-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/md5-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/p256-x86_64-asm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/p256_beeu-x86_64-asm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/rdrand-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/rsaz-avx2.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/sha1-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/sha256-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/sha512-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/vpaes-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/x86_64-mont.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/fipsmodule/x86_64-mont5.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/linux-x86_64/crypto/test/trampoline-x86_64.S
)

set(
  CRYPTO_mac_x86_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/chacha/chacha-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/aesni-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/bn-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/co-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/ghash-ssse3-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/ghash-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/md5-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/sha1-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/sha256-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/sha512-586.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/vpaes-x86.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/fipsmodule/x86-mont.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86/crypto/test/trampoline-x86.S
)

set(
  CRYPTO_mac_x86_64_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/chacha/chacha-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/cipher_extra/aes128gcmsiv-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/cipher_extra/chacha20_poly1305_x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/aesni-gcm-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/aesni-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/ghash-ssse3-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/ghash-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/md5-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/p256-x86_64-asm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/p256_beeu-x86_64-asm.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/rdrand-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/rsaz-avx2.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/sha1-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/sha256-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/sha512-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/vpaes-x86_64.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/x86_64-mont.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/fipsmodule/x86_64-mont5.S
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/mac-x86_64/crypto/test/trampoline-x86_64.S
)

set(
  CRYPTO_win_x86_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/chacha/chacha-x86.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/aesni-x86.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/bn-586.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/co-586.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/ghash-ssse3-x86.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/ghash-x86.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/md5-586.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/sha1-586.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/sha256-586.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/sha512-586.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/vpaes-x86.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/fipsmodule/x86-mont.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86/crypto/test/trampoline-x86.asm
)

set(
  CRYPTO_win_x86_64_SOURCES

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/chacha/chacha-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/cipher_extra/aes128gcmsiv-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/cipher_extra/chacha20_poly1305_x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/aesni-gcm-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/aesni-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/ghash-ssse3-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/ghash-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/md5-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/p256-x86_64-asm.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/p256_beeu-x86_64-asm.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/rdrand-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/rsaz-avx2.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/sha1-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/sha256-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/sha512-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/vpaes-x86_64.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/x86_64-mont.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/fipsmodule/x86_64-mont5.asm
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/win-x86_64/crypto/test/trampoline-x86_64.asm
)

if(APPLE AND ${ARCH} STREQUAL "aarch64")
  set(CRYPTO_ARCH_SOURCES ${CRYPTO_ios_aarch64_SOURCES})
elseif(APPLE AND ${ARCH} STREQUAL "arm")
  set(CRYPTO_ARCH_SOURCES ${CRYPTO_ios_arm_SOURCES})
elseif(APPLE)
  set(CRYPTO_ARCH_SOURCES ${CRYPTO_mac_${ARCH}_SOURCES})
elseif(UNIX)
  set(CRYPTO_ARCH_SOURCES ${CRYPTO_linux_${ARCH}_SOURCES})
elseif(WIN32)
  set(CRYPTO_ARCH_SOURCES ${CRYPTO_win_${ARCH}_SOURCES})
endif()

add_library(
  crypto

  ${CRYPTO_ARCH_SOURCES}
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_bitstr.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_bool.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_d2i_fp.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_dup.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_enum.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_gentm.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_i2d_fp.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_int.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_mbstr.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_object.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_octet.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_print.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_strnid.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_time.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_type.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_utctm.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/a_utf8.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/asn1_lib.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/asn1_par.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/asn_pack.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/f_enum.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/f_int.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/f_string.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/tasn_dec.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/tasn_enc.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/tasn_fre.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/tasn_new.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/tasn_typ.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/tasn_utl.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/asn1/time_support.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/base64/base64.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/bio.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/bio_mem.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/connect.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/fd.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/file.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/hexdump.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/pair.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/printf.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/socket.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bio/socket_helper.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bn_extra/bn_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bn_extra/convert.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/buf/buf.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bytestring/asn1_compat.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bytestring/ber.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bytestring/cbb.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bytestring/cbs.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/bytestring/unicode.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/chacha/chacha.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/cipher_extra.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/derive_key.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/e_aesccm.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/e_aesctrhmac.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/e_aesgcmsiv.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/e_chacha20poly1305.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/e_null.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/e_rc2.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/e_rc4.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/e_tls.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cipher_extra/tls_cbc.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cmac/cmac.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/conf/conf.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cpu-aarch64-fuchsia.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cpu-aarch64-linux.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cpu-arm-linux.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cpu-arm.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cpu-intel.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/cpu-ppc64le.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/crypto.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/curve25519/curve25519.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/curve25519/spake25519.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/dh/check.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/dh/dh.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/dh/dh_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/dh/params.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/digest_extra/digest_extra.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/dsa/dsa.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/dsa/dsa_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/ec_extra/ec_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/ec_extra/ec_derive.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/ec_extra/hash_to_curve.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/ecdh_extra/ecdh_extra.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/ecdsa_extra/ecdsa_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/engine/engine.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/err/err.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/digestsign.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/evp.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/evp_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/evp_ctx.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/p_dsa_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/p_ec.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/p_ec_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/p_ed25519.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/p_ed25519_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/p_rsa.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/p_rsa_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/p_x25519.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/p_x25519_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/pbkdf.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/print.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/scrypt.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/evp/sign.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/ex_data.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/fipsmodule/bcm.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/fipsmodule/fips_shared_support.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/fipsmodule/is_fips.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/hkdf/hkdf.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/hpke/hpke.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/hrss/hrss.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/lhash/lhash.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/mem.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/obj/obj.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/obj/obj_xref.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pem/pem_all.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pem/pem_info.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pem/pem_lib.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pem/pem_oth.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pem/pem_pk8.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pem/pem_pkey.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pem/pem_x509.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pem/pem_xaux.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pkcs7/pkcs7.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pkcs7/pkcs7_x509.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pkcs8/p5_pbev2.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pkcs8/pkcs8.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pkcs8/pkcs8_x509.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/poly1305/poly1305.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/poly1305/poly1305_arm.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/poly1305/poly1305_vec.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/pool/pool.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/rand_extra/deterministic.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/rand_extra/forkunsafe.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/rand_extra/fuchsia.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/rand_extra/rand_extra.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/rand_extra/windows.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/rc4/rc4.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/refcount_c11.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/refcount_lock.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/rsa_extra/rsa_asn1.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/rsa_extra/rsa_print.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/siphash/siphash.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/stack/stack.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/thread.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/thread_none.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/thread_pthread.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/thread_win.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/trust_token/pmbtoken.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/trust_token/trust_token.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/trust_token/voprf.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/a_digest.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/a_sign.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/a_strex.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/a_verify.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/algorithm.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/asn1_gen.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/by_dir.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/by_file.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/i2d_pr.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/rsa_pss.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/t_crl.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/t_req.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/t_x509.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/t_x509a.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_att.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_cmp.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_d2.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_def.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_ext.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_lu.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_obj.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_r2x.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_req.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_set.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_trs.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_txt.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_v3.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_vfy.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509_vpm.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509cset.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509name.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509rset.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x509spki.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_algor.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_all.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_attrib.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_crl.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_exten.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_info.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_name.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_pkey.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_pubkey.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_req.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_sig.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_spki.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_val.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_x509.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509/x_x509a.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/pcy_cache.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/pcy_data.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/pcy_lib.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/pcy_map.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/pcy_node.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/pcy_tree.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_akey.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_akeya.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_alt.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_bcons.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_bitst.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_conf.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_cpols.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_crld.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_enum.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_extku.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_genn.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_ia5.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_info.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_int.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_lib.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_ncons.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_ocsp.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_pci.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_pcia.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_pcons.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_pmaps.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_prn.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_purp.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_skey.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/crypto/x509v3/v3_utl.c
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/generated-src/err_data.c
)

add_library(
  ssl

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/bio_ssl.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/d1_both.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/d1_lib.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/d1_pkt.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/d1_srtp.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/dtls_method.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/dtls_record.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/handoff.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/handshake.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/handshake_client.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/handshake_server.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/s3_both.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/s3_lib.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/s3_pkt.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_aead_ctx.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_asn1.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_buffer.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_cert.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_cipher.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_file.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_key_share.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_lib.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_privkey.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_session.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_stat.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_transcript.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_versions.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/ssl_x509.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/t1_enc.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/t1_lib.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/tls13_both.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/tls13_client.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/tls13_enc.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/tls13_server.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/tls_method.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/ssl/tls_record.cc
)

add_executable(
  bssl

  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/args.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/ciphers.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/client.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/const.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/digest.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/fd.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/file.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/generate_ed25519.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/genrsa.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/pkcs12.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/rand.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/server.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/sign.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/speed.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/tool.cc
  /home/ANT.AMAZON.COM/kauand/Sync/aws-lc/tool/transport_common.cc
)

target_link_libraries(bssl ssl crypto)

if(NOT WIN32 AND NOT ANDROID)
  target_link_libraries(crypto pthread)
endif()

if(WIN32)
  target_link_libraries(bssl ws2_32)
endif()

install(TARGETS crypto
        EXPORT crypto-targets
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)

install(TARGETS ssl
        EXPORT ssl-targets
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)

install(TARGETS bssl
        EXPORT bssl-targets
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)
