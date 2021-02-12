# Copyright (c) 2019 The Chromium Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

# This file is created by generate_build_files.py. Do not edit manually.

cmake_minimum_required(VERSION 3.0)

project(AWSLC LANGUAGES C CXX)

# Fail CMake build when some vulnerable gcc versions are used.
set(VUL_GCC_VERSIONS "")
# These versions are disabled due to a bug reported in memcmp, which means we can't trust them.
# https://gcc.gnu.org/bugzilla/show_bug.cgi?id=95189
list(APPEND VUL_GCC_VERSIONS "9.2" "9.3" "10.1")
if(CMAKE_COMPILER_IS_GNUCXX)
  foreach(vul_gcc_version ${VUL_GCC_VERSIONS})
    if("${vul_gcc_version}" VERSION_EQUAL CMAKE_C_COMPILER_VERSION)
      message(FATAL_ERROR "GCC ${CMAKE_C_COMPILER_VERSION} is not supported.")
    endif()
  endforeach()
endif()

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

install(DIRECTORY ../include/openssl
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

if (ARCH STREQUAL "aarch64" AND CMAKE_BUILD_TYPE_LOWER MATCHES "rel")
  # Enable p256_nistz on ARMv8 (AArch64) by default
  add_definitions(-DOPENSSL_AARCH64_P256)
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

include_directories(../include)

set(
  CRYPTO_ios_aarch64_SOURCES

  ios-aarch64/crypto/chacha/chacha-armv8.S
  ios-aarch64/crypto/fipsmodule/aesv8-armx64.S
  ios-aarch64/crypto/fipsmodule/armv8-mont.S
  ios-aarch64/crypto/fipsmodule/ghash-neon-armv8.S
  ios-aarch64/crypto/fipsmodule/ghashv8-armx64.S
  ios-aarch64/crypto/fipsmodule/p256-armv8-asm.S
  ios-aarch64/crypto/fipsmodule/p256_beeu-armv8-asm.S
  ios-aarch64/crypto/fipsmodule/sha1-armv8.S
  ios-aarch64/crypto/fipsmodule/sha256-armv8.S
  ios-aarch64/crypto/fipsmodule/sha512-armv8.S
  ios-aarch64/crypto/fipsmodule/vpaes-armv8.S
  ios-aarch64/crypto/test/trampoline-armv8.S
)

set(
  CRYPTO_ios_arm_SOURCES

  ios-arm/crypto/chacha/chacha-armv4.S
  ios-arm/crypto/fipsmodule/aesv8-armx32.S
  ios-arm/crypto/fipsmodule/armv4-mont.S
  ios-arm/crypto/fipsmodule/bsaes-armv7.S
  ios-arm/crypto/fipsmodule/ghash-armv4.S
  ios-arm/crypto/fipsmodule/ghashv8-armx32.S
  ios-arm/crypto/fipsmodule/sha1-armv4-large.S
  ios-arm/crypto/fipsmodule/sha256-armv4.S
  ios-arm/crypto/fipsmodule/sha512-armv4.S
  ios-arm/crypto/fipsmodule/vpaes-armv7.S
  ios-arm/crypto/test/trampoline-armv4.S
)

set(
  CRYPTO_linux_aarch64_SOURCES

  linux-aarch64/crypto/chacha/chacha-armv8.S
  linux-aarch64/crypto/fipsmodule/aesv8-armx64.S
  linux-aarch64/crypto/fipsmodule/armv8-mont.S
  linux-aarch64/crypto/fipsmodule/ghash-neon-armv8.S
  linux-aarch64/crypto/fipsmodule/ghashv8-armx64.S
  linux-aarch64/crypto/fipsmodule/p256-armv8-asm.S
  linux-aarch64/crypto/fipsmodule/p256_beeu-armv8-asm.S
  linux-aarch64/crypto/fipsmodule/sha1-armv8.S
  linux-aarch64/crypto/fipsmodule/sha256-armv8.S
  linux-aarch64/crypto/fipsmodule/sha512-armv8.S
  linux-aarch64/crypto/fipsmodule/vpaes-armv8.S
  linux-aarch64/crypto/test/trampoline-armv8.S
)

set(
  CRYPTO_linux_arm_SOURCES

  ../crypto/curve25519/asm/x25519-asm-arm.S
  ../crypto/poly1305/asm/poly1305_asm_arm.S
  linux-arm/crypto/chacha/chacha-armv4.S
  linux-arm/crypto/fipsmodule/aesv8-armx32.S
  linux-arm/crypto/fipsmodule/armv4-mont.S
  linux-arm/crypto/fipsmodule/bsaes-armv7.S
  linux-arm/crypto/fipsmodule/ghash-armv4.S
  linux-arm/crypto/fipsmodule/ghashv8-armx32.S
  linux-arm/crypto/fipsmodule/sha1-armv4-large.S
  linux-arm/crypto/fipsmodule/sha256-armv4.S
  linux-arm/crypto/fipsmodule/sha512-armv4.S
  linux-arm/crypto/fipsmodule/vpaes-armv7.S
  linux-arm/crypto/test/trampoline-armv4.S
)

set(
  CRYPTO_linux_ppc64le_SOURCES

  linux-ppc64le/crypto/fipsmodule/aesp8-ppc.S
  linux-ppc64le/crypto/fipsmodule/ghashp8-ppc.S
  linux-ppc64le/crypto/test/trampoline-ppc.S
)

set(
  CRYPTO_linux_x86_SOURCES

  linux-x86/crypto/chacha/chacha-x86.S
  linux-x86/crypto/fipsmodule/aesni-x86.S
  linux-x86/crypto/fipsmodule/bn-586.S
  linux-x86/crypto/fipsmodule/co-586.S
  linux-x86/crypto/fipsmodule/ghash-ssse3-x86.S
  linux-x86/crypto/fipsmodule/ghash-x86.S
  linux-x86/crypto/fipsmodule/md5-586.S
  linux-x86/crypto/fipsmodule/sha1-586.S
  linux-x86/crypto/fipsmodule/sha256-586.S
  linux-x86/crypto/fipsmodule/sha512-586.S
  linux-x86/crypto/fipsmodule/vpaes-x86.S
  linux-x86/crypto/fipsmodule/x86-mont.S
  linux-x86/crypto/test/trampoline-x86.S
)

set(
  CRYPTO_linux_x86_64_SOURCES

  ../crypto/hrss/asm/poly_rq_mul.S
  linux-x86_64/crypto/chacha/chacha-x86_64.S
  linux-x86_64/crypto/cipher_extra/aes128gcmsiv-x86_64.S
  linux-x86_64/crypto/cipher_extra/chacha20_poly1305_x86_64.S
  linux-x86_64/crypto/fipsmodule/aesni-gcm-x86_64.S
  linux-x86_64/crypto/fipsmodule/aesni-x86_64.S
  linux-x86_64/crypto/fipsmodule/ghash-ssse3-x86_64.S
  linux-x86_64/crypto/fipsmodule/ghash-x86_64.S
  linux-x86_64/crypto/fipsmodule/md5-x86_64.S
  linux-x86_64/crypto/fipsmodule/p256-x86_64-asm.S
  linux-x86_64/crypto/fipsmodule/p256_beeu-x86_64-asm.S
  linux-x86_64/crypto/fipsmodule/rdrand-x86_64.S
  linux-x86_64/crypto/fipsmodule/rsaz-avx2.S
  linux-x86_64/crypto/fipsmodule/sha1-x86_64.S
  linux-x86_64/crypto/fipsmodule/sha256-x86_64.S
  linux-x86_64/crypto/fipsmodule/sha512-x86_64.S
  linux-x86_64/crypto/fipsmodule/vpaes-x86_64.S
  linux-x86_64/crypto/fipsmodule/x86_64-mont.S
  linux-x86_64/crypto/fipsmodule/x86_64-mont5.S
  linux-x86_64/crypto/test/trampoline-x86_64.S
)

set(
  CRYPTO_mac_x86_SOURCES

  mac-x86/crypto/chacha/chacha-x86.S
  mac-x86/crypto/fipsmodule/aesni-x86.S
  mac-x86/crypto/fipsmodule/bn-586.S
  mac-x86/crypto/fipsmodule/co-586.S
  mac-x86/crypto/fipsmodule/ghash-ssse3-x86.S
  mac-x86/crypto/fipsmodule/ghash-x86.S
  mac-x86/crypto/fipsmodule/md5-586.S
  mac-x86/crypto/fipsmodule/sha1-586.S
  mac-x86/crypto/fipsmodule/sha256-586.S
  mac-x86/crypto/fipsmodule/sha512-586.S
  mac-x86/crypto/fipsmodule/vpaes-x86.S
  mac-x86/crypto/fipsmodule/x86-mont.S
  mac-x86/crypto/test/trampoline-x86.S
)

set(
  CRYPTO_mac_x86_64_SOURCES

  mac-x86_64/crypto/chacha/chacha-x86_64.S
  mac-x86_64/crypto/cipher_extra/aes128gcmsiv-x86_64.S
  mac-x86_64/crypto/cipher_extra/chacha20_poly1305_x86_64.S
  mac-x86_64/crypto/fipsmodule/aesni-gcm-x86_64.S
  mac-x86_64/crypto/fipsmodule/aesni-x86_64.S
  mac-x86_64/crypto/fipsmodule/ghash-ssse3-x86_64.S
  mac-x86_64/crypto/fipsmodule/ghash-x86_64.S
  mac-x86_64/crypto/fipsmodule/md5-x86_64.S
  mac-x86_64/crypto/fipsmodule/p256-x86_64-asm.S
  mac-x86_64/crypto/fipsmodule/p256_beeu-x86_64-asm.S
  mac-x86_64/crypto/fipsmodule/rdrand-x86_64.S
  mac-x86_64/crypto/fipsmodule/rsaz-avx2.S
  mac-x86_64/crypto/fipsmodule/sha1-x86_64.S
  mac-x86_64/crypto/fipsmodule/sha256-x86_64.S
  mac-x86_64/crypto/fipsmodule/sha512-x86_64.S
  mac-x86_64/crypto/fipsmodule/vpaes-x86_64.S
  mac-x86_64/crypto/fipsmodule/x86_64-mont.S
  mac-x86_64/crypto/fipsmodule/x86_64-mont5.S
  mac-x86_64/crypto/test/trampoline-x86_64.S
)

set(
  CRYPTO_win_x86_SOURCES

  win-x86/crypto/chacha/chacha-x86.asm
  win-x86/crypto/fipsmodule/aesni-x86.asm
  win-x86/crypto/fipsmodule/bn-586.asm
  win-x86/crypto/fipsmodule/co-586.asm
  win-x86/crypto/fipsmodule/ghash-ssse3-x86.asm
  win-x86/crypto/fipsmodule/ghash-x86.asm
  win-x86/crypto/fipsmodule/md5-586.asm
  win-x86/crypto/fipsmodule/sha1-586.asm
  win-x86/crypto/fipsmodule/sha256-586.asm
  win-x86/crypto/fipsmodule/sha512-586.asm
  win-x86/crypto/fipsmodule/vpaes-x86.asm
  win-x86/crypto/fipsmodule/x86-mont.asm
  win-x86/crypto/test/trampoline-x86.asm
)

set(
  CRYPTO_win_x86_64_SOURCES

  win-x86_64/crypto/chacha/chacha-x86_64.asm
  win-x86_64/crypto/cipher_extra/aes128gcmsiv-x86_64.asm
  win-x86_64/crypto/cipher_extra/chacha20_poly1305_x86_64.asm
  win-x86_64/crypto/fipsmodule/aesni-gcm-x86_64.asm
  win-x86_64/crypto/fipsmodule/aesni-x86_64.asm
  win-x86_64/crypto/fipsmodule/ghash-ssse3-x86_64.asm
  win-x86_64/crypto/fipsmodule/ghash-x86_64.asm
  win-x86_64/crypto/fipsmodule/md5-x86_64.asm
  win-x86_64/crypto/fipsmodule/p256-x86_64-asm.asm
  win-x86_64/crypto/fipsmodule/p256_beeu-x86_64-asm.asm
  win-x86_64/crypto/fipsmodule/rdrand-x86_64.asm
  win-x86_64/crypto/fipsmodule/rsaz-avx2.asm
  win-x86_64/crypto/fipsmodule/sha1-x86_64.asm
  win-x86_64/crypto/fipsmodule/sha256-x86_64.asm
  win-x86_64/crypto/fipsmodule/sha512-x86_64.asm
  win-x86_64/crypto/fipsmodule/vpaes-x86_64.asm
  win-x86_64/crypto/fipsmodule/x86_64-mont.asm
  win-x86_64/crypto/fipsmodule/x86_64-mont5.asm
  win-x86_64/crypto/test/trampoline-x86_64.asm
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
  ../crypto/asn1/a_bitstr.c
  ../crypto/asn1/a_bool.c
  ../crypto/asn1/a_d2i_fp.c
  ../crypto/asn1/a_dup.c
  ../crypto/asn1/a_enum.c
  ../crypto/asn1/a_gentm.c
  ../crypto/asn1/a_i2d_fp.c
  ../crypto/asn1/a_int.c
  ../crypto/asn1/a_mbstr.c
  ../crypto/asn1/a_object.c
  ../crypto/asn1/a_octet.c
  ../crypto/asn1/a_print.c
  ../crypto/asn1/a_strnid.c
  ../crypto/asn1/a_time.c
  ../crypto/asn1/a_type.c
  ../crypto/asn1/a_utctm.c
  ../crypto/asn1/a_utf8.c
  ../crypto/asn1/asn1_lib.c
  ../crypto/asn1/asn1_par.c
  ../crypto/asn1/asn_pack.c
  ../crypto/asn1/f_enum.c
  ../crypto/asn1/f_int.c
  ../crypto/asn1/f_string.c
  ../crypto/asn1/tasn_dec.c
  ../crypto/asn1/tasn_enc.c
  ../crypto/asn1/tasn_fre.c
  ../crypto/asn1/tasn_new.c
  ../crypto/asn1/tasn_typ.c
  ../crypto/asn1/tasn_utl.c
  ../crypto/asn1/time_support.c
  ../crypto/base64/base64.c
  ../crypto/bio/bio.c
  ../crypto/bio/bio_mem.c
  ../crypto/bio/connect.c
  ../crypto/bio/fd.c
  ../crypto/bio/file.c
  ../crypto/bio/hexdump.c
  ../crypto/bio/pair.c
  ../crypto/bio/printf.c
  ../crypto/bio/socket.c
  ../crypto/bio/socket_helper.c
  ../crypto/bn_extra/bn_asn1.c
  ../crypto/bn_extra/convert.c
  ../crypto/buf/buf.c
  ../crypto/bytestring/asn1_compat.c
  ../crypto/bytestring/ber.c
  ../crypto/bytestring/cbb.c
  ../crypto/bytestring/cbs.c
  ../crypto/bytestring/unicode.c
  ../crypto/chacha/chacha.c
  ../crypto/cipher_extra/cipher_extra.c
  ../crypto/cipher_extra/derive_key.c
  ../crypto/cipher_extra/e_aesccm.c
  ../crypto/cipher_extra/e_aesctrhmac.c
  ../crypto/cipher_extra/e_aesgcmsiv.c
  ../crypto/cipher_extra/e_chacha20poly1305.c
  ../crypto/cipher_extra/e_null.c
  ../crypto/cipher_extra/e_rc2.c
  ../crypto/cipher_extra/e_rc4.c
  ../crypto/cipher_extra/e_tls.c
  ../crypto/cipher_extra/tls_cbc.c
  ../crypto/cmac/cmac.c
  ../crypto/conf/conf.c
  ../crypto/cpu-aarch64-fuchsia.c
  ../crypto/cpu-aarch64-linux.c
  ../crypto/cpu-arm-linux.c
  ../crypto/cpu-arm.c
  ../crypto/cpu-intel.c
  ../crypto/cpu-ppc64le.c
  ../crypto/crypto.c
  ../crypto/curve25519/curve25519.c
  ../crypto/curve25519/spake25519.c
  ../crypto/dh/check.c
  ../crypto/dh/dh.c
  ../crypto/dh/dh_asn1.c
  ../crypto/dh/params.c
  ../crypto/digest_extra/digest_extra.c
  ../crypto/dsa/dsa.c
  ../crypto/dsa/dsa_asn1.c
  ../crypto/ec_extra/ec_asn1.c
  ../crypto/ec_extra/ec_derive.c
  ../crypto/ec_extra/hash_to_curve.c
  ../crypto/ecdh_extra/ecdh_extra.c
  ../crypto/ecdsa_extra/ecdsa_asn1.c
  ../crypto/engine/engine.c
  ../crypto/err/err.c
  ../crypto/evp/digestsign.c
  ../crypto/evp/evp.c
  ../crypto/evp/evp_asn1.c
  ../crypto/evp/evp_ctx.c
  ../crypto/evp/p_dsa_asn1.c
  ../crypto/evp/p_ec.c
  ../crypto/evp/p_ec_asn1.c
  ../crypto/evp/p_ed25519.c
  ../crypto/evp/p_ed25519_asn1.c
  ../crypto/evp/p_rsa.c
  ../crypto/evp/p_rsa_asn1.c
  ../crypto/evp/p_x25519.c
  ../crypto/evp/p_x25519_asn1.c
  ../crypto/evp/pbkdf.c
  ../crypto/evp/print.c
  ../crypto/evp/scrypt.c
  ../crypto/evp/sign.c
  ../crypto/ex_data.c
  ../crypto/fipsmodule/bcm.c
  ../crypto/fipsmodule/fips_shared_support.c
  ../crypto/fipsmodule/is_fips.c
  ../crypto/hkdf/hkdf.c
  ../crypto/hpke/hpke.c
  ../crypto/hrss/hrss.c
  ../crypto/lhash/lhash.c
  ../crypto/mem.c
  ../crypto/obj/obj.c
  ../crypto/obj/obj_xref.c
  ../crypto/pem/pem_all.c
  ../crypto/pem/pem_info.c
  ../crypto/pem/pem_lib.c
  ../crypto/pem/pem_oth.c
  ../crypto/pem/pem_pk8.c
  ../crypto/pem/pem_pkey.c
  ../crypto/pem/pem_x509.c
  ../crypto/pem/pem_xaux.c
  ../crypto/pkcs7/pkcs7.c
  ../crypto/pkcs7/pkcs7_x509.c
  ../crypto/pkcs8/p5_pbev2.c
  ../crypto/pkcs8/pkcs8.c
  ../crypto/pkcs8/pkcs8_x509.c
  ../crypto/poly1305/poly1305.c
  ../crypto/poly1305/poly1305_arm.c
  ../crypto/poly1305/poly1305_vec.c
  ../crypto/pool/pool.c
  ../crypto/rand_extra/deterministic.c
  ../crypto/rand_extra/forkunsafe.c
  ../crypto/rand_extra/fuchsia.c
  ../crypto/rand_extra/rand_extra.c
  ../crypto/rand_extra/windows.c
  ../crypto/rc4/rc4.c
  ../crypto/refcount_c11.c
  ../crypto/refcount_lock.c
  ../crypto/rsa_extra/rsa_asn1.c
  ../crypto/rsa_extra/rsa_print.c
  ../crypto/siphash/siphash.c
  ../crypto/stack/stack.c
  ../crypto/thread.c
  ../crypto/thread_none.c
  ../crypto/thread_pthread.c
  ../crypto/thread_win.c
  ../crypto/trust_token/pmbtoken.c
  ../crypto/trust_token/trust_token.c
  ../crypto/trust_token/voprf.c
  ../crypto/x509/a_digest.c
  ../crypto/x509/a_sign.c
  ../crypto/x509/a_strex.c
  ../crypto/x509/a_verify.c
  ../crypto/x509/algorithm.c
  ../crypto/x509/asn1_gen.c
  ../crypto/x509/by_dir.c
  ../crypto/x509/by_file.c
  ../crypto/x509/i2d_pr.c
  ../crypto/x509/rsa_pss.c
  ../crypto/x509/t_crl.c
  ../crypto/x509/t_req.c
  ../crypto/x509/t_x509.c
  ../crypto/x509/t_x509a.c
  ../crypto/x509/x509.c
  ../crypto/x509/x509_att.c
  ../crypto/x509/x509_cmp.c
  ../crypto/x509/x509_d2.c
  ../crypto/x509/x509_def.c
  ../crypto/x509/x509_ext.c
  ../crypto/x509/x509_lu.c
  ../crypto/x509/x509_obj.c
  ../crypto/x509/x509_r2x.c
  ../crypto/x509/x509_req.c
  ../crypto/x509/x509_set.c
  ../crypto/x509/x509_trs.c
  ../crypto/x509/x509_txt.c
  ../crypto/x509/x509_v3.c
  ../crypto/x509/x509_vfy.c
  ../crypto/x509/x509_vpm.c
  ../crypto/x509/x509cset.c
  ../crypto/x509/x509name.c
  ../crypto/x509/x509rset.c
  ../crypto/x509/x509spki.c
  ../crypto/x509/x_algor.c
  ../crypto/x509/x_all.c
  ../crypto/x509/x_attrib.c
  ../crypto/x509/x_crl.c
  ../crypto/x509/x_exten.c
  ../crypto/x509/x_info.c
  ../crypto/x509/x_name.c
  ../crypto/x509/x_pkey.c
  ../crypto/x509/x_pubkey.c
  ../crypto/x509/x_req.c
  ../crypto/x509/x_sig.c
  ../crypto/x509/x_spki.c
  ../crypto/x509/x_val.c
  ../crypto/x509/x_x509.c
  ../crypto/x509/x_x509a.c
  ../crypto/x509v3/pcy_cache.c
  ../crypto/x509v3/pcy_data.c
  ../crypto/x509v3/pcy_lib.c
  ../crypto/x509v3/pcy_map.c
  ../crypto/x509v3/pcy_node.c
  ../crypto/x509v3/pcy_tree.c
  ../crypto/x509v3/v3_akey.c
  ../crypto/x509v3/v3_akeya.c
  ../crypto/x509v3/v3_alt.c
  ../crypto/x509v3/v3_bcons.c
  ../crypto/x509v3/v3_bitst.c
  ../crypto/x509v3/v3_conf.c
  ../crypto/x509v3/v3_cpols.c
  ../crypto/x509v3/v3_crld.c
  ../crypto/x509v3/v3_enum.c
  ../crypto/x509v3/v3_extku.c
  ../crypto/x509v3/v3_genn.c
  ../crypto/x509v3/v3_ia5.c
  ../crypto/x509v3/v3_info.c
  ../crypto/x509v3/v3_int.c
  ../crypto/x509v3/v3_lib.c
  ../crypto/x509v3/v3_ncons.c
  ../crypto/x509v3/v3_ocsp.c
  ../crypto/x509v3/v3_pci.c
  ../crypto/x509v3/v3_pcia.c
  ../crypto/x509v3/v3_pcons.c
  ../crypto/x509v3/v3_pmaps.c
  ../crypto/x509v3/v3_prn.c
  ../crypto/x509v3/v3_purp.c
  ../crypto/x509v3/v3_skey.c
  ../crypto/x509v3/v3_utl.c
  err_data.c
)

add_library(
  ssl

  ../ssl/bio_ssl.cc
  ../ssl/d1_both.cc
  ../ssl/d1_lib.cc
  ../ssl/d1_pkt.cc
  ../ssl/d1_srtp.cc
  ../ssl/dtls_method.cc
  ../ssl/dtls_record.cc
  ../ssl/handoff.cc
  ../ssl/handshake.cc
  ../ssl/handshake_client.cc
  ../ssl/handshake_server.cc
  ../ssl/s3_both.cc
  ../ssl/s3_lib.cc
  ../ssl/s3_pkt.cc
  ../ssl/ssl_aead_ctx.cc
  ../ssl/ssl_asn1.cc
  ../ssl/ssl_buffer.cc
  ../ssl/ssl_cert.cc
  ../ssl/ssl_cipher.cc
  ../ssl/ssl_file.cc
  ../ssl/ssl_key_share.cc
  ../ssl/ssl_lib.cc
  ../ssl/ssl_privkey.cc
  ../ssl/ssl_session.cc
  ../ssl/ssl_stat.cc
  ../ssl/ssl_transcript.cc
  ../ssl/ssl_versions.cc
  ../ssl/ssl_x509.cc
  ../ssl/t1_enc.cc
  ../ssl/t1_lib.cc
  ../ssl/tls13_both.cc
  ../ssl/tls13_client.cc
  ../ssl/tls13_enc.cc
  ../ssl/tls13_server.cc
  ../ssl/tls_method.cc
  ../ssl/tls_record.cc
)

add_executable(
  bssl

  ../tool/args.cc
  ../tool/ciphers.cc
  ../tool/client.cc
  ../tool/const.cc
  ../tool/digest.cc
  ../tool/fd.cc
  ../tool/file.cc
  ../tool/generate_ed25519.cc
  ../tool/genrsa.cc
  ../tool/pkcs12.cc
  ../tool/rand.cc
  ../tool/server.cc
  ../tool/sign.cc
  ../tool/speed.cc
  ../tool/tool.cc
  ../tool/transport_common.cc
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
