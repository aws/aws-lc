include_directories(../../include)

if(ANDROID)
  # Since "--Wa,--noexecstack" is not used during the preprocessor step of Android (because assembler is not invoked),
  # Clang reports that argument as unused. We remove the flag only for the FIPS build of Android.
  string(FIND ${CMAKE_CXX_FLAGS} "noexecstack" CXX_EXTRA_WA)
  string(FIND ${CMAKE_C_FLAGS} "noexecstack" C_EXTRA_WA)
  if(NOT ${CXX_EXTRA_WA} EQUAL '-1')
    string( REPLACE "-Wa,--noexecstack" "" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}" )
  endif()
  if(NOT ${C_EXTRA_WA} EQUAL '-1')
    string( REPLACE "-Wa,--noexecstack" "" CMAKE_C_FLAGS "${CMAKE_C_FLAGS}" )
  endif()
endif()

if(ARCH STREQUAL "x86_64")
  set(
    BCM_ASM_SOURCES

    aesni-gcm-x86_64.${ASM_EXT}
    aesni-x86_64.${ASM_EXT}
    ghash-ssse3-x86_64.${ASM_EXT}
    ghash-x86_64.${ASM_EXT}
    md5-x86_64.${ASM_EXT}
    p256-x86_64-asm.${ASM_EXT}
    p256_beeu-x86_64-asm.${ASM_EXT}
    rdrand-x86_64.${ASM_EXT}
    rsaz-avx2.${ASM_EXT}
    sha1-x86_64.${ASM_EXT}
    sha256-x86_64.${ASM_EXT}
    sha512-x86_64.${ASM_EXT}
    vpaes-x86_64.${ASM_EXT}
    x86_64-mont5.${ASM_EXT}
    x86_64-mont.${ASM_EXT}
  )
endif()

if(ARCH STREQUAL "x86")
  set(
    BCM_ASM_SOURCES

    aesni-x86.${ASM_EXT}
    bn-586.${ASM_EXT}
    co-586.${ASM_EXT}
    ghash-ssse3-x86.${ASM_EXT}
    ghash-x86.${ASM_EXT}
    md5-586.${ASM_EXT}
    sha1-586.${ASM_EXT}
    sha256-586.${ASM_EXT}
    sha512-586.${ASM_EXT}
    vpaes-x86.${ASM_EXT}
    x86-mont.${ASM_EXT}
  )
endif()

if(ARCH STREQUAL "arm")
  set(
    BCM_ASM_SOURCES

    aesv8-armx.${ASM_EXT}
    armv4-mont.${ASM_EXT}
    bsaes-armv7.${ASM_EXT}
    ghash-armv4.${ASM_EXT}
    ghashv8-armx.${ASM_EXT}
    sha1-armv4-large.${ASM_EXT}
    sha256-armv4.${ASM_EXT}
    sha512-armv4.${ASM_EXT}
    vpaes-armv7.${ASM_EXT}
  )
endif()

if(ARCH STREQUAL "aarch64")

  set(
    BCM_ASM_SOURCES

    aesv8-armx.${ASM_EXT}
    armv8-mont.${ASM_EXT}
    ghash-neon-armv8.${ASM_EXT}
    ghashv8-armx.${ASM_EXT}
    p256-armv8-asm.${ASM_EXT}
    p256_beeu-armv8-asm.${ASM_EXT}
    sha1-armv8.${ASM_EXT}
    sha256-armv8.${ASM_EXT}
    sha512-armv8.${ASM_EXT}
    vpaes-armv8.${ASM_EXT}
  )
endif()

if(ARCH STREQUAL "ppc64le")
  set(
    BCM_ASM_SOURCES

    aesp8-ppc.${ASM_EXT}
    ghashp8-ppc.${ASM_EXT}
  )
endif()

if(PERL_EXECUTABLE)
  perlasm(aesni-gcm-x86_64.${ASM_EXT} modes/asm/aesni-gcm-x86_64.pl)
  perlasm(aesni-x86_64.${ASM_EXT} aes/asm/aesni-x86_64.pl)
  perlasm(aesni-x86.${ASM_EXT} aes/asm/aesni-x86.pl)
  perlasm(aesp8-ppc.${ASM_EXT} aes/asm/aesp8-ppc.pl)
  perlasm(aesv8-armx.${ASM_EXT} aes/asm/aesv8-armx.pl)
  perlasm(armv4-mont.${ASM_EXT} bn/asm/armv4-mont.pl)
  perlasm(armv8-mont.${ASM_EXT} bn/asm/armv8-mont.pl)
  perlasm(bn-586.${ASM_EXT} bn/asm/bn-586.pl)
  perlasm(bsaes-armv7.${ASM_EXT} aes/asm/bsaes-armv7.pl)
  perlasm(co-586.${ASM_EXT} bn/asm/co-586.pl)
  perlasm(ghash-armv4.${ASM_EXT} modes/asm/ghash-armv4.pl)
  perlasm(ghashp8-ppc.${ASM_EXT} modes/asm/ghashp8-ppc.pl)
  perlasm(ghashv8-armx.${ASM_EXT} modes/asm/ghashv8-armx.pl)
  perlasm(ghash-neon-armv8.${ASM_EXT} modes/asm/ghash-neon-armv8.pl)
  perlasm(ghash-ssse3-x86_64.${ASM_EXT} modes/asm/ghash-ssse3-x86_64.pl)
  perlasm(ghash-ssse3-x86.${ASM_EXT} modes/asm/ghash-ssse3-x86.pl)
  perlasm(ghash-x86_64.${ASM_EXT} modes/asm/ghash-x86_64.pl)
  perlasm(ghash-x86.${ASM_EXT} modes/asm/ghash-x86.pl)
  perlasm(md5-586.${ASM_EXT} md5/asm/md5-586.pl)
  perlasm(md5-x86_64.${ASM_EXT} md5/asm/md5-x86_64.pl)
  perlasm(p256-x86_64-asm.${ASM_EXT} ec/asm/p256-x86_64-asm.pl)
  perlasm(p256_beeu-x86_64-asm.${ASM_EXT} ec/asm/p256_beeu-x86_64-asm.pl)
  perlasm(p256-armv8-asm.${ASM_EXT} ec/asm/p256-armv8-asm.pl)
  perlasm(p256_beeu-armv8-asm.${ASM_EXT} ec/asm/p256_beeu-armv8-asm.pl)
  perlasm(rdrand-x86_64.${ASM_EXT} rand/asm/rdrand-x86_64.pl)
  perlasm(rsaz-avx2.${ASM_EXT} bn/asm/rsaz-avx2.pl)
  perlasm(sha1-586.${ASM_EXT} sha/asm/sha1-586.pl)
  perlasm(sha1-armv4-large.${ASM_EXT} sha/asm/sha1-armv4-large.pl)
  perlasm(sha1-armv8.${ASM_EXT} sha/asm/sha1-armv8.pl)
  perlasm(sha1-x86_64.${ASM_EXT} sha/asm/sha1-x86_64.pl)
  perlasm(sha256-586.${ASM_EXT} sha/asm/sha256-586.pl)
  perlasm(sha256-armv4.${ASM_EXT} sha/asm/sha256-armv4.pl)
  perlasm(sha256-armv8.${ASM_EXT} sha/asm/sha512-armv8.pl)
  perlasm(sha256-x86_64.${ASM_EXT} sha/asm/sha512-x86_64.pl)
  perlasm(sha512-586.${ASM_EXT} sha/asm/sha512-586.pl)
  perlasm(sha512-armv4.${ASM_EXT} sha/asm/sha512-armv4.pl)
  perlasm(sha512-armv8.${ASM_EXT} sha/asm/sha512-armv8.pl)
  perlasm(sha512-x86_64.${ASM_EXT} sha/asm/sha512-x86_64.pl)
  perlasm(vpaes-armv7.${ASM_EXT} aes/asm/vpaes-armv7.pl)
  perlasm(vpaes-armv8.${ASM_EXT} aes/asm/vpaes-armv8.pl)
  perlasm(vpaes-x86_64.${ASM_EXT} aes/asm/vpaes-x86_64.pl)
  perlasm(vpaes-x86.${ASM_EXT} aes/asm/vpaes-x86.pl)
  perlasm(x86_64-mont5.${ASM_EXT} bn/asm/x86_64-mont5.pl)
  perlasm(x86_64-mont.${ASM_EXT} bn/asm/x86_64-mont.pl)
  perlasm(x86-mont.${ASM_EXT} bn/asm/x86-mont.pl)
endif()

# s2n-bignum files can be compiled on Unix platforms only (except Apple),
# and on x86_64 and aarch64 systems only.
if((ARCH STREQUAL "x86_64" OR ARCH STREQUAL "aarch64") AND
    UNIX AND NOT APPLE AND NOT MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)

  # Set the source directory for s2n-bignum assembly files
  if(ARCH STREQUAL "x86_64")
    set(S2N_BIGNUM_DIR ${PROJECT_SOURCE_DIR}/third_party/s2n-bignum/x86_att)
  else()
    set(S2N_BIGNUM_DIR ${PROJECT_SOURCE_DIR}/third_party/s2n-bignum/arm)
  endif()

  # We add s2n-bignum files to a separate list because they need
  # to go through C preprocessor in case of the static build.
  set(
    S2N_BIGNUM_ASM_SOURCES

    ${S2N_BIGNUM_DIR}/p384/bignum_add_p384.S
    ${S2N_BIGNUM_DIR}/p384/bignum_sub_p384.S
    ${S2N_BIGNUM_DIR}/p384/bignum_neg_p384.S
    ${S2N_BIGNUM_DIR}/p384/bignum_tomont_p384.S
    ${S2N_BIGNUM_DIR}/p384/bignum_deamont_p384.S
    ${S2N_BIGNUM_DIR}/p384/bignum_montmul_p384.S
    ${S2N_BIGNUM_DIR}/p384/bignum_montmul_p384_alt.S
    ${S2N_BIGNUM_DIR}/p384/bignum_montsqr_p384.S
    ${S2N_BIGNUM_DIR}/p384/bignum_montsqr_p384_alt.S
    ${S2N_BIGNUM_DIR}/p384/bignum_nonzero_6.S
    ${S2N_BIGNUM_DIR}/p384/bignum_littleendian_6.S

    ${S2N_BIGNUM_DIR}/p521/bignum_add_p521.S
    ${S2N_BIGNUM_DIR}/p521/bignum_sub_p521.S
    ${S2N_BIGNUM_DIR}/p521/bignum_neg_p521.S
    ${S2N_BIGNUM_DIR}/p521/bignum_mul_p521.S
    ${S2N_BIGNUM_DIR}/p521/bignum_mul_p521_alt.S
    ${S2N_BIGNUM_DIR}/p521/bignum_sqr_p521.S
    ${S2N_BIGNUM_DIR}/p521/bignum_sqr_p521_alt.S
    ${S2N_BIGNUM_DIR}/p521/bignum_tolebytes_p521.S
    ${S2N_BIGNUM_DIR}/p521/bignum_fromlebytes_p521.S
  )
  if(ARCH STREQUAL "x86_64")
    # The files below contain the alternative functions for x86_64.
    # For AArch64, the alternative tomont/deamont functions are
    # the same as the non-alternative ones, so they are defined
    # in the corresponding "non-alt" files (bignum_<deamont|tomont>_p384.S)
    list(APPEND S2N_BIGNUM_ASM_SOURCES
                ${S2N_BIGNUM_DIR}/p384/bignum_tomont_p384_alt.S
                ${S2N_BIGNUM_DIR}/p384/bignum_deamont_p384_alt.S)
  endif()

  if(NOT FIPS_DELOCATE)
    # If we don't have to use the delocate script then s2n-bignum files
    # are simply added to BCM_ASM_SOURCES.
    list(APPEND BCM_ASM_SOURCES ${S2N_BIGNUM_ASM_SOURCES})
  endif()
endif()

function(cpreprocess dest src)
  set(TARGET "")
  if(CMAKE_ASM_COMPILER_TARGET)
    set(TARGET "--target=${CMAKE_ASM_COMPILER_TARGET}")
  endif()

  string(REGEX REPLACE "[ ]+" ";" CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS}")
  add_custom_command(
    OUTPUT ${dest}
    COMMAND ${CMAKE_ASM_COMPILER} ${TARGET} ${CMAKE_ASM_FLAGS} -E ${src} -I${PROJECT_SOURCE_DIR}/include > ${dest}
    DEPENDS
    ${src}
    ${PROJECT_SOURCE_DIR}/include/openssl/arm_arch.h
    WORKING_DIRECTORY .
  )
endfunction()

if(FIPS_DELOCATE)
  if(FIPS_SHARED)
    error("Can't set both delocate and shared mode for FIPS build")
  endif()

  if(OPENSSL_NO_ASM)
    # If OPENSSL_NO_ASM was defined then ASM will not have been enabled, but in
    # FIPS mode we have to have it because the module build requires going via
    # textual assembly.
    enable_language(ASM)
  endif()

  add_library(
    bcm_c_generated_asm

    STATIC

    bcm.c
  )
  target_compile_definitions(bcm_c_generated_asm PRIVATE BORINGSSL_IMPLEMENTATION)

  if(ARCH STREQUAL "aarch64")
    # Perlasm output on Aarch64 needs to pass through the C preprocessor
    # before it can be parsed by delocate.
    foreach(asm ${BCM_ASM_SOURCES})
      cpreprocess(${asm}.s ${asm})
      list(APPEND BCM_ASM_PROCESSED_SOURCES "${asm}.s")
    endforeach()
  else()
    # No preprocessing is required on other platforms.
    set(BCM_ASM_PROCESSED_SOURCES ${BCM_ASM_SOURCES})
  endif()

  if(S2N_BIGNUM_ASM_SOURCES)
    # s2n-bignum assembly files need to pass through the C preprocessor
    # before they can be parsed by delocate.
    foreach(asm ${S2N_BIGNUM_ASM_SOURCES})
      cpreprocess(${asm}.S ${asm})
      list(APPEND BCM_ASM_PROCESSED_SOURCES "${asm}.S")
    endforeach()
  endif()

  add_dependencies(bcm_c_generated_asm global_target)

  set_target_properties(bcm_c_generated_asm PROPERTIES COMPILE_OPTIONS "-S")
  set_target_properties(bcm_c_generated_asm PROPERTIES POSITION_INDEPENDENT_CODE ON)

  go_executable(delocate boringssl.googlesource.com/boringssl/util/fipstools/delocate)
  add_custom_command(
    OUTPUT bcm-delocated.S
    COMMAND ./delocate -a $<TARGET_FILE:bcm_c_generated_asm> -o bcm-delocated.S ${BCM_ASM_PROCESSED_SOURCES}
    DEPENDS bcm_c_generated_asm delocate ${BCM_ASM_PROCESSED_SOURCES}
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
  )

  add_library(
    bcm_hashunset

    STATIC

    bcm-delocated.S
  )
  target_compile_definitions(bcm_hashunset PRIVATE BORINGSSL_IMPLEMENTATION)

  add_dependencies(bcm_hashunset global_target)

  set_target_properties(bcm_hashunset PROPERTIES POSITION_INDEPENDENT_CODE ON)
  set_target_properties(bcm_hashunset PROPERTIES LINKER_LANGUAGE C)

  go_executable(inject_hash
                boringssl.googlesource.com/boringssl/util/fipstools/inject_hash)
  add_custom_command(
    OUTPUT bcm.o
    COMMAND ./inject_hash -o bcm.o -in-archive $<TARGET_FILE:bcm_hashunset> -sha256
    DEPENDS bcm_hashunset inject_hash
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
  )

  # The outputs of add_custom_command cannot be referenced outside of the
  # CMakeLists.txt that defines it. Thus we have to wrap bcm.o in a custom target
  # so that crypto can depend on it.
  add_custom_target(bcm_o_target DEPENDS bcm.o)

  add_library(
    fipsmodule

    OBJECT

    fips_shared_support.c
  )
  target_compile_definitions(fipsmodule PRIVATE BORINGSSL_IMPLEMENTATION)

  add_dependencies(fipsmodule global_target)

  set_target_properties(fipsmodule PROPERTIES LINKER_LANGUAGE C)
elseif(FIPS_SHARED)
  if(NOT BUILD_SHARED_LIBS)
    error("FIPS_SHARED set but not BUILD_SHARED_LIBS")
  endif()

  add_library(
    fipsmodule

    OBJECT

    fips_shared_support.c
  )
  target_compile_definitions(fipsmodule PRIVATE BORINGSSL_IMPLEMENTATION)

  add_dependencies(fipsmodule global_target)

  add_library(
    bcm_library

    STATIC

    bcm.c

    ${BCM_ASM_SOURCES}
  )
  target_compile_definitions(bcm_library PRIVATE BORINGSSL_IMPLEMENTATION)

  add_dependencies(bcm_library global_target)

  if (APPLE)
    # The linker on macOS doesn't have the ability to process linker scripts,
    # so we build the FIPS module differently than on Linux. Similarly to
    # what OpenSSL does we produce two object files: fips_apple_{start, end}.o
    # that contain only the markers for the start and end of __text and __const
    # sections. The module is then produced by linking the files specified in
    # the following order: fips_apple_start.o bcm.o fips_apple_end.o. This will
    # generate the output object file where all the code in the __text section
    # and all the read-only data in the __const section are between the
    # respective start and end markers.
    add_custom_command(
      OUTPUT fips_apple_start.o
      COMMAND ${CMAKE_C_COMPILER} -arch ${CMAKE_SYSTEM_PROCESSOR} -isysroot ${CMAKE_OSX_SYSROOT} -c ${CMAKE_CURRENT_SOURCE_DIR}/fips_apple_support.c -DAWSLC_FIPS_APPLE_START -o fips_apple_start.o
      DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/fips_apple_support.c
    )
    add_custom_command(
      OUTPUT fips_apple_end.o
      COMMAND ${CMAKE_C_COMPILER} -arch ${CMAKE_SYSTEM_PROCESSOR} -isysroot ${CMAKE_OSX_SYSROOT} -c ${CMAKE_CURRENT_SOURCE_DIR}/fips_apple_support.c -DAWSLC_FIPS_APPLE_END -o fips_apple_end.o
      DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/fips_apple_support.c
    )

    add_custom_command(
      OUTPUT bcm.o
      COMMAND ${CMAKE_LINKER} -r fips_apple_start.o -force_load $<TARGET_FILE:bcm_library> fips_apple_end.o -keep_private_externs -o bcm.o
      DEPENDS bcm_library fips_apple_start.o fips_apple_end.o
      WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

  else()
    # Linux is the only OS other than macOS/iOS on which we build FIPS.

    # fips_shared.lds does not have 'clang' prefix because we want to keep merging any changes from upstream.
    set(FIPS_CUSTOM_LINKER_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/fips_shared.lds")
    if (GCC)
      # gcc puts some code in sections named ".text.unlikely", ".text.exit" and ".text.startup".
      # so we have a separate linker script for gcc.
      set(FIPS_CUSTOM_LINKER_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/gcc_fips_shared.lds")
    endif()

    add_custom_command(
      OUTPUT bcm.o
      COMMAND ${CMAKE_LINKER} -r -T ${FIPS_CUSTOM_LINKER_SCRIPT} -o bcm.o --whole-archive $<TARGET_FILE:bcm_library>
      DEPENDS bcm_library ${FIPS_CUSTOM_LINKER_SCRIPT}
      WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )
  endif()


  add_custom_target(bcm_o_target DEPENDS bcm.o)
else()
  add_library(
    fipsmodule

    OBJECT

    bcm.c
    fips_shared_support.c

    ${BCM_ASM_SOURCES}
  )
  target_compile_definitions(fipsmodule PRIVATE BORINGSSL_IMPLEMENTATION)

  add_dependencies(fipsmodule global_target)
endif()

