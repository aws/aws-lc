if(${CMAKE_SYSTEM_NAME} STREQUAL "OpenBSD" AND FIPS)
  if(NOT BUILD_SHARED_LIBS)
    # Disable the stack smash protector for FIPS static builds
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fno-stack-protector")
  endif()
  if(CMAKE_C_COMPILER_ID STREQUAL "Clang")
    # OpenBSD's Clang version has a return trampoline enabled by default that
    # it may inject and cause issues with our custom linker script.
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -mno-retpoline")
  endif()
endif()

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

    aesni-gcm-avx512.${ASM_EXT}
    aesni-gcm-x86_64.${ASM_EXT}
    aesni-xts-avx512.${ASM_EXT}
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
    aesv8-gcm-armv8.${ASM_EXT}
    aesv8-gcm-armv8-unroll8.${ASM_EXT}
    armv8-mont.${ASM_EXT}
    bn-armv8.${ASM_EXT}
    ghash-neon-armv8.${ASM_EXT}
    ghashv8-armx.${ASM_EXT}
    keccak1600-armv8.${ASM_EXT}
    md5-armv8.${ASM_EXT}
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
  perlasm(aesni-gcm-avx512.${ASM_EXT} modes/asm/aesni-gcm-avx512.pl)
  perlasm(aesni-xts-avx512.${ASM_EXT} aes/asm/aesni-xts-avx512.pl)
  perlasm(aesni-x86_64.${ASM_EXT} aes/asm/aesni-x86_64.pl)
  perlasm(aesni-x86.${ASM_EXT} aes/asm/aesni-x86.pl)
  perlasm(aesp8-ppc.${ASM_EXT} aes/asm/aesp8-ppc.pl)
  perlasm(aesv8-armx.${ASM_EXT} aes/asm/aesv8-armx.pl)
  perlasm(aesv8-gcm-armv8.${ASM_EXT} modes/asm/aesv8-gcm-armv8.pl)
  perlasm(aesv8-gcm-armv8-unroll8.${ASM_EXT} modes/asm/aesv8-gcm-armv8-unroll8.pl)
  perlasm(armv4-mont.${ASM_EXT} bn/asm/armv4-mont.pl)
  perlasm(armv8-mont.${ASM_EXT} bn/asm/armv8-mont.pl)
  perlasm(bn-586.${ASM_EXT} bn/asm/bn-586.pl)
  perlasm(bn-armv8.${ASM_EXT} bn/asm/bn-armv8.pl)
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
  perlasm(keccak1600-armv8.${ASM_EXT} sha/asm/keccak1600-armv8.pl)
  perlasm(md5-586.${ASM_EXT} md5/asm/md5-586.pl)
  perlasm(md5-armv8.${ASM_EXT} md5/asm/md5-armv8.pl)
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

# clang-6 (and older) knows how to compile AVX512 assembly instructions,
# but only if it's given the right flags (e.g. -mavx512*).
# The flags are not required for any other compiler we are running in the CI.
if (CLANG AND (CMAKE_ASM_COMPILER_ID MATCHES "Clang" OR CMAKE_ASM_COMPILER MATCHES "clang") AND
    (CMAKE_C_COMPILER_VERSION VERSION_LESS "7.0.0") AND (ARCH STREQUAL "x86_64"))
  set_source_files_properties(${CMAKE_CURRENT_BINARY_DIR}/aesni-gcm-avx512.${ASM_EXT} PROPERTIES COMPILE_FLAGS "-mavx512f -mavx512bw -mavx512dq -mavx512vl")
  set_source_files_properties(${CMAKE_CURRENT_BINARY_DIR}/aesni-xts-avx512.${ASM_EXT} PROPERTIES COMPILE_FLAGS "-mavx512f -mavx512bw -mavx512dq -mavx512vl")
endif()

# s2n-bignum files can be compiled on Unix platforms only (except Apple),
# and on x86_64 and aarch64 systems only.
if((((ARCH STREQUAL "x86_64") AND NOT MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX) OR
      ARCH STREQUAL "aarch64") AND UNIX)

  # Set the source directory for s2n-bignum assembly files
  if(ARCH STREQUAL "x86_64")
    set(S2N_BIGNUM_DIR ${PROJECT_SOURCE_DIR}/third_party/s2n-bignum/x86_att)
  else()
    set(S2N_BIGNUM_DIR ${PROJECT_SOURCE_DIR}/third_party/s2n-bignum/arm)
  endif()

  set(S2N_BIGNUM_INCLUDE_DIR ${PROJECT_SOURCE_DIR}/third_party/s2n-bignum/include)

  # We add s2n-bignum files to a separate list because they need
  # to go through C preprocessor in case of the static build.
  set(
    S2N_BIGNUM_ASM_SOURCES

    p384/bignum_add_p384.S
    p384/bignum_sub_p384.S
    p384/bignum_neg_p384.S
    p384/bignum_tomont_p384.S
    p384/bignum_deamont_p384.S
    p384/bignum_montmul_p384.S
    p384/bignum_montmul_p384_alt.S
    p384/bignum_montsqr_p384.S
    p384/bignum_montsqr_p384_alt.S
    p384/bignum_nonzero_6.S
    p384/bignum_littleendian_6.S

    p521/bignum_add_p521.S
    p521/bignum_sub_p521.S
    p521/bignum_neg_p521.S
    p521/bignum_mul_p521.S
    p521/bignum_mul_p521_alt.S
    p521/bignum_sqr_p521.S
    p521/bignum_sqr_p521_alt.S
    p521/bignum_tolebytes_p521.S
    p521/bignum_fromlebytes_p521.S

    curve25519/bignum_mod_n25519.S
    curve25519/bignum_neg_p25519.S
    curve25519/bignum_madd_n25519.S
    curve25519/bignum_madd_n25519_alt.S
    curve25519/edwards25519_decode.S
    curve25519/edwards25519_decode_alt.S
    curve25519/edwards25519_encode.S
    curve25519/edwards25519_scalarmulbase.S
    curve25519/edwards25519_scalarmulbase_alt.S
    curve25519/edwards25519_scalarmuldouble.S
    curve25519/edwards25519_scalarmuldouble_alt.S
  )

  if(ARCH STREQUAL "x86_64")
    # The files below contain the alternative functions for x86_64.
    # For AArch64, the alternative tomont/deamont functions are
    # the same as the non-alternative ones, so they are defined
    # in the corresponding "non-alt" files (bignum_<deamont|tomont>_p384.S)
    list(APPEND S2N_BIGNUM_ASM_SOURCES
                p384/bignum_tomont_p384_alt.S
                p384/bignum_deamont_p384_alt.S
                curve25519/curve25519_x25519.S
                curve25519/curve25519_x25519_alt.S
                curve25519/curve25519_x25519base.S
                curve25519/curve25519_x25519base_alt.S
    )
  elseif(ARCH STREQUAL "aarch64")
    # byte-level interface for aarch64 s2n-bignum x25519 are in
    # files with "byte" tags, but ed25519 is not, neither are they byte-level...
    list(APPEND S2N_BIGNUM_ASM_SOURCES
                curve25519/curve25519_x25519_byte.S
                curve25519/curve25519_x25519_byte_alt.S
                curve25519/curve25519_x25519base_byte.S
                curve25519/curve25519_x25519base_byte_alt.S
    )

    # Big integer arithmetics using s2n-bignum
    list(APPEND S2N_BIGNUM_ASM_SOURCES
                fastmul/bignum_kmul_16_32.S
                fastmul/bignum_kmul_32_64.S
                fastmul/bignum_ksqr_16_32.S
                fastmul/bignum_ksqr_32_64.S
                fastmul/bignum_emontredc_8n.S

                generic/bignum_ge.S
                generic/bignum_mul.S
                generic/bignum_optsub.S
                generic/bignum_sqr.S

                fastmul/bignum_kmul_16_32_neon.S
                fastmul/bignum_kmul_32_64_neon.S
                fastmul/bignum_ksqr_16_32_neon.S
                fastmul/bignum_ksqr_32_64_neon.S
                fastmul/bignum_emontredc_8n_neon.S

                generic/bignum_copy_row_from_table.S
                generic/bignum_copy_row_from_table_8n_neon.S
                generic/bignum_copy_row_from_table_16_neon.S
                generic/bignum_copy_row_from_table_32_neon.S
    )
  endif()
endif()

function(s2n_asm_cpreprocess dest src)
  # s2n_asm_cpreprocess differs from cpreprocess in that is does additional post-processing
  # based on s2n-bignum https://github.com/awslabs/s2n-bignum/blob/main/x86/Makefile#L264
  get_filename_component(dir ${dest} DIRECTORY)
  if (dir STREQUAL "")
    set(dir ".")
  endif()

  set(TARGET "")
  if(CMAKE_ASM_COMPILER_TARGET)
    set(TARGET "--target=${CMAKE_ASM_COMPILER_TARGET}")
  endif()

  string(REGEX REPLACE "[ ]+" ";" CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS}")

  add_custom_command(
          OUTPUT ${dest}
          COMMAND ${CMAKE_COMMAND} -E make_directory ${dir}
          COMMAND ${CMAKE_ASM_COMPILER} ${TARGET} ${CMAKE_ASM_FLAGS} -E ${S2N_BIGNUM_DIR}/${src} -I${S2N_BIGNUM_INCLUDE_DIR} -DS2N_BN_HIDE_SYMBOLS| tr \"\;\" \"\\n\" > ${dest}
          DEPENDS
          ${S2N_BIGNUM_DIR}/${src}
          WORKING_DIRECTORY .
)
endfunction()

if(S2N_BIGNUM_ASM_SOURCES)
  # s2n-bignum assembly files need to be processed before use
  foreach(asm ${S2N_BIGNUM_ASM_SOURCES})
    s2n_asm_cpreprocess(${asm}.S ${asm})
    list(APPEND BCM_ASM_SOURCES "${asm}.S")
  endforeach()
endif()

if(FIPS_DELOCATE)
  if(FIPS_SHARED)
    message(FATAL_ERROR "Can't set both delocate and shared mode for FIPS build")
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

  add_dependencies(bcm_c_generated_asm boringssl_prefix_symbols)
  # Important: We do not want to add the generated prefix symbols to the include path here!
  # Delocator expects symbols to not be prefixed.
  target_include_directories(bcm_c_generated_asm PRIVATE ${PROJECT_SOURCE_DIR}/include)
  set_target_properties(bcm_c_generated_asm PROPERTIES COMPILE_OPTIONS "-S")
  set_target_properties(bcm_c_generated_asm PROPERTIES POSITION_INDEPENDENT_CODE ON)

  set(TARGET "")
  if(CMAKE_ASM_COMPILER_TARGET)
    set(TARGET "--target=${CMAKE_ASM_COMPILER_TARGET}")
  endif()

  set(DELOCATE_EXTRA_ARGS "")
  # clang-6 (and older) do not appreciate the file number starting at a higher value, and incorrectly
  # assume that all file numbers less than that value are defined upon later use.
  if (CLANG AND (CMAKE_ASM_COMPILER_ID MATCHES "Clang" OR CMAKE_ASM_COMPILER MATCHES "clang") AND
      (CMAKE_C_COMPILER_VERSION VERSION_LESS "7.0.0"))
    set(DELOCATE_EXTRA_ARGS "-no-se-debug-directives")
  endif()

  go_executable(delocate boringssl.googlesource.com/boringssl/util/fipstools/delocate)
  add_custom_command(
    OUTPUT bcm-delocated.S
    COMMAND
    ./delocate
    -a $<TARGET_FILE:bcm_c_generated_asm>
    -o bcm-delocated.S
    -cc ${CMAKE_ASM_COMPILER}
    -cc-flags "${TARGET} ${CMAKE_ASM_FLAGS}"
    ${DELOCATE_EXTRA_ARGS}
    ${PROJECT_SOURCE_DIR}/include/openssl/arm_arch.h
    ${PROJECT_SOURCE_DIR}/include/openssl/asm_base.h
    ${PROJECT_SOURCE_DIR}/include/openssl/target.h
    ${BCM_ASM_SOURCES}
    DEPENDS
    bcm_c_generated_asm
    delocate
    ${BCM_ASM_SOURCES}
    ${PROJECT_SOURCE_DIR}/include/openssl/arm_arch.h
    ${PROJECT_SOURCE_DIR}/include/openssl/asm_base.h
    ${PROJECT_SOURCE_DIR}/include/openssl/target.h
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
  )

  # clang-6 (and older) knows how to compile AVX512 assembly instructions,
  # but only if it's given the right flags (e.g. -mavx512*).
  # The flags are not required for any other compiler we are running in the CI.
  if (CLANG AND (CMAKE_ASM_COMPILER_ID MATCHES "Clang" OR CMAKE_ASM_COMPILER MATCHES "clang") AND
      (CMAKE_C_COMPILER_VERSION VERSION_LESS "7.0.0") AND (ARCH STREQUAL "x86_64"))
    set_source_files_properties(${CMAKE_CURRENT_BINARY_DIR}/bcm-delocated.S PROPERTIES COMPILE_FLAGS "-mavx512f -mavx512bw -mavx512dq -mavx512vl")
  endif()

  add_library(
    bcm_hashunset

    STATIC

    bcm-delocated.S
  )
  target_compile_definitions(bcm_hashunset PRIVATE BORINGSSL_IMPLEMENTATION)

  add_dependencies(bcm_hashunset boringssl_prefix_symbols)
  target_include_directories(bcm_hashunset BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
  target_include_directories(bcm_hashunset PRIVATE ${PROJECT_SOURCE_DIR}/include)

  set_target_properties(bcm_hashunset PROPERTIES POSITION_INDEPENDENT_CODE ON)
  set_target_properties(bcm_hashunset PROPERTIES LINKER_LANGUAGE C)

  go_executable(inject_hash
                boringssl.googlesource.com/boringssl/util/fipstools/inject_hash)
  add_custom_command(
    OUTPUT bcm.o
    COMMAND ./inject_hash -o bcm.o -in-archive $<TARGET_FILE:bcm_hashunset>
    DEPENDS bcm_hashunset inject_hash
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
  )

  # The outputs of add_custom_command cannot be referenced outside of the
  # CMakeLists.txt that defines it. Thus we have to wrap bcm.o in a custom target
  # so that crypto can depend on it.
  add_custom_target(bcm_o_target DEPENDS bcm.o)
  set(BCM_NAME bcm.o PARENT_SCOPE)

  add_library(
    fipsmodule

    OBJECT

    fips_shared_support.c
    cpucap/cpucap.c
  )
  target_compile_definitions(fipsmodule PRIVATE BORINGSSL_IMPLEMENTATION)

  add_dependencies(fipsmodule boringssl_prefix_symbols)
  target_include_directories(fipsmodule BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
  target_include_directories(fipsmodule PRIVATE ${PROJECT_SOURCE_DIR}/include)

  set_target_properties(fipsmodule PROPERTIES LINKER_LANGUAGE C)
elseif(FIPS_SHARED)
  if(NOT BUILD_SHARED_LIBS)
    message(FATAL_ERROR "FIPS_SHARED set but not BUILD_SHARED_LIBS")
  endif()

  add_library(
    fipsmodule

    OBJECT

    fips_shared_support.c
    cpucap/cpucap.c
  )
  target_compile_definitions(fipsmodule PRIVATE BORINGSSL_IMPLEMENTATION)

  add_dependencies(fipsmodule boringssl_prefix_symbols)
  target_include_directories(fipsmodule BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
  target_include_directories(fipsmodule PRIVATE ${PROJECT_SOURCE_DIR}/include)

  add_library(
    bcm_library

    STATIC

    bcm.c

    ${BCM_ASM_SOURCES}
  )
  target_compile_definitions(bcm_library PRIVATE BORINGSSL_IMPLEMENTATION)
  target_include_directories(bcm_library PRIVATE ${PROJECT_SOURCE_DIR}/include)

  add_dependencies(bcm_library boringssl_prefix_symbols)
  target_include_directories(bcm_library BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
  target_include_directories(bcm_library PRIVATE ${PROJECT_SOURCE_DIR}/include)
  if (APPLE)
    set(BCM_NAME bcm.o)
    # The linker on macOS doesn't have the ability to process linker scripts,
    # so we build the FIPS module differently than on Linux. Similarly to
    # what OpenSSL does we produce two object files: fips_apple_{start, end}.o
    # that contain only the markers for the start and end of __text and __const
    # sections. The module is then produced by linking the files specified in
    # the following order: fips_apple_start.o bcm.o fips_apple_end.o. This will
    # generate the output object file where all the code in the __text section
    # and all the read-only data in the __const section are between the
    # respective start and end markers.
    if (CMAKE_OSX_DEPLOYMENT_TARGET)
      if(IOS)
        set(OSX_VERSION_MIN_FLAG "-miphoneos-version-min=${CMAKE_OSX_DEPLOYMENT_TARGET}")
      else()
        set(OSX_VERSION_MIN_FLAG "-mmacosx-version-min=${CMAKE_OSX_DEPLOYMENT_TARGET}")
      endif()
    endif()
    add_custom_command(
      OUTPUT fips_apple_start.o
      COMMAND ${CMAKE_C_COMPILER} -arch ${CMAKE_SYSTEM_PROCESSOR} -isysroot ${CMAKE_OSX_SYSROOT} ${OSX_VERSION_MIN_FLAG} -c ${CMAKE_CURRENT_SOURCE_DIR}/fips_shared_library_marker.c -DAWSLC_FIPS_SHARED_START -o fips_apple_start.o
      DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/fips_shared_library_marker.c
    )
    add_custom_command(
      OUTPUT fips_apple_end.o
      COMMAND ${CMAKE_C_COMPILER} -arch ${CMAKE_SYSTEM_PROCESSOR} -isysroot ${CMAKE_OSX_SYSROOT} ${OSX_VERSION_MIN_FLAG} -c ${CMAKE_CURRENT_SOURCE_DIR}/fips_shared_library_marker.c -DAWSLC_FIPS_SHARED_END -o fips_apple_end.o
      DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/fips_shared_library_marker.c
    )
    add_custom_command(
      OUTPUT bcm.o
      COMMAND ${CMAKE_LINKER} -r fips_apple_start.o -force_load $<TARGET_FILE:bcm_library> fips_apple_end.o -keep_private_externs -o bcm.o
      DEPENDS bcm_library fips_apple_start.o fips_apple_end.o
      WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )
  elseif(MSVC)
    set(BCM_NAME bcm.lib)
    # Like the macOS linker MSVC doesn't support linker scripts. The Windows build uses the same start/end markers
    # as the mac build to control the placement of symbols. However, on Windows the start/bcm/end object files also
    # contain pragmas that instruct the compiler to put the code in specific FIPS sections. These sections have a
    # specific suffix $a through $c that controls the order of the FIPS sections when it is linked together into a
    # Grouped Section.
    add_custom_command(
      OUTPUT fips_msvc_start.obj
      COMMAND ${CMAKE_C_COMPILER} /nologo /c /DAWSLC_FIPS_SHARED_START /Fo:fips_msvc_start.obj ${CMAKE_CURRENT_SOURCE_DIR}/fips_shared_library_marker.c
      DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/fips_shared_library_marker.c
    )
    add_custom_command(
      OUTPUT fips_msvc_end.obj
      COMMAND ${CMAKE_C_COMPILER} /nologo /c /DAWSLC_FIPS_SHARED_END /Fo:fips_msvc_end.obj ${CMAKE_CURRENT_SOURCE_DIR}/fips_shared_library_marker.c
      DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/fips_shared_library_marker.c
    )

    get_filename_component(MSVC_BIN ${CMAKE_LINKER} DIRECTORY)
    set(MSVC_LIB "${MSVC_BIN}/lib.exe")

    add_custom_command(
      OUTPUT ${BCM_NAME}
      # This takes bcm_library which is static library and possibly a collection of assembly files in a CMake list.
      # lib.exe does not handle the CMake list which uses semicolons between items, this generator expression converts
      # it to a list of quoted strings, it also needs to be itself string escaped
      COMMAND ${MSVC_LIB} /nologo fips_msvc_start.obj "\"$<JOIN:$<TARGET_OBJECTS:bcm_library>,\" \">\"" fips_msvc_end.obj /OUT:${BCM_NAME}
      DEPENDS  fips_msvc_start.obj fips_msvc_end.obj bcm_library
      WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )
  else()
    set(BCM_NAME bcm.o)
    # fips_shared.lds does not have 'clang' prefix because we want to keep merging any changes from upstream.
    set(FIPS_CUSTOM_LINKER_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/fips_shared.lds")
    if (GCC)
      # gcc puts some code in sections named ".text.unlikely", ".text.exit" and ".text.startup".
      # so we have a separate linker script for gcc.
      set(FIPS_CUSTOM_LINKER_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/gcc_fips_shared.lds")
    endif()

    add_custom_command(
      OUTPUT ${BCM_NAME}
      COMMAND ${CMAKE_LINKER} -r -T ${FIPS_CUSTOM_LINKER_SCRIPT} -o ${BCM_NAME} --whole-archive $<TARGET_FILE:bcm_library>
      DEPENDS bcm_library ${FIPS_CUSTOM_LINKER_SCRIPT}
      WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )
  endif()

  add_custom_target(bcm_o_target DEPENDS ${BCM_NAME})
  set(BCM_NAME ${BCM_NAME} PARENT_SCOPE)

else()
  add_library(
    fipsmodule

    OBJECT

    bcm.c
    fips_shared_support.c
    cpucap/cpucap.c

    ${BCM_ASM_SOURCES}
  )
  target_compile_definitions(fipsmodule PRIVATE BORINGSSL_IMPLEMENTATION)

  add_dependencies(fipsmodule boringssl_prefix_symbols)
  target_include_directories(fipsmodule BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
  target_include_directories(fipsmodule PRIVATE ${PROJECT_SOURCE_DIR}/include)
endif()
