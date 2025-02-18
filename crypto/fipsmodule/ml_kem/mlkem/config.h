/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_CONFIG_H
#define MLK_CONFIG_H

/******************************************************************************
 * Name:        MLKEM_K
 *
 * Description: Determines the security level for ML-KEM
 *              - MLKEM_K=2 corresponds to ML-KEM-512
 *              - MLKEM_K=3 corresponds to ML-KEM-768
 *              - MLKEM_K=4 corresponds to ML-KEM-1024
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#ifndef MLKEM_K
#define MLKEM_K 3 /* Change this for different security strengths */
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_FILE
 *
 * Description: If defined, this is a header that will be included instead
 *              of this default configuration file mlkem/config.h.
 *
 *              When you need to build mlkem-native in multiple configurations,
 *              using varying MLK_CONFIG_FILE can be more convenient
 *              then configuring everything through CFLAGS.
 *
 *              To use, MLK_CONFIG_FILE _must_ be defined prior
 *              to the inclusion of any mlkem-native headers. For example,
 *              it can be set by passing `-DMLK_CONFIG_FILE="..."`
 *              on the command line.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_FILE "config.h" */

/******************************************************************************
 * Name:        MLK_NAMESPACE_PREFIX
 *
 * Description: The prefix to use to namespace global symbols from mlkem/.
 *
 *              Level-dependent symbols will additionally be prefixed with the
 *              security level if MLK_NAMESPACE_PREFIX_ADD_LEVEL is set.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#if !defined(MLK_NAMESPACE_PREFIX)
#define MLK_NAMESPACE_PREFIX MLK_DEFAULT_NAMESPACE_PREFIX
#endif

/******************************************************************************
 * Name:        MLK_NAMESPACE_PREFIX_ADD_LEVEL
 *
 * Description: If set, the level (512, 768, 1024) is added to the namespace
 *              prefix MLK_NAMESPACE_PREFIX for all functions which are
 *              level-dependent. Level-independent functions will have there
 *              symbol prefixed by MLK_NAMESPACE_PREFIX only.
 *
 *              This is intended to be used for multi-level builds where
 *              level-independent code should be shared across levels.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
/* #define MLK_NAMESPACE_PREFIX_ADD_LEVEL */

/******************************************************************************
 * Name:        MLK_MULTILEVEL_BUILD_WITH_SHARED
 *
 * Description: This is for multi-level builds of mlkem-native only. If you
 *              need only a single security level build of mlkem-native,
 *              keep this unset.
 *
 *              If this is set, all MLKEM_K-independent code will be included
 *              in the build, including code needed only for other security
 *              levels.
 *
 *              Example: poly_cbd3 is only needed for MLKEM_K == 2. Yet, if
 *              this option is set for a build with MLKEM_K==3/4, it would
 *              be included.
 *
 *              To build mlkem-native with support for all security levels,
 *              build it three times -- once per level -- and set the option
 *              MLK_MULTILEVEL_BUILD_WITH_SHARED for exactly one of
 *              them, and MLK_MULTILEVEL_BUILD_NO_SHARED for the
 *              others.
 *
 *              See examples/multilevel_build for an example.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
/* #define MLK_MULTILEVEL_BUILD_WITH_SHARED */

/******************************************************************************
 * Name:        MLK_MULTILEVEL_BUILD_NO_SHARED
 *
 * Description: This is for multi-level builds of mlkem-native only. If you
 *              need only a single security level build of mlkem-native,
 *              keep this unset.
 *
 *              If this is set, no MLKEM_K-independent code will be included
 *              in the build.
 *
 *              To build mlkem-native with support for all security levels,
 *              build it three times -- once per level -- and set the option
 *              MLK_MULTILEVEL_BUILD_WITH_SHARED for exactly one of
 *              them, and MLK_MULTILEVEL_BUILD_NO_SHARED for the
 *              others.
 *
 *              See examples/multilevel_build for an example.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
/* #define MLK_MULTILEVEL_BUILD_NO_SHARED */

/******************************************************************************
 * Name:        MLK_USE_NATIVE_BACKEND_ARITH
 *
 * Description: Determines whether an native arithmetic backend should be used.
 *
 *              The arithmetic backend covers performance critical functions
 *              such as the number-theoretic transform (NTT).
 *
 *              If this option is unset, the C backend will be used.
 *
 *              If this option is set, the arithmetic backend to be use is
 *              determined by MLK_ARITH_BACKEND: If the latter is
 *              unset, the default backend for your the target architecture
 *              will be used. If set, it must be the name of a backend metadata
 *              file.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#if !defined(MLK_USE_NATIVE_BACKEND_ARITH)
/* #define MLK_USE_NATIVE_BACKEND_ARITH */
#endif

/******************************************************************************
 * Name:        MLK_ARITH_BACKEND_FILE
 *
 * Description: The arithmetic backend to use.
 *
 *              If MLK_USE_NATIVE_BACKEND_ARITH is unset, this option
 *              is ignored.
 *
 *              If MLK_USE_NATIVE_BACKEND_ARITH is set, this option must
 *              either be undefined or the filename of an arithmetic backend.
 *              If unset, the default backend will be used.
 *
 *              This can be set using CFLAGS.
 *
 *****************************************************************************/
#if defined(MLK_USE_NATIVE_BACKEND_ARITH) && !defined(MLK_ARITH_BACKEND_FILE)
#define MLK_ARITH_BACKEND_FILE "native/meta.h"
#endif

/******************************************************************************
 * Name:        MLK_USE_NATIVE_BACKEND_FIPS202
 *
 * Description: Determines whether an native FIPS202 backend should be used.
 *
 *              The FIPS202 backend covers 1x/2x/4x-fold Keccak-f1600, which is
 *              the performance bottleneck of SHA3 and SHAKE.
 *
 *              If this option is unset, the C backend will be used.
 *
 *              If this option is set, the FIPS202 backend to be use is
 *              determined by MLK_FIPS202_BACKEND: If the latter is
 *              unset, the default backend for your the target architecture
 *              will be used. If set, it must be the name of a backend metadata
 *              file.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#if !defined(MLK_USE_NATIVE_BACKEND_FIPS202)
/* #define MLK_USE_NATIVE_BACKEND_FIPS202 */
#endif

/******************************************************************************
 * Name:        MLK_FIPS202_BACKEND_FILE
 *
 * Description: The FIPS-202 backend to use.
 *
 *              If MLK_USE_NATIVE_BACKEND_FIPS202 is set, this option must
 *              either be undefined or the filename of a FIPS202 backend.
 *              If unset, the default backend will be used.
 *
 *              This can be set using CFLAGS.
 *
 *****************************************************************************/
#if defined(MLK_USE_NATIVE_BACKEND_FIPS202) && \
    !defined(MLK_FIPS202_BACKEND_FILE)
#define MLK_FIPS202_BACKEND_FILE "fips202/native/meta.h"
#endif

/******************************************************************************
 * Name:        MLK_FIPS202_CUSTOM_HEADER
 *
 * Description: Custom header to use for FIPS-202
 *
 *              This should only be set if you intend to use a custom
 *              FIPS-202 implementation, different from the one shipped
 *              with mlkem-native.
 *
 *              If set, it must be the name of a file serving as the
 *              replacement for mlkem/fips202/fips202.h, and exposing
 *              the same API (see FIPS202.md).
 *
 *****************************************************************************/
/* #define MLK_FIPS202_CUSTOM_HEADER "SOME_FILE.h" */

/******************************************************************************
 * Name:        MLK_FIPS202X4_CUSTOM_HEADER
 *
 * Description: Custom header to use for FIPS-202-X4
 *
 *              This should only be set if you intend to use a custom
 *              FIPS-202 implementation, different from the one shipped
 *              with mlkem-native.
 *
 *              If set, it must be the name of a file serving as the
 *              replacement for mlkem/fips202/fips202x4.h, and exposing
 *              the same API (see FIPS202.md).
 *
 *****************************************************************************/
/* #define MLK_FIPS202X4_CUSTOM_HEADER "SOME_FILE.h" */

/******************************************************************************
 * Name:        MLK_USE_CT_ZEROIZE_NATIVE
 *
 * Description: In compliance with FIPS 203 Section 3.3, mlkem-native zeroizes
 *              intermediate stack buffers before returning from function calls.
 *
 *              Set this option and define `ct_zeroize_native` if you want to
 *              use a custom method to zeroize intermediate stack buffers.
 *              The default implementation uses SecureZeroMemory on Windows
 *              and a memset + compiler barrier otherwise. If neither of those
 *              is available on the target platform, compilation will fail,
 *              and you will need to use MLK_USE_CT_ZEROIZE_NATIVE to provide
 *              a custom implementation of `ct_zeroize_native()`.
 *
 *              WARNING:
 *              The explicit stack zeroization conducted by mlkem-native
 *              reduces the likelihood of data leaking on the stack, but
 *              does not eliminate it! The C standard makes no guarantee about
 *              where a compiler allocates structures and whether/where it makes
 *              copies of them. Also, in addition to entire structures, there
 *              may also be potentially exploitable leakage of individual values
 *              on the stack.
 *
 *              If you need bullet-proof zeroization of the stack, you need to
 *              consider additional measures instead of of what this feature
 *              provides. In this case, you can set ct_zeroize_native to a
 *              no-op.
 *
 *****************************************************************************/
/* #define MLK_USE_CT_ZEROIZE_NATIVE
   #if !defined(__ASSEMBLER__)
   #include <stdint.h>
   #include "sys.h"
   static MLK_INLINE void ct_zeroize_native(void *ptr, size_t len)
   {
       ... your implementation ...
   }
   #endif
*/

/******************************************************************************
 * Name:        MLK_KEYGEN_PCT
 *
 * Description: Compliance with [FIPS 140-3
 *IG](https://csrc.nist.gov/csrc/media/Projects/cryptographic-module-validation-program/documents/fips%20140-3/FIPS%20140-3%20IG.pdf)
 *              requires a Pairwise Consistency Test (PCT) to be carried out
 *              on a freshly generated keypair before it can be exported.
 *
 *              Set this option if such a check should be implemented.
 *              In this case, crypto_kem_keypair_derand and crypto_kem_keypair
 *              will return a non-zero error code if the PCT failed.
 *
 *              NOTE: This feature will drastically lower the performance of
 *              key generation.
 *
 *****************************************************************************/
/* #define MLK_KEYGEN_PCT */

/*************************  Config internals  ********************************/

/* Default namespace
 *
 * Don't change this. If you need a different namespace, re-define
 * MLK_NAMESPACE_PREFIX above instead, and remove the following.
 *
 * The default MLKEM namespace is
 *
 *   PQCP_MLKEM_NATIVE_MLKEM<LEVEL>_
 *
 * e.g., PQCP_MLKEM_NATIVE_MLKEM512_
 */

#if MLKEM_K == 2
#define MLK_DEFAULT_NAMESPACE_PREFIX PQCP_MLKEM_NATIVE_MLKEM512
#elif MLKEM_K == 3
#define MLK_DEFAULT_NAMESPACE_PREFIX PQCP_MLKEM_NATIVE_MLKEM768
#elif MLKEM_K == 4
#define MLK_DEFAULT_NAMESPACE_PREFIX PQCP_MLKEM_NATIVE_MLKEM1024
#endif

#endif /* MLK_CONFIG_H */
