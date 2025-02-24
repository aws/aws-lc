/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLK_COMMON_H
#define MLK_COMMON_H

#if defined(MLK_CONFIG_FILE)
#include MLK_CONFIG_FILE
#else
#include "config.h"
#endif /* MLK_CONFIG_FILE */

#include "params.h"
#include "sys.h"

/* Include backend metadata */
#if defined(MLK_USE_NATIVE_BACKEND_ARITH)
#if defined(MLK_ARITH_BACKEND_FILE)
#include MLK_ARITH_BACKEND_FILE
#else
#error Bad configuration: MLK_USE_NATIVE_BACKEND_ARITH is set, but MLK_ARITH_BACKEND_FILE is not.
#endif
#endif

#if defined(MLK_USE_NATIVE_BACKEND_FIPS202)
#if defined(MLK_FIPS202_BACKEND_FILE)
#include MLK_FIPS202_BACKEND_FILE
#else
#error Bad configuration: MLK_USE_NATIVE_BACKEND_FIPS202 is set, but MLK_FIPS202_BACKEND_FILE is not.
#endif
#endif

#if !defined(MLK_ARITH_BACKEND_NAME)
#define MLK_ARITH_BACKEND_NAME C
#endif

#if !defined(MLK_FIPS202_BACKEND_NAME)
#define MLK_FIPS202_BACKEND_NAME C
#endif

/* For a monobuild (where all compilation units are merged into one), mark
 * all non-public API as static since they don't need external linkage. */
#if !defined(MLK_MONOBUILD)
#define MLK_INTERNAL_API
#else
#define MLK_INTERNAL_API static
#endif

/* Public API may have internal or external linkage, depending on how
 * mlkem-native is used in the monobuild. Keep it external by default,
 * but allow the user to overwrite this in the config. */
#if !defined(MLK_EXTERNAL_API)
#define MLK_EXTERNAL_API
#endif /* MLK_EXTERNAL_API */

#define MLK_MAKE_NAMESPACE_(x1, x2) x1##_##x2
#define MLK_MAKE_NAMESPACE(x1, x2) MLK_MAKE_NAMESPACE_(x1, x2)

#define MLK_NAMESPACE(s) MLK_MAKE_NAMESPACE(MLK_NAMESPACE_PREFIX, s)

#if defined(MLK_NAMESPACE_PREFIX_ADD_LEVEL)
#define MLK_MAKE_NAMESPACE_K_(x1, x2, x3) x1##x2##_##x3
#define MLK_MAKE_NAMESPACE_K(x1, x2, x3) MLK_MAKE_NAMESPACE_K_(x1, x2, x3)
#define MLK_NAMESPACE_K(s) \
  MLK_MAKE_NAMESPACE_K(MLK_NAMESPACE_PREFIX, MLKEM_LVL, s)
#else
#define MLK_NAMESPACE_K(s) MLK_NAMESPACE(s)
#endif

/* On Apple platforms, we need to emit leading underscore
 * in front of assembly symbols. We thus introducee a separate
 * namespace wrapper for ASM symbols. */
#if !defined(__APPLE__)
#define MLK_ASM_NAMESPACE(sym) MLK_NAMESPACE(sym)
#else
#define MLK_PREFIX_UNDERSCORE_(sym) _##sym
#define MLK_PREFIX_UNDERSCORE(sym) MLK_PREFIX_UNDERSCORE_(sym)
#define MLK_ASM_NAMESPACE(sym) MLK_PREFIX_UNDERSCORE(MLK_NAMESPACE(sym))
#endif

/*
 * On X86_64 if control-flow protections (CET) are enabled (through
 * -fcf-protection=), we add an endbr64 instruction at every global function
 * label.  See sys.h for more details
 */
#if defined(MLK_SYS_X86_64)
#define MLK_ASM_FN_SYMBOL(sym) MLK_ASM_NAMESPACE(sym) : MLK_CET_ENDBR
#else
#define MLK_ASM_FN_SYMBOL(sym) MLK_ASM_NAMESPACE(sym) :
#endif

/* We aim to simplify the user's life by supporting builds where
 * all source files are included, even those that are not needed.
 * Those files are appropriately guarded and will be empty when unneeded.
 * The following is to avoid compilers complaining about this. */
#define MLK_EMPTY_CU(s) extern int MLK_NAMESPACE_K(empty_cu_##s);

#if !defined(MLK_FIPS202_CUSTOM_HEADER)
#define MLK_FIPS202_HEADER_FILE "fips202/fips202.h"
#else
#define MLK_FIPS202_HEADER_FILE MLK_FIPS202_CUSTOM_HEADER
#endif

#if !defined(MLK_FIPS202X4_CUSTOM_HEADER)
#define MLK_FIPS202X4_HEADER_FILE "fips202/fips202x4.h"
#else
#define MLK_FIPS202X4_HEADER_FILE MLK_FIPS202X4_CUSTOM_HEADER
#endif

#endif /* MLK_COMMON_H */
