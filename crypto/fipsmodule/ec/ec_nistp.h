/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/
#ifndef EC_NISTP_H
#define EC_NISTP_H

#include <openssl/target.h>

#include <stdint.h>

// We have two implementations of the field arithmetic for NIST curves:
//   - Fiat-crypto
//   - s2n-bignum
// Both Fiat-crypto and s2n-bignum implementations are formally verified.
// Fiat-crypto implementation is fully portable C code, while s2n-bignum
// implements the operations in assembly for x86_64 and aarch64 platforms.
// If (1) x86_64 or aarch64, (2) linux or apple, and (3) OPENSSL_NO_ASM is not
// set, s2n-bignum path is capable.
#if !defined(OPENSSL_NO_ASM) &&                                                \
    (defined(OPENSSL_LINUX) || defined(OPENSSL_APPLE)) &&                      \
    ((defined(OPENSSL_X86_64) && !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)) || \
     defined(OPENSSL_AARCH64))
#  define EC_NISTP_USE_S2N_BIGNUM
#  define EC_NISTP_USE_64BIT_LIMB
#else
// Fiat-crypto has both 64-bit and 32-bit implementation.
#  if defined(BORINGSSL_HAS_UINT128)
#    define EC_NISTP_USE_64BIT_LIMB
#  endif
#endif

#if defined(EC_NISTP_USE_64BIT_LIMB)
typedef uint64_t ec_nistp_felem_limb;
#else
typedef uint32_t ec_nistp_felem_limb;
#endif

// ec_nistp_felem_meth is a struct that holds pointers to implementations of field
// arithmetic functions for specific curves. It is meant to be used
// in higher level functions like this:
//   void point_double(nistp_felem_methods *ctx, ...) {
//     ctx->add(...);
//     ctx->mul(...);
//   }
// This makes the functions reusable between different curves by simply
// providing an appropriate methods object.
typedef struct {
  void (*add)(ec_nistp_felem_limb *c, const ec_nistp_felem_limb *a, const ec_nistp_felem_limb *b);
  void (*sub)(ec_nistp_felem_limb *c, const ec_nistp_felem_limb *a, const ec_nistp_felem_limb *b);
  void (*mul)(ec_nistp_felem_limb *c, const ec_nistp_felem_limb *a, const ec_nistp_felem_limb *b);
  void (*sqr)(ec_nistp_felem_limb *c, const ec_nistp_felem_limb *a);
} ec_nistp_felem_meth;

const ec_nistp_felem_meth *p256_felem_methods(void);
const ec_nistp_felem_meth *p384_felem_methods(void);
const ec_nistp_felem_meth *p521_felem_methods(void);

void ec_nistp_point_double(const ec_nistp_felem_meth *ctx,
                           ec_nistp_felem_limb *x_out,
                           ec_nistp_felem_limb *y_out,
                           ec_nistp_felem_limb *z_out,
                           const ec_nistp_felem_limb *x_in,
                           const ec_nistp_felem_limb *y_in,
                           const ec_nistp_felem_limb *z_in);
#endif // EC_NISTP_H

