// Copyright (c) 2022, Google Inc.
// SPDX-License-Identifier: ISC

#ifndef OPENSSL_HEADER_CRYPTO_FIPSMODULE_DH_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_FIPSMODULE_DH_INTERNAL_H

#include <openssl/base.h>

#include <openssl/thread.h>

#if defined(__cplusplus)
extern "C" {
#endif


#define OPENSSL_DH_MAX_MODULUS_BITS 10000

struct dh_st {
  BIGNUM *p;
  BIGNUM *g;
  BIGNUM *q;
  BIGNUM *pub_key;   // g^x mod p
  BIGNUM *priv_key;  // x

  // priv_length contains the length, in bits, of the private value. If zero,
  // the private value will be the same length as |p|.
  unsigned priv_length;

  CRYPTO_MUTEX method_mont_p_lock;
  BN_MONT_CTX *method_mont_p;

  int flags;
  CRYPTO_refcount_t references;
};

// dh_check_params_fast checks basic invariants on |dh|'s domain parameters. It
// does not check that |dh| forms a valid group, only that the sizes are within
// DoS bounds.
int dh_check_params_fast(const DH *dh);

// dh_fast_path_from_safe_group returns one if |dh| is one of the well-known
// standard safe-prime groups (RFC 3526 MODP or RFC 7919 ffdhe) and can be
// validated without primality testing, and zero otherwise. It requires g = 2
// and p to match a known group prime. A subgroup order q is optional: if
// present, it is accepted only when the matched group defines one (RFC 7919)
// and it equals (p-1)/2; a q that is not part of the group definition returns
// zero so that |DH_check| performs its full validation.
int dh_fast_path_from_safe_group(const DH *dh);

// dh_compute_key_padded_no_self_test does the same as |DH_compute_key_padded|,
// but doesn't try to run the self-test first. This is for use in the self tests
// themselves, to prevent an infinite loop.
int dh_compute_key_padded_no_self_test(unsigned char *out,
                                       const BIGNUM *peers_key, DH *dh);

// DH_get_rfc7919_3072 returns the group `ffdhe3072` from
// https://tools.ietf.org/html/rfc7919#appendix-A.2. It returns NULL if out
// of memory.
OPENSSL_EXPORT DH *DH_get_rfc7919_3072(void);

// DH_get_rfc7919_8192 returns the group `ffdhe8192` from
// https://tools.ietf.org/html/rfc7919#appendix-A.4. It returns NULL if out
// of memory.
OPENSSL_EXPORT DH *DH_get_rfc7919_8192(void);

// dh_calculate_rfc7919_from_p constructs a |DH| from a raw RFC 7919 modulus,
// deriving q = (p-1)/2 and g = 2 as all RFC 7919 groups do. |data| points to
// the |data_len| little-endian |BN_ULONG| words of p. It returns NULL on
// allocation failure.
//
// |DH_get_rfc7919_2048| declaration can be removed when |DH_get_rfc7919_2048|
// has been moved to params.c; |DH_get_rfc7919_2048| is used in a bunch of FIPS
// test code still.
DH *dh_calculate_rfc7919_from_p(const BN_ULONG data[], size_t data_len);

#if defined(__cplusplus)
}
#endif

#endif  // OPENSSL_HEADER_CRYPTO_FIPSMODULE_DH_INTERNAL_H
