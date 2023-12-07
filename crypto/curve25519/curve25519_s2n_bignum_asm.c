// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include "../fipsmodule/cpucap/internal.h"

#if defined(CURVE25519_S2N_BIGNUM_CAPABLE)
#include "../../third_party/s2n-bignum/include/s2n-bignum_aws-lc.h"
#endif

// Stub functions if s2n-bignum implementations are not compiled.
// These functions have to abort, otherwise we risk applications assuming they
// did work without actually doing anything.
#if !defined(CURVE25519_S2N_BIGNUM_CAPABLE)

#define S2N_BIGNUM_STUB_FUNC(return_type, symbol, ...) \
  return_type symbol(__VA_ARGS__); \
  return_type symbol(__VA_ARGS__) { abort(); } \

S2N_BIGNUM_STUB_FUNC(void, bignum_mod_n25519, uint64_t z[4], uint64_t k, uint64_t *x)
S2N_BIGNUM_STUB_FUNC(void, bignum_neg_p25519, uint64_t z[4], uint64_t x[4])
S2N_BIGNUM_STUB_FUNC(void, bignum_madd_n25519, uint64_t z[4], uint64_t x[4], uint64_t y[4], uint64_t c[4])
S2N_BIGNUM_STUB_FUNC(void, bignum_madd_n25519_alt, uint64_t z[4], uint64_t x[4], uint64_t y[4], uint64_t c[4])
S2N_BIGNUM_STUB_FUNC(void, edwards25519_encode, uint8_t z[32], uint64_t p[8])
S2N_BIGNUM_STUB_FUNC(uint64_t, edwards25519_decode, uint64_t z[8], const uint8_t c[32])
S2N_BIGNUM_STUB_FUNC(uint64_t, edwards25519_decode_alt, uint64_t z[8], const uint8_t c[32])
S2N_BIGNUM_STUB_FUNC(void, edwards25519_scalarmulbase, uint64_t res[8],uint64_t scalar[4])
S2N_BIGNUM_STUB_FUNC(void, edwards25519_scalarmulbase_alt, uint64_t res[8],uint64_t scalar[4])
S2N_BIGNUM_STUB_FUNC(void, edwards25519_scalarmuldouble, uint64_t res[8], uint64_t scalar[4], uint64_t point[8], uint64_t bscalar[4])
S2N_BIGNUM_STUB_FUNC(void, edwards25519_scalarmuldouble_alt, uint64_t res[8], uint64_t scalar[4], uint64_t point[8], uint64_t bscalar[4])
S2N_BIGNUM_STUB_FUNC(void, curve25519_x25519_byte, uint8_t res[32], const uint8_t scalar[32], const uint8_t point[32])
S2N_BIGNUM_STUB_FUNC(void, curve25519_x25519_byte_alt, uint8_t res[32], const uint8_t scalar[32], const uint8_t point[32])
S2N_BIGNUM_STUB_FUNC(void, curve25519_x25519base_byte, uint8_t res[32], const uint8_t scalar[32])
S2N_BIGNUM_STUB_FUNC(void, curve25519_x25519base_byte_alt, uint8_t res[32], const uint8_t scalar[32])
#endif // !defined(CURVE25519_S2N_BIGNUM_CAPABLE)

// curve25519_s2n_bignum_use_no_alt_implementation returns 1 if the no_alt
// s2n-bignum implementation should be used and 0 otherwise.
//
// Below is the decision logic for which assembly backend implementation
// of x25519 s2n-bignum we should use if x25519 s2n-bignum capable. Currently,
// we support the following implementations.
//
// x86_64:
//   - s2n-bignum-no-alt: hardware implementation using bmi2+adx instruction sets
//   - s2n-bignum-alt: hardware implementation using standard instructions
//
// aarch64:
//   - s2n-bignum-no-alt: hardware implementation for "low" multiplier throughput
//   - s2n-bignum-alt: hardware implementation for "high" multiplier throughput
//
// Through experiments we have found that:
//
// For x86_64: bmi+adc will almost always give a performance boost. So, here we
//   prefer s2n-bignum-no-alt over s2n-bignum-alt if the former is supported.
// For aarch64: if a wide multiplier is supported, we prefer s2n-bignum-alt over
//   s2n-bignum-no-alt if the former is supported.
//   |curve25519_s2n_bignum_alt_capable| specifically looks to match CPUs that
//   have wide multipliers. this ensures that s2n-bignum-alt will only be used
//   on such CPUs.
OPENSSL_INLINE int curve25519_s2n_bignum_use_no_alt_implementation(void);
OPENSSL_INLINE int curve25519_s2n_bignum_use_no_alt_implementation(void) {
#if defined(OPENSSL_X86_64)
  // For x86_64 the no_alt implementation is bmi2+adx. Prefer if available. 
  if (CRYPTO_is_BMI2_capable() == 1 && CRYPTO_is_ADX_capable() == 1) {
    return 1;
  } else {
    return 0;
  }
#elif defined(OPENSSL_AARCH64)
  // For aarch64 the alt implementation is for wide multipliers. Prefer if
  // available.
  if (CRYPTO_is_ARMv8_wide_multiplier_capable() == 1) {
    return 0;
  } else {
    return 1;
  }
#endif
  // Have to return some default value.
  return 0;
}

void x25519_scalar_mult_generic_s2n_bignum(
  uint8_t out_shared_key[X25519_SHARED_KEY_LEN],
  const uint8_t private_key[X25519_PRIVATE_KEY_LEN],
  const uint8_t peer_public_value[X25519_PUBLIC_VALUE_LEN]) {

  uint8_t private_key_internal_demask[X25519_PRIVATE_KEY_LEN];
  OPENSSL_memcpy(private_key_internal_demask, private_key, X25519_PRIVATE_KEY_LEN);
  private_key_internal_demask[0] &= 248;
  private_key_internal_demask[31] &= 127;
  private_key_internal_demask[31] |= 64;

  if (curve25519_s2n_bignum_use_no_alt_implementation() == 1) {
    curve25519_x25519_byte(out_shared_key, private_key_internal_demask,
      peer_public_value);
  } else {
    curve25519_x25519_byte_alt(out_shared_key, private_key_internal_demask,
      peer_public_value);
  }
}

void x25519_public_from_private_s2n_bignum(
  uint8_t out_public_value[X25519_PUBLIC_VALUE_LEN],
	const uint8_t private_key[X25519_PRIVATE_KEY_LEN]) {

  uint8_t private_key_internal_demask[X25519_PRIVATE_KEY_LEN];
  OPENSSL_memcpy(private_key_internal_demask, private_key, X25519_PRIVATE_KEY_LEN);
  private_key_internal_demask[0] &= 248;
  private_key_internal_demask[31] &= 127;
  private_key_internal_demask[31] |= 64;

  if (curve25519_s2n_bignum_use_no_alt_implementation() == 1) {
    curve25519_x25519base_byte(out_public_value, private_key_internal_demask);
  } else {
    curve25519_x25519base_byte_alt(out_public_value, private_key_internal_demask);
  }
}

void ed25519_public_key_from_hashed_seed_s2n_bignum(
  uint8_t out_public_key[ED25519_PUBLIC_KEY_LEN],
  uint8_t az[SHA512_DIGEST_LENGTH]) {

  uint64_t uint64_point[8] = {0};
  uint64_t uint64_hashed_seed[4] = {0};
  OPENSSL_memcpy(uint64_hashed_seed, az, 32);

  if (curve25519_s2n_bignum_use_no_alt_implementation() == 1) {
    edwards25519_scalarmulbase(uint64_point, uint64_hashed_seed);
  } else {
    edwards25519_scalarmulbase_alt(uint64_point, uint64_hashed_seed);
  }

  edwards25519_encode(out_public_key, uint64_point);
}

void ed25519_sign_s2n_bignum(uint8_t out_sig[ED25519_SIGNATURE_LEN],
  uint8_t r[SHA512_DIGEST_LENGTH], const uint8_t *s, const uint8_t *A,
  const void *message, size_t message_len) {
  
  void (*scalarmulbase)(uint64_t res[8],uint64_t scalar[4]);
  void (*madd)(uint64_t z[4], uint64_t x[4], uint64_t y[4], uint64_t c[4]);

  if (curve25519_s2n_bignum_use_no_alt_implementation() == 1) {
    scalarmulbase = edwards25519_scalarmulbase;
    madd = bignum_madd_n25519;
  } else {
    scalarmulbase = edwards25519_scalarmulbase_alt;
    madd = bignum_madd_n25519_alt;
  }

  uint8_t k[SHA512_DIGEST_LENGTH] = {0};
  uint64_t R[8] = {0};
  uint64_t S[4] = {0};
  uint64_t uint64_r[8] = {0};
  uint64_t uint64_k[8] = {0};
  uint64_t uint64_s[4] = {0};
  OPENSSL_memcpy(uint64_r, r, 64);
  OPENSSL_memcpy(uint64_s, s, 32);

  // Reduce r modulo the order of the base-point B.
  bignum_mod_n25519(uint64_r, 8, uint64_r);

  // Compute [r]B.
  scalarmulbase(R, uint64_r);
  edwards25519_encode(out_sig, R);

  // Compute k = SHA512(R || A || message)
  // R is of length 32 octets
  ed25519_sha512(k, out_sig, 32, A, ED25519_PUBLIC_KEY_LEN, message,
    message_len);
  OPENSSL_memcpy(uint64_k, k, SHA512_DIGEST_LENGTH);
  bignum_mod_n25519(uint64_k, 8, uint64_k);

  // Compute S = r + k * s modulo the order of the base-point B.
  // out_sig = R || S
  madd(S, uint64_k, uint64_s, uint64_r);
  OPENSSL_memcpy(out_sig + 32, S, 32);
}

int ed25519_verify_s2n_bignum(uint8_t R_computed_encoded[32],
  const uint8_t public_key[ED25519_PUBLIC_KEY_LEN], uint8_t R_expected[32],
  uint8_t S[32], const uint8_t *message, size_t message_len) {

  void (*scalarmuldouble)(uint64_t res[8], uint64_t scalar[4],
    uint64_t point[8], uint64_t bscalar[4]);
  uint64_t (*decode)(uint64_t z[8], const uint8_t c[32]);

  if (curve25519_s2n_bignum_use_no_alt_implementation() == 1) {
    scalarmuldouble = edwards25519_scalarmuldouble;
    decode = edwards25519_decode;
  } else {
    scalarmuldouble = edwards25519_scalarmuldouble_alt;
    decode = edwards25519_decode_alt;
  }

  uint8_t k[SHA512_DIGEST_LENGTH] = {0};
  uint64_t uint64_k[8] = {0};
  uint64_t uint64_R[8] = {0};
  uint64_t uint64_S[4] = {0};
  uint64_t A[8] = {0};

  // Decode public key as A'.
  if (decode(A, public_key) != 0) {
    return 0;
  }

  // Step: rfc8032 5.1.7.2
  // Compute k = SHA512(R_expected || public_key || message).
  ed25519_sha512(k, R_expected, 32, public_key, ED25519_PUBLIC_KEY_LEN, message,
    message_len);
  OPENSSL_memcpy(uint64_k, k, SHA512_DIGEST_LENGTH);
  bignum_mod_n25519(uint64_k, 8, uint64_k);

  // Step: rfc8032 5.1.7.3
  // Recall, we must compute [S]B - [k]A'.
  // First negate A'. Point negation for the twisted edwards curve when points
  // are represented in the extended coordinate system is simply:
  //   -(X,Y,Z,T) = (-X,Y,Z,-T).
  // See "Twisted Edwards curves revisited" https://ia.cr/2008/522.
  bignum_neg_p25519(A, A);

  // Compute R_have <- [S]B - [k]A'.
  OPENSSL_memcpy(uint64_S, S, 32);
  scalarmuldouble(uint64_R, uint64_k, A, uint64_S);
  edwards25519_encode(R_computed_encoded, uint64_R);

  return 1;
}
