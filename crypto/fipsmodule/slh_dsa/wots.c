// Copyright (c) The slhdsa-c project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// WOTS+ one-time signatures (FIPS 205, Section 5).

#include "./address.h"
#include "./internal.h"

// FIPS 205, Algorithm 5: chain (page 18).
//
// slh_dsa_wots_chain applies F |steps| times to the n-byte |in|, starting at
// chain position |start|. |out| may alias |in|.
static void slh_dsa_wots_chain(SLHDSA_STATE *state, uint8_t *out,
                               const uint8_t *in, uint32_t start,
                               uint32_t steps,
                               uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  OPENSSL_memmove(out, in, state->params->n);
  for (uint32_t j = start; j < start + steps; j++) {
    slh_dsa_adrs_set_hash_address(adrs, j);
    slh_dsa_f(state, out, adrs, out);
  }
}

// slh_dsa_wots_digits computes the len1 base-w digits of the n-byte |msg|
// followed by the len2 digits of its checksum. This is lines 1-7 of both
// Algorithm 7 and Algorithm 8.
static void slh_dsa_wots_digits(const SLHDSA_PARAMS *params,
                                uint32_t out[SLHDSA_MAX_LEN],
                                const uint8_t *msg) {
  const uint32_t w_minus_1 = (UINT32_C(1) << params->lg_w) - 1;
  slh_dsa_base_2b(out, msg, params->lg_w, params->len1);

  uint32_t csum = 0;
  for (uint32_t i = 0; i < params->len1; i++) {
    csum += w_minus_1 - out[i];
  }
  // Left-shift so the checksum's digits are aligned to a byte boundary.
  const uint32_t csum_bits = params->len2 * params->lg_w;
  csum <<= (8 - (csum_bits % 8)) % 8;

  // toByte(csum, ceil(len2 * lg_w / 8)) (Algorithm 3).
  uint8_t csum_bytes[4] = {0};
  const size_t csum_len = (csum_bits + 7) / 8;
  assert(csum_len <= sizeof(csum_bytes));
  for (size_t i = 0; i < csum_len; i++) {
    csum_bytes[i] = (uint8_t)(csum >> (8 * (csum_len - 1 - i)));
  }
  slh_dsa_base_2b(out + params->len1, csum_bytes, params->lg_w, params->len2);
}

// FIPS 205, Algorithm 6: wots_pkGen (page 18).
void slh_dsa_wots_pkgen(SLHDSA_STATE *state, uint8_t *out_pk,
                        uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  const SLHDSA_PARAMS *params = state->params;
  const size_t n = params->n;
  const uint32_t len = slh_dsa_wots_len(params);
  const uint32_t w_minus_1 = (UINT32_C(1) << params->lg_w) - 1;

  uint8_t sk_adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_copy_key_pair_with_type(sk_adrs, adrs, SLHDSA_ADRS_WOTS_PRF);

  // Each chain starts from a secret value, which is overwritten in place by
  // the chain's public end value.
  uint8_t tmp[SLHDSA_MAX_LEN * SLHDSA_MAX_N];
  for (uint32_t i = 0; i < len; i++) {
    slh_dsa_adrs_set_chain_address(sk_adrs, i);
    slh_dsa_prf(state, tmp + i * n, sk_adrs);
    slh_dsa_adrs_set_chain_address(adrs, i);
    slh_dsa_wots_chain(state, tmp + i * n, tmp + i * n, 0, w_minus_1, adrs);
  }

  uint8_t pk_adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_copy_key_pair_with_type(pk_adrs, adrs, SLHDSA_ADRS_WOTS_PK);
  slh_dsa_t(state, out_pk, pk_adrs, tmp, len * n);
}

// FIPS 205, Algorithm 7: wots_sign (page 20).
void slh_dsa_wots_sign(SLHDSA_STATE *state, uint8_t *out_sig,
                       const uint8_t *msg, uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  const SLHDSA_PARAMS *params = state->params;
  const size_t n = params->n;
  const uint32_t len = slh_dsa_wots_len(params);

  uint32_t digits[SLHDSA_MAX_LEN];
  slh_dsa_wots_digits(params, digits, msg);

  uint8_t sk_adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_copy_key_pair_with_type(sk_adrs, adrs, SLHDSA_ADRS_WOTS_PRF);

  for (uint32_t i = 0; i < len; i++) {
    slh_dsa_adrs_set_chain_address(sk_adrs, i);
    slh_dsa_prf(state, out_sig + i * n, sk_adrs);
    slh_dsa_adrs_set_chain_address(adrs, i);
    slh_dsa_wots_chain(state, out_sig + i * n, out_sig + i * n, 0, digits[i],
                       adrs);
  }
}

// FIPS 205, Algorithm 8: wots_pkFromSig (page 21).
void slh_dsa_wots_pk_from_sig(SLHDSA_STATE *state, uint8_t *out_pk,
                              const uint8_t *sig, const uint8_t *msg,
                              uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  const SLHDSA_PARAMS *params = state->params;
  const size_t n = params->n;
  const uint32_t len = slh_dsa_wots_len(params);
  const uint32_t w_minus_1 = (UINT32_C(1) << params->lg_w) - 1;

  uint32_t digits[SLHDSA_MAX_LEN];
  slh_dsa_wots_digits(params, digits, msg);

  uint8_t tmp[SLHDSA_MAX_LEN * SLHDSA_MAX_N];
  for (uint32_t i = 0; i < len; i++) {
    slh_dsa_adrs_set_chain_address(adrs, i);
    slh_dsa_wots_chain(state, tmp + i * n, sig + i * n, digits[i],
                       w_minus_1 - digits[i], adrs);
  }

  uint8_t pk_adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_copy_key_pair_with_type(pk_adrs, adrs, SLHDSA_ADRS_WOTS_PK);
  slh_dsa_t(state, out_pk, pk_adrs, tmp, len * n);
}
