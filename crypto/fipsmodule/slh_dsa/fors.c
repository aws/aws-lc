// Copyright (c) The slhdsa-c project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// FORS few-time signatures (FIPS 205, Section 8).

#include "./address.h"
#include "./internal.h"

// FIPS 205, Algorithm 14: fors_skGen (page 29).
static void slh_dsa_fors_sk_gen(SLHDSA_STATE *state, uint8_t *out_sk,
                                const uint8_t adrs[SLHDSA_ADRS_BYTES],
                                uint32_t idx) {
  uint8_t sk_adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_copy_key_pair_with_type(sk_adrs, adrs, SLHDSA_ADRS_FORS_PRF);
  slh_dsa_adrs_set_tree_index(sk_adrs, idx);
  slh_dsa_prf(state, out_sk, sk_adrs);
}

// FIPS 205, Algorithm 15: fors_node (page 30).
//
// This uses the same iterative treehash as |slh_dsa_xmss_node|. |adrs| must
// have type FORS_TREE and the key pair address set.
static void slh_dsa_fors_node(SLHDSA_STATE *state, uint8_t *out_node,
                              uint32_t i, uint32_t z,
                              uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  const size_t n = state->params->n;
  // |stack| holds one pending node for each height below z.
  assert(z <= SLHDSA_MAX_A);
  uint8_t stack[SLHDSA_MAX_A][SLHDSA_MAX_N];
  const uint32_t first_leaf = i << z;

  for (uint32_t j = 0; j < (UINT32_C(1) << z); j++) {
    const uint32_t leaf = first_leaf + j;
    uint8_t node[SLHDSA_MAX_N];

    // Algorithm 15, lines 2-5: a leaf is F applied to a FORS secret value,
    // which is overwritten in place.
    slh_dsa_fors_sk_gen(state, node, adrs, leaf);
    slh_dsa_adrs_set_tree_height(adrs, 0);
    slh_dsa_adrs_set_tree_index(adrs, leaf);
    slh_dsa_f(state, node, adrs, node);

    // Algorithm 15, lines 7-11.
    uint32_t height = 0;
    while ((j >> height) & 1) {
      slh_dsa_adrs_set_tree_height(adrs, height + 1);
      slh_dsa_adrs_set_tree_index(adrs, leaf >> (height + 1));
      slh_dsa_h(state, node, adrs, stack[height], node);
      height++;
    }

    if (height == z) {
      OPENSSL_memcpy(out_node, node, n);
    } else {
      OPENSSL_memcpy(stack[height], node, n);
    }
  }
}

// FIPS 205, Algorithm 16: fors_sign (page 31).
void slh_dsa_fors_sign(SLHDSA_STATE *state, uint8_t *out_sig, const uint8_t *md,
                       uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  const SLHDSA_PARAMS *params = state->params;
  const size_t n = params->n;

  uint32_t indices[SLHDSA_MAX_K];
  slh_dsa_base_2b(indices, md, params->a, params->k);

  for (uint32_t i = 0; i < params->k; i++) {
    // The revealed FORS secret value.
    slh_dsa_fors_sk_gen(state, out_sig, adrs, (i << params->a) + indices[i]);
    out_sig += n;

    // Its authentication path.
    for (uint32_t j = 0; j < params->a; j++) {
      const uint32_t s = (indices[i] >> j) ^ 1;
      slh_dsa_fors_node(state, out_sig, (i << (params->a - j)) + s, j, adrs);
      out_sig += n;
    }
  }
}

// FIPS 205, Algorithm 17: fors_pkFromSig (page 32).
void slh_dsa_fors_pk_from_sig(SLHDSA_STATE *state, uint8_t *out_pk,
                              const uint8_t *sig, const uint8_t *md,
                              uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  const SLHDSA_PARAMS *params = state->params;
  const size_t n = params->n;

  uint32_t indices[SLHDSA_MAX_K];
  slh_dsa_base_2b(indices, md, params->a, params->k);

  uint8_t roots[SLHDSA_MAX_K * SLHDSA_MAX_N];
  for (uint32_t i = 0; i < params->k; i++) {
    const uint32_t idx = (i << params->a) + indices[i];
    uint8_t *node = roots + i * n;

    // Compute the leaf from the revealed secret value.
    slh_dsa_adrs_set_tree_height(adrs, 0);
    slh_dsa_adrs_set_tree_index(adrs, idx);
    slh_dsa_f(state, node, adrs, sig);
    sig += n;

    // Compute the root from the leaf and the authentication path.
    for (uint32_t j = 0; j < params->a; j++) {
      slh_dsa_adrs_set_tree_height(adrs, j + 1);
      slh_dsa_adrs_set_tree_index(adrs, idx >> (j + 1));
      if (((indices[i] >> j) & 1) == 0) {
        slh_dsa_h(state, node, adrs, node, sig);
      } else {
        slh_dsa_h(state, node, adrs, sig, node);
      }
      sig += n;
    }
  }

  uint8_t pk_adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_copy_key_pair_with_type(pk_adrs, adrs, SLHDSA_ADRS_FORS_ROOTS);
  slh_dsa_t(state, out_pk, pk_adrs, roots, params->k * n);
}
