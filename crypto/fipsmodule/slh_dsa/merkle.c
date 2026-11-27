// Copyright (c) The slhdsa-c project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// XMSS (FIPS 205, Section 6) and the SLH-DSA hypertree (Section 7).

#include "./address.h"
#include "./internal.h"

// FIPS 205, Algorithm 9: xmss_node (page 23).
//
// FIPS 205 defines xmss_node recursively. This is the equivalent iterative
// treehash: it visits the 2^z leaves under node (i, z) from left to right and
// keeps one pending left sibling per height in |stack|.
void slh_dsa_xmss_node(SLHDSA_STATE *state, uint8_t *out_node, uint32_t i,
                       uint32_t z, uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  const size_t n = state->params->n;
  // |stack| holds one pending node for each height below z.
  assert(z <= SLHDSA_MAX_HP);
  uint8_t stack[SLHDSA_MAX_HP][SLHDSA_MAX_N];
  const uint32_t first_leaf = i << z;

  for (uint32_t j = 0; j < (UINT32_C(1) << z); j++) {
    const uint32_t leaf = first_leaf + j;
    uint8_t node[SLHDSA_MAX_N];

    // Algorithm 9, lines 2-4: a leaf is a WOTS+ public key.
    slh_dsa_adrs_set_type_and_clear(adrs, SLHDSA_ADRS_WOTS_HASH);
    slh_dsa_adrs_set_key_pair_address(adrs, leaf);
    slh_dsa_wots_pkgen(state, node, adrs);

    // Algorithm 9, lines 6-11: while |node| is a right child, combine it
    // with the pending left sibling.
    uint32_t height = 0;
    while ((j >> height) & 1) {
      slh_dsa_adrs_set_type_and_clear(adrs, SLHDSA_ADRS_TREE);
      slh_dsa_adrs_set_tree_height(adrs, height + 1);
      slh_dsa_adrs_set_tree_index(adrs, leaf >> (height + 1));
      slh_dsa_h(state, node, adrs, stack[height], node);
      height++;
    }

    if (height == z) {
      // Only reached on the final leaf, when |node| is the subtree root.
      OPENSSL_memcpy(out_node, node, n);
    } else {
      OPENSSL_memcpy(stack[height], node, n);
    }
  }
}

// FIPS 205, Algorithm 10: xmss_sign (page 24).
//
// slh_dsa_xmss_sign writes (len + h') * n bytes to |out_sig|.
static void slh_dsa_xmss_sign(SLHDSA_STATE *state, uint8_t *out_sig,
                              const uint8_t *msg, uint32_t idx,
                              uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  const SLHDSA_PARAMS *params = state->params;
  const size_t n = params->n;
  uint8_t *auth = out_sig + slh_dsa_wots_len(params) * n;

  // Build the authentication path.
  for (uint32_t j = 0; j < params->hp; j++) {
    const uint32_t k = (idx >> j) ^ 1;
    slh_dsa_xmss_node(state, auth + j * n, k, j, adrs);
  }

  slh_dsa_adrs_set_type_and_clear(adrs, SLHDSA_ADRS_WOTS_HASH);
  slh_dsa_adrs_set_key_pair_address(adrs, idx);
  slh_dsa_wots_sign(state, out_sig, msg, adrs);
}

// FIPS 205, Algorithm 11: xmss_pkFromSig (page 25).
//
// |out_root| may alias |msg|.
static void slh_dsa_xmss_pk_from_sig(SLHDSA_STATE *state, uint8_t *out_root,
                                     uint32_t idx, const uint8_t *sig,
                                     const uint8_t *msg,
                                     uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  const SLHDSA_PARAMS *params = state->params;
  const size_t n = params->n;
  const uint8_t *auth = sig + slh_dsa_wots_len(params) * n;

  // Compute the WOTS+ public key (the leaf) from the WOTS+ signature.
  uint8_t node[SLHDSA_MAX_N];
  slh_dsa_adrs_set_type_and_clear(adrs, SLHDSA_ADRS_WOTS_HASH);
  slh_dsa_adrs_set_key_pair_address(adrs, idx);
  slh_dsa_wots_pk_from_sig(state, node, sig, msg, adrs);

  // Compute the root from the leaf and the authentication path.
  slh_dsa_adrs_set_type_and_clear(adrs, SLHDSA_ADRS_TREE);
  for (uint32_t k = 0; k < params->hp; k++) {
    slh_dsa_adrs_set_tree_height(adrs, k + 1);
    slh_dsa_adrs_set_tree_index(adrs, idx >> (k + 1));
    if (((idx >> k) & 1) == 0) {
      slh_dsa_h(state, node, adrs, node, auth + k * n);
    } else {
      slh_dsa_h(state, node, adrs, auth + k * n, node);
    }
  }
  OPENSSL_memcpy(out_root, node, n);
}

// FIPS 205, Algorithm 12: ht_sign (page 27).
void slh_dsa_ht_sign(SLHDSA_STATE *state, uint8_t *out_sig, const uint8_t *msg,
                     uint64_t idx_tree, uint32_t idx_leaf) {
  const SLHDSA_PARAMS *params = state->params;
  const size_t xmss_sig_len =
      (slh_dsa_wots_len(params) + params->hp) * params->n;
  const uint64_t leaf_mask = (UINT64_C(1) << params->hp) - 1;

  uint8_t adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_zero(adrs);
  slh_dsa_adrs_set_tree_address(adrs, idx_tree);
  slh_dsa_xmss_sign(state, out_sig, msg, idx_leaf, adrs);

  uint8_t root[SLHDSA_MAX_N];
  for (uint32_t j = 1; j < params->d; j++) {
    // Each layer signs the root of the XMSS tree in the layer below. FIPS
    // 205 computes that root at the end of the previous iteration; computing
    // it here is equivalent and skips the unused root of the top layer.
    slh_dsa_xmss_pk_from_sig(state, root, idx_leaf, out_sig,
                             j == 1 ? msg : root, adrs);
    // The root is public. It was computed from SK.seed, so constant-time
    // validation would otherwise treat branches on its WOTS+ digits as
    // secret-dependent.
    CONSTTIME_DECLASSIFY(root, params->n);

    out_sig += xmss_sig_len;
    idx_leaf = (uint32_t)(idx_tree & leaf_mask);
    idx_tree >>= params->hp;
    slh_dsa_adrs_set_layer_address(adrs, j);
    slh_dsa_adrs_set_tree_address(adrs, idx_tree);
    slh_dsa_xmss_sign(state, out_sig, root, idx_leaf, adrs);
  }
}

// FIPS 205, Algorithm 13: ht_verify (page 28).
int slh_dsa_ht_verify(SLHDSA_STATE *state, const uint8_t *msg,
                      const uint8_t *sig, uint64_t idx_tree,
                      uint32_t idx_leaf) {
  const SLHDSA_PARAMS *params = state->params;
  const size_t xmss_sig_len =
      (slh_dsa_wots_len(params) + params->hp) * params->n;
  const uint64_t leaf_mask = (UINT64_C(1) << params->hp) - 1;

  uint8_t adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_zero(adrs);
  slh_dsa_adrs_set_tree_address(adrs, idx_tree);

  uint8_t node[SLHDSA_MAX_N];
  slh_dsa_xmss_pk_from_sig(state, node, idx_leaf, sig, msg, adrs);

  for (uint32_t j = 1; j < params->d; j++) {
    idx_leaf = (uint32_t)(idx_tree & leaf_mask);
    idx_tree >>= params->hp;
    slh_dsa_adrs_set_layer_address(adrs, j);
    slh_dsa_adrs_set_tree_address(adrs, idx_tree);
    sig += xmss_sig_len;
    slh_dsa_xmss_pk_from_sig(state, node, idx_leaf, sig, node, adrs);
  }

  return CRYPTO_memcmp(node, state->pk_root, params->n) == 0;
}
