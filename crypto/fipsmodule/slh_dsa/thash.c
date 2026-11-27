// Copyright (c) The slhdsa-c project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// Tweakable hash functions and PRFs for SLH-DSA using SHAKE (FIPS 205,
// Section 11.1, page 44). Every function is a single SHAKE256 invocation:
//
//   H_msg(R, PK.seed, PK.root, M) = SHAKE256(R || PK.seed || PK.root || M, 8m)
//   PRF(PK.seed, SK.seed, ADRS)   = SHAKE256(PK.seed || ADRS || SK.seed, 8n)
//   PRF_msg(SK.prf, opt_rand, M)  = SHAKE256(SK.prf || opt_rand || M, 8n)
//   F(PK.seed, ADRS, M1)          = SHAKE256(PK.seed || ADRS || M1, 8n)
//   H(PK.seed, ADRS, M2)          = SHAKE256(PK.seed || ADRS || M2, 8n)
//   T_l(PK.seed, ADRS, M_l)       = SHAKE256(PK.seed || ADRS || M_l, 8n)
//
// All of them reuse |state->hash|, which may then hold secret data. Callers
// cleanse it with the rest of |state| at the end of each operation.
//
// The SHAKE_* functions only fail on NULL arguments or an invalid block size,
// neither of which can occur here, so their return values are ignored.

#include "./internal.h"

static void slh_dsa_shake256_begin(SLHDSA_STATE *state) {
  (void)SHAKE_Init(&state->hash, SHAKE256_BLOCKSIZE);
}

static void slh_dsa_shake256_absorb(SLHDSA_STATE *state, const uint8_t *in,
                                    size_t in_len) {
  (void)SHAKE_Absorb(&state->hash, in, in_len);
}

static void slh_dsa_shake256_end(SLHDSA_STATE *state, uint8_t *out,
                                 size_t out_len) {
  (void)SHAKE_Final(out, &state->hash, out_len);
}

// slh_dsa_thash_begin absorbs the common PK.seed || ADRS prefix.
static void slh_dsa_thash_begin(SLHDSA_STATE *state,
                                const uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  slh_dsa_shake256_begin(state);
  slh_dsa_shake256_absorb(state, state->pk_seed, state->params->n);
  slh_dsa_shake256_absorb(state, adrs, SLHDSA_ADRS_BYTES);
}

void slh_dsa_f(SLHDSA_STATE *state, uint8_t *out,
               const uint8_t adrs[SLHDSA_ADRS_BYTES], const uint8_t *in) {
  const size_t n = state->params->n;
  slh_dsa_thash_begin(state, adrs);
  slh_dsa_shake256_absorb(state, in, n);
  slh_dsa_shake256_end(state, out, n);
}

void slh_dsa_h(SLHDSA_STATE *state, uint8_t *out,
               const uint8_t adrs[SLHDSA_ADRS_BYTES], const uint8_t *left,
               const uint8_t *right) {
  const size_t n = state->params->n;
  slh_dsa_thash_begin(state, adrs);
  slh_dsa_shake256_absorb(state, left, n);
  slh_dsa_shake256_absorb(state, right, n);
  slh_dsa_shake256_end(state, out, n);
}

void slh_dsa_t(SLHDSA_STATE *state, uint8_t *out,
               const uint8_t adrs[SLHDSA_ADRS_BYTES], const uint8_t *in,
               size_t in_len) {
  slh_dsa_thash_begin(state, adrs);
  slh_dsa_shake256_absorb(state, in, in_len);
  slh_dsa_shake256_end(state, out, state->params->n);
}

void slh_dsa_prf(SLHDSA_STATE *state, uint8_t *out,
                 const uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  slh_dsa_f(state, out, adrs, state->sk_seed);
}

void slh_dsa_prf_msg(SLHDSA_STATE *state, uint8_t *out, const uint8_t *opt_rand,
                     const uint8_t *pre, size_t pre_len, const uint8_t *msg,
                     size_t msg_len) {
  const size_t n = state->params->n;
  slh_dsa_shake256_begin(state);
  slh_dsa_shake256_absorb(state, state->sk_prf, n);
  slh_dsa_shake256_absorb(state, opt_rand, n);
  slh_dsa_shake256_absorb(state, pre, pre_len);
  slh_dsa_shake256_absorb(state, msg, msg_len);
  slh_dsa_shake256_end(state, out, n);
}

void slh_dsa_h_msg(SLHDSA_STATE *state, uint8_t *out, const uint8_t *r,
                   const uint8_t *pre, size_t pre_len, const uint8_t *msg,
                   size_t msg_len) {
  const size_t n = state->params->n;
  slh_dsa_shake256_begin(state);
  slh_dsa_shake256_absorb(state, r, n);
  slh_dsa_shake256_absorb(state, state->pk_seed, n);
  slh_dsa_shake256_absorb(state, state->pk_root, n);
  slh_dsa_shake256_absorb(state, pre, pre_len);
  slh_dsa_shake256_absorb(state, msg, msg_len);
  slh_dsa_shake256_end(state, out, state->params->m);
}
