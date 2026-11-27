// Copyright (c) The slhdsa-c project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#ifndef OPENSSL_HEADER_CRYPTO_FIPSMODULE_SLH_DSA_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_FIPSMODULE_SLH_DSA_INTERNAL_H

#include <openssl/base.h>
#include <openssl/mem.h>

#include "../../internal.h"
#include "../sha/internal.h"
#include "./slh_dsa.h"

#if defined(__cplusplus)
extern "C" {
#endif

// Upper bounds over all supported parameter sets, used to size stack buffers.
#define SLHDSA_MAX_N 32
#define SLHDSA_MAX_LEN 67  // WOTS+ len = len1 + len2; SHAKE-256s: 64 + 3.
#define SLHDSA_MAX_HP 9    // XMSS tree height h'.
#define SLHDSA_MAX_A 14    // FORS tree height a.
#define SLHDSA_MAX_K 22    // Number of FORS trees k.
#define SLHDSA_MAX_M 47    // H_msg output length m.

#define SLHDSA_ADRS_BYTES 32

// slh_dsa_params_st holds a parameter set (FIPS 205, Section 11, Table 2).
// It contains only integers, so const instances need no relocations inside
// the FIPS module.
struct slh_dsa_params_st {
  uint32_t n;     // Security parameter: hash output length in bytes.
  uint32_t h;     // Total hypertree height.
  uint32_t d;     // Number of hypertree layers.
  uint32_t hp;    // h' = h / d, the height of each XMSS tree.
  uint32_t a;     // Height of each FORS tree.
  uint32_t k;     // Number of FORS trees.
  uint32_t lg_w;  // Number of bits encoded by each WOTS+ chain.
  uint32_t m;     // H_msg output length in bytes.
  uint32_t len1;  // WOTS+ len1 (FIPS 205, Equation 5.1).
  uint32_t len2;  // WOTS+ len2 (FIPS 205, Algorithm 1).
};

// SLHDSA_STATE carries the key material and hash context for one operation.
// It holds secret values (SK.seed, SK.prf, and intermediate hash state)
// during key generation and signing, and must be cleansed with
// |slh_dsa_state_cleanse| before going out of scope.
typedef struct {
  const SLHDSA_PARAMS *params;
  uint8_t sk_seed[SLHDSA_MAX_N];
  uint8_t sk_prf[SLHDSA_MAX_N];
  uint8_t pk_seed[SLHDSA_MAX_N];
  uint8_t pk_root[SLHDSA_MAX_N];
  // hash is scratch space shared by all SHAKE256 invocations of an
  // operation, so that a single cleanse at the end destroys every
  // intermediate value absorbed into it.
  KECCAK1600_CTX hash;
} SLHDSA_STATE;

static inline void slh_dsa_state_cleanse(SLHDSA_STATE *state) {
  OPENSSL_cleanse(state, sizeof(*state));
}

static inline uint32_t slh_dsa_wots_len(const SLHDSA_PARAMS *params) {
  return params->len1 + params->len2;
}

// FIPS 205, Algorithm 4: base_2b (page 16).
//
// slh_dsa_base_2b writes |out_len| base-2^|b| digits of |in| to |out|. |in|
// must hold at least ceil(|out_len| * |b| / 8) bytes. Requires
// 1 <= |b| <= 24.
static inline void slh_dsa_base_2b(uint32_t *out, const uint8_t *in, uint32_t b,
                                   size_t out_len) {
  size_t in_pos = 0;
  uint32_t bits = 0;
  uint32_t total = 0;
  const uint32_t mask = (UINT32_C(1) << b) - 1;
  for (size_t i = 0; i < out_len; i++) {
    while (bits < b) {
      // Bits above |bits| are discarded by |mask| below, so overflow of
      // |total| is harmless.
      total = (total << 8) | in[in_pos++];
      bits += 8;
    }
    bits -= b;
    out[i] = (total >> bits) & mask;
  }
}

// Tweakable hash functions and PRFs for the SHAKE instantiation (FIPS 205,
// Section 11.1). All write n bytes except |slh_dsa_h_msg|, which writes m
// bytes. Outputs may alias inputs.

// slh_dsa_f computes F(PK.seed, ADRS, M1) with an n-byte M1.
void slh_dsa_f(SLHDSA_STATE *state, uint8_t *out,
               const uint8_t adrs[SLHDSA_ADRS_BYTES], const uint8_t *in);

// slh_dsa_h computes H(PK.seed, ADRS, M2) with M2 = |left| || |right|.
void slh_dsa_h(SLHDSA_STATE *state, uint8_t *out,
               const uint8_t adrs[SLHDSA_ADRS_BYTES], const uint8_t *left,
               const uint8_t *right);

// slh_dsa_t computes T_l(PK.seed, ADRS, M_l) with an |in_len|-byte M_l.
void slh_dsa_t(SLHDSA_STATE *state, uint8_t *out,
               const uint8_t adrs[SLHDSA_ADRS_BYTES], const uint8_t *in,
               size_t in_len);

// slh_dsa_prf computes PRF(PK.seed, SK.seed, ADRS).
void slh_dsa_prf(SLHDSA_STATE *state, uint8_t *out,
                 const uint8_t adrs[SLHDSA_ADRS_BYTES]);

// slh_dsa_prf_msg computes PRF_msg(SK.prf, opt_rand, M) with
// M = |pre| || |msg|.
void slh_dsa_prf_msg(SLHDSA_STATE *state, uint8_t *out, const uint8_t *opt_rand,
                     const uint8_t *pre, size_t pre_len, const uint8_t *msg,
                     size_t msg_len);

// slh_dsa_h_msg computes H_msg(R, PK.seed, PK.root, M) with M = |pre| || |msg|.
void slh_dsa_h_msg(SLHDSA_STATE *state, uint8_t *out, const uint8_t *r,
                   const uint8_t *pre, size_t pre_len, const uint8_t *msg,
                   size_t msg_len);

// WOTS+ (FIPS 205, Section 5).

// slh_dsa_wots_pkgen implements wots_pkGen (Algorithm 6).
void slh_dsa_wots_pkgen(SLHDSA_STATE *state, uint8_t *out_pk,
                        uint8_t adrs[SLHDSA_ADRS_BYTES]);

// slh_dsa_wots_sign implements wots_sign (Algorithm 7) on the n-byte |msg|,
// writing len * n bytes to |out_sig|.
void slh_dsa_wots_sign(SLHDSA_STATE *state, uint8_t *out_sig,
                       const uint8_t *msg, uint8_t adrs[SLHDSA_ADRS_BYTES]);

// slh_dsa_wots_pk_from_sig implements wots_pkFromSig (Algorithm 8).
void slh_dsa_wots_pk_from_sig(SLHDSA_STATE *state, uint8_t *out_pk,
                              const uint8_t *sig, const uint8_t *msg,
                              uint8_t adrs[SLHDSA_ADRS_BYTES]);

// XMSS and the hypertree (FIPS 205, Sections 6 and 7).

// slh_dsa_xmss_node implements xmss_node (Algorithm 9).
void slh_dsa_xmss_node(SLHDSA_STATE *state, uint8_t *out_node, uint32_t i,
                       uint32_t z, uint8_t adrs[SLHDSA_ADRS_BYTES]);

// slh_dsa_ht_sign implements ht_sign (Algorithm 12), writing
// d * (len + h') * n bytes to |out_sig|.
void slh_dsa_ht_sign(SLHDSA_STATE *state, uint8_t *out_sig, const uint8_t *msg,
                     uint64_t idx_tree, uint32_t idx_leaf);

// slh_dsa_ht_verify implements ht_verify (Algorithm 13). It returns 1 if the
// hypertree signature is valid and 0 otherwise.
int slh_dsa_ht_verify(SLHDSA_STATE *state, const uint8_t *msg,
                      const uint8_t *sig, uint64_t idx_tree, uint32_t idx_leaf);

// FORS (FIPS 205, Section 8).

// slh_dsa_fors_sign implements fors_sign (Algorithm 16), writing
// k * (a + 1) * n bytes to |out_sig|.
void slh_dsa_fors_sign(SLHDSA_STATE *state, uint8_t *out_sig, const uint8_t *md,
                       uint8_t adrs[SLHDSA_ADRS_BYTES]);

// slh_dsa_fors_pk_from_sig implements fors_pkFromSig (Algorithm 17).
void slh_dsa_fors_pk_from_sig(SLHDSA_STATE *state, uint8_t *out_pk,
                              const uint8_t *sig, const uint8_t *md,
                              uint8_t adrs[SLHDSA_ADRS_BYTES]);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_FIPSMODULE_SLH_DSA_INTERNAL_H
