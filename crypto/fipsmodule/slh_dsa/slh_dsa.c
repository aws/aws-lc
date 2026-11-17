// Copyright (c) The slhdsa-c project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// SLH-DSA (FIPS 205) key generation, signing and verification.

#include "./slh_dsa.h"

#include <openssl/nid.h>
#include <openssl/rand.h>

#include "../service_indicator/internal.h"
#include "./address.h"
#include "./internal.h"

// Parameter sets (FIPS 205, Section 11, Table 2, page 43). len1 and len2 are
// given by Equation 5.1 and Algorithm 1 (gen_len2, page 10). They are
// precomputed here and checked against those formulas in slh_dsa_test.cc.
static const SLHDSA_PARAMS kSLHDSA_SHAKE_128S = {.n = 16,
                                                 .h = 63,
                                                 .d = 7,
                                                 .hp = 9,
                                                 .a = 12,
                                                 .k = 14,
                                                 .lg_w = 4,
                                                 .m = 30,
                                                 .len1 = 32,
                                                 .len2 = 3};

static const SLHDSA_PARAMS kSLHDSA_SHAKE_192S = {.n = 24,
                                                 .h = 63,
                                                 .d = 7,
                                                 .hp = 9,
                                                 .a = 14,
                                                 .k = 17,
                                                 .lg_w = 4,
                                                 .m = 39,
                                                 .len1 = 48,
                                                 .len2 = 3};

static const SLHDSA_PARAMS kSLHDSA_SHAKE_256S = {.n = 32,
                                                 .h = 64,
                                                 .d = 8,
                                                 .hp = 8,
                                                 .a = 14,
                                                 .k = 22,
                                                 .lg_w = 4,
                                                 .m = 47,
                                                 .len1 = 64,
                                                 .len2 = 3};

const SLHDSA_PARAMS *slh_dsa_shake_128s_params(void) {
  return &kSLHDSA_SHAKE_128S;
}
const SLHDSA_PARAMS *slh_dsa_shake_192s_params(void) {
  return &kSLHDSA_SHAKE_192S;
}
const SLHDSA_PARAMS *slh_dsa_shake_256s_params(void) {
  return &kSLHDSA_SHAKE_256S;
}

size_t slh_dsa_public_key_bytes(const SLHDSA_PARAMS *params) {
  return 2 * params->n;
}

size_t slh_dsa_private_key_bytes(const SLHDSA_PARAMS *params) {
  return 4 * params->n;
}

size_t slh_dsa_seed_bytes(const SLHDSA_PARAMS *params) { return 3 * params->n; }

size_t slh_dsa_signature_bytes(const SLHDSA_PARAMS *params) {
  // R, then k FORS secret values with a-node authentication paths, then d
  // XMSS signatures of len WOTS+ values plus an h'-node authentication path
  // (FIPS 205, Section 9.2). d * h' = h.
  return (1 + params->k * (1 + params->a) + params->h +
          params->d * slh_dsa_wots_len(params)) *
         params->n;
}

static size_t slh_dsa_fors_signature_bytes(const SLHDSA_PARAMS *params) {
  return params->k * (1 + params->a) * params->n;
}

static void slh_dsa_state_init(SLHDSA_STATE *state,
                               const SLHDSA_PARAMS *params) {
  OPENSSL_memset(state, 0, sizeof(*state));
  state->params = params;
}

static void slh_dsa_state_init_from_public_key(SLHDSA_STATE *state,
                                               const SLHDSA_PARAMS *params,
                                               const uint8_t *public_key) {
  const size_t n = params->n;
  slh_dsa_state_init(state, params);
  OPENSSL_memcpy(state->pk_seed, public_key, n);
  OPENSSL_memcpy(state->pk_root, public_key + n, n);
}

static void slh_dsa_state_init_from_private_key(SLHDSA_STATE *state,
                                                const SLHDSA_PARAMS *params,
                                                const uint8_t *private_key) {
  const size_t n = params->n;
  slh_dsa_state_init(state, params);
  OPENSSL_memcpy(state->sk_seed, private_key, n);
  OPENSSL_memcpy(state->sk_prf, private_key + n, n);
  OPENSSL_memcpy(state->pk_seed, private_key + 2 * n, n);
  OPENSSL_memcpy(state->pk_root, private_key + 3 * n, n);
  CONSTTIME_SECRET(state->sk_seed, n);
  CONSTTIME_SECRET(state->sk_prf, n);
}

// slh_dsa_split_digest extracts idx_tree and idx_leaf from the H_msg output.
// This is Algorithm 19, lines 6-10 and Algorithm 20, lines 9-13, using toInt
// (Algorithm 2). The FORS message digest md is the first ceil(k * a / 8)
// bytes of |digest|.
static void slh_dsa_split_digest(const SLHDSA_PARAMS *params,
                                 const uint8_t *digest, uint64_t *out_idx_tree,
                                 uint32_t *out_idx_leaf) {
  const size_t md_len = (params->k * params->a + 7) / 8;
  const uint32_t tree_bits = params->h - params->hp;  // h - h/d
  const size_t tree_len = (tree_bits + 7) / 8;
  const size_t leaf_len = (params->hp + 7) / 8;
  assert(md_len + tree_len + leaf_len == params->m);
  // Every parameter set has h - h/d < 64, so the mask below is well-defined.
  assert(tree_bits < 64);

  uint64_t idx_tree = 0;
  for (size_t i = 0; i < tree_len; i++) {
    idx_tree = (idx_tree << 8) | digest[md_len + i];
  }
  uint32_t idx_leaf = 0;
  for (size_t i = 0; i < leaf_len; i++) {
    idx_leaf = (idx_leaf << 8) | digest[md_len + tree_len + i];
  }

  *out_idx_tree = idx_tree & ((UINT64_C(1) << tree_bits) - 1);
  *out_idx_leaf = idx_leaf & ((UINT32_C(1) << params->hp) - 1);
}

// slh_dsa_fors_adrs sets |adrs| to the FORS tree address for the given
// hypertree leaf. This is Algorithm 19, lines 1 and 11-13 and Algorithm 20,
// lines 4 and 14-16.
static void slh_dsa_fors_adrs(uint8_t adrs[SLHDSA_ADRS_BYTES],
                              uint64_t idx_tree, uint32_t idx_leaf) {
  slh_dsa_adrs_zero(adrs);
  slh_dsa_adrs_set_tree_address(adrs, idx_tree);
  slh_dsa_adrs_set_type_and_clear(adrs, SLHDSA_ADRS_FORS_TREE);
  slh_dsa_adrs_set_key_pair_address(adrs, idx_leaf);
}

// The service indicator. The SHAKE and RBG functions used below report each
// call to the FIPS service indicator, which would otherwise mark the enclosing
// SLH-DSA operation as approved. Every exported function that hashes or draws
// randomness locks the indicator when it starts and unlocks it in
// |slh_dsa_finish|. SLH-DSA is not yet an approved service, so nothing updates
// the indicator.

// slh_dsa_scrub_stack overwrites the stack below the caller's frame. The
// hash functions and the WOTS+, XMSS and FORS computations leave intermediate
// values, some derived from SK.seed and SK.prf, in frames that have returned.
// FIPS 205, Section 3.1 requires them to be destroyed, so every exported
// operation calls this before returning. Without the scrub, the deepest
// operation writes about 6 KB below its caller on x86_64 and AArch64; the
// margin allows for other compilers and options. The |StackScrub| test checks
// that nothing is left.
//
// The scrub only covers frames below its caller, so each exported function
// does its work in an |OPENSSL_NOINLINE| helper and scrubs after it returns.
// Otherwise, with link-time optimization, the compiler can inline that work,
// and its secret temporaries, into the exported function's own frame.
//
// It must not be inlined, or analyzed across calls and removed, so GCC also
// gets |noipa|.
#define SLHDSA_STACK_SCRUB_BYTES 16384
#if defined(__GNUC__) && !defined(__clang__) && __GNUC__ >= 8
__attribute__((noipa))
#endif
static OPENSSL_NOINLINE void slh_dsa_scrub_stack(void) {
  uint8_t buf[SLHDSA_STACK_SCRUB_BYTES];
  OPENSSL_cleanse(buf, sizeof(buf));
  // |OPENSSL_cleanse| has no compiler barrier under |OPENSSL_NO_ASM|, so with
  // link-time optimization the compiler can remove it as a dead store.
#if defined(__GNUC__) || defined(__clang__)
  __asm__ __volatile__("" : : "r"(buf) : "memory");
#endif
}

// slh_dsa_finish ends an exported function that locked the service indicator:
// it unlocks the indicator, scrubs the stack and returns |ret|.
static int slh_dsa_finish(int ret) {
  FIPS_service_indicator_unlock_state();
  slh_dsa_scrub_stack();
  return ret;
}

// FIPS 205, Algorithm 18: slh_keygen_internal (page 34).
static OPENSSL_NOINLINE int slh_dsa_keypair_impl(const SLHDSA_PARAMS *params,
                                                 uint8_t *out_public_key,
                                                 uint8_t *out_private_key,
                                                 const uint8_t *seed) {
  const size_t n = params->n;

  SLHDSA_STATE state;
  slh_dsa_state_init(&state, params);
  OPENSSL_memcpy(state.sk_seed, seed, n);
  OPENSSL_memcpy(state.sk_prf, seed + n, n);
  OPENSSL_memcpy(state.pk_seed, seed + 2 * n, n);
  CONSTTIME_SECRET(state.sk_seed, n);
  CONSTTIME_SECRET(state.sk_prf, n);

  // Algorithm 18, lines 1-3: PK.root is the root of the single XMSS tree in
  // the top layer of the hypertree.
  uint8_t adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_zero(adrs);
  slh_dsa_adrs_set_layer_address(adrs, params->d - 1);
  slh_dsa_xmss_node(&state, state.pk_root, 0, params->hp, adrs);
  CONSTTIME_DECLASSIFY(state.pk_root, n);

  // SK = SK.seed || SK.prf || PK.seed || PK.root, PK = PK.seed || PK.root.
  OPENSSL_memcpy(out_private_key, seed, 3 * n);
  OPENSSL_memcpy(out_private_key + 3 * n, state.pk_root, n);
  OPENSSL_memcpy(out_public_key, state.pk_seed, n);
  OPENSSL_memcpy(out_public_key + n, state.pk_root, n);

  slh_dsa_state_cleanse(&state);
  return 1;
}

int slh_dsa_keypair_internal(const SLHDSA_PARAMS *params,
                             uint8_t *out_public_key, size_t public_key_len,
                             uint8_t *out_private_key, size_t private_key_len,
                             const uint8_t *seed, size_t seed_len) {
  if (params == NULL || out_public_key == NULL || out_private_key == NULL ||
      seed == NULL || public_key_len != slh_dsa_public_key_bytes(params) ||
      private_key_len != slh_dsa_private_key_bytes(params) ||
      seed_len != slh_dsa_seed_bytes(params)) {
    return 0;
  }

  FIPS_service_indicator_lock_state();
  return slh_dsa_finish(
      slh_dsa_keypair_impl(params, out_public_key, out_private_key, seed));
}

// FIPS 205, Algorithm 19: slh_sign_internal (page 35).
static OPENSSL_NOINLINE int slh_dsa_sign_impl(
    const SLHDSA_PARAMS *params, uint8_t *out_sig, size_t sig_len,
    const uint8_t *private_key, const uint8_t *pre, size_t pre_len,
    const uint8_t *message, size_t message_len, const uint8_t *addrnd) {
  const size_t n = params->n;

  SLHDSA_STATE state;
  slh_dsa_state_init_from_private_key(&state, params, private_key);

  // Algorithm 19, lines 2-4. The deterministic variant substitutes PK.seed
  // for opt_rand.
  const uint8_t *opt_rand = addrnd != NULL ? addrnd : state.pk_seed;
  uint8_t *r = out_sig;
  slh_dsa_prf_msg(&state, r, opt_rand, pre, pre_len, message, message_len);
  OPENSSL_cleanse(state.sk_prf, sizeof(state.sk_prf));
  // R is public. It was computed from SK.prf, and the message digest
  // derived from it selects tree indices and branches.
  CONSTTIME_DECLASSIFY(r, n);

  // Algorithm 19, lines 5-10.
  uint8_t digest[SLHDSA_MAX_M];
  slh_dsa_h_msg(&state, digest, r, pre, pre_len, message, message_len);
  uint64_t idx_tree = 0;
  uint32_t idx_leaf = 0;
  slh_dsa_split_digest(params, digest, &idx_tree, &idx_leaf);

  // Algorithm 19, lines 11-16: the FORS signature of md, and the FORS
  // public key it implies.
  uint8_t adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_fors_adrs(adrs, idx_tree, idx_leaf);
  uint8_t *sig_fors = out_sig + n;
  slh_dsa_fors_sign(&state, sig_fors, digest, adrs);
  uint8_t pk_fors[SLHDSA_MAX_N];
  slh_dsa_fors_pk_from_sig(&state, pk_fors, sig_fors, digest, adrs);
  // PK_FORS is public and its WOTS+ digits select branches in ht_sign.
  CONSTTIME_DECLASSIFY(pk_fors, n);

  // Algorithm 19, lines 17-18: the hypertree signature of PK_FORS.
  uint8_t *sig_ht = sig_fors + slh_dsa_fors_signature_bytes(params);
  slh_dsa_ht_sign(&state, sig_ht, pk_fors, idx_tree, idx_leaf);
  CONSTTIME_DECLASSIFY(out_sig, sig_len);

  OPENSSL_cleanse(digest, sizeof(digest));
  OPENSSL_cleanse(pk_fors, sizeof(pk_fors));
  slh_dsa_state_cleanse(&state);
  return 1;
}

int slh_dsa_sign_internal(const SLHDSA_PARAMS *params, uint8_t *out_sig,
                          size_t sig_len, const uint8_t *private_key,
                          size_t private_key_len, const uint8_t *pre,
                          size_t pre_len, const uint8_t *message,
                          size_t message_len, const uint8_t *addrnd,
                          size_t addrnd_len) {
  if (params == NULL || out_sig == NULL || private_key == NULL ||
      sig_len != slh_dsa_signature_bytes(params) ||
      private_key_len != slh_dsa_private_key_bytes(params) ||
      (pre == NULL && pre_len != 0) || (message == NULL && message_len != 0) ||
      addrnd_len != (addrnd != NULL ? params->n : 0)) {
    return 0;
  }

  FIPS_service_indicator_lock_state();
  return slh_dsa_finish(slh_dsa_sign_impl(params, out_sig, sig_len, private_key,
                                          pre, pre_len, message, message_len,
                                          addrnd));
}

// FIPS 205, Algorithm 20: slh_verify_internal (page 36).
static OPENSSL_NOINLINE int slh_dsa_verify_impl(
    const SLHDSA_PARAMS *params, const uint8_t *sig, size_t sig_len,
    const uint8_t *public_key, const uint8_t *pre, size_t pre_len,
    const uint8_t *message, size_t message_len) {
  const size_t n = params->n;

  SLHDSA_STATE state;
  slh_dsa_state_init_from_public_key(&state, params, public_key);

  // Algorithm 20, lines 4-13.
  const uint8_t *r = sig;
  const uint8_t *sig_fors = sig + n;
  const uint8_t *sig_ht = sig_fors + slh_dsa_fors_signature_bytes(params);
  uint8_t digest[SLHDSA_MAX_M];
  slh_dsa_h_msg(&state, digest, r, pre, pre_len, message, message_len);
  uint64_t idx_tree = 0;
  uint32_t idx_leaf = 0;
  slh_dsa_split_digest(params, digest, &idx_tree, &idx_leaf);

  // Algorithm 20, lines 14-17.
  uint8_t adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_fors_adrs(adrs, idx_tree, idx_leaf);
  uint8_t pk_fors[SLHDSA_MAX_N];
  slh_dsa_fors_pk_from_sig(&state, pk_fors, sig_fors, digest, adrs);

  // Algorithm 20, line 18.
  const int ok = slh_dsa_ht_verify(&state, pk_fors, sig_ht, idx_tree, idx_leaf);

  OPENSSL_cleanse(digest, sizeof(digest));
  OPENSSL_cleanse(pk_fors, sizeof(pk_fors));
  slh_dsa_state_cleanse(&state);
  return ok;
}

int slh_dsa_verify_internal(const SLHDSA_PARAMS *params, const uint8_t *sig,
                            size_t sig_len, const uint8_t *public_key,
                            size_t public_key_len, const uint8_t *pre,
                            size_t pre_len, const uint8_t *message,
                            size_t message_len) {
  if (params == NULL || sig == NULL || public_key == NULL ||
      public_key_len != slh_dsa_public_key_bytes(params) ||
      (pre == NULL && pre_len != 0) || (message == NULL && message_len != 0)) {
    return 0;
  }
  // Algorithm 20, lines 1-3.
  if (sig_len != slh_dsa_signature_bytes(params)) {
    return 0;
  }

  FIPS_service_indicator_lock_state();
  return slh_dsa_finish(slh_dsa_verify_impl(
      params, sig, sig_len, public_key, pre, pre_len, message, message_len));
}

// FIPS 205, Algorithm 21: slh_keygen (page 37).
static OPENSSL_NOINLINE int slh_dsa_keypair_random(const SLHDSA_PARAMS *params,
                                                   uint8_t *out_public_key,
                                                   size_t public_key_len,
                                                   uint8_t *out_private_key,
                                                   size_t private_key_len) {
  // Algorithm 21, lines 1-6: SK.seed, SK.prf and PK.seed from the RBG.
  uint8_t seed[3 * SLHDSA_MAX_N];
  const size_t seed_len = slh_dsa_seed_bytes(params);
  int ret = 0;
  if (RAND_bytes(seed, seed_len)) {
    ret = slh_dsa_keypair_internal(params, out_public_key, public_key_len,
                                   out_private_key, private_key_len, seed,
                                   seed_len);
  }
  OPENSSL_cleanse(seed, sizeof(seed));
  return ret;
}

int slh_dsa_keypair(const SLHDSA_PARAMS *params, uint8_t *out_public_key,
                    size_t public_key_len, uint8_t *out_private_key,
                    size_t private_key_len) {
  if (params == NULL || out_public_key == NULL || out_private_key == NULL ||
      public_key_len != slh_dsa_public_key_bytes(params) ||
      private_key_len != slh_dsa_private_key_bytes(params)) {
    return 0;
  }
  FIPS_service_indicator_lock_state();
  return slh_dsa_finish(slh_dsa_keypair_random(params, out_public_key,
                                               public_key_len, out_private_key,
                                               private_key_len));
}

static OPENSSL_NOINLINE int slh_dsa_check_private_key_impl(
    const SLHDSA_PARAMS *params, const uint8_t *private_key) {
  const size_t n = params->n;

  SLHDSA_STATE state;
  slh_dsa_state_init_from_private_key(&state, params, private_key);

  // Recompute PK.root as in Algorithm 18, lines 1-3.
  uint8_t adrs[SLHDSA_ADRS_BYTES];
  slh_dsa_adrs_zero(adrs);
  slh_dsa_adrs_set_layer_address(adrs, params->d - 1);
  uint8_t root[SLHDSA_MAX_N];
  slh_dsa_xmss_node(&state, root, 0, params->hp, adrs);
  CONSTTIME_DECLASSIFY(root, n);
  const int ok = CRYPTO_memcmp(root, state.pk_root, n) == 0;

  slh_dsa_state_cleanse(&state);
  return ok;
}

int slh_dsa_check_private_key(const SLHDSA_PARAMS *params,
                              const uint8_t *private_key,
                              size_t private_key_len) {
  if (params == NULL || private_key == NULL ||
      private_key_len != slh_dsa_private_key_bytes(params)) {
    return 0;
  }

  FIPS_service_indicator_lock_state();
  return slh_dsa_finish(slh_dsa_check_private_key_impl(params, private_key));
}

int slh_dsa_public_from_private(const SLHDSA_PARAMS *params,
                                uint8_t *out_public_key, size_t public_key_len,
                                const uint8_t *private_key,
                                size_t private_key_len) {
  if (params == NULL || out_public_key == NULL || private_key == NULL ||
      public_key_len != slh_dsa_public_key_bytes(params) ||
      private_key_len != slh_dsa_private_key_bytes(params) ||
      !slh_dsa_check_private_key(params, private_key, private_key_len)) {
    return 0;
  }
  // PK.seed || PK.root are the last 2n bytes of the private key.
  OPENSSL_memcpy(out_public_key, private_key + 2 * params->n, 2 * params->n);
  return 1;
}

// The DER encodings of the SHAKE128 and SHAKE256 OIDs, 2.16.840.1.101.3.4.2.11
// and 2.16.840.1.101.3.4.2.12 (FIPS 205, Algorithm 23, lines 16 and 19).
#define SLHDSA_HASH_OID_BYTES 11
static const uint8_t kSHAKE128OID[SLHDSA_HASH_OID_BYTES] = {
    0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0b};
static const uint8_t kSHAKE256OID[SLHDSA_HASH_OID_BYTES] = {
    0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0c};

#define SLHDSA_MAX_PREFIX_BYTES \
  (2 + SLHDSA_MAX_CONTEXT_BYTES + SLHDSA_HASH_OID_BYTES)

size_t slh_dsa_prehash_digest_bytes(const SLHDSA_PARAMS *params, int hash_nid) {
  if (params == NULL) {
    return 0;
  }
  switch (hash_nid) {
    case NID_shake128:
      // SHAKE128(M, 256). FIPS 205, Section 10.2.2 limits SHAKE128 to
      // security category 1, which is n = 16.
      return params->n == 16 ? 32 : 0;
    case NID_shake256:
      return 64;  // SHAKE256(M, 512)
    default:
      return 0;
  }
}

static const uint8_t *slh_dsa_prehash_oid(int hash_nid) {
  switch (hash_nid) {
    case NID_shake128:
      return kSHAKE128OID;
    case NID_shake256:
      return kSHAKE256OID;
    default:
      return NULL;
  }
}

// slh_dsa_prefix writes the part of M' that precedes the message (pure) or
// the digest (pre-hash) and returns its length, or zero if |context| is too
// long. This is toByte(0, 1) || toByte(|ctx|, 1) || ctx (Algorithm 22, line 8
// and Algorithm 24, line 4) or, if |hash_oid| is not NULL, toByte(1, 1) ||
// toByte(|ctx|, 1) || ctx || OID (Algorithm 23, line 24 and Algorithm 25,
// line 20).
static size_t slh_dsa_prefix(uint8_t out[SLHDSA_MAX_PREFIX_BYTES],
                             const uint8_t *hash_oid, const uint8_t *context,
                             size_t context_len) {
  // Algorithms 22-25, lines 1-3.
  if (context_len > SLHDSA_MAX_CONTEXT_BYTES ||
      (context == NULL && context_len != 0)) {
    return 0;
  }
  out[0] = hash_oid != NULL ? 1 : 0;
  out[1] = (uint8_t)context_len;
  OPENSSL_memcpy(out + 2, context, context_len);
  size_t len = 2 + context_len;
  if (hash_oid != NULL) {
    OPENSSL_memcpy(out + len, hash_oid, SLHDSA_HASH_OID_BYTES);
    len += SLHDSA_HASH_OID_BYTES;
  }
  return len;
}

// slh_dsa_sign_hedged signs prefix || message with fresh randomness
// (Algorithm 22, lines 4-9 and Algorithm 23, lines 4-7 and 24-25). The caller
// must hold the service indicator lock.
static OPENSSL_NOINLINE int slh_dsa_sign_hedged(
    const SLHDSA_PARAMS *params, uint8_t *out_sig, size_t sig_len,
    const uint8_t *private_key, size_t private_key_len, const uint8_t *prefix,
    size_t prefix_len, const uint8_t *message, size_t message_len) {
  if (out_sig == NULL || private_key == NULL ||
      sig_len != slh_dsa_signature_bytes(params) ||
      private_key_len != slh_dsa_private_key_bytes(params)) {
    return 0;
  }
  uint8_t addrnd[SLHDSA_MAX_N];
  int ret = 0;
  if (RAND_bytes(addrnd, params->n)) {
    ret = slh_dsa_sign_internal(params, out_sig, sig_len, private_key,
                                private_key_len, prefix, prefix_len, message,
                                message_len, addrnd, params->n);
  }
  OPENSSL_cleanse(addrnd, sizeof(addrnd));
  return ret;
}

// FIPS 205, Algorithm 22: slh_sign (page 39).
int slh_dsa_sign(const SLHDSA_PARAMS *params, uint8_t *out_sig, size_t sig_len,
                 const uint8_t *private_key, size_t private_key_len,
                 const uint8_t *message, size_t message_len,
                 const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  uint8_t prefix[SLHDSA_MAX_PREFIX_BYTES];
  const size_t prefix_len =
      slh_dsa_prefix(prefix, /*hash_oid=*/NULL, context, context_len);
  int ret = 0;
  if (params != NULL && prefix_len != 0) {
    ret = slh_dsa_sign_hedged(params, out_sig, sig_len, private_key,
                              private_key_len, prefix, prefix_len, message,
                              message_len);
  }
  OPENSSL_cleanse(prefix, sizeof(prefix));
  return slh_dsa_finish(ret);
}

// FIPS 205, Algorithm 24: slh_verify (page 41).
int slh_dsa_verify(const SLHDSA_PARAMS *params, const uint8_t *sig,
                   size_t sig_len, const uint8_t *public_key,
                   size_t public_key_len, const uint8_t *message,
                   size_t message_len, const uint8_t *context,
                   size_t context_len) {
  FIPS_service_indicator_lock_state();
  uint8_t prefix[SLHDSA_MAX_PREFIX_BYTES];
  const size_t prefix_len =
      slh_dsa_prefix(prefix, /*hash_oid=*/NULL, context, context_len);
  int ret = 0;
  if (prefix_len != 0) {
    ret = slh_dsa_verify_internal(params, sig, sig_len, public_key,
                                  public_key_len, prefix, prefix_len, message,
                                  message_len);
  }
  OPENSSL_cleanse(prefix, sizeof(prefix));
  return slh_dsa_finish(ret);
}

// slh_dsa_prehash computes PH_M, SHAKE128(M, 256) or SHAKE256(M, 512)
// (Algorithm 23, lines 17 and 20 and Algorithm 25, lines 13 and 16). |out|
// must have room for |slh_dsa_prehash_digest_bytes(params, hash_nid)| bytes.
// The caller must hold the service indicator lock.
static OPENSSL_NOINLINE int slh_dsa_prehash(const SLHDSA_PARAMS *params,
                                            int hash_nid, uint8_t *out,
                                            const uint8_t *message,
                                            size_t message_len) {
  const size_t out_len = slh_dsa_prehash_digest_bytes(params, hash_nid);
  if (out_len == 0 || (message == NULL && message_len != 0)) {
    return 0;
  }
  return hash_nid == NID_shake128
             ? SHAKE128(message, message_len, out, out_len) != NULL
             : SHAKE256(message, message_len, out, out_len) != NULL;
}

// slh_dsa_prehash_prefix writes the pre-hash prefix for |hash_nid| and
// |context| to |out| and returns its length, or zero if |hash_nid|, |context|
// or |digest_len| is invalid for |params|.
static size_t slh_dsa_prehash_prefix(uint8_t out[SLHDSA_MAX_PREFIX_BYTES],
                                     const SLHDSA_PARAMS *params, int hash_nid,
                                     size_t digest_len, const uint8_t *context,
                                     size_t context_len) {
  const uint8_t *hash_oid = slh_dsa_prehash_oid(hash_nid);
  const size_t expected_len = slh_dsa_prehash_digest_bytes(params, hash_nid);
  if (hash_oid == NULL || expected_len == 0 || digest_len != expected_len) {
    return 0;
  }
  return slh_dsa_prefix(out, hash_oid, context, context_len);
}

// FIPS 205, Algorithm 23: hash_slh_sign (page 40), given PH_M rather than M.
// The caller must hold the service indicator lock.
static int slh_dsa_hash_sign(const SLHDSA_PARAMS *params, uint8_t *out_sig,
                             size_t sig_len, const uint8_t *private_key,
                             size_t private_key_len, int hash_nid,
                             const uint8_t *digest, size_t digest_len,
                             const uint8_t *context, size_t context_len) {
  uint8_t prefix[SLHDSA_MAX_PREFIX_BYTES];
  const size_t prefix_len = slh_dsa_prehash_prefix(
      prefix, params, hash_nid, digest_len, context, context_len);
  int ret = 0;
  if (prefix_len != 0 && digest != NULL) {
    ret = slh_dsa_sign_hedged(params, out_sig, sig_len, private_key,
                              private_key_len, prefix, prefix_len, digest,
                              digest_len);
  }
  OPENSSL_cleanse(prefix, sizeof(prefix));
  return ret;
}

// FIPS 205, Algorithm 25: hash_slh_verify (page 42), given PH_M rather than M.
static int slh_dsa_hash_verify(const SLHDSA_PARAMS *params, const uint8_t *sig,
                               size_t sig_len, const uint8_t *public_key,
                               size_t public_key_len, int hash_nid,
                               const uint8_t *digest, size_t digest_len,
                               const uint8_t *context, size_t context_len) {
  uint8_t prefix[SLHDSA_MAX_PREFIX_BYTES];
  const size_t prefix_len = slh_dsa_prehash_prefix(
      prefix, params, hash_nid, digest_len, context, context_len);
  int ret = 0;
  if (prefix_len != 0 && digest != NULL) {
    ret = slh_dsa_verify_internal(params, sig, sig_len, public_key,
                                  public_key_len, prefix, prefix_len, digest,
                                  digest_len);
  }
  OPENSSL_cleanse(prefix, sizeof(prefix));
  return ret;
}

int slh_dsa_prehash_sign_digest(const SLHDSA_PARAMS *params, uint8_t *out_sig,
                                size_t sig_len, const uint8_t *private_key,
                                size_t private_key_len, int hash_nid,
                                const uint8_t *digest, size_t digest_len,
                                const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  const int ret =
      slh_dsa_hash_sign(params, out_sig, sig_len, private_key, private_key_len,
                        hash_nid, digest, digest_len, context, context_len);
  return slh_dsa_finish(ret);
}

int slh_dsa_prehash_sign(const SLHDSA_PARAMS *params, uint8_t *out_sig,
                         size_t sig_len, const uint8_t *private_key,
                         size_t private_key_len, int hash_nid,
                         const uint8_t *message, size_t message_len,
                         const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  uint8_t digest[SLHDSA_MAX_PREHASH_DIGEST_BYTES];
  int ret = 0;
  if (slh_dsa_prehash(params, hash_nid, digest, message, message_len)) {
    ret = slh_dsa_hash_sign(params, out_sig, sig_len, private_key,
                            private_key_len, hash_nid, digest,
                            slh_dsa_prehash_digest_bytes(params, hash_nid),
                            context, context_len);
  }
  OPENSSL_cleanse(digest, sizeof(digest));
  return slh_dsa_finish(ret);
}

int slh_dsa_prehash_verify_digest(const SLHDSA_PARAMS *params,
                                  const uint8_t *sig, size_t sig_len,
                                  const uint8_t *public_key,
                                  size_t public_key_len, int hash_nid,
                                  const uint8_t *digest, size_t digest_len,
                                  const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  const int ret =
      slh_dsa_hash_verify(params, sig, sig_len, public_key, public_key_len,
                          hash_nid, digest, digest_len, context, context_len);
  return slh_dsa_finish(ret);
}

int slh_dsa_prehash_verify(const SLHDSA_PARAMS *params, const uint8_t *sig,
                           size_t sig_len, const uint8_t *public_key,
                           size_t public_key_len, int hash_nid,
                           const uint8_t *message, size_t message_len,
                           const uint8_t *context, size_t context_len) {
  FIPS_service_indicator_lock_state();
  uint8_t digest[SLHDSA_MAX_PREHASH_DIGEST_BYTES];
  int ret = 0;
  if (slh_dsa_prehash(params, hash_nid, digest, message, message_len)) {
    ret = slh_dsa_hash_verify(
        params, sig, sig_len, public_key, public_key_len, hash_nid, digest,
        slh_dsa_prehash_digest_bytes(params, hash_nid), context, context_len);
  }
  OPENSSL_cleanse(digest, sizeof(digest));
  return slh_dsa_finish(ret);
}
