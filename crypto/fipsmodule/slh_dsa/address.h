// Copyright (c) The slhdsa-c project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#ifndef OPENSSL_HEADER_CRYPTO_FIPSMODULE_SLH_DSA_ADDRESS_H
#define OPENSSL_HEADER_CRYPTO_FIPSMODULE_SLH_DSA_ADDRESS_H

#include "./internal.h"

#if defined(__cplusplus)
extern "C" {
#endif

// The 32-byte ADRS structure (FIPS 205, Section 4.2). All fields are
// big-endian:
//
//   bytes  0..3   layer address
//   bytes  4..15  tree address (the top four bytes are always zero)
//   bytes 16..19  type
//   bytes 20..23  key pair address
//   bytes 24..27  chain address / tree height
//   bytes 28..31  hash address / tree index

// ADRS types (FIPS 205, Section 4.2).
#define SLHDSA_ADRS_WOTS_HASH 0
#define SLHDSA_ADRS_WOTS_PK 1
#define SLHDSA_ADRS_TREE 2
#define SLHDSA_ADRS_FORS_TREE 3
#define SLHDSA_ADRS_FORS_ROOTS 4
#define SLHDSA_ADRS_WOTS_PRF 5
#define SLHDSA_ADRS_FORS_PRF 6

static inline void slh_dsa_adrs_zero(uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  OPENSSL_memset(adrs, 0, SLHDSA_ADRS_BYTES);
}

static inline void slh_dsa_adrs_copy(uint8_t out[SLHDSA_ADRS_BYTES],
                                     const uint8_t in[SLHDSA_ADRS_BYTES]) {
  OPENSSL_memcpy(out, in, SLHDSA_ADRS_BYTES);
}

static inline void slh_dsa_adrs_set_layer_address(
    uint8_t adrs[SLHDSA_ADRS_BYTES], uint32_t layer) {
  CRYPTO_store_u32_be(adrs, layer);
}

static inline void slh_dsa_adrs_set_tree_address(
    uint8_t adrs[SLHDSA_ADRS_BYTES], uint64_t tree) {
  CRYPTO_store_u32_be(adrs + 4, 0);
  CRYPTO_store_u64_be(adrs + 8, tree);
}

// slh_dsa_adrs_set_type_and_clear sets the type and zeroes bytes 20..31.
static inline void slh_dsa_adrs_set_type_and_clear(
    uint8_t adrs[SLHDSA_ADRS_BYTES], uint32_t type) {
  CRYPTO_store_u32_be(adrs + 16, type);
  OPENSSL_memset(adrs + 20, 0, 12);
}

static inline void slh_dsa_adrs_set_key_pair_address(
    uint8_t adrs[SLHDSA_ADRS_BYTES], uint32_t key_pair) {
  CRYPTO_store_u32_be(adrs + 20, key_pair);
}

static inline uint32_t slh_dsa_adrs_get_key_pair_address(
    const uint8_t adrs[SLHDSA_ADRS_BYTES]) {
  return CRYPTO_load_u32_be(adrs + 20);
}

static inline void slh_dsa_adrs_set_chain_address(
    uint8_t adrs[SLHDSA_ADRS_BYTES], uint32_t chain) {
  CRYPTO_store_u32_be(adrs + 24, chain);
}

static inline void slh_dsa_adrs_set_tree_height(uint8_t adrs[SLHDSA_ADRS_BYTES],
                                                uint32_t height) {
  CRYPTO_store_u32_be(adrs + 24, height);
}

static inline void slh_dsa_adrs_set_hash_address(
    uint8_t adrs[SLHDSA_ADRS_BYTES], uint32_t hash) {
  CRYPTO_store_u32_be(adrs + 28, hash);
}

static inline void slh_dsa_adrs_set_tree_index(uint8_t adrs[SLHDSA_ADRS_BYTES],
                                               uint32_t index) {
  CRYPTO_store_u32_be(adrs + 28, index);
}

// slh_dsa_adrs_copy_key_pair_with_type sets |out| to a copy of |in| with the
// given type, cleared trailing fields, and |in|'s key pair address. This is
// the "ADRS copy; setTypeAndClear; setKeyPairAddress" sequence FIPS 205
// uses to derive skADRS, wotspkADRS and forspkADRS.
static inline void slh_dsa_adrs_copy_key_pair_with_type(
    uint8_t out[SLHDSA_ADRS_BYTES], const uint8_t in[SLHDSA_ADRS_BYTES],
    uint32_t type) {
  slh_dsa_adrs_copy(out, in);
  slh_dsa_adrs_set_type_and_clear(out, type);
  slh_dsa_adrs_set_key_pair_address(out, slh_dsa_adrs_get_key_pair_address(in));
}

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_FIPSMODULE_SLH_DSA_ADDRESS_H
