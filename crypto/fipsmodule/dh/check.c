// Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com) All rights reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/dh.h>

#include <openssl/bn.h>
#include <openssl/err.h>

#include "../bn/internal.h"
#include "internal.h"

int dh_check_params_fast(const DH *dh) {
  // Most operations scale with p and q.
  if (BN_is_negative(dh->p) || !BN_is_odd(dh->p) ||
      BN_num_bits(dh->p) > OPENSSL_DH_MAX_MODULUS_BITS) {
    OPENSSL_PUT_ERROR(DH, DH_R_INVALID_PARAMETERS);
    return 0;
  }

  // q must be bounded by p.
  if (dh->q != NULL && (BN_is_negative(dh->q) || BN_ucmp(dh->q, dh->p) > 0)) {
    OPENSSL_PUT_ERROR(DH, DH_R_INVALID_PARAMETERS);
    return 0;
  }

  // g must be an element of p's multiplicative group.
  if (BN_is_negative(dh->g) || BN_is_zero(dh->g) ||
      BN_ucmp(dh->g, dh->p) >= 0) {
    OPENSSL_PUT_ERROR(DH, DH_R_INVALID_PARAMETERS);
    return 0;
  }

  return 1;
}

int DH_check_pub_key(const DH *dh, const BIGNUM *pub_key, int *out_flags) {
  *out_flags = 0;
  if (!dh_check_params_fast(dh)) {
    return 0;
  }

  BN_CTX *ctx = BN_CTX_new();
  if (ctx == NULL) {
    return 0;
  }
  BN_CTX_start(ctx);

  int ok = 0;

  // Check |pub_key| is greater than 1.
  if (BN_cmp(pub_key, BN_value_one()) <= 0) {
    *out_flags |= DH_CHECK_PUBKEY_TOO_SMALL;
  }

  // Check |pub_key| is less than |dh->p| - 1.
  BIGNUM *tmp = BN_CTX_get(ctx);
  if (tmp == NULL ||
      !BN_copy(tmp, dh->p) ||
      !BN_sub_word(tmp, 1)) {
    goto err;
  }
  if (BN_cmp(pub_key, tmp) >= 0) {
    *out_flags |= DH_CHECK_PUBKEY_TOO_LARGE;
  }

  if (dh->q != NULL) {
    // Check |pub_key|^|dh->q| is 1 mod |dh->p|. This is necessary for RFC 5114
    // groups which are not safe primes but pick a generator on a prime-order
    // subgroup of size |dh->q|.
    if (!BN_mod_exp_mont(tmp, pub_key, dh->q, dh->p, ctx, NULL)) {
      goto err;
    }
    if (!BN_is_one(tmp)) {
      *out_flags |= DH_CHECK_PUBKEY_INVALID;
    }
  }

  ok = 1;

err:
  BN_CTX_end(ctx);
  BN_CTX_free(ctx);
  return ok;
}


// DH_MAX_KNOWN_GROUP_WORDS is the number of words in the modulus of the largest
// group |dh_fast_path_from_safe_group| recognizes.
#define DH_MAX_KNOWN_GROUP_WORDS (8192 / BN_BITS2)

// dh_fast_path_from_safe_group returns one if |dh| is one of the well-known
// standard safe-prime groups (RFC 3526 MODP or RFC 7919 ffdhe), so that
// |DH_check| may accept it without primality testing, and zero otherwise. It
// requires g = 2 and p to match a known group prime. A subgroup order q is
// optional: if present, it is accepted only when the matched group defines one
// (RFC 7919) and it equals (p-1)/2; a q that is not part of the group
// definition returns zero so that |DH_check| performs its full validation.
static int dh_fast_path_from_safe_group(const DH *dh) {
  // Every group we recognize (RFC 3526 MODP and RFC 7919 ffdhe) uses g = 2. A
  // different generator is not the named group, so let the full checks run.
  if (!BN_is_word(dh->g, 2)) {
    return 0;
  }

  // p must match a known group prime. Both families are safe primes p = 2q+1,
  // so recognizing p means both p and (p-1)/2 are prime by definition; that is
  // what lets |DH_check| skip primality testing.
  const int is_rfc7919 = dh_is_rfc7919_prime(dh->p);
  if (!is_rfc7919 && !dh_is_rfc3526_prime(dh->p)) {
    return 0;
  }

  if (dh->q == NULL) {
    return 1;
  }

  // A subgroup order is only part of the RFC 7919 group definitions (where
  // q = (p-1)/2 and g = 2 lies in that subgroup). For an RFC 3526 prime a
  // supplied q is not something the group definition vouches for, so we do not
  // fast-path it.
  if (!is_rfc7919) {
    return 0;
  }

  // q must be exactly the group's subgroup order, (p-1)/2. The group's p is
  // odd, so that is p >> 1, which we compute in a stack buffer rather than
  // allocating a |BIGNUM| to shift into.
  BN_ULONG p_words[DH_MAX_KNOWN_GROUP_WORDS];
  BN_ULONG q_words[DH_MAX_KNOWN_GROUP_WORDS];
  if (!bn_copy_words(p_words, DH_MAX_KNOWN_GROUP_WORDS, dh->p)) {
    return 0;
  }
  bn_rshift1_words(q_words, p_words, DH_MAX_KNOWN_GROUP_WORDS);

  BIGNUM expected_q;
  BN_init(&expected_q);
  bn_set_static_words(&expected_q, q_words, DH_MAX_KNOWN_GROUP_WORDS);
  return BN_cmp(dh->q, &expected_q) == 0;
}

// DH_check confirms that the Diffie-Hellman parameters dh are valid.
int DH_check(const DH *dh, int *out_flags) {
  *out_flags = 0;
  if (!dh_check_params_fast(dh)) {
    return 0;
  }

  // Keep this below |dh_check_params_fast()|, so that |DH_check| does not
  // depend on |dh_fast_path_from_safe_group()| to bound the sizes and signs of
  // p, q and g. |dh_check_params_fast()| is only a few word comparisons anyway.
  if (dh_fast_path_from_safe_group(dh)) {
    return 1;
  }

  // Check that p is a safe prime.
  int ok = 0, r, q_good = 0;
  BN_CTX *ctx = NULL;
  BIGNUM *t1 = NULL, *t2 = NULL;

  ctx = BN_CTX_new();
  if (ctx == NULL) {
    goto err;
  }
  BN_CTX_start(ctx);
  t1 = BN_CTX_get(ctx);
  if (t1 == NULL) {
    goto err;
  }
  t2 = BN_CTX_get(ctx);
  if (t2 == NULL) {
    goto err;
  }

  if (dh->q) {
    if (BN_ucmp(dh->p, dh->q) > 0) {
      q_good = 1;
    } else {
      *out_flags |= DH_CHECK_INVALID_Q_VALUE;
    }
  }

  if (q_good) {
    if (BN_cmp(dh->g, BN_value_one()) <= 0) {
      *out_flags |= DH_CHECK_NOT_SUITABLE_GENERATOR;
    } else if (BN_cmp(dh->g, dh->p) >= 0) {
      *out_flags |= DH_CHECK_NOT_SUITABLE_GENERATOR;
    } else {
      // Check g^q == 1 mod p
      if (!BN_mod_exp_mont(t1, dh->g, dh->q, dh->p, ctx, NULL)) {
        goto err;
      }
      if (!BN_is_one(t1)) {
        *out_flags |= DH_CHECK_NOT_SUITABLE_GENERATOR;
      }
    }
    r = BN_is_prime_ex(dh->q, BN_prime_checks_for_validation, ctx, NULL);
    if (r < 0) {
      goto err;
    }
    if (!r) {
      *out_flags |= DH_CHECK_Q_NOT_PRIME;
    }
    // Check p == 1 mod q  i.e. q divides p - 1
    if (!BN_div(t1, t2, dh->p, dh->q, ctx)) {
      goto err;
    }
    if (!BN_is_one(t2)) {
      *out_flags |= DH_CHECK_INVALID_Q_VALUE;
    }
  }

  r = BN_is_prime_ex(dh->p, BN_prime_checks_for_validation, ctx, NULL);
  if (r < 0) {
    goto err;
  }
  if (!r) {
    *out_flags |= DH_CHECK_P_NOT_PRIME;
  } else if (!dh->q) {
    if (!BN_rshift1(t1, dh->p)) {
      goto err;
    }
    r = BN_is_prime_ex(t1, BN_prime_checks_for_validation, ctx, NULL);
    if (r < 0) {
      goto err;
    }
    if (!r) {
      *out_flags |= DH_CHECK_P_NOT_SAFE_PRIME;
    }
  }
  ok = 1;

err:
  if (ctx != NULL) {
    BN_CTX_end(ctx);
    BN_CTX_free(ctx);
  }
  return ok;
}
