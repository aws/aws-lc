// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bn.h>
#include <openssl/rsa.h>

#include <limits.h>

#include "internal/backend/keymgmt.h"

// AWS-LC refuses a public exponent wider than this unless the key is built by
// a _large_e constructor.
#define AWSLC_PROV_RSA_MAX_SMALL_E_BITS 33

static RSA *awslc_prov_rsa_from_bns(
    const BIGNUM *const bn[AWSLC_PROV_RSA_COMPONENT_COUNT]) {
  const BIGNUM *n = bn[AWSLC_PROV_RSA_N];
  const BIGNUM *e = bn[AWSLC_PROV_RSA_E];
  const BIGNUM *d = bn[AWSLC_PROV_RSA_D];
  int large_e = 0;
  int crt = 0;

  if (n == NULL || e == NULL) {
    return NULL;
  }
  large_e = BN_num_bits(e) > AWSLC_PROV_RSA_MAX_SMALL_E_BITS;
  for (int i = AWSLC_PROV_RSA_P; i < AWSLC_PROV_RSA_COMPONENT_COUNT; i++) {
    crt += bn[i] != NULL;
  }

  if (d == NULL && crt == 0) {
    return large_e ? RSA_new_public_key_large_e(n, e)
                   : RSA_new_public_key(n, e);
  }
  if (d != NULL && crt == 0) {
    // There is no _large_e form of this constructor, so a large e is refused.
    return RSA_new_private_key_no_crt(n, e, d);
  }
  if (d != NULL && crt == AWSLC_PROV_RSA_CRT_COUNT) {
    const BIGNUM *p = bn[AWSLC_PROV_RSA_P];
    const BIGNUM *q = bn[AWSLC_PROV_RSA_Q];
    const BIGNUM *dmp1 = bn[AWSLC_PROV_RSA_DMP1];
    const BIGNUM *dmq1 = bn[AWSLC_PROV_RSA_DMQ1];
    const BIGNUM *iqmp = bn[AWSLC_PROV_RSA_IQMP];

    return large_e
               ? RSA_new_private_key_large_e(n, e, d, p, q, dmp1, dmq1, iqmp)
               : RSA_new_private_key(n, e, d, p, q, dmp1, dmq1, iqmp);
  }
  return NULL;
}

void *awslc_prov_rsa_new(
    const AWSLC_PROV_BN_BYTES components[AWSLC_PROV_RSA_COMPONENT_COUNT]) {
  BIGNUM *owned[AWSLC_PROV_RSA_COMPONENT_COUNT] = {NULL};
  const BIGNUM *view[AWSLC_PROV_RSA_COMPONENT_COUNT] = {NULL};
  RSA *rsa = NULL;
  int ok = components != NULL;

  for (int i = 0; ok && i < AWSLC_PROV_RSA_COMPONENT_COUNT; i++) {
    if (components[i].data != NULL) {
      owned[i] = awslc_prov_bn_from_bytes(&components[i]);
      view[i] = owned[i];
      ok = owned[i] != NULL;
    }
  }
  if (ok) {
    rsa = awslc_prov_rsa_from_bns(view);
  }
  for (int i = 0; i < AWSLC_PROV_RSA_COMPONENT_COUNT; i++) {
    BN_clear_free(owned[i]);
  }
  return rsa;
}

void *awslc_prov_rsa_new_public(const void *rsa) {
  const BIGNUM *view[AWSLC_PROV_RSA_COMPONENT_COUNT] = {NULL};

  if (rsa == NULL) {
    return NULL;
  }
  view[AWSLC_PROV_RSA_N] = RSA_get0_n((const RSA *)rsa);
  view[AWSLC_PROV_RSA_E] = RSA_get0_e((const RSA *)rsa);
  return awslc_prov_rsa_from_bns(view);
}

void awslc_prov_rsa_free(void *rsa) { RSA_free((RSA *)rsa); }

int awslc_prov_rsa_up_ref(void *rsa) {
  return rsa != NULL && RSA_up_ref((RSA *)rsa);
}

const void *awslc_prov_rsa_get0(const void *rsa,
                                AWSLC_PROV_RSA_COMPONENT component) {
  const RSA *key = (const RSA *)rsa;

  if (key == NULL) {
    return NULL;
  }
  switch (component) {
    case AWSLC_PROV_RSA_N:
      return RSA_get0_n(key);
    case AWSLC_PROV_RSA_E:
      return RSA_get0_e(key);
    case AWSLC_PROV_RSA_D:
      return RSA_get0_d(key);
    case AWSLC_PROV_RSA_P:
      return RSA_get0_p(key);
    case AWSLC_PROV_RSA_Q:
      return RSA_get0_q(key);
    case AWSLC_PROV_RSA_DMP1:
      return RSA_get0_dmp1(key);
    case AWSLC_PROV_RSA_DMQ1:
      return RSA_get0_dmq1(key);
    case AWSLC_PROV_RSA_IQMP:
      return RSA_get0_iqmp(key);
    case AWSLC_PROV_RSA_COMPONENT_COUNT:
      break;
  }
  return NULL;
}

unsigned awslc_prov_rsa_bits(const void *rsa) {
  return rsa == NULL ? 0 : RSA_bits((const RSA *)rsa);
}

unsigned awslc_prov_rsa_size(const void *rsa) {
  return rsa == NULL ? 0 : RSA_size((const RSA *)rsa);
}

unsigned awslc_prov_rsa_security_bits(const void *rsa) {
  const unsigned bits = awslc_prov_rsa_bits(rsa);

  // SP 800-57 Part 1 rev 5, Table 2.
  if (bits >= 15360) {
    return 256;
  }
  if (bits >= 7680) {
    return 192;
  }
  if (bits >= 3072) {
    return 128;
  }
  if (bits >= 2048) {
    return 112;
  }
  if (bits >= 1024) {
    return 80;
  }
  return 0;
}

int awslc_prov_rsa_check(const void *rsa) {
  return rsa != NULL && RSA_check_key((const RSA *)rsa);
}

void *awslc_prov_rsa_generate(unsigned bits) {
  RSA *rsa = NULL;

  if (bits > (unsigned)INT_MAX) {
    return NULL;
  }
  rsa = RSA_new();
  if (rsa == NULL) {
    return NULL;
  }
  if (!RSA_generate_key_fips(rsa, (int)bits, NULL)) {
    RSA_free(rsa);
    return NULL;
  }
  return rsa;
}
