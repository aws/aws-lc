// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_INTERNAL_BACKEND_KEYMGMT_H
#define AWSLC_PROVIDER_INTERNAL_BACKEND_KEYMGMT_H

#include <stddef.h>

#if defined(__cplusplus)
extern "C" {
#endif

// A big number in OSSL_PARAM integer encoding: |len| bytes at |data| in host
// byte order, two's complement when |is_signed|.
typedef struct {
  const unsigned char *data;
  size_t len;
  int is_signed;
} AWSLC_PROV_BN_BYTES;

// Allocates a new BIGNUM holding |in|, or NULL. Negative values are refused.
void *awslc_prov_bn_from_bytes(const AWSLC_PROV_BN_BYTES *in);

// Write |bn| under OSSL_PARAM_set_BN's contract. A NULL |out| sets |*out_len|
// to the bytes required. Otherwise all |out_size| bytes of |out| are written,
// padded, and |*out_len| is |out_size|. An |out_size| short of the bytes
// required fails with |*out_len| set to them. Negative values are refused.
int awslc_prov_bn_to_bytes(const void *bn, int is_signed, unsigned char *out,
                           size_t out_size, size_t *out_len);

int awslc_prov_bn_equal(const void *a, const void *b);

// RSA key components, in the order OpenSSL exports them.
typedef enum {
  AWSLC_PROV_RSA_N = 0,
  AWSLC_PROV_RSA_E,
  AWSLC_PROV_RSA_D,
  AWSLC_PROV_RSA_P,
  AWSLC_PROV_RSA_Q,
  AWSLC_PROV_RSA_DMP1,
  AWSLC_PROV_RSA_DMQ1,
  AWSLC_PROV_RSA_IQMP,
  AWSLC_PROV_RSA_COMPONENT_COUNT
} AWSLC_PROV_RSA_COMPONENT;

#define AWSLC_PROV_RSA_CRT_COUNT \
  (AWSLC_PROV_RSA_COMPONENT_COUNT - AWSLC_PROV_RSA_P)

// A new RSA key from |components|, where a NULL |data| is an absent component.
// The present set must be n and e; n, e, and d; or all eight. Any other set,
// or values AWS-LC rejects, return NULL.
void *awslc_prov_rsa_new(
    const AWSLC_PROV_BN_BYTES components[AWSLC_PROV_RSA_COMPONENT_COUNT]);

// A new RSA key holding only |rsa|'s n and e.
void *awslc_prov_rsa_new_public(const void *rsa);

void awslc_prov_rsa_free(void *rsa);
int awslc_prov_rsa_up_ref(void *rsa);

// |rsa|'s |component| as a BIGNUM that lives as long as |rsa|, or NULL when
// the key lacks it.
const void *awslc_prov_rsa_get0(const void *rsa,
                                AWSLC_PROV_RSA_COMPONENT component);

// Zero for a NULL |rsa|.
unsigned awslc_prov_rsa_bits(const void *rsa);
unsigned awslc_prov_rsa_size(const void *rsa);
unsigned awslc_prov_rsa_security_bits(const void *rsa);

int awslc_prov_rsa_check(const void *rsa);

// A new two-prime key with e = 65537 by FIPS 186-5 key generation, or NULL.
// AWS-LC refuses a |bits| under 2048 or not a multiple of 128.
void *awslc_prov_rsa_generate(unsigned bits);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_INTERNAL_BACKEND_KEYMGMT_H
