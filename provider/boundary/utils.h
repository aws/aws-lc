// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_BOUNDARY_UTILS_H
#define AWSLC_PROVIDER_BOUNDARY_UTILS_H

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

// OpenSSL's canonical name for the digest |name| spells, such as "SHA2-256"
// for "sha256", or NULL when AWS-LC has no such digest. The returned string is
// static.
const char *awslc_prov_digest_canonical_name(const char *name);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_BOUNDARY_UTILS_H
