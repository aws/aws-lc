// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/bn.h>

#include "internal/backend/keymgmt.h"

void *awslc_prov_bn_from_bytes(const AWSLC_PROV_BN_BYTES *in) {
  if (in == NULL || in->data == NULL) {
    return NULL;
  }
  if (in->is_signed && in->len > 0) {
#if defined(OPENSSL_BIG_ENDIAN)
    const unsigned char most_significant = in->data[0];
#else
    const unsigned char most_significant = in->data[in->len - 1];
#endif
    if ((most_significant & 0x80) != 0) {
      return NULL;
    }
  }
#if defined(OPENSSL_BIG_ENDIAN)
  return BN_bin2bn(in->data, in->len, NULL);
#else
  return BN_le2bn(in->data, in->len, NULL);
#endif
}

int awslc_prov_bn_to_bytes(const void *bn, int is_signed, unsigned char *out,
                           size_t out_size, size_t *out_len) {
  const BIGNUM *value = (const BIGNUM *)bn;
  size_t required = 0;

  if (value == NULL || out_len == NULL || BN_is_negative(value)) {
    return 0;
  }
  // A signed encoding needs room for a clear sign bit, and zero still takes a
  // byte.
  required = BN_num_bytes(value) + (is_signed ? 1 : 0);
  if (required == 0) {
    required = 1;
  }
  *out_len = required;
  if (out == NULL) {
    return 1;
  }
  if (out_size < required) {
    return 0;
  }
#if defined(OPENSSL_BIG_ENDIAN)
  if (!BN_bn2bin_padded(out, out_size, value)) {
    return 0;
  }
#else
  if (!BN_bn2le_padded(out, out_size, value)) {
    return 0;
  }
#endif
  *out_len = out_size;
  return 1;
}

int awslc_prov_bn_equal(const void *a, const void *b) {
  return a != NULL && b != NULL &&
         BN_cmp((const BIGNUM *)a, (const BIGNUM *)b) == 0;
}
