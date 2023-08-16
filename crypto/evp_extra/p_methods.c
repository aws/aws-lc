// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>

#include "../fipsmodule/evp/internal.h"
#include "../internal.h"
#include "internal.h"

static const EVP_PKEY_METHOD *const non_fips_pkey_evp_methods[] = {
  &ed25519_pkey_meth,
  &x25519_pkey_meth,
#ifdef ENABLE_DILITHIUM
  &dilithium3_pkey_meth,
#endif
  &kem_pkey_meth,
};

static const EVP_PKEY_ASN1_METHOD *const asn1_evp_pkey_methods[] = {
  &rsa_asn1_meth,
  &rsa_pss_asn1_meth,
  &ec_asn1_meth,
  &dsa_asn1_meth,
  &ed25519_asn1_meth,
  &x25519_asn1_meth,
#ifdef ENABLE_DILITHIUM
  &dilithium3_asn1_meth,
#endif
  &kem_asn1_meth,
};

OPENSSL_STATIC_ASSERT(
  NON_FIPS_EVP_PKEY_METHODS == OPENSSL_ARRAY_SIZE(non_fips_pkey_evp_methods),
  NON_FIPS_EVP_PKEY_METHODS_does_not_have_the_expected_value)
OPENSSL_STATIC_ASSERT(
  ASN1_EVP_PKEY_METHODS == OPENSSL_ARRAY_SIZE(asn1_evp_pkey_methods),
  ASN1_EVP_PKEY_METHODS_does_not_have_the_expected_value)

const EVP_PKEY_METHOD *const *AWSLC_non_fips_pkey_evp_methods(void) {
  return non_fips_pkey_evp_methods;
}

const EVP_PKEY_ASN1_METHOD *const *AWSLC_non_fips_pkey_evp_asn1_methods(void) {
  return asn1_evp_pkey_methods;
}
