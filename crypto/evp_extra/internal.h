// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWS_LC_EVP_EXTRA_INTERNAL_H
#define AWS_LC_EVP_EXTRA_INTERNAL_H

#include <openssl/base.h>
#include "../fipsmodule/evp/internal.h"

#include "../fipsmodule/ml_dsa/ml_dsa.h"

#define PKCS8_VERSION_ONE 0
#define PKCS8_VERSION_TWO 1

typedef struct {
  uint8_t pub[32];
  uint8_t priv[32];
  char has_private;
} X25519_KEY;

extern const size_t asn1_evp_pkey_methods_size;
extern const EVP_PKEY_ASN1_METHOD *const asn1_evp_pkey_methods[];
extern const EVP_PKEY_ASN1_METHOD dsa_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD ec_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD rsa_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD rsa_pss_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD ed25519_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD x25519_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD pqdsa_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD kem_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD hmac_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD dh_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD ed25519ph_asn1_meth;

extern const EVP_PKEY_METHOD x25519_pkey_meth;
extern const EVP_PKEY_METHOD hkdf_pkey_meth;
extern const EVP_PKEY_METHOD hmac_pkey_meth;
extern const EVP_PKEY_METHOD dh_pkey_meth;
extern const EVP_PKEY_METHOD dsa_pkey_meth;
extern const EVP_PKEY_METHOD pqdsa_pkey_meth;
extern const EVP_PKEY_METHOD ed25519ph_pkey_meth;

// evp_pkey_set_method behaves like |EVP_PKEY_set_type|, but takes a pointer to
// a method table. This avoids depending on every |EVP_PKEY_ASN1_METHOD|.
void evp_pkey_set_method(EVP_PKEY *pkey, const EVP_PKEY_ASN1_METHOD *method);

// Returns a reference to the list |non_fips_pkey_evp_methods|. The list has
// size |NON_FIPS_EVP_PKEY_METHODS|.
const EVP_PKEY_METHOD *const *AWSLC_non_fips_pkey_evp_methods(void);

// Returns a reference to the list |asn1_evp_pkey_methods|. The list has
// size |ASN1_EVP_PKEY_METHODS|.
const EVP_PKEY_ASN1_METHOD *const *AWSLC_non_fips_pkey_evp_asn1_methods(void);

#endif
