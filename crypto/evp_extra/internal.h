// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/base.h>

typedef struct {
  union {
    uint8_t priv[64];
    struct {
      // Shift the location of the public key to align with where it is in the
      // private key representation.
      uint8_t pad[32];
      uint8_t value[32];
    } pub;
  } key;
  char has_private;
} ED25519_KEY;

typedef struct {
  uint8_t pub[32];
  uint8_t priv[32];
  char has_private;
} X25519_KEY;

extern const EVP_PKEY_ASN1_METHOD dsa_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD ec_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD rsa_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD rsa_pss_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD ed25519_asn1_meth;
extern const EVP_PKEY_ASN1_METHOD x25519_asn1_meth;

extern const EVP_PKEY_METHOD ed25519_pkey_meth;
extern const EVP_PKEY_METHOD x25519_pkey_meth;

// Returns a reference to the list |non_fips_pkey_evp_methods|. The list has
// size |NON_FIPS_EVP_PKEY_METHODS|.
const EVP_PKEY_METHOD *const *AWSLC_non_fips_pkey_evp_methods(void);

// Returns a reference to the list |asn1_evp_pkey_methods|. The list has
// size |ASN1_EVP_PKEY_METHODS|.
const EVP_PKEY_ASN1_METHOD *const *AWSLC_non_fips_pkey_evp_asn1_methods(void);
