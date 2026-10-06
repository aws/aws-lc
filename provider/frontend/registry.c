// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/core.h>
#include <openssl/core_dispatch.h>

#include "boundary/names.h"
#include "frontend/operations/rsa.h"
#include "frontend/operations/sha2.h"
#include "frontend/provider.h"

// A macro for defining algorithm rows for the OpenSSL provider dispatch table.
//
// |names| is the row's AWSLC_PROV_NAMES_* string from boundary/names.h.
//
// |property_definition| is the row's property string.
//
// |algorithm| is the symbol-name stem for each specific algorithm's macro
// defined symbols and should be given in lower_snake_case.
//
// |description| is a simple string description for the algorithm.
#define AWSLC_PROV_ALG(names, property_definition, algorithm, description) \
  {names, property_definition, awslc_prov_##algorithm##_functions, description},

// The digest rows, expanded once per table below. |fips_property_definition| is
// given to every algorithm AWS-LC can approve; a row AWS-LC can never approve
// uses AWSLC_PROV_PROPERTIES directly.
#define AWSLC_PROV_DIGESTS(fips_property_definition)                           \
  AWSLC_PROV_ALG(AWSLC_PROV_NAMES_SHA2_224, fips_property_definition,          \
                 sha224, "AWS-LC SHA2-224 implementation")                     \
  AWSLC_PROV_ALG(AWSLC_PROV_NAMES_SHA2_256, fips_property_definition,          \
                 sha256, "AWS-LC SHA2-256 implementation")                     \
  AWSLC_PROV_ALG(AWSLC_PROV_NAMES_SHA2_384, fips_property_definition,          \
                 sha384, "AWS-LC SHA2-384 implementation")                     \
  AWSLC_PROV_ALG(AWSLC_PROV_NAMES_SHA2_512, fips_property_definition,          \
                 sha512, "AWS-LC SHA2-512 implementation")                     \
  AWSLC_PROV_ALG(AWSLC_PROV_NAMES_SHA2_512_224, fips_property_definition,      \
                 sha512_224, "AWS-LC SHA2-512/224 implementation")             \
  AWSLC_PROV_ALG(AWSLC_PROV_NAMES_SHA2_512_256, fips_property_definition,      \
                 sha512_256, "AWS-LC SHA2-512/256 implementation")

static const OSSL_ALGORITHM awslc_prov_digests_fips[] = {
    AWSLC_PROV_DIGESTS(AWSLC_PROV_FIPS_PROPERTIES)
    {NULL, NULL, NULL, NULL}};
static const OSSL_ALGORITHM awslc_prov_digests[] = {
    AWSLC_PROV_DIGESTS(AWSLC_PROV_PROPERTIES)
    {NULL, NULL, NULL, NULL}};

// The key management rows, expanded the same way as the digest rows.
#define AWSLC_PROV_KEYMGMT(fips_property_definition)                           \
  /* PROV_NAMES_RSA */                                                         \
  AWSLC_PROV_ALG("RSA:rsaEncryption:1.2.840.113549.1.1.1",                     \
                 fips_property_definition, rsa_keymgmt,                        \
                 "AWS-LC RSA implementation")

static const OSSL_ALGORITHM awslc_prov_keymgmt_fips[] = {
    AWSLC_PROV_KEYMGMT(AWSLC_PROV_FIPS_PROPERTIES)
    {NULL, NULL, NULL, NULL}};
static const OSSL_ALGORITHM awslc_prov_keymgmt[] = {
    AWSLC_PROV_KEYMGMT(AWSLC_PROV_PROPERTIES)
    {NULL, NULL, NULL, NULL}};

const OSSL_ALGORITHM *awslc_prov_query_operation(void *provctx,
                                                 int operation_id,
                                                 int *no_store) {
  // FIPS mode is fixed for the process, so the core may cache either table.
  if (no_store != NULL) {
    *no_store = 0;
  }

  switch (operation_id) {
    case OSSL_OP_DIGEST:
      return awslc_prov_ctx_is_fips(provctx) ? awslc_prov_digests_fips
                                             : awslc_prov_digests;
    case OSSL_OP_KEYMGMT:
      return awslc_prov_ctx_is_fips(provctx) ? awslc_prov_keymgmt_fips
                                             : awslc_prov_keymgmt;
    default:
      // Returning NULL is what lets the fetch fall through to another provider
      // rather than fail, so every class we do not serve must land here.
      return NULL;
  }
}
