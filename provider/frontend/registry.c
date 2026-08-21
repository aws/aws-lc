// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/core.h>
#include <openssl/core_dispatch.h>

#include "internal/frontend/digests.h"
#include "internal/provider.h"

// A macro for defining algorithm rows for the OpenSSL provider dispatch table.
//
// |names| are provided as ':' separated values and come verbatim from OpenSSL's
// providers/implementations/include/prov/names.h
// They include legacy spellings, aliases, and the OID.
//
// |algorithm| is the symbol-name stem for each specific algorithm's macro
// defined symbols and should be given in lower_snake_case.
//
// |description| is a simple string description for the algorithm.
#define AWSLC_PROV_ALG(names, algorithm, description)                     \
  { names, AWSLC_PROV_PROPERTIES, awslc_prov_##algorithm##_functions,     \
    description }

// One table per operation class.
static const OSSL_ALGORITHM awslc_prov_digests[] = {
    AWSLC_PROV_ALG("SHA2-256:SHA-256:SHA256:2.16.840.1.101.3.4.2.1", sha256,
                   "AWS-LC SHA2-256 implementation"),
    {NULL, NULL, NULL, NULL}};

const OSSL_ALGORITHM *awslc_prov_query_operation(void *provctx,
                                                 int operation_id,
                                                 int *no_store) {
  (void)provctx;
  // The tables are static and cacheable, so the core may keep them.
  *no_store = 0;

  switch (operation_id) {
    case OSSL_OP_DIGEST:
      return awslc_prov_digests;
    default:
      // Returning NULL is what lets the fetch fall through to another provider
      // rather than fail, so every class we do not serve must land here.
      return NULL;
  }
}
