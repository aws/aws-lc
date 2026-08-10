// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_PROVIDER_H
#define AWSLC_PROVIDER_PROVIDER_H

// Shared between the provider's OpenSSL-facing files.

#include <openssl/core.h>
#include <openssl/core_dispatch.h>

#if defined(__cplusplus)
extern "C" {
#endif

// The property string every algorithm we register carries.
#define AWSLC_PROV_PROPERTIES "provider=awslc"

// AWSLC_PROV_CTX is the per-load provider context.
typedef struct awslc_prov_ctx_st AWSLC_PROV_CTX;

// The libctx the core handed us at init. Stored so operations that need a
// library context use the same one the core called us with.
OSSL_LIB_CTX *awslc_prov_ctx_libctx(const AWSLC_PROV_CTX *ctx);

// The core handle for this load, used when raising errors back to the core.
const OSSL_CORE_HANDLE *awslc_prov_ctx_handle(const AWSLC_PROV_CTX *ctx);

// The fan-out, implemented in registry.c and published by provider.c in the
// top-level dispatch table. The dispatch tables it hands out are declared in
// per-class headers, which only registry.c and the class implementations include.
const OSSL_ALGORITHM *awslc_prov_query_operation(void *provctx, int operation_id,
                                                 int *no_store);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_PROVIDER_H
