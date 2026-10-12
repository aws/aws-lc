// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_PROVIDER_H
#define AWSLC_PROVIDER_PROVIDER_H

// Shared between the provider's OpenSSL-facing files.

#include <stdint.h>

#include <openssl/core.h>
#include <openssl/core_dispatch.h>

#if defined(__cplusplus)
extern "C" {
#endif

// The property strings every algorithm we register carries.
#define AWSLC_PROV_PROPERTIES "provider=awslc"
// Apply fips=yes to algorithms that AWS-LC can approve in FIPS mode.
#define AWSLC_PROV_FIPS_PROPERTIES AWSLC_PROV_PROPERTIES ",fips=yes"

// AWSLC_PROV_CTX is the per-load provider context.
typedef struct awslc_prov_ctx_st AWSLC_PROV_CTX;

// The core handle for this load, used when raising errors back to the core.
const OSSL_CORE_HANDLE *awslc_prov_ctx_handle(const AWSLC_PROV_CTX *ctx);

// Whether the linked AWS-LC reported FIPS mode when this provider initialized.
int awslc_prov_ctx_is_fips(const AWSLC_PROV_CTX *ctx);

// Close a bracket opened by awslc_prov_service_indicator_before_call() after the
// service succeeded. An unapproved verdict clears |*approved|; in FIPS mode it
// also notifies the application. Zero means the application vetoed the result,
// and the caller must discard any output and fail the operation.
int awslc_prov_indicator_end(AWSLC_PROV_CTX *ctx, uint64_t before,
                             const char *type, const char *description,
                             int *approved);

// The fan-out, implemented in registry.c and published by provider.c in the
// top-level dispatch table. The dispatch tables it hands out are declared in
// per-class headers, which only registry.c and the class implementations include.
const OSSL_ALGORITHM *awslc_prov_query_operation(void *provctx, int operation_id,
                                                 int *no_store);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_PROVIDER_H
