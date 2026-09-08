// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_INTERNAL_BACKEND_DIGESTS_H
#define AWSLC_PROVIDER_INTERNAL_BACKEND_DIGESTS_H

// The digest entry points the back side implements, one set per algorithm.
//
// This header crosses the boundary, so it obeys the rule ../backend.h states:
// plain C types only. Read that file first; it documents the whole arrangement.
//
// Every algorithm here has the same shape, which is what lets the front side's
// slots be thin:
//
//   ctx_size()               bytes the caller must allocate for the context
//   digest_size()            the digest length
//   block_size()             the input block length
//   init(ctx)                initialize a caller-allocated context
//   update(ctx, data, len)   absorb input
//   final(ctx, out, size)    write the digest, rejecting an undersized |out|
//   copy(dst, src)           duplicate context state
//
// Returning 1 on success and 0 on failure, per ../backend.h.

#include <stddef.h>

#if defined(__cplusplus)
extern "C" {
#endif

// SHA-256, from backend/operations/digests/sha2.c.

size_t awslc_prov_sha256_ctx_size(void);

size_t awslc_prov_sha256_digest_size(void);

size_t awslc_prov_sha256_block_size(void);

int awslc_prov_sha256_init(void *ctx);

int awslc_prov_sha256_update(void *ctx, const void *data, size_t len);

int awslc_prov_sha256_final(void *ctx, unsigned char *out, size_t out_size);

int awslc_prov_sha256_copy(void *dst, const void *src);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_INTERNAL_BACKEND_DIGESTS_H
