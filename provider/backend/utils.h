// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_BACKEND_UTILS_H
#define AWSLC_PROVIDER_BACKEND_UTILS_H

// Back-side helpers shared across operation classes. These name AWS-LC types,
// so this header is never part of the boundary.

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

// The AWS-LC digest any of OpenSSL's spellings of |name| denotes, matched
// without case, or NULL.
const EVP_MD *awslc_prov_digest_md(const char *name);

// OpenSSL's canonical name for |md|, or NULL.
const char *awslc_prov_digest_md_name(const EVP_MD *md);

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_BACKEND_UTILS_H
