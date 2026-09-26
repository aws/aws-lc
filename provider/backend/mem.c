// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Expose openssl/mem.h functions from AWS-LC for use in the provider.

#include <openssl/mem.h>

#include "internal/backend.h"

void *awslc_prov_zalloc(size_t size) {
  return OPENSSL_zalloc(size);
}

void awslc_prov_clear_free(void *ptr, size_t size) {
  OPENSSL_clear_free(ptr, size);
}

void awslc_prov_cleanse(void *ptr, size_t size) {
  OPENSSL_cleanse(ptr, size);
}
