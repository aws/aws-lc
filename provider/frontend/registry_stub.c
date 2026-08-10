// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This provider intentionally advertises no operations.

#include <stddef.h>

#include "internal/provider.h"

const OSSL_ALGORITHM *awslc_prov_query_operation(void *provctx,
                                                 int operation_id,
                                                 int *no_store) {
  (void)provctx;
  (void)operation_id;
  *no_store = 0;
  return NULL;
}
