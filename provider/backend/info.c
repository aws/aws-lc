// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/crypto.h>
#include <openssl/service_indicator.h>

#include "internal/backend.h"

const char *awslc_prov_backend_version(void) {
  return awslc_version_string();
}

int awslc_prov_backend_is_fips(void) {
  return FIPS_mode();
}
