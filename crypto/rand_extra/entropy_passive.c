// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "../fipsmodule/rand/internal.h"

#if defined(AWSLC_FIPS)

void RAND_module_entropy_depleted(void) {
  uint8_t entropy[ENTROPY_POOL_SIZE] = {0};

  // Next step: draw entropy from either CPU source of system source
  // and put into |entropy|.

  RAND_load_entropy(entropy);
}

#endif
