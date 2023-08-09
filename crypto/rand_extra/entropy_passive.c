// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "../fipsmodule/rand/internal.h"

#if defined(FIPS_ENTROPY_SOURCE_PASSIVE)

void RAND_module_entropy_depleted(uint8_t out_entropy[CTR_DRBG_ENTROPY_LEN],
                                  int *out_want_additional_input) {

  uint8_t entropy[PASSIVE_ENTROPY_LOAD_LENGTH] = {0};
  CRYPTO_get_seed_entropy(entropy, out_want_additional_input);
  RAND_load_entropy(out_entropy, entropy);
}

#endif
