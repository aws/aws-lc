// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include "../../../rand_extra/internal.h"

int maine_coon_initialize(struct entropy_source_t *entropy_source) {
    return 1;
}

void maine_coon_zeroize_thread(struct entropy_source_t *entropy_source) {}
void maine_coon_free_thread(struct entropy_source_t *entropy_source) {}

 int maine_coon_get_seed(const struct entropy_source_t *entropy_source,
    uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
    CRYPTO_sysrand(seed, CTR_DRBG_ENTROPY_LEN);
    return 1;
}
