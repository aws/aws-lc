// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include "../../../rand_extra/internal.h"

int snapsafe_fallback_initialize(struct entropy_source_t *entropy_source) {
    return 1;
}

void snapsafe_fallback_zeroize_thread(struct entropy_source_t *entropy_source) {}
void snapsafe_fallback_free_thread(struct entropy_source_t *entropy_source) {}

 int snapsafe_fallback_get_seed(const struct entropy_source_t *entropy_source,
    uint8_t seed[CTR_DRBG_ENTROPY_LEN]) {
    CRYPTO_sysrand(seed, CTR_DRBG_ENTROPY_LEN);
    return 1;
}
