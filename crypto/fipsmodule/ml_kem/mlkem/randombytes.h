/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLK_RANDOMBYTES_H
#define MLK_RANDOMBYTES_H

#include <stddef.h>
#include <stdint.h>

#include "cbmc.h"

void randombytes(uint8_t *out, size_t outlen)
__contract__(
  requires(memory_no_alias(out, outlen))
  assigns(memory_slice(out, outlen))
);

#endif /* MLK_RANDOMBYTES_H */
