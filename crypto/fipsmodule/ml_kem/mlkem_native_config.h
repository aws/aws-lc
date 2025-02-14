/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_CONFIG_H
#define MLK_CONFIG_H

#include "../../internal.h"

/* Namespacing: All symbols are of the form mlkem*. Level-specific
 * symbols are further prefixed with their security level, e.g.
 * mlkem512*, mlkem768*, mlkem1024*. */
#define MLK_NAMESPACE_PREFIX mlkem
#define MLK_NAMESPACE_PREFIX_ADD_LEVEL
#define MLK_MONOBUILD

#if defined(AWSLC_FIPS)
#define MLK_KEYGEN_PCT
#endif /* AWSLC_FIPS */

#if defined(BORINGSSL_CONSTANT_TIME_VALIDATION)
#define MLK_CT_TESTING_ENABLED
#endif /* BORINGSSL_CONSTANT_TIME_VALIDATION */

#endif /* MLkEM_NATIVE_CONFIG_H */
