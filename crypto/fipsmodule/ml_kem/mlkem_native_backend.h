// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef MLKEM_NATIVE_BACKEND_H
#define MLKEM_NATIVE_BACKEND_H

#include <openssl/target.h>

// For now, we only include an AArch64 backend, used on Linux and MacOS systems
#if !defined(OPENSSL_NO_ASM) &&				\
    defined(OPENSSL_AARCH64) &&				\
    (defined(OPENSSL_LINUX) || defined(OPENSSL_APPLE))
#include "mlkem/native/aarch64/meta.h"
#endif

#endif /* MLKEM_NATIVE_BACKEND_H */
