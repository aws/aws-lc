// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// C side of the Rust integration. CMake compiles it only when ENABLE_RUST is
// on. It is empty without AWSLC_RUST, because some builds, such as aws-lc-sys's
// cc builder, compile every .c file under crypto/.

#include <openssl/err.h>

#include "internal.h"

#if defined(AWSLC_RUST)

int CRYPTO_rust_byte_sum(const uint8_t *in, size_t in_len, uint64_t *out) {
  if (!caracal_byte_sum(in, in_len, out)) {
    OPENSSL_PUT_ERROR(CRYPTO, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  }
  return 1;
}

#endif  // AWSLC_RUST
