// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#if defined(OPENSSL_AARCH64) && !defined(OPENSSL_STATIC_ARMCAP)

#include "cpu_aarch64.h"

void handle_cpu_env(uint32_t *out, const char *in) {
  const int invert = in[0] == '~';
  const int or = in[0] == '|';
  const int skip_first_byte = invert || or;
  const int hex = in[skip_first_byte] == '0' && in[skip_first_byte+1] == 'x';
  uint32_t armcap = out[0];

  int sscanf_result;
  uint32_t v;
  if (hex) {
    sscanf_result = sscanf(in + skip_first_byte + 2, "%" PRIx32, &v);
  } else {
    sscanf_result = sscanf(in + skip_first_byte, "%" PRIu32, &v);
  }

  if (!sscanf_result) {
    return;
  }

  // Detect if the user is trying to use the environment variable to set
  // a capability that is _not_ available on the CPU:
  // If the runtime capability check (e.g via getauxval() on Linux)
  // returned a non-zero hwcap in `armcap` (out)
  // and a bit set in the requested `v` is not set in `armcap`,
  // abort instead of crashing later.
  // The case of invert cannot enable an unexisting capability;
  // it can only disable an existing one.
  if (!invert && armcap && (~armcap & v))
  {
    fprintf(stderr,
            "Fatal Error: HW capability found: 0x%02X, but HW capability requested: 0x%02X.\n",
            armcap, v);
    abort();
  }

  if (invert) {
    out[0] &= ~v;
  } else if (or) {
    out[0] |= v;
  } else {
    out[0] = v;
  }
}

#endif // OPENSSL_AARCH64 && !OPENSSL_STATIC_ARMCAP
