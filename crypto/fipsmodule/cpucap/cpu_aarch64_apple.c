/* Copyright (c) 2021, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include "internal.h"

#if defined(OPENSSL_AARCH64) && defined(OPENSSL_APPLE) && \
    !defined(OPENSSL_STATIC_ARMCAP)

#include <sys/sysctl.h>
#include <sys/types.h>

#include <openssl/arm_arch.h>


extern uint32_t OPENSSL_armcap_P;
extern uint8_t OPENSSL_cpucap_initialized;

static int has_hw_feature(const char *name) {
  int value;
  size_t len = sizeof(value);
  if (sysctlbyname(name, &value, &len, NULL, 0) != 0) {
    return 0;
  }
  if (len != sizeof(int)) {
    // This should not happen. All the values queried should be integer-valued.
    assert(0);
    return 0;
  }

  // Per sys/sysctl.h:
  //
  //   Selectors that return errors are not support on the system. Supported
  //   features will return 1 if they are recommended or 0 if they are supported
  //   but are not expected to help performance. Future versions of these
  //   selectors may return larger values as necessary so it is best to test for
  //   non zero.
  return value != 0;
}

// This function compares the brand retrieved with the input string
// up to the length of the shortest of these 2 strings.
static int is_brand(const char *in_str) {
  char brand[64];
  size_t len = sizeof(brand);
  if (sysctlbyname("machdep.cpu.brand_string", brand, &len, NULL, 0) != 0 ||
      strncmp(brand, in_str, strnlen(in_str, len)) != 0) {
    return 0;
  }

  if (len > sizeof(brand)) {
    // This should not happen; too large of a brand for this function.
    assert(0);
    return 0;
  }

  return 1;
}

// handle_cpu_env applies the value from |in| to the CPUID values in |out[0]|.
// See the comment in |OPENSSL_cpuid_setup| about this.
static void handle_cpu_env(uint32_t *out, const char *in) {
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
  // If getauxval() returned a non-zero hwcap in `armcap` (out)
  // and a bit set in the requested `v` is not set in `armcap`,
  // abort instead of crashing later.
  // The case of invert cannot enable an unexisting capability;
  // it can only disable an existing one.
  if (!invert && armcap && (~armcap & v))
  {
    fprintf(stderr,
            "Fatal Error: HW capability found: 0x%02X, but HW capability requested: 0x%02X.\n",
            armcap, v);
    exit(1);
  }

  if (invert) {
    out[0] &= ~v;
  } else if (or) {
    out[0] |= v;
  } else {
    out[0] = v;
  }
}

void OPENSSL_cpuid_setup(void) {
  // Apple ARM64 platforms have NEON and cryptography extensions available
  // statically, so we do not need to query them. In particular, there sometimes
  // are no sysctls corresponding to such features. See below.
#if !defined(__ARM_NEON) || !defined(__ARM_FEATURE_AES) || \
    !defined(__ARM_FEATURE_SHA2)
#error "NEON and crypto extensions should be statically available."
#endif
  OPENSSL_armcap_P =
      ARMV7_NEON | ARMV8_AES | ARMV8_PMULL | ARMV8_SHA1 | ARMV8_SHA256;

  // See Apple's documentation for sysctl names:
  // https://developer.apple.com/documentation/kernel/1387446-sysctlbyname/determining_instruction_set_characteristics
  //
  // The new feature names, e.g. "hw.optional.arm.FEAT_SHA512", are only
  // available in macOS 12. For compatibility with macOS 11, we also support
  // the old names. The old names don't have values for features like FEAT_AES,
  // so instead we detect them statically above.
  if (has_hw_feature("hw.optional.arm.FEAT_SHA512") ||
      has_hw_feature("hw.optional.armv8_2_sha512")) {
    OPENSSL_armcap_P |= ARMV8_SHA512;
  }

  if (has_hw_feature("hw.optional.armv8_2_sha3")) {
    OPENSSL_armcap_P |= ARMV8_SHA3;
  }

  if (is_brand("Apple M1")) {
    OPENSSL_armcap_P |= ARMV8_APPLE_M1;
  }

  // OPENSSL_armcap is a 32-bit, unsigned value which may start with "0x" to
  // indicate a hex value. Prior to the 32-bit value, a '~' or '|' may be given.
  //
  // If the '~' prefix is present:
  //   the value is inverted and ANDed with the probed CPUID result
  // If the '|' prefix is present:
  //   the value is ORed with the probed CPUID result
  // Otherwise:
  //   the value is taken as the result of the CPUID
  const char *env;
  env = getenv("OPENSSL_armcap");
  if (env != NULL) {
    handle_cpu_env(&OPENSSL_armcap_P, env);
  }

  OPENSSL_cpucap_initialized = 1;
}

#endif  // OPENSSL_AARCH64 && OPENSSL_APPLE && !OPENSSL_STATIC_ARMCAP
