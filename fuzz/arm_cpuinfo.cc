// Copyright (c) 2018, Google Inc.
// SPDX-License-Identifier: ISC

#include "../crypto/fipsmodule/cpucap/cpu_arm_linux.h"


extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  STRING_PIECE sp = {reinterpret_cast<const char *>(buf), len};
  crypto_get_arm_hwcap2_from_cpuinfo(&sp);
  return 0;
}
