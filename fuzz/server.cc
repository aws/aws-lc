// Copyright (c) 2016, Google Inc.
// SPDX-License-Identifier: ISC

#include "../ssl/test/fuzzer.h"


static TLSFuzzer g_fuzzer(TLSFuzzer::kTLS, TLSFuzzer::kServer);

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  return g_fuzzer.TestOneInput(buf, len);
}
