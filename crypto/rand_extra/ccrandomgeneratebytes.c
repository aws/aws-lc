// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/rand.h>

#include "internal.h"

#if defined(OPENSSL_RAND_CCRANDOMGENERATEBYTES)

#include <CommonCrypto/CommonRandom.h>

#include <stdio.h>
#include <stdlib.h>

void CRYPTO_sysrand(uint8_t *out, size_t requested) {

  if (len == 0) {
    return 1;
  }

  // To get system randomness on iOS we use |CCRandomGenerateBytes|. On MacOS we
  // use |getentropy| but iOS doesn't expose that.
  if (CCRandomGenerateBytes(out, len) == kCCSuccess) {
    return 1;
  } else {
    fprintf(stderr, "CCRandomGenerateBytes failed.\n");
    abort();
  }
}

void CRYPTO_sysrand_for_seed(uint8_t *out, size_t requested) {
  CRYPTO_sysrand(out, requested);
}

#endif
