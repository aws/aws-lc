// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>

#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/ssl.h>

struct GlobalState {
  GlobalState() : ctx(SSL_CTX_new(TLS_method())) {}

  bssl::UniquePtr<SSL_CTX> ctx;
};

static GlobalState g_state;

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  bssl::UniquePtr<SSL> ssl(SSL_from_bytes(buf, len, g_state.ctx.get()));

  // If the format was invalid, just return.
  if (!ssl) {
    return 0;
  }

  // Stress the encoder.
  size_t encoded_len;
  uint8_t *encoded;
  if (!SSL_to_bytes(ssl.get(), &encoded, &encoded_len)) {
    fprintf(stderr, "In Fuzz, SSL_to_bytes failed.\n");
    return 1;
  }

  OPENSSL_free(encoded);
  return 0;
}
