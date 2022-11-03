// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

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
  // Clean error code queue before starting test.
  ERR_clear_error();
  // |SSL_from_bytes| should only be called on the output of |SSL_to_bytes|.
  // The method call order is reversed here for Fuzz.
  bssl::UniquePtr<SSL> ssl(SSL_from_bytes(buf, len, g_state.ctx.get()));

  // If the format was invalid, just return.
  if (!ssl) {
    return 0;
  }

  // Stress the encoder.
  size_t encoded_len;
  uint8_t *encoded;
  if (!SSL_to_bytes(ssl.get(), &encoded, &encoded_len)) {
    uint32_t e = ERR_get_error();
    if (e == 0) {
      fprintf(stderr, "In Fuzz, SSL_to_bytes failed without giving a error code.\n");
      return 1;
    }
    uint32_t e_lib = ERR_GET_LIB(e);
    uint32_t e_reason = ERR_GET_REASON(e);
    if (e_reason == SSL_R_SERIALIZATION_UNSUPPORTED) {
      return 0;
    }
    fprintf(stderr, "In Fuzz, SSL_to_bytes failed with error: lib %u, reason %u, str %s\n", 
      e_lib, e_reason, ERR_reason_error_string(e));
    return 1;
  }

  OPENSSL_free(encoded);
  return 0;
}
