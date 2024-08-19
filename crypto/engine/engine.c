/* Copyright (c) 2014, Google Inc.
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

#include <openssl/engine.h>

#include <string.h>
#include <assert.h>

#include <openssl/ec_key.h>
#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/rsa.h>
#include <openssl/thread.h>

#include "../internal.h"


struct engine_st {
  RSA_METHOD *rsa_method;
  ECDSA_METHOD *ecdsa_method;
};

ENGINE *ENGINE_new(void) { return OPENSSL_zalloc(sizeof(ENGINE)); }

int ENGINE_free(ENGINE *engine) {
  // Methods are currently required to be static so are not unref'ed.
  OPENSSL_free(engine);
  return 1;
}

int ENGINE_set_RSA(ENGINE *engine, const RSA_METHOD *method) {
  if(engine) {
    engine->rsa_method = (RSA_METHOD *)method;
    return 1;
  }

  return 0;
}

const RSA_METHOD *ENGINE_get_RSA(const ENGINE *engine) {
  return engine->rsa_method;
}

int ENGINE_set_ECDSA(ENGINE *engine, const ECDSA_METHOD *method) {
  if(engine) {
    engine->ecdsa_method = (ECDSA_METHOD *)method;
    return 1;
  }

  return 0;
}

const ECDSA_METHOD *ENGINE_get_ECDSA(const ENGINE *engine) {
  return engine->ecdsa_method;
}

OPENSSL_DECLARE_ERROR_REASON(ENGINE, OPERATION_NOT_SUPPORTED)

void ENGINE_cleanup(void) {}
