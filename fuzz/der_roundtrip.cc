// Copyright (c) 2022, Google Inc.
// SPDX-License-Identifier: ISC

#include <stdlib.h>
#include <string.h>

#include <openssl/bytestring.h>
#include <openssl/ecdsa.h>
#include <openssl/mem.h>


extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  CBS cbs, body;
  CBS_ASN1_TAG tag;
  CBS_init(&cbs, buf, len);
  if (CBS_get_any_asn1(&cbs, &body, &tag)) {
    // DER has a unique encoding, so any parsed input should round-trip
    // correctly.
    size_t consumed = len - CBS_len(&cbs);
    bssl::ScopedCBB cbb;
    CBB body_cbb;
    if (!CBB_init(cbb.get(), consumed) ||
        !CBB_add_asn1(cbb.get(), &body_cbb, tag) ||
        !CBB_add_bytes(&body_cbb, CBS_data(&body), CBS_len(&body)) ||
        !CBB_flush(cbb.get()) ||
        CBB_len(cbb.get()) != consumed ||
        memcmp(CBB_data(cbb.get()), buf, consumed) != 0) {
      abort();
    }
  }

  ECDSA_SIG *sig = ECDSA_SIG_from_bytes(buf, len);
  if (sig != NULL) {
    uint8_t *enc;
    size_t enc_len;
    if (!ECDSA_SIG_to_bytes(&enc, &enc_len, sig) ||
        enc_len != len ||
        memcmp(buf, enc, len) != 0) {
      abort();
    }
    OPENSSL_free(enc);
    ECDSA_SIG_free(sig);
  }

  return 0;
}
