// Copyright (c) 2022, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/bio.h>
#include <openssl/conf.h>
#include <openssl/x509.h>

#include <algorithm>

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  // The string-based extensions APIs routinely produce output quadratic in
  // their input. Cap the input size to mitigate this. See also
  // https://crbug.com/boringssl/611.
  len = std::min(len, size_t{8 * 1024});

  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(buf, len));
  bssl::UniquePtr<CONF> conf(NCONF_new(nullptr));
  if (NCONF_load_bio(conf.get(), bio.get(), nullptr)) {
    // Run with and without |X509V3_CTX| information.
    bssl::UniquePtr<X509> cert(X509_new());
    X509V3_CTX ctx;
    X509V3_set_ctx(&ctx, /*subject=*/cert.get(), /*issuer=*/cert.get(), nullptr,
                   nullptr, 0);
    X509V3_EXT_add_nconf(conf.get(), &ctx, "default", cert.get());

    cert.reset(X509_new());
    X509V3_EXT_add_nconf(conf.get(), nullptr, "default", cert.get());
  }
  return 0;
}
