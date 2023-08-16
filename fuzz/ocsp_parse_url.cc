// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/mem.h>
#include <openssl/ocsp.h>
#include <string>

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  std::string input(reinterpret_cast<const char *>(buf), len);
  char *host = nullptr;
  char *path = nullptr;
  char *port = nullptr;
  int is_ssl;

  if (OCSP_parse_url(input.c_str(), &host, &port, &path, &is_ssl)) {
    // Check that parameters have been assigned values.
    if (!host && !path && !port && (is_ssl != 1 && is_ssl != 0)) {
      return 1;
    }
    OPENSSL_free(host);
    OPENSSL_free(path);
    OPENSSL_free(port);
  } else {
    // Check that parameters have not been assigned values.
    if (host && path && port) {
      return 1;
    }
  }

  return 0;
}
