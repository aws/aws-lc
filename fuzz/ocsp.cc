// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/ocsp.h>


extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  OCSP_RESPONSE *ocsp_response = d2i_OCSP_RESPONSE(NULL, &buf, len);
  if (ocsp_response != NULL) {
    // Extract the basic response
    OCSP_BASICRESP *basic_response = OCSP_response_get1_basic(ocsp_response);
    if (basic_response != NULL) {
      OCSP_BASICRESP_free(basic_response);
    }

    // Reserialize the structure.
    uint8_t *der = NULL;
    i2d_OCSP_RESPONSE(ocsp_response, &der);
    OPENSSL_free(der);
  }
  OCSP_RESPONSE_free(ocsp_response);
  ERR_clear_error();
  return 0;
}
