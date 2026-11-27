// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/ssl.h>

#if defined(__cplusplus)
#error "This test must be compiled as C."
#endif

size_t SSL_compat_get_ocsp_response_mutable(const SSL *ssl,
                                            unsigned char **out);
size_t SSL_compat_get_ocsp_response_const(const SSL *ssl, const uint8_t **out);

size_t SSL_compat_get_ocsp_response_mutable(const SSL *ssl,
                                            unsigned char **out) {
  return SSL_get_tlsext_status_ocsp_resp(ssl, out);
}

size_t SSL_compat_get_ocsp_response_const(const SSL *ssl, const uint8_t **out) {
  return SSL_get_tlsext_status_ocsp_resp(ssl, out);
}
