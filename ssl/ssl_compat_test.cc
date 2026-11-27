// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/pool.h>
#include <openssl/ssl.h>

#include "../crypto/test/test_util.h"
#include "internal.h"

extern "C" {
size_t SSL_compat_get_ocsp_response_mutable(const SSL *ssl,
                                            unsigned char **out);
size_t SSL_compat_get_ocsp_response_const(const SSL *ssl, const uint8_t **out);
}

namespace {

void CheckOCSPResponsePointers(const SSL *ssl, const uint8_t *expected,
                               size_t expected_len) {
  unsigned char sentinel = 0;
  unsigned char *mutable_response = &sentinel;
  const uint8_t *const_response = &sentinel;
  EXPECT_EQ(expected_len,
            SSL_get_tlsext_status_ocsp_resp(ssl, &mutable_response));
  EXPECT_EQ(expected, mutable_response);
  EXPECT_EQ(expected_len,
            SSL_get_tlsext_status_ocsp_resp(ssl, &const_response));
  EXPECT_EQ(expected, const_response);

  mutable_response = &sentinel;
  const_response = &sentinel;
  EXPECT_EQ(expected_len,
            SSL_compat_get_ocsp_response_mutable(ssl, &mutable_response));
  EXPECT_EQ(expected, mutable_response);
  EXPECT_EQ(expected_len,
            SSL_compat_get_ocsp_response_const(ssl, &const_response));
  EXPECT_EQ(expected, const_response);
}

}  // namespace

TEST(SSLCompatTest, OCSPResponsePointers) {
  bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ctx);
  bssl::UniquePtr<SSL> client(SSL_new(ctx.get()));
  ASSERT_TRUE(client);
  SSL_set_connect_state(client.get());
  CheckOCSPResponsePointers(client.get(), nullptr, 0);

  // Install a session directly to exercise the getter without a handshake.
  client->s3->established_session.reset(SSL_SESSION_new(ctx.get()));
  ASSERT_TRUE(client->s3->established_session);
  SSL_SESSION *session = client->s3->established_session.get();
  CheckOCSPResponsePointers(client.get(), nullptr, 0);

  const uint8_t kResponse[] = {0x30, 0x03, 0x0a, 0x01, 0x00};
  session->ocsp_response.reset(
      CRYPTO_BUFFER_new(kResponse, sizeof(kResponse), nullptr));
  ASSERT_TRUE(session->ocsp_response);
  const uint8_t *expected = CRYPTO_BUFFER_data(session->ocsp_response.get());
  CheckOCSPResponsePointers(client.get(), expected, sizeof(kResponse));
  EXPECT_EQ(Bytes(kResponse), Bytes(expected, sizeof(kResponse)));

  bssl::UniquePtr<SSL> server(SSL_new(ctx.get()));
  ASSERT_TRUE(server);
  SSL_set_accept_state(server.get());
  server->s3->established_session = bssl::UpRef(session);
  CheckOCSPResponsePointers(server.get(), nullptr, 0);

  session->ocsp_response.reset();
  CheckOCSPResponsePointers(client.get(), nullptr, 0);
}
