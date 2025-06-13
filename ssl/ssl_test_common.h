// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//
// Created by Smith, Justin on 6/13/25.
//

#ifndef SSL_TEST_H
#define SSL_TEST_H
#include "openssl/base.h"

#include <gtest/gtest.h>

BSSL_NAMESPACE_BEGIN

extern UniquePtr<SSL_SESSION> g_last_session;

struct SSLTestParam {
  // SSL transfer: the sever SSL is encoded into bytes, and then decoded to
  // another SSL. After transfer, the encoded SSL is freed. The decoded one is
  // used to exchange data. This flag is to replay existing tests with the
  // transferred SSL. If false, the tests use the original server SSL. If true,
  // the tests are replayed with the transferred server SSL. Note: SSL transfer
  // works only with either TLS 1.2 or TLS 1.3 after handshake finished and all
  // post-handshake messages have been flushed.
  bool transfer_ssl;
};

int SaveLastSession(SSL *ssl, SSL_SESSION *session);

class SSLTest : public testing::TestWithParam<SSLTestParam> {};

UniquePtr<SSL_CTX> CreateContextWithTestCertificate(const SSL_METHOD *method);

void SetUpExpectedNewCodePoint(SSL_CTX *ctx);

UniquePtr<X509> GetTestCertificate();

UniquePtr<EVP_PKEY> GetTestKey();

UniquePtr<EVP_PKEY> KeyFromPEM(const char *pem);

bool CreateClientAndServer(bssl::UniquePtr<SSL> *out_client,
                                  bssl::UniquePtr<SSL> *out_server,
                                  SSL_CTX *client_ctx, SSL_CTX *server_ctx);

bool CompleteHandshakes(SSL *client, SSL *server);

void SetUpExpectedOldCodePoint(SSL_CTX *ctx);

UniquePtr<EVP_PKEY> KeyFromPEM(const char *pem);

BSSL_NAMESPACE_END

#endif //SSL_TEST_H
