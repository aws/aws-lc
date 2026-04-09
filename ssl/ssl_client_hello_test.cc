/* Copyright (c) 2024, Amazon.
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

#include <gtest/gtest.h>

#include <openssl/ssl.h>
#include <openssl/tls1.h>

#include "ssl_common_test.h"

BSSL_NAMESPACE_BEGIN

namespace {

// Test SSL client hello callback functionality
TEST(SSLClientHelloTest, ClientHelloCallback) {
  UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  // Test that callback is called and can access client hello data
  bool callback_called = false;
  SSL_CTX_set_client_hello_cb(
      server_ctx.get(),
      [](SSL *ssl, int *al, void *arg) -> int {
        bool *called = static_cast<bool *>(arg);
        *called = true;

        // Test SSL_client_hello_isv2 - should return 0 (not SSLv2)
        EXPECT_EQ(0, SSL_client_hello_isv2(ssl));

        // Test SSL_client_hello_get0_ext for a common extension
        const unsigned char *ext_data = nullptr;
        size_t ext_len = 0;
        // Try to get server_name extension (type 0)
        (void)SSL_client_hello_get0_ext(ssl, TLSEXT_TYPE_server_name, &ext_data,
                                        &ext_len);
        // Extension may or may not be present, but function should not crash

        return SSL_CLIENT_HELLO_SUCCESS;
      },
      &callback_called);

  UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));
  EXPECT_TRUE(callback_called);
}

// Test client hello callback return values
TEST(SSLClientHelloTest, ClientHelloCallbackReturnValues) {
  UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  // Test SSL_CLIENT_HELLO_ERROR causes connection failure
  SSL_CTX_set_client_hello_cb(
      server_ctx.get(),
      [](SSL *ssl, int *al, void *arg) -> int {
        *al = SSL_AD_INTERNAL_ERROR;
        return SSL_CLIENT_HELLO_ERROR;
      },
      nullptr);

  UniquePtr<SSL> client, server;
  ASSERT_FALSE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                      server_ctx.get()));
}

// Test SSL_client_hello_get0_ext with various extensions
TEST(SSLClientHelloTest, ClientHelloGetExtension) {
  UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  struct ExtensionTest {
    bool found_supported_versions = false;
    bool found_key_share = false;
  } test_data;

  SSL_CTX_set_client_hello_cb(
      server_ctx.get(),
      [](SSL *ssl, int *al, void *arg) -> int {
        ExtensionTest *data = static_cast<ExtensionTest *>(arg);
        const unsigned char *ext_data = nullptr;
        size_t ext_len = 0;

        // Test common TLS 1.3 extensions
        // Supported versions extension (43)
        if (SSL_client_hello_get0_ext(ssl, TLSEXT_TYPE_supported_versions,
                                      &ext_data, &ext_len)) {
          data->found_supported_versions = true;
          EXPECT_GT(ext_len, 0u);
          EXPECT_NE(nullptr, ext_data);
        }

        // Key share extension (51) - TLS 1.3
        if (SSL_client_hello_get0_ext(ssl, TLSEXT_TYPE_key_share, &ext_data,
                                      &ext_len)) {
          data->found_key_share = true;
          EXPECT_GT(ext_len, 0u);
          EXPECT_NE(nullptr, ext_data);
        }

        // Test non-existent extension (should return 0)
        EXPECT_EQ(0,
                  SSL_client_hello_get0_ext(ssl, 65535, &ext_data, &ext_len));

        return SSL_CLIENT_HELLO_SUCCESS;
      },
      &test_data);

  UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  // In TLS 1.3, we should find supported_versions extension
  EXPECT_TRUE(test_data.found_supported_versions);
}

// Test that SSL_client_hello_isv2 correctly identifies non-SSLv2 hellos
TEST(SSLClientHelloTest, ClientHelloIsV2) {
  UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  // Test with different TLS versions
  for (uint16_t version :
       {TLS1_VERSION, TLS1_1_VERSION, TLS1_2_VERSION, TLS1_3_VERSION}) {
    SCOPED_TRACE(version);

    ASSERT_TRUE(SSL_CTX_set_min_proto_version(client_ctx.get(), version));
    ASSERT_TRUE(SSL_CTX_set_max_proto_version(client_ctx.get(), version));
    ASSERT_TRUE(SSL_CTX_set_min_proto_version(server_ctx.get(), version));
    ASSERT_TRUE(SSL_CTX_set_max_proto_version(server_ctx.get(), version));

    bool tested = false;
    SSL_CTX_set_client_hello_cb(
        server_ctx.get(),
        [](SSL *ssl, int *al, void *arg) -> int {
          bool *tested_ptr = static_cast<bool *>(arg);
          *tested_ptr = true;
          // Should always return 0 since SSLv2 is not supported
          EXPECT_EQ(0, SSL_client_hello_isv2(ssl));
          return SSL_CLIENT_HELLO_SUCCESS;
        },
        &tested);

    UniquePtr<SSL> client, server;
    ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                       server_ctx.get()));
    EXPECT_TRUE(tested);
  }
}

// Test multiple callbacks and state management
TEST(SSLClientHelloTest, ClientHelloCallbackState) {
  UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  int call_count = 0;
  SSL_CTX_set_client_hello_cb(
      server_ctx.get(),
      [](SSL *ssl, int *al, void *arg) -> int {
        int *count = static_cast<int *>(arg);
        (*count)++;
        return SSL_CLIENT_HELLO_SUCCESS;
      },
      &call_count);

  // First connection
  {
    UniquePtr<SSL> client, server;
    ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                       server_ctx.get()));
  }
  EXPECT_EQ(1, call_count);

  // Second connection should call callback again
  {
    UniquePtr<SSL> client, server;
    ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                       server_ctx.get()));
  }
  EXPECT_EQ(2, call_count);

  // Reset callback to nullptr
  SSL_CTX_set_client_hello_cb(server_ctx.get(), nullptr, nullptr);

  // Third connection should not increment count
  {
    UniquePtr<SSL> client, server;
    ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                       server_ctx.get()));
  }
  EXPECT_EQ(2, call_count);
}

// Test error handling with invalid parameters
TEST(SSLClientHelloTest, ClientHelloCallbackErrorHandling) {
  UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(server_ctx);
  UniquePtr<SSL> ssl(SSL_new(server_ctx.get()));
  ASSERT_TRUE(ssl);

  // Test SSL_client_hello_isv2 with invalid SSL context (before handshake)
  // Should not crash but return reasonable value
  EXPECT_EQ(0, SSL_client_hello_isv2(ssl.get()));

  // Test SSL_client_hello_get0_ext with invalid parameters
  const unsigned char *ext_data = nullptr;
  size_t ext_len = 0;
  EXPECT_EQ(0, SSL_client_hello_get0_ext(ssl.get(), 0, &ext_data, &ext_len));
}

// Test interaction with other callbacks (select_certificate_cb)
TEST(SSLClientHelloTest, ClientHelloCallbackWithSelectCertificate) {
  UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  bool client_hello_called = false;

  SSL_CTX_set_client_hello_cb(
      server_ctx.get(),
      [](SSL *ssl, int *al, void *arg) -> int {
        bool *called = static_cast<bool *>(arg);
        *called = true;
        return SSL_CLIENT_HELLO_SUCCESS;
      },
      &client_hello_called);

  SSL_CTX_set_select_certificate_cb(
      server_ctx.get(),
      [](const SSL_CLIENT_HELLO *client_hello) -> ssl_select_cert_result_t {
        // Just verify the callback is called by testing the SSL pointer
        EXPECT_NE(nullptr, client_hello->ssl);
        return ssl_select_cert_success;
      });

  UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  // Client hello callback should be called
  EXPECT_TRUE(client_hello_called);
}

// Test SSL_CLIENT_HELLO_RETRY return value (though treated as error in current
// implementation)
TEST(SSLClientHelloTest, ClientHelloCallbackRetry) {
  UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  // Test SSL_CLIENT_HELLO_RETRY causes connection failure
  SSL_CTX_set_client_hello_cb(
      server_ctx.get(),
      [](SSL *ssl, int *al, void *arg) -> int {
        return SSL_CLIENT_HELLO_RETRY;
      },
      nullptr);

  UniquePtr<SSL> client, server;
  // Currently, RETRY is treated as failure in AWS-LC
  ASSERT_FALSE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                      server_ctx.get()));
}

// Test extension retrieval with known extensions
TEST(SSLClientHelloTest, ClientHelloKnownExtensions) {
  UniquePtr<SSL_CTX> client_ctx(SSL_CTX_new(TLS_method()));
  UniquePtr<SSL_CTX> server_ctx =
      CreateContextWithTestCertificate(TLS_method());
  ASSERT_TRUE(client_ctx);
  ASSERT_TRUE(server_ctx);

  struct ExtensionResults {
    bool found_signature_algorithms = false;
    bool found_supported_groups = false;
    size_t signature_algorithms_len = 0;
    size_t supported_groups_len = 0;
  } results;

  SSL_CTX_set_client_hello_cb(
      server_ctx.get(),
      [](SSL *ssl, int *al, void *arg) -> int {
        ExtensionResults *res = static_cast<ExtensionResults *>(arg);
        const unsigned char *ext_data = nullptr;
        size_t ext_len = 0;

        // Check signature_algorithms extension (13)
        if (SSL_client_hello_get0_ext(ssl, TLSEXT_TYPE_signature_algorithms,
                                      &ext_data, &ext_len)) {
          res->found_signature_algorithms = true;
          res->signature_algorithms_len = ext_len;
        }

        // Check supported_groups extension (10)
        if (SSL_client_hello_get0_ext(ssl, TLSEXT_TYPE_supported_groups,
                                      &ext_data, &ext_len)) {
          res->found_supported_groups = true;
          res->supported_groups_len = ext_len;
        }

        return SSL_CLIENT_HELLO_SUCCESS;
      },
      &results);

  UniquePtr<SSL> client, server;
  ASSERT_TRUE(ConnectClientAndServer(&client, &server, client_ctx.get(),
                                     server_ctx.get()));

  // These extensions should be present in modern TLS handshakes
  EXPECT_TRUE(results.found_signature_algorithms);
  EXPECT_TRUE(results.found_supported_groups);
  EXPECT_GT(results.signature_algorithms_len, 0u);
  EXPECT_GT(results.supported_groups_len, 0u);
}

}  // namespace

BSSL_NAMESPACE_END
