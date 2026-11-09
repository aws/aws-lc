// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/evp.h>
#include <openssl/obj.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/ssl.h>
#include <openssl/x509.h>

#include <string>
#include <thread>

#include "../tool/transport_common.h"
#include "internal.h"

// These tests connect to a live, remote host, so they are built into the
// integration_test executable rather than tool_openssl_test. See
// ssl/CMakeLists.txt.

// Test -connect
TEST(SClientIntegrationTest, Connect) {
  args_list_t args = {"-connect", "amazon.com:443"};
  int result = SClientTool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -connect, -verify, -showcerts
TEST(SClientIntegrationTest, ConnectVerifyShowcerts) {
  args_list_t args = {"-connect", "amazon.com:443", "-verify", "99", "-showcerts"};
  int result = SClientTool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -cipher
TEST(SClientIntegrationTest, Cipher) {
  // Pin to TLS 1.2 so the -cipher list is actually enforced. Without a version
  // pin the handshake can negotiate TLS 1.3, whose cipher suites are configured
  // separately, leaving -cipher effectively ignored.
  args_list_t args = {"-connect", "amazon.com:443", "-cipher",
                      "ECDHE-RSA-AES128-GCM-SHA256", "-tls1_2"};
  int result = SClientTool(args);
  ASSERT_EQ(kToolExitSuccess, result);
}

// The TLS 1.1 tests below do not use a remote host. Public endpoints no longer
// negotiate TLS 1.1 (amazon.com now replies with a protocol_version alert), so
// the tool's -tls1_1 path is exercised against an in-process loopback server
// configured to speak TLS 1.1 only. This keeps coverage of the flag without
// depending on any external server's willingness to negotiate a deprecated
// protocol.

namespace {

// MakeSelfSignedRSACert generates a 2048-bit RSA key and a matching self-signed
// certificate. An RSA key is required so the server can offer the RSA-authed
// cipher suites used by the TLS 1.1 tests (e.g. ECDHE-RSA-AES128-SHA).
static bool MakeSelfSignedRSACert(bssl::UniquePtr<EVP_PKEY> *out_pkey,
                                  bssl::UniquePtr<X509> *out_cert) {
  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> e(BN_new());
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  if (!rsa || !e || !pkey || !BN_set_word(e.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), 2048, e.get(), nullptr) ||
      !EVP_PKEY_assign_RSA(pkey.get(), rsa.release())) {
    return false;
  }

  bssl::UniquePtr<X509> x509(X509_new());
  uint64_t serial;
  if (!x509 || !X509_set_version(x509.get(), X509_VERSION_3) ||
      !RAND_bytes(reinterpret_cast<uint8_t *>(&serial), sizeof(serial)) ||
      !ASN1_INTEGER_set_uint64(X509_get_serialNumber(x509.get()), serial) ||
      !X509_gmtime_adj(X509_get_notBefore(x509.get()), 0) ||
      !X509_gmtime_adj(X509_get_notAfter(x509.get()), 60 * 60 * 24)) {
    return false;
  }

  X509_NAME *subject = X509_get_subject_name(x509.get());
  if (!X509_NAME_add_entry_by_txt(subject, "O", MBSTRING_ASC,
                                  reinterpret_cast<const uint8_t *>("AWS-LC"),
                                  -1, -1, 0) ||
      !X509_set_issuer_name(x509.get(), subject) ||
      !X509_set_pubkey(x509.get(), pkey.get()) ||
      !X509_sign(x509.get(), pkey.get(), EVP_sha256())) {
    return false;
  }

  *out_pkey = std::move(pkey);
  *out_cert = std::move(x509);
  return true;
}

// TLS11LoopbackServer binds a loopback socket, accepts a single connection, and
// completes a TLS 1.1 handshake on a background thread. The bound port is
// available via |port()| for the client to connect to.
class TLS11LoopbackServer {
 public:
  bool Start() {
    if (!InitSocketLibrary() || !listener_.Init("0")) {
      return false;
    }
    port_ = listener_.GetLocalPort();
    if (port_ <= 0) {
      return false;
    }

    ctx_.reset(SSL_CTX_new(TLS_method()));
    bssl::UniquePtr<EVP_PKEY> pkey;
    bssl::UniquePtr<X509> cert;
    if (!ctx_ || !MakeSelfSignedRSACert(&pkey, &cert) ||
        !SSL_CTX_use_PrivateKey(ctx_.get(), pkey.get()) ||
        !SSL_CTX_use_certificate(ctx_.get(), cert.get()) ||
        !SSL_CTX_set_min_proto_version(ctx_.get(), TLS1_1_VERSION) ||
        !SSL_CTX_set_max_proto_version(ctx_.get(), TLS1_1_VERSION) ||
        // Offer the RSA-authed CBC-SHA1 suites available at TLS 1.1. aws-lc does
        // not implement OpenSSL's @SECLEVEL cipher-string token or security-level
        // gating, so a plain cipher list suffices.
        !SSL_CTX_set_cipher_list(
            ctx_.get(),
            "ECDHE-RSA-AES128-SHA:ECDHE-RSA-AES256-SHA:AES128-SHA:AES256-SHA")) {
      return false;
    }

    thread_ = std::thread([this] { Run(); });
    return true;
  }

  int port() const { return port_; }

  // Join waits for the handshake thread and returns whether SSL_accept
  // succeeded.
  bool Join() {
    if (thread_.joinable()) {
      thread_.join();
    }
    return handshake_ok_;
  }

 private:
  void Run() {
    int sock = -1;
    if (!listener_.Accept(&sock)) {
      return;
    }
    BIO *bio = BIO_new_socket(sock, BIO_CLOSE);
    bssl::UniquePtr<SSL> ssl(SSL_new(ctx_.get()));
    if (bio == nullptr || !ssl) {
      if (bio != nullptr) {
        BIO_free(bio);
      }
      return;
    }
    SSL_set_bio(ssl.get(), bio, bio);
    if (SSL_accept(ssl.get()) == 1) {
      handshake_ok_ = true;
      // Send close_notify so the client's transfer loop observes a clean EOF
      // and the tool returns success.
      SSL_shutdown(ssl.get());
    }
  }

  Listener listener_;
  bssl::UniquePtr<SSL_CTX> ctx_;
  std::thread thread_;
  int port_ = -1;
  bool handshake_ok_ = false;
};

}  // namespace

// Test -tls1_1 against a loopback TLS 1.1 server.
TEST(SClientIntegrationTest, Tls1_1) {
  TLS11LoopbackServer server;
  ASSERT_TRUE(server.Start());

  std::string connect = "[::1]:" + std::to_string(server.port());
  args_list_t args = {"-connect", connect, "-tls1_1"};
  int result = SClientTool(args);

  EXPECT_TRUE(server.Join());
  ASSERT_EQ(kToolExitSuccess, result);
}

// Test -cipher and -tls1_1 together against a loopback TLS 1.1 server.
TEST(SClientIntegrationTest, CipherAndTls1_1) {
  TLS11LoopbackServer server;
  ASSERT_TRUE(server.Start());

  // TLS 1.1 has no AEAD/SHA-256 suites, so this stays on a CBC-SHA1 cipher, but
  // prefer the forward-secret ECDHE variant over static-RSA AES128-SHA.
  std::string connect = "[::1]:" + std::to_string(server.port());
  args_list_t args = {"-connect", connect, "-cipher", "ECDHE-RSA-AES128-SHA",
                      "-tls1_1"};
  int result = SClientTool(args);

  EXPECT_TRUE(server.Join());
  ASSERT_EQ(kToolExitSuccess, result);
}
