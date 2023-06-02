// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <ctime>

#include <openssl/ocsp.h>
#include <openssl/pem.h>
#include <openssl/ssl.h>

#include "../internal.h"
#include "../../tool/transport_common.h"
#include "../test/test_util.h"
#include "internal.h"

#define OCSP_VERIFYSTATUS_SUCCESS 1
#define OCSP_VERIFYSTATUS_ERROR 0
#define OCSP_VERIFYSTATUS_FATALERROR -1

std::string GetTestData(const char *path);

// Certificates always expire and that applies to the root certificates we're
// using in our trust store too.
static void isCertificateExpiring(X509 *cert) {
  // Get the current time and add 1 year to it.
  int64_t warning_time = time(nullptr) + 31536000;

  if (X509_cmp_time_posix(X509_get_notAfter(cert), warning_time) < 0) {
    fprintf(stdout, "\n\n\n\n");
    X509_NAME_print_ex_fp(stdout, X509_get_subject_name(cert), 0, 0);
    fprintf(stdout, " WILL EXPIRE IN A YEAR, PLEASE REPLACE ME WITH THE NEW"
            " EXPECTED ROOT CERTIFICATE FROM THE ENDPOINT.\n\n\n\n");
  }
}

static X509_STORE *SetupTrustStore() {
  X509_STORE *trust_store = X509_STORE_new();
  for (int i = 1; i <= 3; i++) {
    std::ostringstream oss;
    oss << "crypto/ocsp/test/integration-tests/AmazonRootCA" << i << ".pem";
    bssl::UniquePtr<X509> ca_cert(
        CertFromPEM(GetTestData(oss.str().c_str()).c_str()));
    EXPECT_TRUE(X509_STORE_add_cert(trust_store, ca_cert.get()));
    isCertificateExpiring(ca_cert.get());
  }
  return trust_store;
}

static OCSP_RESPONSE *GetOCSPResponse(const char *ocsp_responder_host,
                            X509 *certificate,
                            OCSP_REQUEST *request) {
  // Connect to OCSP Host. Connect to the defined OCSP responder if specified.
  // Otherwise, we connect to the OCSP responder specified in the cert.
  char *host = nullptr;
  bssl::UniquePtr<BIO> http_bio;
  if (ocsp_responder_host) {
    http_bio = bssl::UniquePtr<BIO>(BIO_new_connect(ocsp_responder_host));
  } else {
    bssl::UniquePtr<STACK_OF(OPENSSL_STRING)> responder(
        X509_get1_ocsp(certificate));
    char *path, *port;
    int is_ssl;
    EXPECT_TRUE(OCSP_parse_url(sk_OPENSSL_STRING_value(responder.get(), 0),
                               &host, &port, &path, &is_ssl));
    http_bio = bssl::UniquePtr<BIO>(BIO_new_connect(host));
    OPENSSL_free(path);
    OPENSSL_free(port);
  }
  EXPECT_TRUE(http_bio);
  BIO_set_conn_port(http_bio.get(), "80");
  BIO_set_retry_read(http_bio.get());
  EXPECT_TRUE(BIO_do_connect(http_bio.get()));

  // Set up an |OCSP_REQ_CTX| to be sent out.
  bssl::UniquePtr<OCSP_REQ_CTX> ocsp_ctx(
      OCSP_sendreq_new(http_bio.get(), "/", nullptr, -1));
  OCSP_REQ_CTX_add1_header(
      ocsp_ctx.get(), "Host",
      ocsp_responder_host ? ocsp_responder_host : host);
  OCSP_REQ_CTX_set1_req(ocsp_ctx.get(), request);

  // Try connecting to the OCSP responder endpoint with a timeout of 3 seconds.
  // Sends out an OCSP request and expects an OCSP response.
  OCSP_RESPONSE *resp = nullptr;
  time_t start_time = time(nullptr);
  double timeout = 3;
  int rv;
  do {
    rv = OCSP_sendreq_nbio(&resp, ocsp_ctx.get());
  } while ((rv == -1) && difftime(time(nullptr), start_time) < timeout);

  OPENSSL_free(host);
  return resp;
}

static void ValidateOCSPResponse(OCSP_RESPONSE *response,
                                 bool authorized_responder,
                                 X509 *certificate,
                                 X509 *issuer,
                                 X509_STORE *trust_store,
                                 OCSP_CERTID *cert_id,
                                 int expected_verify_status,
                                 int expected_cert_status) {
  ASSERT_EQ(OCSP_response_status(response),
            authorized_responder ? OCSP_RESPONSE_STATUS_SUCCESSFUL
                                 : OCSP_RESPONSE_STATUS_UNAUTHORIZED);
  bssl::UniquePtr<OCSP_BASICRESP> basic_response(
      OCSP_response_get1_basic(response));

  // The OCSP response should not have any additional data to parse if it's an
  // unauthorized responder.
  if (!authorized_responder) {
    ASSERT_FALSE(basic_response);
    return;
  }
  ASSERT_TRUE(basic_response);

  bssl::UniquePtr<STACK_OF(X509)> untrusted_chain(sk_X509_new_null());
  EXPECT_TRUE(sk_X509_push(untrusted_chain.get(), X509_dup(certificate)));
  EXPECT_TRUE(sk_X509_push(untrusted_chain.get(), X509_dup(issuer)));

  // Verifies the OCSP responder's signature on the OCSP response data.
  EXPECT_EQ(OCSP_basic_verify(basic_response.get(), untrusted_chain.get(),
                              trust_store, 0),
            expected_verify_status);

  // Checks revocation status of the response.
  int status;
  ASN1_GENERALIZEDTIME *thisupdate, *nextupdate;
  EXPECT_TRUE(OCSP_resp_find_status(basic_response.get(), cert_id, &status,
                                    nullptr, nullptr, &thisupdate,
                                    &nextupdate));
  EXPECT_EQ(status, expected_cert_status);

  // We just got an OCSP response, so this should never be out of date.
  EXPECT_TRUE(OCSP_check_validity(thisupdate, nextupdate, 0, -1));
}

struct IntegrationTestVector {
  const char *url_host;
  // Connect to the OCSP responder specified in the cert if NULL.
  const char *ocsp_responder_host;
  // This is true if we successfully connect to the OCSP responder.
  bool expected_conn_status;
  // This is true if the OCSP responder is authorized to validate the cert.
  bool authorized_responder;
  int expected_verify_status;
  int expected_cert_status;
};

// We connect to "ocsp.sca[0-4]a.amazontrust.com" OCSP responder endpoints.
// The following URLs in the test suite were taken from Amazon Trust
// Services: https://www.amazontrust.com/repository/.
// To avoid having timebomb failures when hard-coded certs expire, we do an
// SSL connection with a specified URL and retrieve the certificate chain the
// server uses. "valid.*.amazontrust.com" endpoints rotate their cert
// periodically, so we can trust that doing OCSP verification with their
// certificate chain will not result in any timebomb failures further down the
// line. We also connect against the OCSP responder URI specified in the
// cert, so that our tests aren't sensitive to changes in the endpoint's OCSP
// responder URI.
static const IntegrationTestVector kIntegrationTestVectors[] = {
    {"valid.rootca1.demo.amazontrust.com", nullptr, true, true,
     OCSP_VERIFYSTATUS_SUCCESS, V_OCSP_CERTSTATUS_GOOD},
    {"valid.rootca2.demo.amazontrust.com", nullptr, true, true,
     OCSP_VERIFYSTATUS_SUCCESS, V_OCSP_CERTSTATUS_GOOD},
    {"valid.rootca3.demo.amazontrust.com", nullptr, true, true,
     OCSP_VERIFYSTATUS_SUCCESS, V_OCSP_CERTSTATUS_GOOD},
    // A revoked cert will succeed OCSP cert verification, but the OCSP
    // responder will indicate it has been revoked.
    {"revoked.rootca1.demo.amazontrust.com", nullptr, true, true,
     OCSP_VERIFYSTATUS_SUCCESS, V_OCSP_CERTSTATUS_REVOKED},
    {"revoked.rootca2.demo.amazontrust.com", nullptr, true, true,
     OCSP_VERIFYSTATUS_SUCCESS, V_OCSP_CERTSTATUS_REVOKED},
    {"revoked.rootca3.demo.amazontrust.com", nullptr, true, true,
     OCSP_VERIFYSTATUS_SUCCESS, V_OCSP_CERTSTATUS_REVOKED},
    // Connect to an unauthorized OCSP responder endpoint. This will
    // successfully get an OCSP response, but will only have the field
    // |OCSP_RESPONSE_STATUS_UNAUTHORIZED|.
    {"valid.rootca1.demo.amazontrust.com", "ocsp.comodoca.com", true, false, 0,
     0},
    // Connect to a non-OCSP responder endpoint. These should fail to get an
    // OCSP response, unless these hosts decide to become OCSP responders.
    {"valid.rootca1.demo.amazontrust.com", "amazon.com", false, false, 0, 0},
    {"valid.rootca2.demo.amazontrust.com", "www.example.com", false, false, 0,
     0},
};

class OCSPIntegrationTest
    : public testing::TestWithParam<IntegrationTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, OCSPIntegrationTest,
                         testing::ValuesIn(kIntegrationTestVectors));

TEST_P(OCSPIntegrationTest, AmazonTrustServices) {
  const IntegrationTestVector &t = GetParam();

  // Connect to the specified endpoint. We do this to retrieve the
  // certificate chain the endpoint uses.
  int sock = -1;
  ASSERT_TRUE(InitSocketLibrary());
  ASSERT_TRUE(Connect(&sock, t.url_host));
  ASSERT_TRUE(SSL_library_init());
  bssl::UniquePtr<SSL_CTX> ssl_ctx(SSL_CTX_new(TLS_method()));
  ASSERT_TRUE(ssl_ctx);

  // Set up trust store.
  bssl::UniquePtr<X509_STORE> trust_store(SetupTrustStore());
  ASSERT_TRUE(SSL_CTX_set1_verify_cert_store(ssl_ctx.get(), trust_store.get()));
  bssl::UniquePtr<BIO> bio(BIO_new_socket(sock, BIO_CLOSE));
  bssl::UniquePtr<SSL> ssl(SSL_new(ssl_ctx.get()));

  // Let the endpoint know what we're trying to connect to since multiple
  // websites can be served on one server.
  SSL_set_tlsext_host_name(ssl.get(), t.url_host);
  SSL_set_bio(ssl.get(), bio.get(), bio.get());
  ASSERT_TRUE(SSL_connect(ssl.get()));

  STACK_OF(X509) *chain = SSL_get_peer_full_cert_chain(ssl.get());
  EXPECT_EQ(SSL_get_verify_result(ssl.get()), X509_V_OK);
  // Leaf to be verified should be the first one in the chain.
  X509 *certificate = sk_X509_value(chain, 0);
  ASSERT_TRUE(certificate);
  // find the issuer in the chain.
  X509 *issuer = nullptr;
  for (size_t i = 0; i < sk_X509_num(chain); ++i) {
    X509 *issuer_candidate = sk_X509_value(chain, i);
    const int issuer_value = X509_check_issued(issuer_candidate, certificate);
    if (issuer_value == X509_V_OK) {
      issuer = issuer_candidate;
      break;
    }
  }
  ASSERT_TRUE(issuer);

  bssl::UniquePtr<OCSP_REQUEST> request(OCSP_REQUEST_new());
  bssl::UniquePtr<OCSP_CERTID> cert_id(
      OCSP_cert_to_id(EVP_sha1(), certificate, issuer));
  ASSERT_TRUE(OCSP_request_add0_id(request.get(), cert_id.get()));

  bssl::UniquePtr<OCSP_RESPONSE> resp(
      GetOCSPResponse(t.ocsp_responder_host, certificate, request.get()));

  if (t.expected_conn_status) {
    EXPECT_TRUE(resp);
    ValidateOCSPResponse(resp.get(), t.authorized_responder, certificate,
                         issuer, trust_store.get(), cert_id.get(),
                         t.expected_verify_status, t.expected_cert_status);
  } else {
    EXPECT_FALSE(resp);
  }

  bio.release();
  cert_id.release();
}
