// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
#include <gtest/gtest.h>
#include <ctime>

#include "openssl/ocsp.h"
#include "openssl/pem.h"

#include "../internal.h"
#include "../test/test_util.h"
#include "internal.h"

#define OCSP_RESPONDER_CONN_SUCCESS 1
#define OCSP_RESPONDER_CONN_ERROR 0

std::string GetTestData(const char *path);

struct IntegrationTestVector {
  const char *issuer;
  const char *cert;
  const char *host;
  int expected_status;
};

// We connect to "ocsp.sca[0-4]a.amazontrust.com" OCSP responder endpoints.
// The following certs used in the test suite were taken from Amazon Trust
// Services: https://www.amazontrust.com/repository/.
// We can renew these certs periodically if needed, but we should never let
// tests rely on real-time OCSP response verification to pass. This could
// create time bomb tests once the root or intermediate certs go out of
// expiration.
static const IntegrationTestVector kIntegrationTestVectors[] = {
    // AmazonInter1 is the intermediate cert for AmazonRootCA1.
    // AmazonRootCA1's expiration date is Jan 17, 2038 GMT.
    // AmazonInter1's expiration date is Oct 19, 2025 GMT.
    // good.sca1a.amazontrust.com's expiration date is Sep 23, 2023 GMT.
    {"AmazonRootCA1", "AmazonInter1", "ocsp.sca0a.amazontrust.com",
     OCSP_RESPONDER_CONN_SUCCESS},
    {"AmazonInter1", "good.sca1a.amazontrust.com", "ocsp.sca1a.amazontrust.com",
     OCSP_RESPONDER_CONN_SUCCESS},
    {"AmazonInter1", "revoked.sca1a.amazontrust.com",
     "ocsp.sca2a.amazontrust.com", OCSP_RESPONDER_CONN_SUCCESS},
    {"AmazonInter1", "expired.sca1a.amazontrust.com",
     "ocsp.sca3a.amazontrust.com", OCSP_RESPONDER_CONN_SUCCESS},
    // AmazonInter2 is the intermediate cert for AmazonRootCA2.
    // AmazonRootCA2's expiration date is May 26, 2040 GMT.
    // AmazonInter2's expiration date is Oct 19, 2025 GMT.
    // good.sca2a.amazontrust.com's expiration date is Sep 23, 2023 GMT.
    {"AmazonRootCA2", "AmazonInter2", "ocsp.sca4a.amazontrust.com",
     OCSP_RESPONDER_CONN_SUCCESS},
    {"AmazonInter2", "good.sca2a.amazontrust.com", "ocsp.sca0a.amazontrust.com",
     OCSP_RESPONDER_CONN_SUCCESS},
    {"AmazonInter2", "revoked.sca2a.amazontrust.com",
     "ocsp.sca1a.amazontrust.com", OCSP_RESPONDER_CONN_SUCCESS},
    {"AmazonInter2", "expired.sca2a.amazontrust.com",
     "ocsp.sca2a.amazontrust.com", OCSP_RESPONDER_CONN_SUCCESS},
    // Try connecting to the OCSP responder with an invalid OCSP request.
    // These should fail.
    {"AmazonInter1", nullptr, "ocsp.sca3a.amazontrust.com",
     OCSP_RESPONDER_CONN_ERROR},
    {"AmazonInter2", nullptr, "ocsp.sca4a.amazontrust.com",
     OCSP_RESPONDER_CONN_ERROR},
    // Connect to an unauthorized OCSP responder endpoint. This will
    // successfully get an OCSP response, but will only have the field
    // |OCSP_RESPONSE_STATUS_UNAUTHORIZED|.
    {"AmazonRootCA1", "AmazonInter1", "ocsp.sca1b.amazontrust.com",
     OCSP_RESPONDER_CONN_SUCCESS},
    // Connect to a non-OCSP responder endpoint. These should fail to get an
    // OCSP response, unless these hosts decide to become OCSP responders.
    {"AmazonInter1", "good.sca1a.amazontrust.com", "www.amazon.com",
     OCSP_RESPONDER_CONN_ERROR},
    {"AmazonInter1", "good.sca1a.amazontrust.com", "www.example.com",
     OCSP_RESPONDER_CONN_ERROR},
};

class OCSPIntegrationTest
    : public testing::TestWithParam<IntegrationTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, OCSPIntegrationTest,
                         testing::ValuesIn(kIntegrationTestVectors));

// To avoid having timebomb failures in the next few years when the certs
// in these tests expire, we don't verify the OCSP response we get from the
// OCSP responder against the root and intermediate certs. We test for cert
// validation correctness against hard-coded OCSP responses in the |OCSPTest|
// Test suites instead.
// This test suite focuses on connecting to an actual OCSP responder. If an
// OCSP request is valid, the OCSP responder should always send back an OCSP
// response. It's up to the OCSP requester to verify the contents of the OCSP
// response's validity and expiration time.
TEST_P(OCSPIntegrationTest, AmazonTrustServices) {
  const IntegrationTestVector &t = GetParam();

  // Get Issuer and Cert to be validated from path and set up the OCSP request.
  bssl::UniquePtr<X509> issuer(CertFromPEM(
      GetTestData(std::string("crypto/ocsp/test/integration-tests/" +
                              std::string(t.issuer) + ".cer")
                      .c_str())
          .c_str()));
  ASSERT_TRUE(issuer);
  bssl::UniquePtr<X509> certificate;
  if (t.cert) {
    certificate = bssl::UniquePtr<X509>(CertFromPEM(
        GetTestData(std::string("crypto/ocsp/test/integration-tests/" +
                                std::string(t.cert) + ".cer")
                        .c_str())
            .c_str()));
    ASSERT_TRUE(certificate);
  }
  bssl::UniquePtr<OCSP_REQUEST> request(OCSP_REQUEST_new());
  OCSP_CERTID *id =
      OCSP_cert_to_id(EVP_sha1(), certificate.get(), issuer.get());
  ASSERT_TRUE(OCSP_request_add0_id(request.get(), id));

  // Connect to Host.
  bssl::UniquePtr<BIO> bio(BIO_new_connect(t.host));
  ASSERT_TRUE(bio);
  BIO_set_conn_port(bio.get(), "80");
  BIO_set_retry_read(bio.get());
  ASSERT_TRUE(BIO_do_connect(bio.get()));

  // Set up a |OCSP_REQ_CTX| to be sent out.
  bssl::UniquePtr<OCSP_REQ_CTX> ctx(
      OCSP_sendreq_new(bio.get(), "/", nullptr, -1));
  OCSP_REQ_CTX_add1_header(ctx.get(), "Host", t.host);
  OCSP_REQ_CTX_set1_req(ctx.get(), request.get());

  // Try connecting to the OCSP responder endpoint with a timeout of 3 seconds.
  // Sends out an OCSP request and expects an OCSP response.
  OCSP_RESPONSE *resp = nullptr;
  time_t start_time = time(nullptr);
  double timeout = 3;
  int rv = 0;
  do {
    rv = OCSP_sendreq_nbio(&resp, ctx.get());
  } while ((rv == -1) && difftime(time(nullptr), start_time) < timeout);

  // Check if an OCSP response has been successfully retrieved.
  if (t.expected_status == OCSP_RESPONDER_CONN_SUCCESS) {
    EXPECT_TRUE(resp);
    OCSP_RESPONSE_free(resp);
  } else {
    EXPECT_FALSE(resp);
  }
}
