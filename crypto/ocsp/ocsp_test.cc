// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
#include <gtest/gtest.h>
#include <ctime>

#include "openssl/ocsp.h"
#include "openssl/pem.h"

#include "../internal.h"
#include "../test/test_util.h"
#include "internal.h"

static const time_t invalid_before_ocsp_update_time = 1621988613;
static const time_t valid_after_ocsp_update_time = 1621988615;
static const time_t valid_before_ocsp_expire_time = 1937348613;
static const time_t invalid_after_ocsp_expire_time = 1937348615;

static const time_t invalid_before_ocsp_update_time_sha256 = 1622145762;
static const time_t valid_after_ocsp_update_time_sha256 = 1622145764;
static const time_t valid_before_ocsp_expire_time_sha256 = 1937505762;
static const time_t invalid_after_ocsp_expire_time_sha256 = 1937505764;

#define OCSP_VERIFYSTATUS_SUCCESS 1
#define OCSP_VERIFYSTATUS_ERROR 0
#define OCSP_VERIFYSTATUS_FATALERROR -1

#define OCSP_RESPFINDSTATUS_SUCCESS 1
#define OCSP_RESPFINDSTATUS_ERROR 0

#define OCSP_REQUEST_PARSE_SUCCESS 1
#define OCSP_REQUEST_PARSE_ERROR 0

#define OCSP_HTTP_PARSE_SUCCESS 1
#define OCSP_HTTP_PARSE_ERROR 0

#define OCSP_REQUEST_SIGN_SUCCESS 1
#define OCSP_REQUEST_SIGN_ERROR 0

#define OCSP_URL_PARSE_SUCCESS 1
#define OCSP_URL_PARSE_ERROR 0

std::string GetTestData(const char *path);

static bool DecodeBase64(std::vector<uint8_t> *out, const char *in) {
  int temp_length = 0;
  size_t total_length = 0;
  EVP_ENCODE_CTX ctx;
  EVP_DecodeInit(&ctx);
  out->resize(strlen(in));

  int decode_update_result = EVP_DecodeUpdate(&ctx, out->data(), &temp_length,
                                              (const uint8_t *)in, strlen(in));
  if (decode_update_result != 1 && decode_update_result != 0) {
    fprintf(stderr, "EVP_DecodeUpdate failed\n");
    return false;
  }
  total_length += temp_length;
  temp_length = 0;

  if (1 != EVP_DecodeFinal(&ctx, &out->data()[total_length], &temp_length)) {
    fprintf(stderr, "EVP_DecodeFinal failed\n");
    return false;
  }
  total_length += temp_length;
  out->resize(total_length);
  return true;
}

// CertFromPEM parses the given, NUL-terminated pem block and returns an
// |X509*|.
static bssl::UniquePtr<X509> CertFromPEM(const char *pem) {
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem, strlen(pem)));
  return bssl::UniquePtr<X509>(
      PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
}

static bssl::UniquePtr<RSA> RSAFromPEM(const char *pem) {
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem, strlen(pem)));
  return bssl::UniquePtr<RSA>(
      PEM_read_bio_RSAPrivateKey(bio.get(), nullptr, nullptr, nullptr));
}

static bssl::UniquePtr<EC_KEY> ECDSAFromPEM(const char *pem) {
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem, strlen(pem)));
  return bssl::UniquePtr<EC_KEY>(
      PEM_read_bio_ECPrivateKey(bio.get(), nullptr, nullptr, nullptr));
}

static bssl::UniquePtr<STACK_OF(X509)> CertChainFromPEM(const char *pem) {
  bssl::UniquePtr<STACK_OF(X509)> stack(sk_X509_new_null());
  if (!stack) {
    return nullptr;
  }

  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem, strlen(pem)));
  for (;;) {
    bssl::UniquePtr<X509> cert = bssl::UniquePtr<X509>(
        PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
    if (cert == nullptr) {
      break;
    }
    if (!bssl::PushToStack(stack.get(), bssl::UpRef(cert.get()))) {
      return nullptr;
    }
  }
  return stack;
}

static bssl::UniquePtr<STACK_OF(X509)> CertsToStack(
    const std::vector<X509 *> &certs) {
  bssl::UniquePtr<STACK_OF(X509)> stack(sk_X509_new_null());
  if (!stack) {
    return nullptr;
  }
  for (auto cert : certs) {
    if (!bssl::PushToStack(stack.get(), bssl::UpRef(cert))) {
      return nullptr;
    }
  }
  return stack;
}

static bssl::UniquePtr<OCSP_RESPONSE> LoadOCSP_RESPONSE(
    bssl::Span<const uint8_t> der) {
  const uint8_t *ptr = der.data();
  return bssl::UniquePtr<OCSP_RESPONSE>(
      d2i_OCSP_RESPONSE(nullptr, &ptr, der.size()));
}

static bssl::UniquePtr<OCSP_REQUEST> LoadOCSP_REQUEST(
    bssl::Span<const uint8_t> der) {
  const uint8_t *ptr = der.data();
  return bssl::UniquePtr<OCSP_REQUEST>(
      d2i_OCSP_REQUEST(nullptr, &ptr, der.size()));
}

static void ExtractAndVerifyBasicOCSP(
    bssl::Span<const uint8_t> der, int expected_ocsp_status,
    const std::string expected_ocsp_status_string,
    const std::string ca_cert_file, const std::string server_cert_file,
    int expected_ocsp_verify_status,
    bssl::UniquePtr<OCSP_BASICRESP> *basic_response,
    bssl::UniquePtr<STACK_OF(X509)> *server_cert_chain) {
  bssl::UniquePtr<OCSP_RESPONSE> ocsp_response;

  ocsp_response = LoadOCSP_RESPONSE(der);
  ASSERT_TRUE(ocsp_response);

  int ret = OCSP_response_status(ocsp_response.get());
  ASSERT_EQ(expected_ocsp_status, ret);
  ASSERT_EQ(expected_ocsp_status_string, OCSP_response_status_str(ret));
  if (ret != OCSP_RESPONSE_STATUS_SUCCESSFUL) {
    return;
  }

  *basic_response = bssl::UniquePtr<OCSP_BASICRESP>(
      OCSP_response_get1_basic(ocsp_response.get()));
  ASSERT_TRUE(*basic_response);

  // Set up trust store and certificate chain.
  bssl::UniquePtr<X509> ca_cert(CertFromPEM(
      GetTestData(
          std::string("crypto/ocsp/test/aws/" + ca_cert_file + ".pem").c_str())
          .c_str()));
  bssl::UniquePtr<X509> server_cert(
      CertFromPEM(GetTestData(std::string("crypto/ocsp/test/aws/" +
                                          server_cert_file + ".pem")
                                  .c_str())
                      .c_str()));

  bssl::UniquePtr<X509_STORE> trust_store(X509_STORE_new());
  X509_STORE_add_cert(trust_store.get(), ca_cert.get());
  *server_cert_chain = CertsToStack({server_cert.get(), ca_cert.get()});
  ASSERT_TRUE(*server_cert_chain);

  // Verifies the OCSP responder's signature on the OCSP response data.
  const int ocsp_verify_err = OCSP_basic_verify(
      basic_response->get(), server_cert_chain->get(), trust_store.get(), 0);
  ASSERT_EQ(expected_ocsp_verify_status, ocsp_verify_err);
}

static void CheckOCSP_CERTSTATUS(
    bssl::UniquePtr<OCSP_BASICRESP> *basic_response,
    bssl::UniquePtr<STACK_OF(X509)> *server_cert_chain, const EVP_MD *dgst,
    int expected_resp_find_status, int *status, ASN1_GENERALIZEDTIME **thisupd,
    ASN1_GENERALIZEDTIME **nextupd) {
  X509 *subject = sk_X509_value(server_cert_chain->get(), 0);
  X509 *issuer = sk_X509_value(server_cert_chain->get(), 1);
  // Convert issuer certificate to |OCSP_CERTID|.
  bssl::UniquePtr<OCSP_CERTID> cert_id =
      bssl::UniquePtr<OCSP_CERTID>(OCSP_cert_to_id(dgst, subject, issuer));
  ASSERT_TRUE(cert_id);

  int reason = 0;
  ASN1_GENERALIZEDTIME *revtime;
  // Checks revocation status of the response.
  const int ocsp_resp_find_status_res =
      OCSP_resp_find_status(basic_response->get(), cert_id.get(), status,
                            &reason, &revtime, thisupd, nextupd);
  ASSERT_EQ(expected_resp_find_status, ocsp_resp_find_status_res);
}

// Test data below are taken from s2n's ocsp test files:
// https://github.com/aws/s2n-tls/blob/main/tests/pems/ocsp
// OCSP testing methods were taken from s2n's validation tests:
// https://github.com/aws/s2n-tls/blob/main/tests/unit/s2n_x509_validator_test.c
struct OCSPTestVectorExtended {
  const char *ocsp_response;
  const char *cafile;
  const char *server_cert;
  const EVP_MD *dgst;
  int expected_ocsp_status;
  const char *expected_ocsp_status_string;
  int expected_ocsp_verify_status;
  int expected_ocsp_resp_find_status;
  int expected_ocsp_cert_status;
  const char *expected_ocsp_cert_status_string;
};

static const OCSPTestVectorExtended nTestVectors[] = {
    // === SHA1 OCSP RESPONSES ===
    // Test valid OCSP response signed by an OCSP responder.
    {"ocsp_response", "ca_cert", "server_cert", EVP_sha1(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_SUCCESS, V_OCSP_CERTSTATUS_GOOD, "good"},
    // Test against same good OCSP response, but checking behavior of not
    // specifying hash algorithm used for |OCSP_cert_to_id| this time (should
    // default to sha1). When |*dgst| is set to NULL, the default hash algorithm
    // should automatically be set to sha1. The revocation status check of the
    // response should work if hash algorithm of |cert_id| has been set to sha1
    // successfully.
    {"ocsp_response", "ca_cert", "server_cert", nullptr,
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_SUCCESS, V_OCSP_CERTSTATUS_GOOD, "good"},
    // Test valid OCSP response directly signed by the CA certificate.
    {"ocsp_response_ca_signed", "ca_cert", "server_cert", EVP_sha1(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_SUCCESS, V_OCSP_CERTSTATUS_GOOD, "good"},
    // Test OCSP response status is revoked.
    {"ocsp_response_revoked", "ca_cert", "server_cert", EVP_sha1(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_SUCCESS, V_OCSP_CERTSTATUS_REVOKED, "revoked"},
    // Test OCSP response status is unknown.
    {"ocsp_response_unknown", "ca_cert", "server_cert", EVP_sha1(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_SUCCESS, V_OCSP_CERTSTATUS_UNKNOWN, "unknown"},
    // Test OCSP response signed by the correct responder certificate, but not
    // for
    // the requested certificate. (So this would be a completely valid response
    // to a
    // different OCSP request for the other certificate.)
    {"ocsp_response", "ca_cert", "server_ecdsa_cert", EVP_sha1(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_ERROR, 0, nullptr},
    // Test OCSP response where the requested certificate was signed by the OCSP
    // responder, but signed by the wrong requested OCSP responder key
    // certificate.
    // However, this incorrect OCSP responder certificate may be a valid OCSP
    // responder for some other case and also chains to a trusted root.
    {"ocsp_response_wrong_signer", "ca_cert", "server_cert", EVP_sha1(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_ERROR, 0,
     0, nullptr},

    // === SHA256 OCSP RESPONSES ===
    // Test valid OCSP response signed by an OCSP responder.
    {"ocsp_response_sha256", "ca_cert", "server_cert", EVP_sha256(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_SUCCESS, V_OCSP_CERTSTATUS_GOOD, "good"},
    // Test a SHA-256 revoked OCSP response status.
    {"ocsp_response_revoked_sha256", "ca_cert", "server_cert", EVP_sha256(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_SUCCESS, V_OCSP_CERTSTATUS_REVOKED, "revoked"},
    // Test a SHA-256 unknown OCSP response status.
    {"ocsp_response_unknown_sha256", "ca_cert", "server_cert", EVP_sha256(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_SUCCESS, V_OCSP_CERTSTATUS_UNKNOWN, "unknown"},
    // Test a SHA-256 OCSP response signed by the correct responder certificate,
    // but not for the requested certificate. (So this would be a completely
    // valid response to a different OCSP request for the other certificate.)
    {"ocsp_response_sha256", "ca_cert", "server_ecdsa_cert", EVP_sha256(),
     OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful", OCSP_VERIFYSTATUS_SUCCESS,
     OCSP_RESPFINDSTATUS_ERROR, 0, nullptr},
    // Test a SHA-256 OCSP response signed by the wrong responder certificate,
    // but the requested certificate was signed. (however this incorrect OCSP
    // responder certificate is a valid OCSP responder for some other case and
    // chains to a trusted root). Thus, this response is not valid for any
    // request.
    {"ocsp_response_wrong_signer_sha256", "ca_cert", "server_cert",
     EVP_sha256(), OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful",
     OCSP_VERIFYSTATUS_ERROR, 0, 0, nullptr},

    // === Invalid OCSP response requests sent back an OCSP responder ===
    // https://datatracker.ietf.org/doc/html/rfc6960#section-4.2.1
    // OCSPResponseStatus: malformedRequest
    {"ocsp_response_malformedrequest", "", "", nullptr,
     OCSP_RESPONSE_STATUS_MALFORMEDREQUEST, "malformedrequest", 0, 0, 0,
     nullptr},
    // OCSPResponseStatus: internalError
    {"ocsp_response_internalerror", "", "", nullptr,
     OCSP_RESPONSE_STATUS_INTERNALERROR, "internalerror", 0, 0, 0, nullptr},
    // OCSPResponseStatus: tryLater
    {"ocsp_response_trylater", "", "", nullptr, OCSP_RESPONSE_STATUS_TRYLATER,
     "trylater", 0, 0, 0, nullptr},
    // OCSPResponseStatus: sigRequired
    {"ocsp_response_sigrequired", "", "", nullptr,
     OCSP_RESPONSE_STATUS_SIGREQUIRED, "sigrequired", 0, 0, 0, nullptr},
    // OCSPResponseStatus: unauthorized
    {"ocsp_response_unauthorized", "", "", nullptr,
     OCSP_RESPONSE_STATUS_UNAUTHORIZED, "unauthorized", 0, 0, 0, nullptr},
};

class OCSPTestExtended : public testing::TestWithParam<OCSPTestVectorExtended> {
};

INSTANTIATE_TEST_SUITE_P(All, OCSPTestExtended,
                         testing::ValuesIn(nTestVectors));

TEST_P(OCSPTestExtended, VerifyOCSPResponseExtended) {
  const OCSPTestVectorExtended &t = GetParam();

  std::string data =
      GetTestData(std::string("crypto/ocsp/test/aws/" +
                              std::string(t.ocsp_response) + ".der")
                      .c_str());
  std::vector<uint8_t> ocsp_reponse_data(data.begin(), data.end());

  // OCSP response parsing and verification step.
  bssl::UniquePtr<OCSP_BASICRESP> basic_response;
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  ExtractAndVerifyBasicOCSP(ocsp_reponse_data, t.expected_ocsp_status,
                            t.expected_ocsp_status_string, t.cafile,
                            t.server_cert, t.expected_ocsp_verify_status,
                            &basic_response, &server_cert_chain);

  // If OCSP basic verify is successful, we check the OCSP response status.
  if (t.expected_ocsp_verify_status == OCSP_VERIFYSTATUS_SUCCESS) {
    int status = 0;
    ASN1_GENERALIZEDTIME *thisupd, *nextupd;
    CheckOCSP_CERTSTATUS(&basic_response, &server_cert_chain, t.dgst,
                         t.expected_ocsp_resp_find_status, &status, &thisupd,
                         &nextupd);
    // If OCSP response status retrieving is successful, we check if the cert
    // status of the OCSP response is correct.
    if (t.expected_ocsp_resp_find_status == OCSP_RESPFINDSTATUS_SUCCESS) {
      ASSERT_EQ(t.expected_ocsp_cert_status, status);
      ASSERT_EQ(std::string(t.expected_ocsp_cert_status_string),
                std::string(OCSP_cert_status_str(status)));
    }
  }
}

// === Specific test cases ===

// Test valid OCSP response signed by an OCSP responder along with check for
// correct time field parsing.
TEST(OCSPTest, TestGoodOCSP) {
  std::string data = GetTestData(
      std::string("crypto/ocsp/test/aws/ocsp_response.der").c_str());
  std::vector<uint8_t> ocsp_reponse_data(data.begin(), data.end());

  bssl::UniquePtr<OCSP_BASICRESP> basic_response;
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  ExtractAndVerifyBasicOCSP(ocsp_reponse_data, OCSP_RESPONSE_STATUS_SUCCESSFUL,
                            "successful", "ca_cert", "server_cert",
                            OCSP_VERIFYSTATUS_SUCCESS, &basic_response,
                            &server_cert_chain);

  int status = 0;
  ASN1_GENERALIZEDTIME *thisupd, *nextupd;
  CheckOCSP_CERTSTATUS(&basic_response, &server_cert_chain, EVP_sha1(),
                       OCSP_RESPFINDSTATUS_SUCCESS, &status, &thisupd,
                       &nextupd);
  ASSERT_EQ(V_OCSP_CERTSTATUS_GOOD, status);

  // If OCSP response is verifiable and all good, an OCSP client should check
  // time fields to see if the response is still valid.

  // Check before OCSP was last updated connection timestamp
  time_t connection_time = invalid_before_ocsp_update_time;
  ASSERT_EQ(1, X509_cmp_time(thisupd, &connection_time));
  ASSERT_EQ(1, X509_cmp_time(nextupd, &connection_time));

  // Check valid connection timestamp right after OCSP response was validated.
  connection_time = valid_after_ocsp_update_time;
  ASSERT_EQ(-1, X509_cmp_time(thisupd, &connection_time));
  ASSERT_EQ(1, X509_cmp_time(nextupd, &connection_time));

  // Check valid connection timestamp right before OCSP response expires.
  connection_time = valid_before_ocsp_expire_time;
  ASSERT_EQ(-1, X509_cmp_time(thisupd, &connection_time));
  ASSERT_EQ(1, X509_cmp_time(nextupd, &connection_time));

  // Check expired connection timestamp
  connection_time = invalid_after_ocsp_expire_time;
  ASSERT_EQ(-1, X509_cmp_time(thisupd, &connection_time));
  ASSERT_EQ(-1, X509_cmp_time(nextupd, &connection_time));

  // Check that |OCSP_check_validity| sees that |thisupd| is more than 100
  // seconds in the past, and disallows it.
  EXPECT_FALSE(OCSP_check_validity(thisupd, nextupd, 0, 100));
  uint32_t err = ERR_get_error();
  EXPECT_EQ(OCSP_R_STATUS_TOO_OLD, ERR_GET_REASON(err));

  // We offset "nsec" in |OCSP_check_validity| with a negative timestamp
  // equal to the current time. We offset this larger timestamp on purpose to
  // check if |OCSP_check_validity| can properly reject improper timestamps.
  // This will cause the function to fail in two places, once when checking
  // if "(current_time + nsec) > thisupd [Status Not Yet Valid]", and a second
  // time when checking if "nextupd > (current_time - nsec) [Status Expired]".
  EXPECT_FALSE(OCSP_check_validity(thisupd, nextupd, -time(nullptr), -1));
  err = ERR_get_error();
  EXPECT_EQ(OCSP_R_STATUS_NOT_YET_VALID, ERR_GET_REASON(err));
  err = ERR_get_error();
  EXPECT_EQ(OCSP_R_STATUS_EXPIRED, ERR_GET_REASON(err));

  // Check that "NEXTUPDATE_BEFORE_THISUPDATE" is properly detected. We have to
  // use |valid_after_ocsp_update_time| instead of |nextupd| to avoid a
  // ticking time-bomb test. |nextupd| will throw an additional
  // "STATUS_NOT_YET_VALID" error until it is a valid timestamp.
  bssl::UniquePtr<ASN1_GENERALIZEDTIME> after_thisupd(
      ASN1_GENERALIZEDTIME_new());
  ASN1_GENERALIZEDTIME_set(after_thisupd.get(), valid_after_ocsp_update_time);
  EXPECT_FALSE(OCSP_check_validity(after_thisupd.get(), thisupd, 0, -1));
  err = ERR_get_error();
  EXPECT_EQ(OCSP_R_STATUS_EXPIRED, ERR_GET_REASON(err));
  err = ERR_get_error();
  EXPECT_EQ(OCSP_R_NEXTUPDATE_BEFORE_THISUPDATE, ERR_GET_REASON(err));

  // We set |nextupd| to NULL on purpose to avoid another ticking time-bomb
  // expiration in our tests. We only check if |thisupd| is a valid timestamp
  // in the past.
  EXPECT_TRUE(OCSP_check_validity(thisupd, nullptr, 0, -1));
}

// Test valid OCSP response, but the data itself is untrusted.
TEST(OCSPTest, TestUntrustedDataOCSP) {
  std::string data = GetTestData(
      std::string("crypto/ocsp/test/aws/ocsp_response.der").c_str());
  std::vector<uint8_t> ocsp_reponse_data(data.begin(), data.end());

  // Mess up a byte right in the middle of the cert.
  ocsp_reponse_data[800] = ocsp_reponse_data[800] + 1;

  bssl::UniquePtr<OCSP_BASICRESP> basic_response;
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  ExtractAndVerifyBasicOCSP(ocsp_reponse_data, OCSP_RESPONSE_STATUS_SUCCESSFUL,
                            "successful", "ca_cert", "server_cert",
                            OCSP_VERIFYSTATUS_ERROR, &basic_response,
                            &server_cert_chain);
}


// Test valid OCSP response hashed with sha256 along with check for correct time
// field parsing.
TEST(OCSPTest, TestGoodOCSP_SHA256) {
  std::string data = GetTestData(
      std::string("crypto/ocsp/test/aws/ocsp_response_sha256.der").c_str());
  std::vector<uint8_t> ocsp_reponse_data(data.begin(), data.end());

  bssl::UniquePtr<OCSP_BASICRESP> basic_response;
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  ExtractAndVerifyBasicOCSP(ocsp_reponse_data, OCSP_RESPONSE_STATUS_SUCCESSFUL,
                            "successful", "ca_cert", "server_cert",
                            OCSP_VERIFYSTATUS_SUCCESS, &basic_response,
                            &server_cert_chain);

  int status = 0;
  ASN1_GENERALIZEDTIME *thisupd, *nextupd;
  CheckOCSP_CERTSTATUS(&basic_response, &server_cert_chain, EVP_sha256(),
                       OCSP_RESPFINDSTATUS_SUCCESS, &status, &thisupd,
                       &nextupd);
  ASSERT_EQ(V_OCSP_CERTSTATUS_GOOD, status);

  // If OCSP response is verifiable and all good, an OCSP client should check
  // time fields to see if the response is still valid.

  // Check before OCSP was last updated connection timestamp.
  time_t connection_time = invalid_before_ocsp_update_time_sha256;
  ASSERT_EQ(1, X509_cmp_time(thisupd, &connection_time));
  ASSERT_EQ(1, X509_cmp_time(nextupd, &connection_time));

  // Check valid connection timestamp right after OCSP response was validated.
  connection_time = valid_after_ocsp_update_time_sha256;
  ASSERT_EQ(-1, X509_cmp_time(thisupd, &connection_time));
  ASSERT_EQ(1, X509_cmp_time(nextupd, &connection_time));

  // Check valid connection timestamp right before OCSP response expires.
  connection_time = valid_before_ocsp_expire_time_sha256;
  ASSERT_EQ(-1, X509_cmp_time(thisupd, &connection_time));
  ASSERT_EQ(1, X509_cmp_time(nextupd, &connection_time));

  // Check expired connection timestamp.
  connection_time = invalid_after_ocsp_expire_time_sha256;
  ASSERT_EQ(-1, X509_cmp_time(thisupd, &connection_time));
  ASSERT_EQ(-1, X509_cmp_time(nextupd, &connection_time));
}

// === Translation of OpenSSL's OCSP tests ===

// https://github.com/openssl/openssl/blob/OpenSSL_1_1_1-stable/test/recipes/80-test_ocsp.t
struct OCSPTestVector {
  const char *ocsp_response;
  const char *cafile;
  const char *untrusted;
  int expected_ocsp_verify_status;
};

// Test vectors from OpenSSL OCSP's tests
static const OCSPTestVector kTestVectors[] = {
    // === VALID OCSP RESPONSES ===
    {"ND1", "ND1_Issuer_ICA", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND2", "ND2_Issuer_Root", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND3", "ND3_Issuer_Root", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND1", "ND1_Cross_Root", "ND1_Issuer_ICA-Cross",
     OCSP_VERIFYSTATUS_SUCCESS},
    {"D1", "D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"D2", "D2_Issuer_Root", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"D3", "D3_Issuer_Root", "", OCSP_VERIFYSTATUS_SUCCESS},
    // === INVALID SIGNATURE on the OCSP RESPONSE ===
    {"ISOP_ND1", "ND1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_ND2", "ND2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_ND3", "ND3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_D1", "D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_D2", "D2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_D3", "D3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG RESPONDERID in the OCSP RESPONSE ===
    {"WRID_ND1", "ND1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_ND2", "ND2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_ND3", "ND3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_D1", "D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_D2", "D2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_D3", "D3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG ISSUERNAMEHASH in the OCSP RESPONSE ===
    {"WINH_ND1", "ND1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_ND2", "ND2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_ND3", "ND3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_D1", "D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_D2", "D2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_D3", "D3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG ISSUERKEYHASH in the OCSP RESPONSE ===
    {"WIKH_ND1", "ND1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_ND2", "ND2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_ND3", "ND3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_D1", "D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_D2", "D2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_D3", "D3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG KEY in the DELEGATED OCSP SIGNING CERTIFICATE ===
    {"WKDOSC_D1", "D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"WKDOSC_D2", "D2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"WKDOSC_D3", "D3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    // === INVALID SIGNATURE on the DELEGATED OCSP SIGNING CERTIFICATE ===
    {"ISDOSC_D1", "D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"ISDOSC_D1", "D2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"ISDOSC_D1", "D3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG SUBJECT NAME in the ISSUER CERTIFICATE ===
    {"ND1", "WSNIC_ND1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"ND2", "WSNIC_ND2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"ND3", "WSNIC_ND3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"D1", "WSNIC_D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"D2", "WSNIC_D2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"D3", "WSNIC_D3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG KEY in the ISSUER CERTIFICATE ===
    {"ND1", "WKIC_ND1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"ND2", "WKIC_ND2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"ND3", "WKIC_ND3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"D1", "WKIC_D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_ERROR},
    {"D2", "WKIC_D2_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    {"D3", "WKIC_D3_Issuer_Root", "", OCSP_VERIFYSTATUS_ERROR},
    // === INVALID SIGNATURE on the ISSUER CERTIFICATE ===
    // Expect success, because we're explicitly trusting the issuer certificate.
    // https://datatracker.ietf.org/doc/html/rfc6960#section-2.6
    {"ND1", "ISIC_ND1_Issuer_ICA", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND2", "ISIC_ND2_Issuer_Root", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND3", "ISIC_ND3_Issuer_Root", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"D1", "ISIC_D1_Issuer_ICA", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"D2", "ISIC_D2_Issuer_Root", "", OCSP_VERIFYSTATUS_SUCCESS},
    {"D3", "ISIC_D3_Issuer_Root", "", OCSP_VERIFYSTATUS_SUCCESS},
};


class OCSPTest : public testing::TestWithParam<OCSPTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, OCSPTest, testing::ValuesIn(kTestVectors));

TEST_P(OCSPTest, VerifyOCSPResponse) {
  const OCSPTestVector &t = GetParam();

  bssl::UniquePtr<OCSP_RESPONSE> ocsp_response;
  bssl::UniquePtr<OCSP_BASICRESP> basic_response;

  // Get OCSP response from path.
  std::string data = GetTestData(
      std::string("crypto/ocsp/test/" + std::string(t.ocsp_response) + ".ors")
          .c_str());
  std::vector<uint8_t> input;
  ASSERT_TRUE(DecodeBase64(&input, data.c_str()));

  ocsp_response = LoadOCSP_RESPONSE(input);
  ASSERT_TRUE(ocsp_response);

  int ret = OCSP_response_status(ocsp_response.get());
  ASSERT_EQ(OCSP_RESPONSE_STATUS_SUCCESSFUL, ret);

  basic_response = bssl::UniquePtr<OCSP_BASICRESP>(
      OCSP_response_get1_basic(ocsp_response.get()));
  ASSERT_TRUE(basic_response);

  // Set up OpenSSL OCSP tests trust store parameters and cert chain.
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  bssl::UniquePtr<X509_STORE> trust_store(X509_STORE_new());
  bssl::UniquePtr<X509_VERIFY_PARAM> vpm(X509_VERIFY_PARAM_new());
  X509_VERIFY_PARAM_set_time(vpm.get(), (time_t)1355875200);
  // Discussion for whether this flag should be on by default or not:
  // https://github.com/openssl/openssl/issues/7871
  ASSERT_EQ(X509_VERIFY_PARAM_set_flags(vpm.get(), X509_V_FLAG_PARTIAL_CHAIN),
            1);

  // Get CA root certificate from path and set up trust store.
  bssl::UniquePtr<X509> ca_certificate(
      CertFromPEM(GetTestData(std::string("crypto/ocsp/test/" +
                                          std::string(t.cafile) + ".pem")
                                  .c_str())
                      .c_str()));
  X509_STORE_add_cert(trust_store.get(), ca_certificate.get());
  ASSERT_EQ(X509_STORE_set1_param(trust_store.get(), vpm.get()), 1);

  // If untrusted cert chain isn't available, we only use CA cert as root
  // cert.
  if (std::string(t.untrusted).empty()) {
    server_cert_chain = CertsToStack({ca_certificate.get()});
  } else {
    server_cert_chain = CertChainFromPEM(
        GetTestData(
            std::string("crypto/ocsp/test/" + std::string(t.untrusted) + ".pem")
                .c_str())
            .c_str());
  }
  ASSERT_TRUE(server_cert_chain);

  // Does basic verification on OCSP response.
  const int ocsp_verify_status = OCSP_basic_verify(
      basic_response.get(), server_cert_chain.get(), trust_store.get(), 0);
  ASSERT_EQ(t.expected_ocsp_verify_status, ocsp_verify_status);
}

struct OCSPReqTestVector {
  const char *ocsp_request;
  int expected_parse_status;
  int expected_sign_status;
  const char *signer_cert;
  const char *private_key;
  const EVP_MD *dgst;
};

static const OCSPReqTestVector kRequestTestVectors[] = {
    {"ocsp_request", OCSP_REQUEST_PARSE_SUCCESS, OCSP_REQUEST_SIGN_SUCCESS,
     "server_cert", "server_key", EVP_sha1()},
    {"ocsp_request", OCSP_REQUEST_PARSE_SUCCESS, OCSP_REQUEST_SIGN_SUCCESS,
     "server_cert", "server_key", EVP_sha256()},
    {"ocsp_request_attached_cert", OCSP_REQUEST_PARSE_SUCCESS,
     OCSP_REQUEST_SIGN_ERROR, "server_cert", "server_key", nullptr},
    {"ocsp_request_no_nonce", OCSP_REQUEST_PARSE_SUCCESS,
     OCSP_REQUEST_SIGN_SUCCESS, "server_cert", "server_key", EVP_sha512()},
    {"ocsp_request_signed", OCSP_REQUEST_PARSE_SUCCESS, OCSP_REQUEST_SIGN_ERROR,
     "server_cert", "server_key", nullptr},
    {"ocsp_request_signed_sha256", OCSP_REQUEST_PARSE_SUCCESS,
     OCSP_REQUEST_SIGN_ERROR, "server_cert", "server_key", nullptr},
    {"ocsp_response", OCSP_REQUEST_PARSE_ERROR, OCSP_REQUEST_SIGN_ERROR,
     "server_cert", "server_key", nullptr},
    // Test signing with ECDSA certs and keys.
    {"ocsp_request", OCSP_REQUEST_PARSE_SUCCESS, OCSP_REQUEST_SIGN_SUCCESS,
     "server_ecdsa_cert", "server_ecdsa_key", EVP_sha1()},
    {"ocsp_request", OCSP_REQUEST_PARSE_SUCCESS, OCSP_REQUEST_SIGN_SUCCESS,
     "server_ecdsa_cert", "server_ecdsa_key", EVP_sha256()},
    {"ocsp_request_no_nonce", OCSP_REQUEST_PARSE_SUCCESS,
     OCSP_REQUEST_SIGN_SUCCESS, "server_cert", "server_key", EVP_sha256()},
    {"ocsp_request_no_nonce", OCSP_REQUEST_PARSE_SUCCESS,
     OCSP_REQUEST_SIGN_SUCCESS, "server_ecdsa_cert", "server_ecdsa_key",
     EVP_sha256()},
    // Test certificate type mismatch.
    {"ocsp_request", OCSP_REQUEST_PARSE_SUCCESS, OCSP_REQUEST_SIGN_ERROR,
     "server_cert", "server_ecdsa_key", EVP_sha256()},
    {"ocsp_request", OCSP_REQUEST_PARSE_SUCCESS, OCSP_REQUEST_SIGN_ERROR,
     "server_ecdsa_cert", "server_key", EVP_sha256()},
    // Test certificate key and cert mismatch.
    {"ocsp_request", OCSP_REQUEST_PARSE_SUCCESS, OCSP_REQUEST_SIGN_ERROR,
     "ca_cert", "server_key", EVP_sha256()},
};

class OCSPRequestTest : public testing::TestWithParam<OCSPReqTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, OCSPRequestTest,
                         testing::ValuesIn(kRequestTestVectors));

static const char good_http_request_hdr[] =
    "POST / HTTP/1.0\r\n"
    "Content-Type: application/ocsp-request\r\n"
    "Content-Length: ";

TEST_P(OCSPRequestTest, OCSPRequestParse) {
  const OCSPReqTestVector &t = GetParam();

  std::string data =
      GetTestData(std::string("crypto/ocsp/test/aws/" +
                              std::string(t.ocsp_request) + ".der")
                      .c_str());
  std::vector<uint8_t> ocsp_request_data(data.begin(), data.end());

  bssl::UniquePtr<OCSP_REQUEST> ocspRequest =
      LoadOCSP_REQUEST(ocsp_request_data);

  if (t.expected_parse_status == OCSP_REQUEST_PARSE_SUCCESS) {
    ASSERT_TRUE(ocspRequest);

    // If request parsing is successful, try setting up a |OCSP_REQ_CTX| with
    // default settings.
    bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
    const uint8_t *out;
    size_t outlen;
    bssl::UniquePtr<OCSP_REQ_CTX> ocspReqCtx(
        OCSP_sendreq_new(bio.get(), nullptr, ocspRequest.get(), 0));
    ASSERT_TRUE(ocspReqCtx);
    // Get internal memory of |OCSP_REQ_CTX| and ensure contents are written.
    ASSERT_TRUE(BIO_mem_contents(OCSP_REQ_CTX_get0_mem_bio(ocspReqCtx.get()),
                                 &out, &outlen));
    ASSERT_GT(outlen, (size_t)0);

    // Set up |OCSP_REQ_CTX| without a |OCSP_REQUEST|. Then finalize the context
    // later.
    bssl::UniquePtr<BIO> bio2(BIO_new(BIO_s_mem()));
    const uint8_t *out2;
    size_t outlen2;
    bssl::UniquePtr<OCSP_REQ_CTX> ocspReqCtxLater(
        OCSP_sendreq_new(bio2.get(), nullptr, nullptr, 0));
    ASSERT_TRUE(ocspReqCtxLater);
    ASSERT_TRUE(
        OCSP_REQ_CTX_set1_req(ocspReqCtxLater.get(), ocspRequest.get()));
    ASSERT_TRUE(BIO_mem_contents(
        OCSP_REQ_CTX_get0_mem_bio(ocspReqCtxLater.get()), &out2, &outlen2));

    // Ensure header contents are written as expected.
    EXPECT_EQ(
        good_http_request_hdr + std::to_string(ocsp_request_data.size()) + "\r",
        std::string(reinterpret_cast<const char *>(out),
                    sizeof(good_http_request_hdr) +
                        std::to_string(ocsp_request_data.size()).size()));
    // Check |OCSP_REQ_CTX| construction methods write the exact same contents.
    ASSERT_EQ(Bytes(out, outlen), Bytes(out2, outlen2));
  } else {
    ASSERT_FALSE(ocspRequest);
  }
}

TEST_P(OCSPRequestTest, OCSPRequestSign) {
  const OCSPReqTestVector &t = GetParam();

  std::string data =
      GetTestData(std::string("crypto/ocsp/test/aws/" +
                              std::string(t.ocsp_request) + ".der")
                      .c_str());
  std::vector<uint8_t> ocsp_request_data(data.begin(), data.end());
  bssl::UniquePtr<OCSP_REQUEST> ocspRequest =
      LoadOCSP_REQUEST(ocsp_request_data);

  bssl::UniquePtr<X509> server_cert(
      CertFromPEM(GetTestData(std::string("crypto/ocsp/test/aws/" +
                                          std::string(t.signer_cert) + ".pem")
                                  .c_str())
                      .c_str()));
  ASSERT_TRUE(server_cert);
  bssl::UniquePtr<STACK_OF(X509)> additional_cert(CertChainFromPEM(
      GetTestData(std::string("crypto/ocsp/test/aws/ca_cert.pem").c_str())
          .c_str()));
  ASSERT_TRUE(additional_cert);

  if (t.expected_parse_status == OCSP_REQUEST_PARSE_SUCCESS) {
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    if (std::string(t.private_key) == "server_key") {
      bssl::UniquePtr<RSA> rsa(RSAFromPEM(
          GetTestData(std::string("crypto/ocsp/test/aws/" +
                                  std::string(t.private_key) + ".pem")
                          .c_str())
              .c_str()));
      ASSERT_TRUE(rsa);
      ASSERT_TRUE(EVP_PKEY_set1_RSA(pkey.get(), rsa.get()));
    } else {
      bssl::UniquePtr<EC_KEY> ecdsa(ECDSAFromPEM(
          GetTestData(std::string("crypto/ocsp/test/aws/" +
                                  std::string(t.private_key) + ".pem")
                          .c_str())
              .c_str()));
      ASSERT_TRUE(ecdsa);
      ASSERT_TRUE(EVP_PKEY_set1_EC_KEY(pkey.get(), ecdsa.get()));
    }

    int ret = OCSP_request_sign(ocspRequest.get(), server_cert.get(),
                                pkey.get(), t.dgst, additional_cert.get(), 0);
    if (t.expected_sign_status == OCSP_REQUEST_SIGN_SUCCESS) {
      ASSERT_TRUE(ret);
    } else {
      ASSERT_FALSE(ret);
    }
  }
}

static const char extended_good_http_request_hdr[] =
    "POST / HTTP/1.0\r\n"
    "Accept-Charset: character-set\r\n"
    "Content-Type: application/ocsp-request\r\n"
    "Content-Length: ";

// Check HTTP header can be written with OCSP_REQ_CTX_add1_header().
TEST(OCSPRequestTest, AddHeader) {
  std::string data = GetTestData(std::string("crypto/ocsp/test/aws/"
                                             "ocsp_request.der")
                                     .c_str());
  std::vector<uint8_t> ocsp_request_data(data.begin(), data.end());
  bssl::UniquePtr<OCSP_REQUEST> ocspRequest =
      LoadOCSP_REQUEST(ocsp_request_data);

  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  const uint8_t *out;
  size_t outlen;
  bssl::UniquePtr<OCSP_REQ_CTX> ocspReqCtx(
      OCSP_sendreq_new(bio.get(), nullptr, nullptr, 0));
  ASSERT_TRUE(ocspReqCtx);
  // Set an additional HTTP header.
  ASSERT_TRUE(OCSP_REQ_CTX_add1_header(ocspReqCtx.get(), "Accept-Charset",
                                       "character-set"));
  ASSERT_TRUE(OCSP_REQ_CTX_set1_req(ocspReqCtx.get(), ocspRequest.get()));

  ASSERT_TRUE(BIO_mem_contents(OCSP_REQ_CTX_get0_mem_bio(ocspReqCtx.get()),
                               &out, &outlen));

  // Ensure additional header contents are written as expected.
  EXPECT_EQ(
      extended_good_http_request_hdr +
          std::to_string(ocsp_request_data.size()) + "\r\n",
      std::string(reinterpret_cast<const char *>(out),
                  sizeof(extended_good_http_request_hdr) +
                      std::to_string(ocsp_request_data.size()).size() + 1));
}

// Check a |OCSP_CERTID| can be added to an |OCSP_REQUEST| with
// OCSP_request_add0_id().
TEST(OCSPRequestTest, AddCert) {
  std::string data = GetTestData(std::string("crypto/ocsp/test/aws/"
                                             "ocsp_request.der")
                                     .c_str());
  std::vector<uint8_t> ocsp_request_data(data.begin(), data.end());
  bssl::UniquePtr<OCSP_REQUEST> ocspRequest =
      LoadOCSP_REQUEST(ocsp_request_data);
  ASSERT_TRUE(ocspRequest);

  // Construct |OCSP_CERTID| from certs.
  bssl::UniquePtr<X509> ca_cert(CertFromPEM(
      GetTestData(std::string("crypto/ocsp/test/aws/ca_cert.pem").c_str())
          .c_str()));
  bssl::UniquePtr<X509> server_cert(CertFromPEM(
      GetTestData(std::string("crypto/ocsp/test/aws/server_cert.pem").c_str())
          .c_str()));
  OCSP_CERTID *certId =
      OCSP_cert_to_id(nullptr, ca_cert.get(), server_cert.get());
  ASSERT_TRUE(certId);

  OCSP_ONEREQ *oneRequest = OCSP_request_add0_id(ocspRequest.get(), certId);
  ASSERT_TRUE(oneRequest);
  // OCSP_request_add0_id() allocates a new |OCSP_ONEREQ| and assigns the
  // pointer to |OCSP_CERTID| to it, then adds it to the stack within
  // |OCSP_REQUEST|.
  // |OCSP_REQUEST| now takes ownership of the pointer to |OCSP_CERTID| and
  // still maintains ownership of the pointer |OCSP_ONEREQ|, so we have to set
  // the references to NULL to avoid freeing the same pointers twice.
  oneRequest = nullptr;
  certId = nullptr;
}

static const char good_http_response_hdr[] =
    "HTTP/1.1 200 OK\r\n"
    "Content-Type: application/ocsp-response\r\n"
    "Content-Length: ";

// Test that |OCSP_set_max_response_length| correctly sets the maximum response
// length.
TEST(OCSPRequestTest, SetResponseLength) {
  std::string data = GetTestData(std::string("crypto/ocsp/test/aws/"
                                             "ocsp_request.der")
                                     .c_str());
  std::vector<uint8_t> ocsp_request_data(data.begin(), data.end());
  bssl::UniquePtr<OCSP_REQUEST> ocspRequest =
      LoadOCSP_REQUEST(ocsp_request_data);
  ASSERT_TRUE(ocspRequest);

  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  bssl::UniquePtr<OCSP_REQ_CTX> ocspReqCtx(
      OCSP_sendreq_new(bio.get(), nullptr, nullptr, 0));
  ASSERT_TRUE(ocspReqCtx);

  // Check custom length is set correctly.
  int new_len = 40000;
  OCSP_set_max_response_length(ocspReqCtx.get(), new_len);
  EXPECT_EQ((int)ocspReqCtx.get()->max_resp_len, new_len);

  // Check that default length is set correctly.
  OCSP_set_max_response_length(ocspReqCtx.get(), 0);
  EXPECT_EQ((int)ocspReqCtx.get()->max_resp_len, OCSP_MAX_RESP_LENGTH);

  // Write an HTTP OCSP response into the BIO.
  std::string respData = GetTestData(
      std::string("crypto/ocsp/test/aws/ocsp_response.der").c_str());
  std::vector<uint8_t> ocsp_response_data(respData.begin(), respData.end());
  const int respLen = (int)ocsp_response_data.size();
  ASSERT_GT(BIO_printf(bio.get(), "%s", good_http_response_hdr), 0);
  ASSERT_GT(BIO_printf(bio.get(), "%d\r\n\r\n", respLen), 0);
  ASSERT_EQ(BIO_write(bio.get(), ocsp_response_data.data(), respLen), respLen);

  // Set max response length to a length that is too short on purpose.
  OCSP_set_max_response_length(ocspReqCtx.get(), 1);

  // Sends out an OCSP request and expects an OCSP response in |BIO| with
  // |OCSP_REQ_CTX_nbio|. This should fail if the expected length is too short.
  EXPECT_FALSE(OCSP_REQ_CTX_nbio(ocspReqCtx.get()));
}

static const char malformed_http_response_hdr[] =
    "HTTP/1.200 OK\r\n"
    "Content-Type: application/ocsp-response\r\n"
    "Content-Length: ";

// This parses in OpenSSL, but fails in AWS-LC because we check for the HTTP
// protocol characters at the front.
static const char non_http_response_hdr[] =
    "HTPT/1.1 200 OK\r\n"
    "Content-Type: application/ocsp-response\r\n"
    "Content-Length: ";

// Only status code 200 should be accepted.
static const char not_ok_http_response_hdr[] =
    "HTTP/1.1 404 OK\r\n"
    "Content-Type: application/ocsp-response\r\n"
    "Content-Length: ";

// This should parse. Only the status code is mandatory, subsequent lines are
// optional.
static const char no_type_http_response_hdr[] =
    "HTTP/1.1 200 OK\r\n"
    "Content-Length: ";

// This should parse. Only the status code is mandatory, additional information
// is optional.
static const char no_info_http_response_hdr[] =
    "HTTP/1.0 200\r\n"
    "Content-Length: ";

// OpenSSL uses isspace() to test for white-space characters, which includes
// the following. ``\t''``\n''``\v''``\f''``\r''`` '
// This should parse. "\n" is not included since it will skip the header to the
// next line and fail the http parsing.
static const char additional_space_http_response_hdr[] =
    "HTTP/1.1 \t\v\r\f\t 200  \t\v\f\r\t   OK   \r\n"
    "Content-Type: application/ocsp-response\r\n"
    "Content-Length: ";

// This should fail, since the status code is expected on the first line.
static const char next_line_http_response_hdr[] =
    "HTTP/1.1   \n   200    \f   OK\r\n"
    "Content-Type: application/ocsp-response\r\n"
    "Content-Length: ";

// This should fail. Protocol info is expected at the front.
static const char only_code_http_response_hdr[] =
    "200\r\n"
    "Content-Length: ";

struct OCSPHTTPTestVector {
  const char *http_header;
  bool response_attached;
  int expected_status;
};

static const OCSPHTTPTestVector kResponseHTTPVectors[] = {
    {good_http_response_hdr, true, OCSP_HTTP_PARSE_SUCCESS},
    {malformed_http_response_hdr, true, OCSP_HTTP_PARSE_ERROR},
    {non_http_response_hdr, true, OCSP_HTTP_PARSE_ERROR},
    {not_ok_http_response_hdr, true, OCSP_HTTP_PARSE_ERROR},
    {no_type_http_response_hdr, true, OCSP_REQUEST_PARSE_SUCCESS},
    {no_info_http_response_hdr, true, OCSP_REQUEST_PARSE_SUCCESS},
    {additional_space_http_response_hdr, true, OCSP_REQUEST_PARSE_SUCCESS},
    {next_line_http_response_hdr, true, OCSP_HTTP_PARSE_ERROR},
    {only_code_http_response_hdr, true, OCSP_HTTP_PARSE_ERROR},
    // HTTP Header is OK, but no actual response is attached.
    {good_http_response_hdr, false, OCSP_HTTP_PARSE_ERROR},
    {no_type_http_response_hdr, false, OCSP_HTTP_PARSE_ERROR},
    {no_info_http_response_hdr, false, OCSP_HTTP_PARSE_ERROR},
};

class OCSPHTTPTest : public testing::TestWithParam<OCSPHTTPTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, OCSPHTTPTest,
                         testing::ValuesIn(kResponseHTTPVectors));

// Test if OCSP_sendreq_bio() can properly send out an HTTP request with
// a |OCSP_REQUEST|, and expect an HTTP response with an OCSP response back.
// Always sends the same OCSP request and replies with the same OCSP response.
// This test focuses parsing the OCSP response with HTTP. We have other tests
// to test if the actual OCSP response is parsable and verifiable.
TEST_P(OCSPHTTPTest, OCSPRequestHTTP) {
  const OCSPHTTPTestVector &t = GetParam();

  std::string data =
      GetTestData(std::string("crypto/ocsp/test/aws/ocsp_request.der").c_str());
  std::vector<uint8_t> ocsp_request_data(data.begin(), data.end());
  std::string respData = GetTestData(
      std::string("crypto/ocsp/test/aws/ocsp_response.der").c_str());
  std::vector<uint8_t> ocsp_response_data(respData.begin(), respData.end());

  // Write an HTTP OCSP response into the BIO.
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_mem()));
  const int respLen = (int)ocsp_response_data.size();
  ASSERT_GT(BIO_printf(bio.get(), "%s", t.http_header), 0);
  ASSERT_GT(BIO_printf(bio.get(), "%d\r\n\r\n", respLen), 0);
  if (t.response_attached) {
    ASSERT_EQ(BIO_write(bio.get(), ocsp_response_data.data(), respLen),
              respLen);
  }

  // Sends out an OCSP request and expects an OCSP response in |BIO|.
  bssl::UniquePtr<OCSP_REQUEST> ocspRequest =
      LoadOCSP_REQUEST(ocsp_request_data);
  ASSERT_TRUE(ocspRequest);
  bssl::UniquePtr<OCSP_RESPONSE> ocspResponse(
      OCSP_sendreq_bio(bio.get(), nullptr, ocspRequest.get()));
  if (t.expected_status == OCSP_HTTP_PARSE_SUCCESS && t.response_attached) {
    ASSERT_TRUE(ocspResponse);
  } else {
    ASSERT_FALSE(ocspResponse);
  }
}

struct OCSPURLTestVector {
  const char *ocsp_url;
  const char *expected_host;
  const char *expected_port;
  const char *expected_path;
  int expected_ssl;
  int expected_status;
};

static const OCSPURLTestVector kOCSPURLVectors[] = {
    // === VALID URLs ===
    {"http://ocsp.example.com/", "ocsp.example.com", "80", "/", 0,
     OCSP_URL_PARSE_SUCCESS},
    // Non-standard port.
    {"http://ocsp.example.com:8080/", "ocsp.example.com", "8080", "/", 0,
     OCSP_URL_PARSE_SUCCESS},
    {"http://ocsp.example.com/ocsp", "ocsp.example.com", "80", "/ocsp", 0,
     OCSP_URL_PARSE_SUCCESS},
    // Port for HTTPS is 443.
    {"https://ocsp.example.com/", "ocsp.example.com", "443", "/", 1,
     OCSP_URL_PARSE_SUCCESS},
    // Empty path, the default should be "/".
    {"https://ocsp.example.com", "ocsp.example.com", "443", "/", 1,
     OCSP_URL_PARSE_SUCCESS},
    // Parsing an IPv6 host address.
    {"http://[2001:db8::1]/ocsp", "2001:db8::1", "80", "/ocsp", 0,
     OCSP_URL_PARSE_SUCCESS},
    {"https://[2001:db8::1]/ocsp", "2001:db8::1", "443", "/ocsp", 1,
     OCSP_URL_PARSE_SUCCESS},
    // Parsing a URL with an invalid port, but OpenSSL still parses the string
    // where the port is expected.
    {"http://ocsp.example.com:invalid/", "ocsp.example.com", "invalid", "/", 0,
     OCSP_URL_PARSE_SUCCESS},
    // Empty host component.
    {"http:///ocsp", "", "80", "/ocsp", 0, OCSP_URL_PARSE_SUCCESS},

    // === INVALID URLs ===
    // Not http or https in front.
    {"htp://ocsp.example.com/", nullptr, nullptr, nullptr, 0,
     OCSP_URL_PARSE_ERROR},
    // Double slash is mandatory.
    {"http:/ocsp.example.com/", nullptr, nullptr, nullptr, 0,
     OCSP_URL_PARSE_ERROR},
    // Malformed.
    {"httocsp.example.com/", nullptr, nullptr, nullptr, 0,
     OCSP_URL_PARSE_ERROR},
    // No closing bracket for ipv6.
    {"http://[2001:db8::1/", nullptr, nullptr, nullptr, 0,
     OCSP_URL_PARSE_ERROR},
};

class OCSPURLTest : public testing::TestWithParam<OCSPURLTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, OCSPURLTest, testing::ValuesIn(kOCSPURLVectors));

TEST_P(OCSPURLTest, OCSPParseURL) {
  const OCSPURLTestVector &t = GetParam();

  char *host = nullptr;
  char *path = nullptr;
  char *port = nullptr;
  int is_ssl;

  int ret = OCSP_parse_url(t.ocsp_url, &host, &port, &path, &is_ssl);
  if (t.expected_status == OCSP_URL_PARSE_SUCCESS) {
    EXPECT_EQ(ret, OCSP_URL_PARSE_SUCCESS);
    EXPECT_EQ(std::string(host), std::string(t.expected_host));
    EXPECT_EQ(std::string(port), std::string(t.expected_port));
    EXPECT_EQ(std::string(path), std::string(t.expected_path));
    EXPECT_EQ(std::string(path), std::string(t.expected_path));
    OPENSSL_free(host);
    OPENSSL_free(path);
    OPENSSL_free(port);
  } else {
    EXPECT_EQ(ret, OCSP_URL_PARSE_ERROR);
    EXPECT_FALSE(host);
    EXPECT_FALSE(port);
    EXPECT_FALSE(path);
  }
}
