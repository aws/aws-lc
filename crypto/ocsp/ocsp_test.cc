// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#include <time.h>

#include <gtest/gtest.h>

#include "openssl/ocsp.h"
#include "openssl/pem.h"

#include "../internal.h"

static const time_t invalid_before_ocsp_update_time = 1621988613;
static const time_t valid_after_ocsp_update_time = 1621988615;
static const time_t valid_before_ocsp_expire_time = 1937348613;
static const time_t invalid_after_ocsp_expire_time = 1937348615;

static const time_t invalid_before_ocsp_update_time_sha256 = 1622145762;
static const time_t valid_after_ocsp_update_time_sha256 = 1622145764;
static const time_t valid_before_ocsp_expire_time_sha256 = 1937505762;
static const time_t invalid_after_ocsp_expire_time_sha256 = 1937505764;

#define OCSP_VERIFYSTATUS_SUCCESS                   1
#define OCSP_VERIFYSTATUS_ERROR                     0
#define OCSP_VERIFYSTATUS_FATALERROR                -1

#define OCSP_RESPFINDSTATUS_SUCCESS                 1
#define OCSP_RESPFINDSTATUS_ERROR                   0


std::string GetTestData(const char *path);

static bool DecodeBase64(std::vector<uint8_t> *out, const char *in) {
  int temp_length = 0;
  size_t total_length = 0;
  EVP_ENCODE_CTX ctx;
  EVP_DecodeInit(&ctx);
  out->resize(strlen(in));

  int decode_update_result = EVP_DecodeUpdate(&ctx, out->data(), &temp_length, (const uint8_t *) in, strlen(in));
  if(decode_update_result != 1 && decode_update_result != 0) {
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

// CertFromPEM parses the given, NUL-terminated pem block and returns an |X509*|.
static bssl::UniquePtr<X509> CertFromPEM(const char *pem) {
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem, strlen(pem)));
  return bssl::UniquePtr<X509>(
      PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
}

static bssl::UniquePtr<STACK_OF(X509)> CertChainFromPEM(const char *pem) {
  bssl::UniquePtr<STACK_OF(X509)> stack(sk_X509_new_null());
  if (!stack) {
    return nullptr;
  }

  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem, strlen(pem)));
  for (;;) {
    bssl::UniquePtr<X509> cert = bssl::UniquePtr<X509>(PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
    if(cert == nullptr){
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
  return bssl::UniquePtr<OCSP_RESPONSE>(d2i_OCSP_RESPONSE(nullptr, &ptr, der.size()));
}

static void ExtractAndVerifyBasicOCSP(
    bssl::Span<const uint8_t> der,
    int expected_ocsp_status,
    const std::string ca_cert_file,
    const std::string server_cert_file,
    int expected_ocsp_verify_status,
    bssl::UniquePtr<OCSP_BASICRESP> *basic_response,
    bssl::UniquePtr<STACK_OF(X509)> *server_cert_chain){
  bssl::UniquePtr<OCSP_RESPONSE> ocsp_response;

  ocsp_response = LoadOCSP_RESPONSE(der);
  ASSERT_TRUE(ocsp_response);

  int ret = OCSP_response_status(ocsp_response.get());
  ASSERT_EQ(expected_ocsp_status, ret);
  if(ret != OCSP_RESPONSE_STATUS_SUCCESSFUL) {
    return;
  }

  *basic_response = bssl::UniquePtr<OCSP_BASICRESP>(OCSP_response_get1_basic(ocsp_response.get()));
  ASSERT_TRUE(*basic_response);

  // Set up trust store and certificate chain.
  bssl::UniquePtr<X509> ca_cert(CertFromPEM(
      GetTestData(std::string("crypto/ocsp/test/aws/" + ca_cert_file + ".pem").c_str()).c_str()));
  bssl::UniquePtr<X509> server_cert(CertFromPEM(
      GetTestData(std::string("crypto/ocsp/test/aws/" + server_cert_file+ ".pem").c_str()).c_str()));

  bssl::UniquePtr<X509_STORE> trust_store(X509_STORE_new());
  X509_STORE_add_cert(trust_store.get(),ca_cert.get());
  *server_cert_chain = CertsToStack(
      {server_cert.get(),ca_cert.get()});
  ASSERT_TRUE(*server_cert_chain);

  // Verifies the OCSP responder's signature on the OCSP response data.
  const int ocsp_verify_err = OCSP_basic_verify(basic_response->get(), server_cert_chain->get(), trust_store.get(), 0);
  ASSERT_EQ(expected_ocsp_verify_status, ocsp_verify_err);
}

static void CheckOCSP_CERTSTATUS(
    bssl::UniquePtr<OCSP_BASICRESP> *basic_response,
    bssl::UniquePtr<STACK_OF(X509)> *server_cert_chain,
    const EVP_MD *dgst,
    int expected_resp_find_status,
    int *status,
    ASN1_GENERALIZEDTIME **thisupd,
    ASN1_GENERALIZEDTIME **nextupd){
  X509 *subject = sk_X509_value(server_cert_chain->get(), 0);
  X509 *issuer = sk_X509_value(server_cert_chain->get(), 1);
  // Convert issuer certificate to |OCSP_CERTID|.
  bssl::UniquePtr<OCSP_CERTID> cert_id = bssl::UniquePtr<OCSP_CERTID>(OCSP_cert_to_id(dgst, subject, issuer));
  ASSERT_TRUE(cert_id);

  int reason = 0;
  ASN1_GENERALIZEDTIME *revtime;
  // Checks revocation status of the response.
  const int ocsp_resp_find_status_res = OCSP_resp_find_status(basic_response->get(), cert_id.get(), status, &reason, &revtime, thisupd, nextupd);
  ASSERT_EQ(expected_resp_find_status, ocsp_resp_find_status_res);
}

// Test data below are taken from s2n's ocsp test files:
// https://github.com/aws/s2n-tls/blob/main/tests/pems/ocsp
// OCSP testing methods were taken from s2n's validation tests:
// https://github.com/aws/s2n-tls/blob/main/tests/unit/s2n_x509_validator_test.c
struct OCSPTestVectorExtended {
  std::string ocsp_response;
  std::string cafile;
  std::string server_cert;
  const EVP_MD *dgst;
  int expected_ocsp_status;
  int expected_ocsp_verify_status;
  int expected_ocsp_resp_find_status;
  int expected_ocsp_cert_status;
};

static const OCSPTestVectorExtended nTestVectors[] = {
    // === SHA1 OCSP RESPONSES ===
    // Test valid OCSP response signed by an OCSP responder.
    {
        "ocsp_response",
        "ca_cert",
        "server_cert",
        EVP_sha1(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_SUCCESS,
        V_OCSP_CERTSTATUS_GOOD
    },
    // Test against same good OCSP response, but checking behavior of not
    // specifying hash algorithm used for |OCSP_cert_to_id| this time (should
    // default to sha1). When |*dgst| is set to NULL, the default hash algorithm
    // should automatically be set to sha1. The revocation status check of the
    // response should work if hash algorithm of |cert_id| has been set to sha1
    // successfully.
    {
        "ocsp_response",
        "ca_cert",
        "server_cert",
        nullptr,
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_SUCCESS,
        V_OCSP_CERTSTATUS_GOOD
    },
    // Test valid OCSP response directly signed by the CA certificate.
    {
        "ocsp_response_ca_signed",
        "ca_cert",
        "server_cert",
        EVP_sha1(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_SUCCESS,
        V_OCSP_CERTSTATUS_GOOD
    },
    // Test OCSP response status is revoked.
    {
        "ocsp_response_revoked",
        "ca_cert",
        "server_cert",
        EVP_sha1(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_SUCCESS,
        V_OCSP_CERTSTATUS_REVOKED
    },
    // Test OCSP response status is unknown.
    {
        "ocsp_response_unknown",
        "ca_cert",
        "server_cert",
        EVP_sha1(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_SUCCESS,
        V_OCSP_CERTSTATUS_UNKNOWN
    },
    // Test OCSP response signed by the correct responder certificate, but not for
    // the requested certificate. (So this would be a completely valid response to a
    // different OCSP request for the other certificate.)
    {
        "ocsp_response",
        "ca_cert",
        "server_ecdsa_cert",
        EVP_sha1(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_ERROR,
        0
    },
    // Test OCSP response where the requested certificate was signed by the OCSP
    // responder, but signed by the wrong requested OCSP responder key certificate.
    // However, this incorrect OCSP responder certificate may be a valid OCSP
    // responder for some other case and also chains to a trusted root.
    {
        "ocsp_response_wrong_signer",
        "ca_cert",
        "server_cert",
        EVP_sha1(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_ERROR,
        0,
        0
    },

    // === SHA256 OCSP RESPONSES ===
    // Test valid OCSP response signed by an OCSP responder.
    {
        "ocsp_response_sha256",
        "ca_cert",
        "server_cert",
        EVP_sha256(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_SUCCESS,
        V_OCSP_CERTSTATUS_GOOD
    },
    // Test a SHA-256 revoked OCSP response status.
    {
        "ocsp_response_revoked_sha256",
        "ca_cert",
        "server_cert",
        EVP_sha256(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_SUCCESS,
        V_OCSP_CERTSTATUS_REVOKED
    },
    // Test a SHA-256 unknown OCSP response status.
    {
        "ocsp_response_unknown_sha256",
        "ca_cert",
        "server_cert",
        EVP_sha256(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_SUCCESS,
        V_OCSP_CERTSTATUS_UNKNOWN
    },
    // Test a SHA-256 OCSP response signed by the correct responder certificate,
    // but not for the requested certificate. (So this would be a completely
    // valid response to a different OCSP request for the other certificate.)
    {
        "ocsp_response_sha256",
        "ca_cert",
        "server_ecdsa_cert",
        EVP_sha256(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_SUCCESS,
        OCSP_RESPFINDSTATUS_ERROR,
        0
    },
    // Test a SHA-256 OCSP response signed by the wrong responder certificate,
    // but the requested certificate was signed. (however this incorrect OCSP
    // responder certificate is a valid OCSP responder for some other case and
    // chains to a trusted root). Thus, this response is not valid for any
    // request.
    {
        "ocsp_response_wrong_signer_sha256",
        "ca_cert",
        "server_cert",
        EVP_sha256(),
        OCSP_RESPONSE_STATUS_SUCCESSFUL,
        OCSP_VERIFYSTATUS_ERROR,
        0,
        0
    },

    // === Invalid OCSP response requests sent back an OCSP responder ===
    // https://datatracker.ietf.org/doc/html/rfc6960#section-4.2.1
    // OCSPResponseStatus: malformedRequest
    {
        "ocsp_response_malformedrequest",
        "",
        "",
        nullptr,
        OCSP_RESPONSE_STATUS_MALFORMEDREQUEST,
        0,
        0,
        0
    },
    // OCSPResponseStatus: internalError
    {
        "ocsp_response_internalerror",
        "",
        "",
        nullptr,
        OCSP_RESPONSE_STATUS_INTERNALERROR,
        0,
        0,
        0
    },
    // OCSPResponseStatus: tryLater
    {
        "ocsp_response_trylater",
        "",
        "",
        nullptr,
        OCSP_RESPONSE_STATUS_TRYLATER,
        0,
        0,
        0
    },
    // OCSPResponseStatus: sigRequired
    {
        "ocsp_response_sigrequired",
        "",
        "",
        nullptr,
        OCSP_RESPONSE_STATUS_SIGREQUIRED,
        0,
        0,
        0
    },
    // OCSPResponseStatus: unauthorized
    {
        "ocsp_response_unauthorized",
        "",
        "",
        nullptr,
        OCSP_RESPONSE_STATUS_UNAUTHORIZED,
        0,
        0,
        0
    },
};

class OCSPTestExtended : public testing::TestWithParam<OCSPTestVectorExtended> {};

INSTANTIATE_TEST_SUITE_P(All, OCSPTestExtended, testing::ValuesIn(nTestVectors));

TEST_P(OCSPTestExtended, VerifyOCSPResponseExtended) {
  const OCSPTestVectorExtended &t = GetParam();

  std::string data = GetTestData(std::string("crypto/ocsp/test/aws/" + t.ocsp_response + ".der").c_str());
  std::vector<uint8_t> ocsp_reponse_data(data.begin(), data.end());

  // OCSP response parsing and verification step.
  bssl::UniquePtr<OCSP_BASICRESP> basic_response;
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  ExtractAndVerifyBasicOCSP(ocsp_reponse_data,
                            t.expected_ocsp_status,
                            t.cafile,
                            t.server_cert,
                            t.expected_ocsp_verify_status,
                            &basic_response,
                            &server_cert_chain);

  // If OCSP basic verify is successful, we check the OCSP response status.
  if(t.expected_ocsp_verify_status == OCSP_VERIFYSTATUS_SUCCESS) {
    int status = 0;
    ASN1_GENERALIZEDTIME *thisupd, *nextupd;
    CheckOCSP_CERTSTATUS(&basic_response, &server_cert_chain, t.dgst,
                         t.expected_ocsp_resp_find_status, &status, &thisupd,
                         &nextupd);
    // If OCSP response status retrieving is successful, we check if the cert
    // status of the OCSP response is correct.
    if (t.expected_ocsp_resp_find_status == OCSP_RESPFINDSTATUS_SUCCESS) {
      ASSERT_EQ(t.expected_ocsp_cert_status, status);
    }
  }
}

// === Specific test cases ===

// Test valid OCSP response signed by an OCSP responder along with check for
// correct time field parsing.
TEST(OCSPTest, TestGoodOCSP) {
  std::string data = GetTestData(std::string("crypto/ocsp/test/aws/ocsp_response.der").c_str());
  std::vector<uint8_t> ocsp_reponse_data(data.begin(), data.end());

  bssl::UniquePtr<OCSP_BASICRESP> basic_response;
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  ExtractAndVerifyBasicOCSP(ocsp_reponse_data,
                            OCSP_RESPONSE_STATUS_SUCCESSFUL,
                            "ca_cert",
                            "server_cert",
                            OCSP_VERIFYSTATUS_SUCCESS,
                            &basic_response,
                            &server_cert_chain);

  int status = 0;
  ASN1_GENERALIZEDTIME *thisupd, *nextupd;
  CheckOCSP_CERTSTATUS(&basic_response,
                       &server_cert_chain,
                       EVP_sha1(),
                       OCSP_RESPFINDSTATUS_SUCCESS,
                       &status,
                       &thisupd,
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
}

// Test valid OCSP response, but the data itself is untrusted.
TEST(OCSPTest, TestUntrustedDataOCSP) {
  std::string data = GetTestData(std::string("crypto/ocsp/test/aws/ocsp_response.der").c_str());
  std::vector<uint8_t> ocsp_reponse_data(data.begin(), data.end());

  // Mess up a byte right in the middle of the cert.
  ocsp_reponse_data[800] = ocsp_reponse_data[800] + 1;

  bssl::UniquePtr<OCSP_BASICRESP> basic_response;
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  ExtractAndVerifyBasicOCSP(ocsp_reponse_data,
                            OCSP_RESPONSE_STATUS_SUCCESSFUL,
                            "ca_cert",
                            "server_cert",
                            OCSP_VERIFYSTATUS_ERROR,
                            &basic_response,
                            &server_cert_chain);
}


// Test valid OCSP response hashed with sha256 along with check for correct time
// field parsing.
TEST(OCSPTest, TestGoodOCSP_SHA256) {
  std::string data = GetTestData(std::string("crypto/ocsp/test/aws/ocsp_response_sha256.der").c_str());
  std::vector<uint8_t> ocsp_reponse_data(data.begin(), data.end());

  bssl::UniquePtr<OCSP_BASICRESP> basic_response;
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  ExtractAndVerifyBasicOCSP(ocsp_reponse_data,
                            OCSP_RESPONSE_STATUS_SUCCESSFUL,
                            "ca_cert",
                            "server_cert",
                            OCSP_VERIFYSTATUS_SUCCESS,
                            &basic_response,
                            &server_cert_chain);

  int status = 0;
  ASN1_GENERALIZEDTIME *thisupd, *nextupd;
  CheckOCSP_CERTSTATUS(&basic_response,
                       &server_cert_chain,
                       EVP_sha256(),
                       OCSP_RESPFINDSTATUS_SUCCESS,
                       &status,
                       &thisupd,
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
struct OCSPTestVector{
  std::string ocsp_response;
  std::string cafile;
  std::string untrusted;
  int expected_ocsp_verify_status;
};

// Test vectors from OpenSSL OCSP's tests
static const OCSPTestVector kTestVectors[] = {
    // === VALID OCSP RESPONSES ===
    {"ND1","ND1_Issuer_ICA","", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND2","ND2_Issuer_Root","", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND3","ND3_Issuer_Root","", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND1","ND1_Cross_Root","ND1_Issuer_ICA-Cross", OCSP_VERIFYSTATUS_SUCCESS},
    {"D1","D1_Issuer_ICA","", OCSP_VERIFYSTATUS_SUCCESS},
    {"D2","D2_Issuer_Root","", OCSP_VERIFYSTATUS_SUCCESS},
    {"D3","D3_Issuer_Root","", OCSP_VERIFYSTATUS_SUCCESS},
    // === INVALID SIGNATURE on the OCSP RESPONSE ===
    {"ISOP_ND1","ND1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_ND2","ND2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_ND3","ND3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_D1","D1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_D2","D2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"ISOP_D3","D3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG RESPONDERID in the OCSP RESPONSE ===
    {"WRID_ND1","ND1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_ND2","ND2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_ND3","ND3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_D1","D1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_D2","D2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WRID_D3","D3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG ISSUERNAMEHASH in the OCSP RESPONSE ===
    {"WINH_ND1","ND1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_ND2","ND2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_ND3","ND3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_D1","D1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_D2","D2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WINH_D3","D3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG ISSUERKEYHASH in the OCSP RESPONSE ===
    {"WIKH_ND1","ND1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_ND2","ND2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_ND3","ND3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_D1","D1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_D2","D2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WIKH_D3","D3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG KEY in the DELEGATED OCSP SIGNING CERTIFICATE ===
    {"WKDOSC_D1","D1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"WKDOSC_D2","D2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"WKDOSC_D3","D3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    // === INVALID SIGNATURE on the DELEGATED OCSP SIGNING CERTIFICATE ===
    {"ISDOSC_D1","D1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"ISDOSC_D1","D2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"ISDOSC_D1","D3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG SUBJECT NAME in the ISSUER CERTIFICATE ===
    {"ND1","WSNIC_ND1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"ND2","WSNIC_ND2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"ND3","WSNIC_ND3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"D1","WSNIC_D1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"D2","WSNIC_D2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"D3","WSNIC_D3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    // === WRONG KEY in the ISSUER CERTIFICATE ===
    {"ND1","WKIC_ND1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"ND2","WKIC_ND2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"ND3","WKIC_ND3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"D1","WKIC_D1_Issuer_ICA","", OCSP_VERIFYSTATUS_ERROR},
    {"D2","WKIC_D2_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    {"D3","WKIC_D3_Issuer_Root","", OCSP_VERIFYSTATUS_ERROR},
    // === INVALID SIGNATURE on the ISSUER CERTIFICATE ===
    // Expect success, because we're explicitly trusting the issuer certificate.
    // https://datatracker.ietf.org/doc/html/rfc6960#section-2.6
    {"ND1","ISIC_ND1_Issuer_ICA","", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND2","ISIC_ND2_Issuer_Root","", OCSP_VERIFYSTATUS_SUCCESS},
    {"ND3","ISIC_ND3_Issuer_Root","", OCSP_VERIFYSTATUS_SUCCESS},
    {"D1","ISIC_D1_Issuer_ICA","", OCSP_VERIFYSTATUS_SUCCESS},
    {"D2","ISIC_D2_Issuer_Root","", OCSP_VERIFYSTATUS_SUCCESS},
    {"D3","ISIC_D3_Issuer_Root","", OCSP_VERIFYSTATUS_SUCCESS},
};


class OCSPTest : public testing::TestWithParam<OCSPTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, OCSPTest, testing::ValuesIn(kTestVectors));

TEST_P(OCSPTest, VerifyOCSPResponse) {
  const OCSPTestVector &t = GetParam();

  bssl::UniquePtr<OCSP_RESPONSE> ocsp_response;
  bssl::UniquePtr<OCSP_BASICRESP> basic_response;

  // Get OCSP response from path.
  std::string data = GetTestData(std::string("crypto/ocsp/test/" + t.ocsp_response + ".ors").c_str());
  std::vector<uint8_t> input;
  ASSERT_TRUE(DecodeBase64(&input, data.c_str()));

  ocsp_response = LoadOCSP_RESPONSE(input);
  ASSERT_TRUE(ocsp_response);

  int ret = OCSP_response_status(ocsp_response.get());
  ASSERT_EQ(OCSP_RESPONSE_STATUS_SUCCESSFUL, ret);

  basic_response = bssl::UniquePtr<OCSP_BASICRESP>(OCSP_response_get1_basic(ocsp_response.get()));
  ASSERT_TRUE(basic_response);

  // Set up OpenSSL OCSP tests trust store parameters and cert chain.
  bssl::UniquePtr<STACK_OF(X509)> server_cert_chain;
  bssl::UniquePtr<X509_STORE> trust_store(X509_STORE_new());
  bssl::UniquePtr<X509_VERIFY_PARAM> vpm(X509_VERIFY_PARAM_new());
  X509_VERIFY_PARAM_set_time(vpm.get(), (time_t)1355875200);
  // Discussion for whether this flag should be on by default or not:
  // https://github.com/openssl/openssl/issues/7871
  ASSERT_EQ(X509_VERIFY_PARAM_set_flags(vpm.get(), X509_V_FLAG_PARTIAL_CHAIN), 1);

  // Get CA root certificate from path and set up trust store.
  bssl::UniquePtr<X509> ca_certificate(CertFromPEM(
      GetTestData(std::string("crypto/ocsp/test/" + t.cafile + ".pem").c_str()).c_str()));
  X509_STORE_add_cert(trust_store.get(),ca_certificate.get());
  ASSERT_EQ(X509_STORE_set1_param(trust_store.get(), vpm.get()), 1);

  // If untrusted cert chain isn't available, we only use CA cert as root cert.
  if(t.untrusted.empty()){
    server_cert_chain = CertsToStack({ca_certificate.get()});
  }
  else {
    server_cert_chain = CertChainFromPEM(GetTestData(std::string("crypto/ocsp/test/" + t.untrusted + ".pem").c_str()).c_str());
  }
  ASSERT_TRUE(server_cert_chain);

  // Does basic verification on OCSP response.
  const int ocsp_verify_status = OCSP_basic_verify(basic_response.get(), server_cert_chain.get(), trust_store.get(), 0);
  ASSERT_EQ(t.expected_ocsp_verify_status, ocsp_verify_status);
}
