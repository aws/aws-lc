// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#include <gtest/gtest.h>

#include "openssl/ocsp.h"
#include "openssl/pem.h"

#include "../test/test_util.h"

struct OpenSSL_OCSPTestVector{
  std::string ocsp_response;
  std::string cafile;
  std::string untrusted;
  int expected_ocsp_verify_status;
};

// Test vectors from OpenSSL OCSP's tests
// https://github.com/openssl/openssl/blob/OpenSSL_1_1_1-stable/test/recipes/80-test_ocsp.t
static const OpenSSL_OCSPTestVector kTestVectors[] = {
    // === VALID OCSP RESPONSES ===
    {"ND1","ND1_Issuer_ICA","",1},
    {"ND2","ND2_Issuer_Root","",1},
    {"ND3","ND3_Issuer_Root","",1},
    {"ND1","ND1_Cross_Root","ND1_Issuer_ICA-Cross",1},
    {"D1","D1_Issuer_ICA","",1},
    {"D2","D2_Issuer_Root","",1},
    {"D3","D3_Issuer_Root","",1},
    // === INVALID SIGNATURE on the OCSP RESPONSE ===
    {"ISOP_ND1","ND1_Issuer_ICA","",0},
    {"ISOP_ND2","ND2_Issuer_Root","",0},
    {"ISOP_ND3","ND3_Issuer_Root","",0},
    {"ISOP_D1","D1_Issuer_ICA","",0},
    {"ISOP_D2","D2_Issuer_Root","",0},
    {"ISOP_D3","D3_Issuer_Root","",0},
    // === WRONG RESPONDERID in the OCSP RESPONSE ===
    {"WRID_ND1","ND1_Issuer_ICA","",0},
    {"WRID_ND2","ND2_Issuer_Root","",0},
    {"WRID_ND3","ND3_Issuer_Root","",0},
    {"WRID_D1","D1_Issuer_ICA","",0},
    {"WRID_D2","D2_Issuer_Root","",0},
    {"WRID_D3","D3_Issuer_Root","",0},
    // === WRONG ISSUERNAMEHASH in the OCSP RESPONSE ===
    {"WINH_ND1","ND1_Issuer_ICA","",0},
    {"WINH_ND2","ND2_Issuer_Root","",0},
    {"WINH_ND3","ND3_Issuer_Root","",0},
    {"WINH_D1","D1_Issuer_ICA","",0},
    {"WINH_D2","D2_Issuer_Root","",0},
    {"WINH_D3","D3_Issuer_Root","",0},
    // === WRONG ISSUERKEYHASH in the OCSP RESPONSE ===
    {"WIKH_ND1","ND1_Issuer_ICA","",0},
    {"WIKH_ND2","ND2_Issuer_Root","",0},
    {"WIKH_ND3","ND3_Issuer_Root","",0},
    {"WIKH_D1","D1_Issuer_ICA","",0},
    {"WIKH_D2","D2_Issuer_Root","",0},
    {"WIKH_D3","D3_Issuer_Root","",0},
    // === WRONG KEY in the DELEGATED OCSP SIGNING CERTIFICATE ===
    {"WKDOSC_D1","D1_Issuer_ICA","",0},
    {"WKDOSC_D2","D2_Issuer_Root","",0},
    {"WKDOSC_D3","D3_Issuer_Root","",0},
    // === INVALID SIGNATURE on the DELEGATED OCSP SIGNING CERTIFICATE ===
    {"ISDOSC_D1","D1_Issuer_ICA","",0},
    {"ISDOSC_D1","D2_Issuer_Root","",0},
    {"ISDOSC_D1","D3_Issuer_Root","",0},
    // === WRONG SUBJECT NAME in the ISSUER CERTIFICATE ===
    {"ND1","WSNIC_ND1_Issuer_ICA","",0},
    {"ND2","WSNIC_ND2_Issuer_Root","",0},
    {"ND3","WSNIC_ND3_Issuer_Root","",0},
    {"D1","WSNIC_D1_Issuer_ICA","",0},
    {"D2","WSNIC_D2_Issuer_Root","",0},
    {"D3","WSNIC_D3_Issuer_Root","",0},
    // === WRONG KEY in the ISSUER CERTIFICATE ===
    {"ND1","WKIC_ND1_Issuer_ICA","",0},
    {"ND2","WKIC_ND2_Issuer_Root","",0},
    {"ND3","WKIC_ND3_Issuer_Root","",0},
    {"D1","WKIC_D1_Issuer_ICA","",0},
    {"D2","WKIC_D2_Issuer_Root","",0},
    {"D3","WKIC_D3_Issuer_Root","",0},
    // === INVALID SIGNATURE on the ISSUER CERTIFICATE ===
    // Expect success, because we're explicitly trusting the issuer certificate.
    // https://datatracker.ietf.org/doc/html/rfc6960#section-2.6
    {"ND1","ISIC_ND1_Issuer_ICA","",1},
    {"ND2","ISIC_ND2_Issuer_Root","",1},
    {"ND3","ISIC_ND3_Issuer_Root","",1},
    {"D1","ISIC_D1_Issuer_ICA","",1},
    {"D2","ISIC_D2_Issuer_Root","",1},
    {"D3","ISIC_D3_Issuer_Root","",1},
};


class OpenSSL_OCSPTest : public testing::TestWithParam<OpenSSL_OCSPTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, OpenSSL_OCSPTest, testing::ValuesIn(kTestVectors));


std::string GetTestData(const char *path);

static bool DecodeBase64(std::vector<uint8_t> *out, const char *in) {
  size_t len;
  if (!EVP_DecodedLength(&len, strlen(in))) {
    fprintf(stderr, "EVP_DecodedLength failed\n");
    return false;
  }

  out->resize(len);
  if (!EVP_DecodeBase64(out->data(), &len, len, (const uint8_t *)in,
                        strlen(in))) {
    fprintf(stderr, "EVP_DecodeBase64 failed\n");
    return false;
  }
  out->resize(len);
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
    X509 *cert = PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr);
    if(cert == nullptr){
      break;
    }
    if (!bssl::PushToStack(stack.get(), bssl::UpRef(cert))) {
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

TEST_P(OpenSSL_OCSPTest, VerifyOpenSSL_OCSP_response) {
  const OpenSSL_OCSPTestVector &t = GetParam();

  bssl::UniquePtr<OCSP_RESPONSE> ocsp_response;
  bssl::UniquePtr<OCSP_BASICRESP> basic_response;

  // Get OCSP response from path.
  std::string data = GetTestData(std::string("crypto/ocsp/test/openssl-ocsp/" + t.ocsp_response + ".ors").c_str());
  data.erase(std::remove(data.begin(), data.end(), '\n'), data.end());
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
  ASSERT_EQ(X509_VERIFY_PARAM_set_flags(vpm.get(), X509_V_FLAG_PARTIAL_CHAIN), 1);

  // Get CA root certificate from path and set up trust store.
  bssl::UniquePtr<X509> ca_cert(CertFromPEM(
      GetTestData(std::string("crypto/ocsp/test/openssl-ocsp/" + t.cafile + ".pem").c_str()).c_str()));
  X509_STORE_add_cert(trust_store.get(),ca_cert.get());
  ASSERT_EQ(X509_STORE_set1_param(trust_store.get(), vpm.get()), 1);

  // If untrusted cert chain isn't available, we only use CA cert as root cert.
  if(t.untrusted.compare("") == 0){
    server_cert_chain = CertsToStack({ca_cert.get()});
  }
  else {
    server_cert_chain = CertChainFromPEM(GetTestData(std::string("crypto/ocsp/test/openssl-ocsp/" + t.untrusted + ".pem").c_str()).c_str());
  }
  ASSERT_TRUE(server_cert_chain);

  // Does basic verification on OCSP response.
  const int ocsp_verify_status = OCSP_basic_verify(basic_response.get(), server_cert_chain.get(), trust_store.get(), 0);
  ASSERT_EQ(t.expected_ocsp_verify_status, ocsp_verify_status);
}
