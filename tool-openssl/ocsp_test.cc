// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bn.h>
#include <openssl/evp.h>
#include <openssl/ocsp.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>
#include <stdio.h>

#include <gtest/gtest.h>

#include "internal.h"
#include "test_util.h"

class OcspTest : public ::testing::Test {
 protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(ca_cert_path), 0u);
    ASSERT_GT(createTempFILEpath(ca_key_path), 0u);
    ASSERT_GT(createTempFILEpath(leaf_cert_path), 0u);
    ASSERT_GT(createTempFILEpath(index_path), 0u);
    ASSERT_GT(createTempFILEpath(reqout_path), 0u);
    ASSERT_GT(createTempFILEpath(respout_path), 0u);
    CreateCerts();
  }

  void TearDown() override {
    RemoveFile(ca_cert_path);
    RemoveFile(ca_key_path);
    RemoveFile(leaf_cert_path);
    RemoveFile(index_path);
    RemoveFile(reqout_path);
    RemoveFile(respout_path);
  }

  static bssl::UniquePtr<EVP_PKEY> MakeRsaKey() {
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    bssl::UniquePtr<RSA> rsa(RSA_new());
    bssl::UniquePtr<BIGNUM> e(BN_new());
    if (!pkey || !rsa || !e || !BN_set_word(e.get(), RSA_F4) ||
        !RSA_generate_key_ex(rsa.get(), 2048, e.get(), nullptr) ||
        !EVP_PKEY_assign_RSA(pkey.get(), rsa.release())) {
      return nullptr;
    }
    return pkey;
  }

  void CreateCerts() {
    ca_key_ = MakeRsaKey();
    ASSERT_TRUE(ca_key_);
    leaf_key_ = MakeRsaKey();
    ASSERT_TRUE(leaf_key_);

    ca_cert_.reset(X509_new());
    ASSERT_TRUE(ca_cert_);
    ASSERT_TRUE(X509_set_version(ca_cert_.get(), 2));
    bssl::UniquePtr<ASN1_INTEGER> ca_serial(ASN1_INTEGER_new());
    ASSERT_TRUE(ca_serial && ASN1_INTEGER_set(ca_serial.get(), 1));
    ASSERT_TRUE(X509_set_serialNumber(ca_cert_.get(), ca_serial.get()));
    ASSERT_TRUE(X509_gmtime_adj(X509_getm_notBefore(ca_cert_.get()), 0));
    ASSERT_TRUE(
        X509_gmtime_adj(X509_getm_notAfter(ca_cert_.get()), 365 * 24 * 3600));
    bssl::UniquePtr<X509_NAME> ca_name(X509_NAME_new());
    ASSERT_TRUE(ca_name);
    ASSERT_TRUE(X509_NAME_add_entry_by_txt(ca_name.get(), "CN", MBSTRING_ASC,
                                           (const uint8_t *)"Test OCSP CA", -1,
                                           -1, 0));
    ASSERT_TRUE(X509_set_subject_name(ca_cert_.get(), ca_name.get()));
    ASSERT_TRUE(X509_set_issuer_name(ca_cert_.get(), ca_name.get()));
    ASSERT_TRUE(X509_set_pubkey(ca_cert_.get(), ca_key_.get()));
    ASSERT_TRUE(X509_sign(ca_cert_.get(), ca_key_.get(), EVP_sha256()));

    leaf_.reset(X509_new());
    ASSERT_TRUE(leaf_);
    ASSERT_TRUE(X509_set_version(leaf_.get(), 2));
    bssl::UniquePtr<ASN1_INTEGER> leaf_serial(ASN1_INTEGER_new());
    // 0x1000 so BN_bn2hex yields "1000", matching the index serial field.
    ASSERT_TRUE(leaf_serial && ASN1_INTEGER_set(leaf_serial.get(), 0x1000));
    ASSERT_TRUE(X509_set_serialNumber(leaf_.get(), leaf_serial.get()));
    ASSERT_TRUE(X509_gmtime_adj(X509_getm_notBefore(leaf_.get()), 0));
    ASSERT_TRUE(X509_gmtime_adj(X509_getm_notAfter(leaf_.get()), 365 * 24 * 3600));
    bssl::UniquePtr<X509_NAME> leaf_name(X509_NAME_new());
    ASSERT_TRUE(leaf_name);
    ASSERT_TRUE(X509_NAME_add_entry_by_txt(leaf_name.get(), "CN", MBSTRING_ASC,
                                           (const uint8_t *)"end", -1, -1, 0));
    ASSERT_TRUE(X509_set_subject_name(leaf_.get(), leaf_name.get()));
    ASSERT_TRUE(X509_set_issuer_name(leaf_.get(),
                                     X509_get_subject_name(ca_cert_.get())));
    ASSERT_TRUE(X509_set_pubkey(leaf_.get(), leaf_key_.get()));
    ASSERT_TRUE(X509_sign(leaf_.get(), ca_key_.get(), EVP_sha256()));

    WritePEMCert(ca_cert_path, ca_cert_.get());
    WritePEMKey(ca_key_path, ca_key_.get());
    WritePEMCert(leaf_cert_path, leaf_.get());
  }

  static void WritePEMCert(const char *path, X509 *cert) {
    ScopedFILE f(fopen(path, "wb"));
    ASSERT_TRUE(f);
    ASSERT_TRUE(PEM_write_X509(f.get(), cert));
  }

  static void WritePEMKey(const char *path, EVP_PKEY *key) {
    ScopedFILE f(fopen(path, "wb"));
    ASSERT_TRUE(f);
    ASSERT_TRUE(
        PEM_write_PrivateKey(f.get(), key, nullptr, nullptr, 0, nullptr, nullptr));
  }

  void WriteIndex(char type) {
    ScopedFILE f(fopen(index_path, "w"));
    ASSERT_TRUE(f);
    if (type == 'R') {
      fprintf(f.get(),
              "R\t350101000000Z\t250101000000Z\t1000\tunknown\t/CN=end\n");
    } else if (type == 'V') {
      fprintf(f.get(), "V\t350101000000Z\t\t1000\tunknown\t/CN=end\n");
    } else {
      // An entry for an unrelated serial, so the leaf is absent.
      fprintf(f.get(), "V\t350101000000Z\t\t2000\tunknown\t/CN=other\n");
    }
  }

  bssl::UniquePtr<OCSP_CERTID> LeafId() {
    return bssl::UniquePtr<OCSP_CERTID>(
        OCSP_cert_to_id(nullptr, leaf_.get(), ca_cert_.get()));
  }

  void BuildRequest() {
    args_list_t args = {"-issuer", ca_cert_path, "-cert", leaf_cert_path,
                        "-reqout", reqout_path};
    ASSERT_EQ(kToolExitSuccess, ocspTool(args));
  }

  int RespondAndFindLeafStatus() {
    args_list_t args = {"-reqin",   reqout_path, "-index",   index_path,
                        "-CA",      ca_cert_path, "-rsigner", ca_cert_path,
                        "-rkey",    ca_key_path,  "-respout", respout_path,
                        "-ndays",   "1"};
    EXPECT_EQ(kToolExitSuccess, ocspTool(args));

    bssl::UniquePtr<BIO> bio(BIO_new_file(respout_path, "rb"));
    EXPECT_TRUE(bio);
    bssl::UniquePtr<OCSP_RESPONSE> resp(
        d2i_OCSP_RESPONSE_bio(bio.get(), nullptr));
    EXPECT_TRUE(resp);
    EXPECT_EQ(OCSP_RESPONSE_STATUS_SUCCESSFUL,
              OCSP_response_status(resp.get()));
    bssl::UniquePtr<OCSP_BASICRESP> basic(
        OCSP_response_get1_basic(resp.get()));
    EXPECT_TRUE(basic);
    bssl::UniquePtr<OCSP_CERTID> id = LeafId();
    EXPECT_TRUE(id);
    int status = -1, reason = 0;
    ASN1_GENERALIZEDTIME *revtime = nullptr, *thisupd = nullptr,
                         *nextupd = nullptr;
    if (!OCSP_resp_find_status(basic.get(), id.get(), &status, &reason,
                               &revtime, &thisupd, &nextupd)) {
      return -1;
    }
    return status;
  }

  char ca_cert_path[PATH_MAX];
  char ca_key_path[PATH_MAX];
  char leaf_cert_path[PATH_MAX];
  char index_path[PATH_MAX];
  char reqout_path[PATH_MAX];
  char respout_path[PATH_MAX];
  bssl::UniquePtr<EVP_PKEY> ca_key_;
  bssl::UniquePtr<EVP_PKEY> leaf_key_;
  bssl::UniquePtr<X509> ca_cert_;
  bssl::UniquePtr<X509> leaf_;
};

TEST_F(OcspTest, RequestContainsRequestedCertificate) {
  BuildRequest();

  bssl::UniquePtr<BIO> bio(BIO_new_file(reqout_path, "rb"));
  ASSERT_TRUE(bio);
  bssl::UniquePtr<OCSP_REQUEST> req(d2i_OCSP_REQUEST_bio(bio.get(), nullptr));
  ASSERT_TRUE(req);
  EXPECT_EQ(1, OCSP_request_onereq_count(req.get()));
}

TEST_F(OcspTest, RespondsGoodForValidCertificate) {
  BuildRequest();
  WriteIndex('V');
  EXPECT_EQ(V_OCSP_CERTSTATUS_GOOD, RespondAndFindLeafStatus());
}

TEST_F(OcspTest, RespondsRevokedForRevokedCertificate) {
  BuildRequest();
  WriteIndex('R');
  EXPECT_EQ(V_OCSP_CERTSTATUS_REVOKED, RespondAndFindLeafStatus());
}

TEST_F(OcspTest, RespondsUnknownForAbsentCertificate) {
  BuildRequest();
  WriteIndex('X');  // index without the leaf's serial
  EXPECT_EQ(V_OCSP_CERTSTATUS_UNKNOWN, RespondAndFindLeafStatus());
}

TEST_F(OcspTest, FailsWithoutOperation) {
  args_list_t args = {"-issuer", ca_cert_path, "-cert", leaf_cert_path};
  EXPECT_EQ(kToolExitFailure, ocspTool(args));
}

// Negative: request mode needs both -issuer and -cert.
TEST_F(OcspTest, RequestRequiresIssuerAndCert) {
  args_list_t args = {"-issuer", ca_cert_path, "-reqout", reqout_path};
  EXPECT_EQ(kToolExitFailure, ocspTool(args));
}

// Negative: responder mode needs all of -reqin/-index/-CA/-rsigner/-rkey.
TEST_F(OcspTest, ResponderRequiresAllInputs) {
  BuildRequest();
  args_list_t args = {"-reqin",   reqout_path,  "-index",   index_path,
                      "-CA",      ca_cert_path, "-rsigner", ca_cert_path,
                      "-respout", respout_path};  // no -rkey
  EXPECT_EQ(kToolExitFailure, ocspTool(args));
}

// Negative: a request that is not a valid DER OCSP request is rejected.
TEST_F(OcspTest, ResponderRejectsCorruptRequest) {
  {
    ScopedFILE f(fopen(reqout_path, "wb"));
    ASSERT_TRUE(f);
    ASSERT_EQ(4u, fwrite("junk", 1, 4, f.get()));
  }
  WriteIndex('V');
  args_list_t args = {"-reqin",   reqout_path,  "-index",   index_path,
                      "-CA",      ca_cert_path, "-rsigner", ca_cert_path,
                      "-rkey",    ca_key_path,  "-respout", respout_path,
                      "-ndays",   "1"};
  EXPECT_EQ(kToolExitFailure, ocspTool(args));
}

// Negative: a missing responder key file is an error.
TEST_F(OcspTest, FailsOnMissingKeyFile) {
  BuildRequest();
  WriteIndex('V');
  args_list_t args = {"-reqin",   reqout_path,
                      "-index",   index_path,
                      "-CA",      ca_cert_path,
                      "-rsigner", ca_cert_path,
                      "-rkey",    "/nonexistent/responder_key.pem",
                      "-respout", respout_path,
                      "-ndays",   "1"};
  EXPECT_EQ(kToolExitFailure, ocspTool(args));
}

// Positive: the response is actually signed by the responder key.
TEST_F(OcspTest, ResponseIsSignedByResponder) {
  BuildRequest();
  WriteIndex('V');
  args_list_t args = {"-reqin",   reqout_path,  "-index",   index_path,
                      "-CA",      ca_cert_path, "-rsigner", ca_cert_path,
                      "-rkey",    ca_key_path,  "-respout", respout_path,
                      "-ndays",   "1"};
  ASSERT_EQ(kToolExitSuccess, ocspTool(args));

  bssl::UniquePtr<BIO> bio(BIO_new_file(respout_path, "rb"));
  ASSERT_TRUE(bio);
  bssl::UniquePtr<OCSP_RESPONSE> resp(d2i_OCSP_RESPONSE_bio(bio.get(), nullptr));
  ASSERT_TRUE(resp);
  bssl::UniquePtr<OCSP_BASICRESP> basic(OCSP_response_get1_basic(resp.get()));
  ASSERT_TRUE(basic);

  bssl::UniquePtr<STACK_OF(X509)> certs(sk_X509_new_null());
  ASSERT_TRUE(certs);
  ASSERT_TRUE(X509_up_ref(ca_cert_.get()));
  ASSERT_TRUE(sk_X509_push(certs.get(), ca_cert_.get()));
  bssl::UniquePtr<X509_STORE> store(X509_STORE_new());
  ASSERT_TRUE(store);
  // OCSP_NOVERIFY checks the signature without validating the signer chain.
  EXPECT_EQ(1, OCSP_basic_verify(basic.get(), certs.get(), store.get(),
                                 OCSP_NOVERIFY));
}

// Positive: a revoked status carries a revocation time.
TEST_F(OcspTest, RevokedResponseHasRevocationTime) {
  BuildRequest();
  WriteIndex('R');
  args_list_t args = {"-reqin",   reqout_path,  "-index",   index_path,
                      "-CA",      ca_cert_path, "-rsigner", ca_cert_path,
                      "-rkey",    ca_key_path,  "-respout", respout_path,
                      "-ndays",   "1"};
  ASSERT_EQ(kToolExitSuccess, ocspTool(args));

  bssl::UniquePtr<BIO> bio(BIO_new_file(respout_path, "rb"));
  ASSERT_TRUE(bio);
  bssl::UniquePtr<OCSP_RESPONSE> resp(d2i_OCSP_RESPONSE_bio(bio.get(), nullptr));
  ASSERT_TRUE(resp);
  bssl::UniquePtr<OCSP_BASICRESP> basic(OCSP_response_get1_basic(resp.get()));
  ASSERT_TRUE(basic);
  bssl::UniquePtr<OCSP_CERTID> id = LeafId();
  ASSERT_TRUE(id);

  int status = -1, reason = 0;
  ASN1_GENERALIZEDTIME *revtime = nullptr, *thisupd = nullptr,
                       *nextupd = nullptr;
  ASSERT_TRUE(OCSP_resp_find_status(basic.get(), id.get(), &status, &reason,
                                    &revtime, &thisupd, &nextupd));
  EXPECT_EQ(V_OCSP_CERTSTATUS_REVOKED, status);
  EXPECT_NE(nullptr, revtime);
}
