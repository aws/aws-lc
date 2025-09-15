// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "test_util.h"
#include <openssl/pem.h>

void CreateAndSignX509Certificate(bssl::UniquePtr<X509> &x509,
                                  bssl::UniquePtr<EVP_PKEY> *pkey_p) {
  x509.reset(X509_new());
  if (!x509) {
    fprintf(stderr, "Error creating new X509 certificate\n");
    return;
  }

  // Set version to X509v3
  X509_set_version(x509.get(), X509_VERSION_3);

  // Set validity period for 30 days
  if (!X509_gmtime_adj(X509_getm_notBefore(x509.get()), 0) ||
      !X509_gmtime_adj(X509_getm_notAfter(x509.get()), 60 * 60 * 24 * 30L)) {
    fprintf(stderr, "Error setting expiration date\n");
    return;
  }

  EVP_PKEY *pkey = EVP_PKEY_new();

  if (!pkey) {
    fprintf(stderr, "Error creating new private key\n");
    return;
  }

  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn || !BN_set_word(bn.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr) ||
      !EVP_PKEY_assign_RSA(pkey, rsa.release())) {
    fprintf(stderr, "Error generating new key\n");
    return;
  }
  if (!X509_set_pubkey(x509.get(), pkey)) {
    fprintf(stderr, "Error setting public key\n");
    return;
  }

  X509_NAME *subject_name = X509_NAME_new();
  if (!X509_NAME_add_entry_by_NID(
          subject_name, NID_organizationName, MBSTRING_UTF8,
          reinterpret_cast<const unsigned char *>("Org"), /*len=*/-1,
          /*loc=*/-1,
          /*set=*/0) ||
      !X509_NAME_add_entry_by_NID(
          subject_name, NID_commonName, MBSTRING_UTF8,
          reinterpret_cast<const unsigned char *>("Name"), /*len=*/-1,
          /*loc=*/-1,
          /*set=*/0)) {
    fprintf(stderr, "Error creating a subject\n");
    return;
  }

  // self-signed
  if (!X509_set_subject_name(x509.get(), subject_name) ||
      !X509_set_issuer_name(x509.get(), subject_name)) {
    fprintf(stderr, "Error setting certificate subject and issuer\n");
    return;
  };
  X509_NAME_free(subject_name);

  // Add X509v3 extensions
  X509V3_CTX ctx;
  X509V3_set_ctx_nodb(&ctx);
  X509V3_set_ctx(&ctx, x509.get(), x509.get(), nullptr, nullptr, 0);

  X509_EXTENSION *ext;
  if (!(ext = X509V3_EXT_conf_nid(nullptr, &ctx, NID_basic_constraints,
                                  const_cast<char *>("critical,CA:TRUE"))) ||
      !X509_add_ext(x509.get(), ext, -1)) {
    fprintf(stderr, "Error setting extension\n");
    return;
  }

  if (!(ext = X509V3_EXT_conf_nid(nullptr, &ctx, NID_subject_key_identifier,
                                  const_cast<char *>("hash"))) ||
      !X509_add_ext(x509.get(), ext, -1)) {
    fprintf(stderr, "Error setting subject key identifier extension\n");
    return;
  }
  X509_EXTENSION_free(ext);

  if (X509_sign(x509.get(), pkey, EVP_sha256()) <= 0) {
    fprintf(stderr, "Error signing certificate\n");
    return;
  }

  if (pkey_p != nullptr) {
    pkey_p->reset(pkey);
  } else {
    EVP_PKEY_free(pkey);
  }
}

// Load a CSR from a PEM file
bssl::UniquePtr<X509_REQ> LoadCSR(const char *path) {
  bssl::UniquePtr<BIO> bio(BIO_new_file(path, "r"));
  if (!bio) {
    return NULL;
  }

  bssl::UniquePtr<X509_REQ> csr(
      PEM_read_bio_X509_REQ(bio.get(), nullptr, nullptr, nullptr));
  return csr;
}

// Load an X509 certificate from a PEM file
bssl::UniquePtr<X509> LoadPEMCertificate(const char *path) {
  bssl::UniquePtr<BIO> bio(BIO_new_file(path, "r"));
  if (!bio) {
    return NULL;
  }

  bssl::UniquePtr<X509> cert(
      PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
  return cert;
}

bool CompareCSRs(X509_REQ *csr1, X509_REQ *csr2) {
  if (!csr1 || !csr2)
    return false;

  // 1. Compare subjects
  X509_NAME *name1 = X509_REQ_get_subject_name(csr1);
  X509_NAME *name2 = X509_REQ_get_subject_name(csr2);
  if (X509_NAME_cmp(name1, name2) != 0)
    return false;

  // 2. Compare signature algorithms
  int sig_nid1 = X509_REQ_get_signature_nid(csr1);
  int sig_nid2 = X509_REQ_get_signature_nid(csr2);
  if (sig_nid1 != sig_nid2)
    return false;

  // 3. Compare public key type and parameters
  EVP_PKEY *pkey1 = X509_REQ_get0_pubkey(csr1);
  EVP_PKEY *pkey2 = X509_REQ_get0_pubkey(csr2);
  if (!pkey1 || !pkey2) {
    return false;
  }
  if (EVP_PKEY_id(pkey1) != EVP_PKEY_id(pkey2)) {
    return false;
  }

  // For RSA keys, check key size
  if (EVP_PKEY_id(pkey1) == EVP_PKEY_RSA) {
    RSA *rsa1 = EVP_PKEY_get0_RSA(pkey1);
    RSA *rsa2 = EVP_PKEY_get0_RSA(pkey2);
    if (!rsa1 || !rsa2) {
      return false;
    }
    if (RSA_size(rsa1) != RSA_size(rsa2)) {
      return false;
    }
  }

  // 4. Verify that both CSRs have valid signatures
  if (X509_REQ_verify(csr1, pkey1) != 1) {
    return false;
  }
  if (X509_REQ_verify(csr2, pkey2) != 1) {
    return false;
  }

  return true;
}

bool CheckCertificateValidityPeriod(X509 *cert, int expected_days) {
  if (!cert)
    return false;

  const ASN1_TIME *not_before = X509_get0_notBefore(cert);
  const ASN1_TIME *not_after = X509_get0_notAfter(cert);
  if (!not_before || !not_after)
    return false;

  // Get the difference in days between not_before and not_after
  int days, seconds;
  if (!ASN1_TIME_diff(&days, &seconds, not_before, not_after)) {
    return false;
  }

  return (days == expected_days);
}

// Improved certificate comparison function
bool CompareCertificates(X509 *cert1, X509 *cert2, X509 *ca_cert,
                         int expected_days) {
  if (!cert1 || !cert2 || !ca_cert) {
    return false;
  }

  // 1. Compare subjects
  X509_NAME *subj1 = X509_get_subject_name(cert1);
  X509_NAME *subj2 = X509_get_subject_name(cert2);
  if (X509_NAME_cmp(subj1, subj2) != 0) {
    return false;
  }

  // 2. Compare issuers
  X509_NAME *issuer1 = X509_get_issuer_name(cert1);
  X509_NAME *issuer2 = X509_get_issuer_name(cert2);
  if (X509_NAME_cmp(issuer1, issuer2) != 0) {
    return false;
  }

  // 3. Both certificates should be self-signed
  X509_NAME *ca_name = X509_get_issuer_name(ca_cert);
  if (X509_NAME_cmp(issuer1, ca_name) != 0) {
    return false;
  }
  if (X509_NAME_cmp(issuer2, ca_name) != 0) {
    return false;
  }

  // 4. Compare signature algorithms
  int sig_nid1 = X509_get_signature_nid(cert1);
  int sig_nid2 = X509_get_signature_nid(cert2);
  if (sig_nid1 != sig_nid2) {
    return false;
  }

  // 5. Check validity periods
  if (!CheckCertificateValidityPeriod(cert1, expected_days)) {
    return false;
  }
  if (!CheckCertificateValidityPeriod(cert2, expected_days)) {
    return false;
  }

  // 6. Check public key type and parameters
  EVP_PKEY *pkey1 = X509_get0_pubkey(cert1);
  EVP_PKEY *pkey2 = X509_get0_pubkey(cert2);
  if (!pkey1 || !pkey2) {
    return false;
  }

  if (EVP_PKEY_id(pkey1) != EVP_PKEY_id(pkey2)) {
    return false;
  }

  // For RSA keys, check key size
  if (EVP_PKEY_id(pkey1) == EVP_PKEY_RSA) {
    RSA *rsa1 = EVP_PKEY_get0_RSA(pkey1);
    RSA *rsa2 = EVP_PKEY_get0_RSA(pkey2);
    if (!rsa1 || !rsa2) {
      return false;
    }

    if (RSA_size(rsa1) != RSA_size(rsa2)) {
      return false;
    }
  }

  // 7. Verify signatures
  EVP_PKEY *ca_pkey = X509_get0_pubkey(ca_cert);
  if (X509_verify(cert1, ca_pkey) != 1) {
    return false;
  }

  if (X509_verify(cert2, ca_pkey) != 1) {
    return false;
  }
  // if (X509_verify(cert1, pkey1) != X509_verify(cert2, pkey2)) {
  //   return false;
  // }

  // 8. Compare extensions - simplified approach
  int ext_count1 = X509_get_ext_count(cert1);
  int ext_count2 = X509_get_ext_count(cert2);
  if (ext_count1 != ext_count2) {
    return false;
  }

  // Compare each extension by index (assuming same order)
  for (int i = 0; i < ext_count1; i++) {
    X509_EXTENSION *ext1 = X509_get_ext(cert1, i);
    X509_EXTENSION *ext2 = X509_get_ext(cert2, i);
    if (!ext1 || !ext2) {
      return false;
    }

    // Compare extension OIDs
    ASN1_OBJECT *obj1 = X509_EXTENSION_get_object(ext1);
    ASN1_OBJECT *obj2 = X509_EXTENSION_get_object(ext2);
    if (!obj1 || !obj2) {
      return false;
    }

    if (OBJ_cmp(obj1, obj2) != 0) {
      return false;
    }

    // Compare critical flags
    if (X509_EXTENSION_get_critical(ext1) !=
        X509_EXTENSION_get_critical(ext2)) {
      return false;
    }
  }

  return true;
}