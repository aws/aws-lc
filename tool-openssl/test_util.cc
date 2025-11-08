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

  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());

  if (!pkey) {
    fprintf(stderr, "Error creating new private key\n");
    return;
  }

  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn || !BN_set_word(bn.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr) ||
      !EVP_PKEY_assign_RSA(pkey.get(), rsa.release())) {
    fprintf(stderr, "Error generating new key\n");
    return;
  }
  if (!X509_set_pubkey(x509.get(), pkey.get())) {
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

  X509_EXTENSION *ext = nullptr;
  if (!(ext = X509V3_EXT_conf_nid(nullptr, &ctx, NID_basic_constraints,
                                  const_cast<char *>("critical,CA:TRUE"))) ||
      !X509_add_ext(x509.get(), ext, -1)) {
    fprintf(stderr, "Error setting extension\n");
    return;
  }
  X509_EXTENSION_free(ext);

  if (!(ext = X509V3_EXT_conf_nid(nullptr, &ctx, NID_subject_key_identifier,
                                  const_cast<char *>("hash"))) ||
      !X509_add_ext(x509.get(), ext, -1)) {
    fprintf(stderr, "Error setting subject key identifier extension\n");
    return;
  }
  X509_EXTENSION_free(ext);

  if (X509_sign(x509.get(), pkey.get(), EVP_sha256()) <= 0) {
    fprintf(stderr, "Error signing certificate\n");
    return;
  }

  if (pkey_p != nullptr) {
    pkey_p->reset(pkey.release());
  }
}

// Load a CSR from a PEM file
bssl::UniquePtr<X509_REQ> LoadPEMCSR(const char *path) {
  bssl::UniquePtr<BIO> bio(BIO_new_file(path, "r"));
  if (!bio) {
    return nullptr;
  }

  bssl::UniquePtr<X509_REQ> csr(
      PEM_read_bio_X509_REQ(bio.get(), nullptr, nullptr, nullptr));
  return csr;
}

// Load a CSR from a DER file
bssl::UniquePtr<X509_REQ> LoadDERCSR(const char *path) {
  bssl::UniquePtr<BIO> bio(BIO_new_file(path, "rb"));
  if (!bio) {
    return nullptr;
  }

  bssl::UniquePtr<X509_REQ> csr(d2i_X509_REQ_bio(bio.get(), nullptr));
  return csr;
}

// Load an X509 certificate from a PEM file
bssl::UniquePtr<X509> LoadPEMCertificate(const char *path) {
  bssl::UniquePtr<BIO> bio(BIO_new_file(path, "r"));
  if (!bio) {
    return nullptr;
  }

  bssl::UniquePtr<X509> cert(
      PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
  return cert;
}

// Load an X509 certificate from a DER file
bssl::UniquePtr<X509> LoadDERCertificate(const char *path) {
  bssl::UniquePtr<BIO> bio(BIO_new_file(path, "r"));
  if (!bio) {
    return nullptr;
  }

  bssl::UniquePtr<X509> cert(d2i_X509_bio(bio.get(), nullptr));
  return cert;
}

bool CompareCSRs(X509_REQ *csr1, X509_REQ *csr2) {
  if (!csr1 || !csr2) {
    std::cout << "Invalid CSRs" << std::endl;
    return false;
  }

  // 1. Compare subjects
  X509_NAME *name1 = X509_REQ_get_subject_name(csr1);
  X509_NAME *name2 = X509_REQ_get_subject_name(csr2);

  if (!name1 || !name2) {
    return false;
  }

  int count1 = X509_NAME_entry_count(name1);
  int count2 = X509_NAME_entry_count(name2);
  if (count1 < 0 || count2 < 0) {
    return false;
  }

  if (count1 != count2) {
    std::cout << "CSRs have different number of subject entries" << std::endl;
    return false;
  }

  // Check each entry in AWS-LC's CSR exists in OpenSSL's CSR
  for (int i = 0; i < count1; i++) {
    X509_NAME_ENTRY *entry1 = X509_NAME_get_entry(name1, i);
    ASN1_OBJECT *obj1 = X509_NAME_ENTRY_get_object(entry1);
    ASN1_STRING *data1 = X509_NAME_ENTRY_get_data(entry1);

    int idx = X509_NAME_get_index_by_OBJ(name2, obj1, -1);
    if (idx < 0) {
      std::cout << "AWS-LC contains an entry for "
                << OBJ_nid2ln(OBJ_obj2nid(obj1))
                << " that is not present in OpenSSL's CSR" << std::endl;
      return false;
    }

    X509_NAME_ENTRY *entry2 = X509_NAME_get_entry(name2, idx);
    ASN1_STRING *data2 = X509_NAME_ENTRY_get_data(entry2);

    if (ASN1_STRING_cmp(data1, data2) != 0) {
      std::cout << "CSRs have different values for entry "
                << OBJ_nid2ln(OBJ_obj2nid(obj1)) << std::endl;
      return false;
    }
  }

  // 2. Compare signature algorithms
  int sig_nid1 = X509_REQ_get_signature_nid(csr1);
  int sig_nid2 = X509_REQ_get_signature_nid(csr2);
  if (sig_nid1 != sig_nid2) {
    std::cout << "CSRs use different signature algorithms" << std::endl;
    return false;
  }

  // 3. Compare public key type and parameters
  EVP_PKEY *pkey1 = X509_REQ_get0_pubkey(csr1);
  EVP_PKEY *pkey2 = X509_REQ_get0_pubkey(csr2);
  if (!pkey1 || !pkey2) {
    std::cout << "CSRs have different public keys" << std::endl;
    return false;
  }
  if (EVP_PKEY_id(pkey1) != EVP_PKEY_id(pkey2)) {
    std::cout << "CSRs have different public key types" << std::endl;
    return false;
  }

  // For RSA keys, check key size
  if (EVP_PKEY_id(pkey1) == EVP_PKEY_RSA) {
    RSA *rsa1 = EVP_PKEY_get0_RSA(pkey1);
    RSA *rsa2 = EVP_PKEY_get0_RSA(pkey2);
    if (!rsa1 || !rsa2) {
      std::cout << "Failed to obtain RSA keys from CSRs" << std::endl;
      return false;
    }
    if (RSA_size(rsa1) != RSA_size(rsa2)) {
      std::cout << "CSRs have different RSA key sizes" << std::endl;
      return false;
    }
  }

  // 4. Verify that both CSRs have valid signatures
  if (X509_REQ_verify(csr1, pkey1) != 1) {
    std::cout << "AWS-LC CSR has invalid signature" << std::endl;
    return false;
  }
  if (X509_REQ_verify(csr2, pkey2) != 1) {
    std::cout << "OpenSSL CSR has invalid signature" << std::endl;
    return false;
  }

  return true;
}

bool CheckCertificateValidityPeriod(X509 *cert, int expected_days) {
  if (!cert) {
    return false;
  }

  const ASN1_TIME *not_before = X509_get0_notBefore(cert);
  const ASN1_TIME *not_after = X509_get0_notAfter(cert);
  if (!not_before || !not_after) {
    return false;
  }

  // Get the difference in days between not_before and not_after
  int days = 0, seconds = 0;
  if (!ASN1_TIME_diff(&days, &seconds, not_before, not_after)) {
    return false;
  }

  return (days == expected_days);
}

// Improved certificate comparison function
bool CompareCertificates(X509 *cert1, X509 *cert2, X509 *ca_cert,
                         int expected_days) {
  if (!cert1 || !cert2) {
    std::cout << "Invalid certificates" << std::endl;
    return false;
  }

  // 1. Compare subjects
  X509_NAME *subj1 = X509_get_subject_name(cert1);
  X509_NAME *subj2 = X509_get_subject_name(cert2);
  if (X509_NAME_cmp(subj1, subj2) != 0) {
    std::cout << "Certificates have different subject names" << std::endl;
    return false;
  }

  // 2. Compare issuers
  X509_NAME *issuer1 = X509_get_issuer_name(cert1);
  X509_NAME *issuer2 = X509_get_issuer_name(cert2);
  if (X509_NAME_cmp(issuer1, issuer2) != 0) {
    std::cout << "Certificates have different issuer names" << std::endl;
    return false;
  }

  // 3. Validate issuers
  if (ca_cert) {
    X509_NAME *ca_name = X509_get_issuer_name(ca_cert);
    if (X509_NAME_cmp(issuer1, ca_name) != 0) {
      std::cout << "AWS-LC certificate has the wrong issuer name" << std::endl;
      return false;
    }
    if (X509_NAME_cmp(issuer2, ca_name) != 0) {
      std::cout << "OpenSSL certificate has the wrong issuer name" << std::endl;
      return false;
    }
  } else {
    if (X509_NAME_cmp(subj1, issuer1) != 0) {
      std::cout << "Issuer and subject names do not match for AWS-LC's "
                   "self-signed certificate"
                << std::endl;
      return false;
    }
    if (X509_NAME_cmp(subj2, issuer2) != 0) {
      std::cout << "Issuer and subject names do not match for OpenSSL's "
                   "self-signed certificate"
                << std::endl;
      return false;
    }
  }

  // 4. Compare signature algorithms
  int sig_nid1 = X509_get_signature_nid(cert1);
  int sig_nid2 = X509_get_signature_nid(cert2);
  if (sig_nid1 != sig_nid2) {
    std::cout << "Certificates use different signature algorithms" << std::endl;
    return false;
  }

  // 5. Check validity periods
  if (!CheckCertificateValidityPeriod(cert1, expected_days)) {
    std::cout
        << "AWS-LC certificate's validity period is different than expected"
        << std::endl;
    return false;
  }
  if (!CheckCertificateValidityPeriod(cert2, expected_days)) {
    std::cout
        << "OpenSSL certificate's validity period is different than expected"
        << std::endl;
    return false;
  }

  // 6. Check public key type and parameters
  EVP_PKEY *pkey1 = X509_get0_pubkey(cert1);
  EVP_PKEY *pkey2 = X509_get0_pubkey(cert2);
  if (!pkey1 || !pkey2) {
    std::cout << "Certificates have different public keys" << std::endl;
    return false;
  }

  if (EVP_PKEY_id(pkey1) != EVP_PKEY_id(pkey2)) {
    std::cout << "Certificates have different public key types" << std::endl;
    return false;
  }

  // For RSA keys, check key size
  if (EVP_PKEY_id(pkey1) == EVP_PKEY_RSA) {
    RSA *rsa1 = EVP_PKEY_get0_RSA(pkey1);
    RSA *rsa2 = EVP_PKEY_get0_RSA(pkey2);
    if (!rsa1 || !rsa2) {
      std::cout << "Failed to obtain RSA keys from certificates" << std::endl;
      return false;
    }

    if (RSA_size(rsa1) != RSA_size(rsa2)) {
      std::cout << "Certificates have different RSA key sizes" << std::endl;
      return false;
    }
  }

  // 7. Verify signatures
  if (ca_cert) {
    EVP_PKEY *ca_pkey = X509_get0_pubkey(ca_cert);
    if (!ca_pkey) {
      std::cout << "Failed to parse CA public key" << std::endl;
      return false;
    }

    if (X509_verify(cert1, ca_pkey) != 1) {
      std::cout << "Signature verification failed for AWS-LC's certificate"
                << std::endl;
      return false;
    }

    if (X509_verify(cert2, ca_pkey) != 1) {
      std::cout << "Signature verification failed for OpenSSL's certificate"
                << std::endl;
      return false;
    }
  } else {
    if (X509_verify(cert1, pkey1) != 1) {
      std::cout << "Signature verification failed for AWS-LC's certificate"
                << std::endl;
      return false;
    }

    if (X509_verify(cert2, pkey2) != 1) {
      std::cout << "Signature verification failed for OpenSSL's certificate"
                << std::endl;
      return false;
    }
  }

  // 8. Compare extensions - simplified approach
  // Skip extension count check if OpenSSL version <= 3.1
  int ext_count1 = X509_get_ext_count(cert1);
  int ext_count2 = X509_get_ext_count(cert2);

  const char *openssl_version = getenv("OPENSSL_TOOL_VERSION");
  if (openssl_version && strcmp(openssl_version, "3.1") > 0) {
    if (ext_count1 != ext_count2) {
      std::cout << "Certificates have different extension counts" << std::endl;
      return false;
    }
  }

  // Check for duplicate extension in AWS-LC's certificate
  std::set<int> cert1_nids;
  std::set<int> cert2_nids;
  for (int i = 0; i < ext_count1; i++) {
    X509_EXTENSION *ext = X509_get_ext(cert1, i);
    if (!ext) {
      std::cout << "Failed to obtain extension from AWS-LC's certificate"
                << std::endl;
      return false;
    }
    int nid = OBJ_obj2nid(X509_EXTENSION_get_object(ext));
    if (!cert1_nids.insert(nid).second) {
      std::cout << "AWS-LC's certificate has duplicate extensions" << std::endl;
      return false;
    }
  }

  for (int i = ext_count2 - 1; i >= 0; i--) {
    X509_EXTENSION *ext2 = X509_get_ext(cert2, i);
    if (!ext2) {
      std::cout << "Failed to obtain extension from OpenSSL's certificate"
                << std::endl;
      return false;
    }

    int nid2 = OBJ_obj2nid(X509_EXTENSION_get_object(ext2));

    // OpenSSL<=3.1 does not clear existing extensions, resulting in duplicates.
    // Skip over those duplicates
    if (openssl_version && strcmp(openssl_version, "1.1.1") == 0) {
      if (!cert2_nids.insert(nid2).second) {
        continue;
      }
    }

    int idx = X509_get_ext_by_NID(cert1, nid2, -1);
    if (idx < 0) {
      std::cout << "Extension " << OBJ_nid2sn(nid2)
                << " present in OpenSSL's certificate but missing in AWS-LC's "
                   "certificate"
                << std::endl;
      return false;
    }
    X509_EXTENSION *ext1 = X509_get_ext(cert1, idx);

    // Compare extension OIDs
    ASN1_OBJECT *obj1 = X509_EXTENSION_get_object(ext1);
    ASN1_OBJECT *obj2 = X509_EXTENSION_get_object(ext2);
    if (!obj1 || !obj2) {
      std::cout << "Failed to obtain extension OID" << std::endl;
      return false;
    }

    if (OBJ_cmp(obj1, obj2) != 0) {
      std::cout << "Extension content within the certificates do not match"
                << std::endl;
      return false;
    }

    // Compare critical flags
    if (X509_EXTENSION_get_critical(ext1) !=
        X509_EXTENSION_get_critical(ext2)) {
      std::cout << "Certificates have different extension critical flags"
                << std::endl;
      return false;
    }
  }
  return true;
}

// Helper function to decrypt a private key from a file
EVP_PKEY *DecryptPrivateKey(const char *path, const char *password) {
  if (!path) {
    return nullptr;
  }

  // Use a BIO for better compatibility
  bssl::UniquePtr<BIO> bio(BIO_new_file(path, "r"));
  if (!bio) {
    return nullptr;
  }

  EVP_PKEY *pkey = PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr,
                                           const_cast<char *>(password));
  return pkey;
}

bool CompareKeyEquality(EVP_PKEY *key1, EVP_PKEY *key2) {
  // Early return if either pointer is null or keys are different types
  if (!key1 || !key2 || EVP_PKEY_id(key1) != EVP_PKEY_id(key2)) {
    std::cout << "Keys are different" << std::endl;
    return false;
  }

  // Check if keys are RSA type
  if (EVP_PKEY_id(key1) != EVP_PKEY_RSA) {
    std::cout << "AWS-LC key is not an RSA key" << std::endl;
    return false;
  }

  if (EVP_PKEY_id(key2) != EVP_PKEY_RSA) {
    std::cout << "OpenSSL key is not an RSA key" << std::endl;
    return false;
  }

  // Get RSA structures
  const RSA *rsa1 = EVP_PKEY_get0_RSA(key1);
  const RSA *rsa2 = EVP_PKEY_get0_RSA(key2);
  if (!rsa1 || !rsa2) {
    std::cout << "Failed to obtain RSA keys" << std::endl;
    return false;
  }

  // Get key components
  const BIGNUM *n1 = nullptr, *e1 = nullptr, *d1 = nullptr;
  const BIGNUM *n2 = nullptr, *e2 = nullptr, *d2 = nullptr;
  RSA_get0_key(rsa1, &n1, &e1, &d1);
  RSA_get0_key(rsa2, &n2, &e2, &d2);

  // Compare modulus first as it's most likely to be different
  if (BN_cmp(n1, n2) != 0) {
    std::cout << "Modulus of keys do not match" << std::endl;
    return false;
  }

  // Compare public exponent next (usually smaller)
  if (BN_cmp(e1, e2) != 0) {
    std::cout << "Public exponents of keys do not match" << std::endl;
    return false;
  }

  // Finally compare private exponent
  return BN_cmp(d1, d2) == 0;
}

bool CompareRandomGeneratedKeys(EVP_PKEY *key1, EVP_PKEY *key2,
                                unsigned int expected_bits) {
  if (!key1 || !key2 || EVP_PKEY_id(key1) != EVP_PKEY_id(key2)) {
    std::cout << "Keys are different" << std::endl;
    return false;
  }

  // Check if keys are RSA type
  if (EVP_PKEY_id(key1) != EVP_PKEY_RSA) {
    std::cout << "AWS-LC key is not an RSA key" << std::endl;
    return false;
  }

  if (EVP_PKEY_id(key2) != EVP_PKEY_RSA) {
    std::cout << "OpenSSL key is not an RSA key" << std::endl;
    return false;
  }

  // Get RSA structures
  const RSA *rsa1 = EVP_PKEY_get0_RSA(key1);
  const RSA *rsa2 = EVP_PKEY_get0_RSA(key2);
  if (!rsa1 || !rsa2) {
    std::cout << "Failed to obtain RSA keys" << std::endl;
    return false;
  }

  if (RSA_bits(rsa1) != expected_bits) {
    std::cout << "AWS-LC key has " << RSA_bits(rsa1) << " bits, expected "
              << expected_bits << std::endl;
    return false;
  }

  if (RSA_bits(rsa2) != expected_bits) {
    std::cout << "OpenSSL key has " << RSA_bits(rsa2) << " bits, expected "
              << expected_bits << std::endl;
    return false;
  }

  return true;
}
