// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <cstdint>
#include <cstring>

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/pkcs7.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>

static const char kCert[] = R"(
-----BEGIN CERTIFICATE-----
MIIFazCCA1OgAwIBAgIURVkPzF/4dwy7419Qk75uhIuyf0EwDQYJKoZIhvcNAQEL
BQAwRTELMAkGA1UEBhMCQVUxEzARBgNVBAgMClNvbWUtU3RhdGUxITAfBgNVBAoM
GEludGVybmV0IFdpZGdpdHMgUHR5IEx0ZDAeFw0yMTA5MjExOTIyMTJaFw0yMjA5
MjExOTIyMTJaMEUxCzAJBgNVBAYTAkFVMRMwEQYDVQQIDApTb21lLVN0YXRlMSEw
HwYDVQQKDBhJbnRlcm5ldCBXaWRnaXRzIFB0eSBMdGQwggIiMA0GCSqGSIb3DQEB
AQUAA4ICDwAwggIKAoICAQC1+MOn+BopcEVR4QMvjXdAxGkWFllXyQFDToL+qOiP
RU1yN7C8KCtkbOAFttJIO4O/i0iZ7KqYbnmB6YUA/ONAcakocnrdoESgRJcVMeAx
Dk/11OtMF5yIfeOOO/TUeVNmAUaT63gFbKy/adpqhzJtOv9BBl5VcYNGGSE+0wtb
mjpmNsxunEQR1KLDc97fGYHeRfKoSyrCIEE8IaAEpKGR2Sku3v9Jwh7RpjupgiUA
kH6pJk7VMZm5vl2wFjYvfysgjeN5ZtsxFDMaPYZStpxMxpNd5C9DsO2Ljp5NMpGf
NGmG4ZqiaQg8z2cIM6ESmN1zDJdUh5IXed1fOxBZD/poUFH0wDRFWnvzlaPmjJEF
rYLMK8svnE5nEQp9vu93ISFBx7cofs+niMaUXPEqaRSqruifN2M1it3kOf/8YZl1
vurs+VtHD6nOJo6bd11+37aBidIB/BaWnzLrDmSTcPFa1tkTHwoLqc9+jThTq9jZ
6w3lAMPpsoenyD19UmQB589+4kNp2SIO/TtzVQCGgQPXE2jDCl6G9aIPMkfvpPZK
4THVil3WQRCFYnYdDO4HQXo2ZuC4RiqgY5ygfeoL+fa9k383lgxxAHQLS7xsbaVB
40RmfdbdevgPYIwZNNO78ddRmMdSv6IknSW9gydGzY//btY+t1SWcBZWzn1Ewq8g
2QIDAQABo1MwUTAdBgNVHQ4EFgQUotZD9ajEvnQYVezIWzcW4pzvMcUwHwYDVR0j
BBgwFoAUotZD9ajEvnQYVezIWzcW4pzvMcUwDwYDVR0TAQH/BAUwAwEB/zANBgkq
hkiG9w0BAQsFAAOCAgEAqCe42PIWoyLDx9bR+5cSp99N5xo5lLiSLtWx2emDbZB2
AunqKYeEgIV+TWNF2w1SZ/ckFgV7SlL2Yl73N/veSNRfNAnpjLksGDFpdJb7YXrx
cUvxdy1mr8oau6J7PC9JGjBTBrnhqwCQX1FtcAxODKll2Lsfuj6+bdC3rCK7KBEo
ENamMJZIeo8lRP9qFF2xwCEzZjRv2zvB6O5o9045aTUcdCrwUfKE2sqY6EXRzFTC
waK0HRCd1FLv9omhz/Ug5PMHP4d6MZfnAbFm+AzAhnpkrk/9TJYSOoNTNLWsuqhp
dN0rKqiFWv1zIwfknXvTh1P1Ap+G5jffAca0zWUH1oKjE7ZZioSsaZ6gySnD8+WQ
TPbOYtG+n0mhCH1TrU8Dqi3rd8g5IbC8loYLRH94QtodOnevD4Qo9Orfrsr8hGOW
ABespanZArhoQ03DAtpNhtHm2NWJQF2uHNqcTrkq0omqZBTbMD1GKMBujoNooAUu
w51U9r+RycPJTFqEGHb0nd7EjoyXEXtuX1Ld5fTZjQ9SszmQKQ8w3lHqRGNlkSiO
e3IOOq2ruXmq1jykxpmi82IcTRUE8TZBfL/yz0nxpHKAYC1VwMezrkgZDGz4npxf
1z2+qd58xU6/jsf7/+3xdPFubeEJujdbCkWQsQC5Rzm48zDWGq/pyzFji44K3TA=
-----END CERTIFICATE-----
)";

class SharedData {
public:
  X509_STORE *store = nullptr;
  STACK_OF(X509) *certs = nullptr;

  SharedData() {
    X509 *cert = nullptr;
    {
      BIO *cert_bio = BIO_new_mem_buf(const_cast<char *>(kCert), sizeof(kCert) - 1);
      cert = PEM_read_bio_X509(cert_bio, nullptr, nullptr, nullptr);
      BIO_free(cert_bio);
    }
    store = X509_STORE_new();
    if (!store) {
      abort();
    }
    if (!X509_STORE_add_cert(store, cert)) {
      abort();
    }
    certs = sk_X509_new_null();
    if (!certs || !sk_X509_unshift(certs, cert)) {
      abort();
    }
    X509_free(cert);
  }

  ~SharedData() {
    X509_STORE_free(store);
    sk_X509_free(certs);
  }
};

static SharedData sharedData;

OPENSSL_BEGIN_ALLOW_DEPRECATED
extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  BIO* data_bio = nullptr;

  PKCS7 *pkcs7 = d2i_PKCS7(nullptr, &buf, len);
  if (!pkcs7) {
    goto end;
  }

  static const char kSignedData[] = "signed data";
  data_bio = BIO_new_mem_buf(kSignedData, strlen(kSignedData));
  if (!data_bio) {
    goto end;
  }

  PKCS7_verify(pkcs7, sharedData.certs, sharedData.store, data_bio, nullptr, 0);

end:
  BIO_free(data_bio);
  PKCS7_free(pkcs7);
  return 0;
}
OPENSSL_END_ALLOW_DEPRECATED
