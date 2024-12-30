// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <cstdint>

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/pkcs7.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>
#include <openssl/pem.h>

// The corpus was created using the following key.
// If you change the key, the corpus should be augmented with inputs
// created using (or "seeded" from) PKCS7 values encrypted with
// the new key.
static const char kKey[] = R"(
-----BEGIN PRIVATE KEY-----
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
hJTbHtjEDJ7BHLC/CNUhXbpyyu1y
-----END PRIVATE KEY-----
)";

static const char kCert[] = R"(
-----BEGIN CERTIFICATE-----
MIIEqzCCApOgAwIBAgIBADANBgkqhkiG9w0BAQsFADAPMQ0wCwYDVQQDDARSb290
MCAXDTcwMDEwMTAwMDAwMFoYDzk5OTkxMjMxMjM1OTU5WjAPMQ0wCwYDVQQDDARM
ZWFmMIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAtfjDp/gaKXBFUeED
L413QMRpFhZZV8kBQ06C/qjoj0VNcjewvCgrZGzgBbbSSDuDv4tImeyqmG55gemF
APzjQHGpKHJ63aBEoESXFTHgMQ5P9dTrTBeciH3jjjv01HlTZgFGk+t4BWysv2na
aocybTr/QQZeVXGDRhkhPtMLW5o6ZjbMbpxEEdSiw3Pe3xmB3kXyqEsqwiBBPCGg
BKShkdkpLt7/ScIe0aY7qYIlAJB+qSZO1TGZub5dsBY2L38rII3jeWbbMRQzGj2G
UracTMaTXeQvQ7Dti46eTTKRnzRphuGaomkIPM9nCDOhEpjdcwyXVIeSF3ndXzsQ
WQ/6aFBR9MA0RVp785Wj5oyRBa2CzCvLL5xOZxEKfb7vdyEhQce3KH7Pp4jGlFzx
KmkUqq7onzdjNYrd5Dn//GGZdb7q7PlbRw+pziaOm3ddft+2gYnSAfwWlp8y6w5k
k3DxWtbZEx8KC6nPfo04U6vY2esN5QDD6bKHp8g9fVJkAefPfuJDadkiDv07c1UA
hoED1xNowwpehvWiDzJH76T2SuEx1Ypd1kEQhWJ2HQzuB0F6NmbguEYqoGOcoH3q
C/n2vZN/N5YMcQB0C0u8bG2lQeNEZn3W3Xr4D2CMGTTTu/HXUZjHUr+iJJ0lvYMn
Rs2P/27WPrdUlnAWVs59RMKvINkCAwEAAaMQMA4wDAYDVR0TAQH/BAIwADANBgkq
hkiG9w0BAQsFAAOCAgEAMZR8p6FGActr5RNICECEKnp6qfgaZiQFwKg64uovggh3
PU4VhRGWtNAD4E8/G37I1WjEJwSh6YrthQJrSmfnVxUgXwZqW3Ou5UJpaWwReEMV
xXwznJTwoUwD9pzh/+2QeNYV+6CPmGPD8znhh9QzOoo1mIaUNdDGN7K6dVBBBr7O
Dm67qWXf8AoWLUO5XTiha5V19Jsyxszo2Ntfef9mK4LIszuRbMrpfMlUEvuO3oLa
SLScdPonEPF7CGuyJcyVVJ4T+mqTzmQ9AKzujjXk3sqw5rFbPIC+ei5Fdf0SXsgS
jEX83uZPZRIMjkyiVjDsWwDDumaTJ/KCUhaqGzJ6/ZKLEvKCgtgDQg2QetmRzS5j
c9CC6I6Kfx01cJ6wOlJY22DDjWJAviEP40/TVk1xoEWyiErEiYq3vdCRRoxSR55N
/tjiQM0XbiGfKfx2KrAHFIsRQsqHF0bL4HDjCh29cz3jleWdLGNPwrdfLtPMcXf8
Eu6/5vlz8BUuaR08fjv59tfdedLDRlbpZFERMio6PINFoRuVtbcgVw5xHucHjl3p
shp0eY7uylv5j8j1X7m5fp+BZKILGHLKVrE2ihJgyS9je2Jf40Fb+Hu+1dcsAKd+
jbgtnMeOs3SWELGeAG2TXsKmNOb0OwzGeL5jJpe6tsEUiQQQxhfarBIlxoTPizI=
-----END CERTIFICATE-----
)";

class SharedData {
public:
  EVP_PKEY *key = nullptr;
  X509 *cert = nullptr;

  SharedData() {
    {
      BIO *key_bio = BIO_new_mem_buf(const_cast<char *>(kKey), sizeof(kKey) - 1);
      key = PEM_read_bio_PrivateKey(key_bio, nullptr, nullptr, nullptr);
      BIO_free(key_bio);
    }
    {
      BIO *cert_bio = BIO_new_mem_buf(const_cast<char *>(kCert), sizeof(kCert) - 1);
      cert = PEM_read_bio_X509(cert_bio, nullptr, nullptr, nullptr);
      BIO_free(cert_bio);
    }
  }

  ~SharedData() {
    X509_free(cert);
    EVP_PKEY_free(key);
  }
};

static SharedData sharedData;


extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  PKCS7 *pkcs7 = nullptr;

  pkcs7 = d2i_PKCS7(nullptr, &buf, len);
  if (pkcs7 == nullptr) {
    goto end;
  }

  {
    BIO *data_bio = BIO_new(BIO_s_mem());
OPENSSL_BEGIN_ALLOW_DEPRECATED
    PKCS7_decrypt(pkcs7, sharedData.key, NULL, data_bio, 0);
OPENSSL_END_ALLOW_DEPRECATED
    BIO_free(data_bio);
  }

  {
    BIO *data_bio = BIO_new(BIO_s_mem());
OPENSSL_BEGIN_ALLOW_DEPRECATED
    PKCS7_decrypt(pkcs7, sharedData.key, sharedData.cert, data_bio, 0);
OPENSSL_END_ALLOW_DEPRECATED
    BIO_free(data_bio);
  }

end:
  PKCS7_free(pkcs7);

  return 0;
}
