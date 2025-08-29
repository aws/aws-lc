// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/base.h>
#include <openssl/bio.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/pem.h>
#include <openssl/pkcs8.h>
#include <openssl/ssl.h>
#include "../fipsmodule/evp/internal.h"
#include "../fipsmodule/kem/internal.h"
#include "../test/test_util.h"
#include <openssl/experimental/kem_deterministic_api.h>


// https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates/
// All example keys are from Appendix C in the above standard
// Example ML-KEM-512 public key
const char *mlkem_512_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "MIIDMjALBglghkgBZQMEBAEDggMhADmVgV5ZfRBDVc8pqlMzyTJRhp1bzb5IcST2\n"
    "Ari2pmwWxHYWSK12XPXYAGtRXpBafwrAdrDGLvoygVPnylcBaZ8TBfHmvG+QsOSb\n"
    "aTUSts6ZKouAFt38GmYsfj+WGcvYad13GvMIlszVkYrGy3dGbF53mZbWf/mqvJdQ\n"
    "Pyx7fi0ADYZFD7GAfKTKvaRlgloxx4mht6SRqzhydl0yDQtxkg+iE8lAk0Frg7gS\n"
    "Tmn2XmLLUADcw3qpoP/3OXDEdy81fSQYnKb1MFVowOI3ajdipoxgXlY8XSCVcuD8\n"
    "dTLKKUcpU1VntfxBPF6HktJGRTbMgI+YrddGZPFBVm+QFqkKVBgpqYoEZM5BqLtE\n"
    "wtT6PCwglGByjvFKGnxMm5jRIgO0zDUpFgqasteDj3/2tTrgWqMafWRrevpsRZMl\n"
    "JqPDdVYZvplMIRwqMcBbNEeDbLIVC+GCna5rBMVTXP9Ubjkrp5dBFyD5JPSQpaxU\n"
    "lfITVtVQt4KmTBaItrZVvMeEIZekNML2Vjtbfwmni8xIgjJ4NWHRb0y6tnVUAAUH\n"
    "gVcMZmBLgXrRJSKUc26LAYYaS1p0UZuLb+UUiaUHI5Llh2JscTd2V10zgGocjicy\n"
    "r5fCaA9RZmMxxOuLvAQxxPloMtrxs8RVKPuhU/bHixwZhwKUfM0zdyekb7U7oR3l\n"
    "y0GRNGhZUWy2rXJADzzyCbI2rvNaWArIfrPjD6/WaXPKin3SZ1r0H3oXthQzzRr4\n"
    "D3cIhp9mVIhJeYCxrBCgzctjagDthoGzXkKRJMqANQcluF+DperDpKPMFgCQPmUp\n"
    "NWC5szblrw1SnawaBIEZMCy3qbzBELlIUb8CEX8ZncSFqFK3Rz8JuDGmgx1bVMC3\n"
    "kNIlz2u5LZRiomzbM92lEjx6rw4moLg2Ve6ii/OoB0clAY/WuuS2Ac9huqtxp6PT\n"
    "UZejQ+dLSicsEl1UCJZCbYW3lY07OKa6mH7DciXHtEzbEt3kU5tKsII2NoPwS/eg\n"
    "nMXEHf6DChsWLgsyQzQ2LwhKFEZ3IzRLrdAA+NjFN8SPmY8FMHzr0e3guBw7xZoG\n"
    "WhttY7Js\n"
    "-----END PUBLIC KEY-----\n";

// https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates/
// Example ML-KEM-768 public key
const char *mlkem_768_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "MIIEsjALBglghkgBZQMEBAIDggShACmKoQ1CPI3aBp0CvFnmzfA6CWuLPaTKubgM\n"
    "pKFJB2cszvHsT68jSgvFt+nUc/KzEzs7JqHRdctnp4BZGWmcAvdlMbmcX4kYBwS7\n"
    "TKRTXFuJcmecZgoHxeUUuHAJyGLrj1FXaV77P8QKne9rgcHMAqJJrk8JStDZvTSF\n"
    "wcHGgIBSCnyMYyAyzuc4FU5cUXbAfaVgJHdqQw/nbqz2ZaP3uDIQIhW8gvEJOcg1\n"
    "VwQzao+sHYHkuwSFql18dNa1m75cXpcqDYusQRtVtdVVfNaAoaj3G064a8SMmgUJ\n"
    "cxpUvZ1ykLJ5Y+Q3Lcmxmc/crAsBrNKKYjlREuTENkjWIsSMgjTQFEDozDdskn8j\n"
    "pa/JrAR0xmInTkJFJchVLs47P+JlFt6QG8fVFb3olVjmJslcgLkzQvgBAATznmxs\n"
    "lIccXjRMqzlmyDX5qWpZr9McQChrOLHBp4RwurlHUYk0RTzoZzapGfH1ptUQqG9U\n"
    "VPw5gMtcdlvSvV97NrFBDWY1yM60fE3aDXaijqyTnHHDAkgEhmxxYmZYRCFjwsIh\n"
    "F+UKzvzmN4qYVlIwKk7wws4Mxxa3eW4ray43d9+hrD2iWaMbWptTD4y2OKgaYqww\n"
    "GEmrr5WnMBvaMAaJCb/bfmfbzLs4pVUaJbGjoPaFdIrVdT2IgPABbGJ0hhZjhMVX\n"
    "H+I2WQA2TQODEeLYdds2ZoaTK17GAkMKNp6Hpu9cM4eGZXglvUwFes65I+sJNeaQ\n"
    "XmO0ztf4CFenc91ksVDSZhLqmsEgUtsgF78YQ8y0sygbaQ3HKK36hcACgbjjwJKH\n"
    "M1+Fa0/CiS9povV5Ia2gGRTECYhmLVd2lmKnhjUbm2ZJPat5WU2YbeIQDWW6D/Tq\n"
    "WLgVONJKRDWiWPrCVASqf0H2WLE4UGXhWNy2ARVzJyD0BFmqrBXkBpU6kKxSmX0c\n"
    "zQcAYO/GXbnmUzVEZ/rVbscTyG51QMQjrPJmn1L6b0rGiI2HHvPoR8ApqKr7uS4X\n"
    "skqgebH0GbphdbRCr7EZCdSla3CgM1soc5IYqnyTSOLDwvPrPRWkHmQXwN2Uv+sh\n"
    "QZsxGnuxOhgLvoMyGKmmsXRHzIXyJYWVh6cwdwSay8/UTQ8CVDjhXRU4Jw1Ybhv4\n"
    "MZKpRZz2PA6XL4UpdnmDHs8SFQmFHLg0D28Qew+hoO/Rs2qBibwIXE9ct4TlU/Qb\n"
    "kY+AOXzhlW94W+43fKmqi+aZitowwmt8PYxrVSVMyWIDsgxCruCsTh67QI5JqeP4\n"
    "edCrB4XrcCVCXRMFoimcAV4SDRY7DhlJTOVyU9AkbRgnRcuBl6t0OLPBu3lyvsWj\n"
    "BuujVnhVwBRpn+9lrlTHcKDYXBhADPZCrtxmB3e6SxOFAr1aeBL2IfhKSClrmN1D\n"
    "IrbxWCi4qPDgCoukSlPDqLFDVxsHQKvVZ9rxzenHnCBLbV4lnRdmoxu7y05qBc9F\n"
    "AhdrMBwcL0Ekd1AVe87IXoCbMKTWDXdHzdD1uZqoyCaYdRd5OqqAgKCxJKhVjfcr\n"
    "vje3X07btr6CFtbGM/srIoDiURPYaV5DSBw+6zl+sZJQUim2eiAeqJPD4ssy2ovD\n"
    "QvpN6gV4\n"
    "-----END PUBLIC KEY-----\n";

// https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates/
// Example ML-KEM-1024 public key
const char *mlkem_1024_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "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\n"
    "uYOILhF1\n"
    "-----END PUBLIC KEY-----\n";

const char *mlkem_512_priv_expanded_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "JCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+Pw==\n"
    "-----END PRIVATE KEY-----\n";

const char *mlkem_768_priv_expanded_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "JCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+Pw==\n"
    "-----END PRIVATE KEY-----\n";

const char *mlkem_1024_priv_expanded_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "JCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+Pw==\n"
    "-----END PRIVATE KEY-----\n";

// The following private/public keys were generated externally and encoded using the Java library BouncyCastle which is a JCA provider. 
// Private keys generated were encoded in expandedKey format. 
// Implementation: https://github.com/bcgit/bc-java/tree/b41f23936724284a20f10dff13c76896a846031b/prov/src/main/java/org/bouncycastle/jcajce/provider/asymmetric/mlkem
// Encoder: https://github.com/bcgit/bc-java/blob/0e100a58af34d0cf91ea5cfd1f0a6d36681c3653/core/src/main/java/org/bouncycastle/pqc/crypto/util/PrivateKeyInfoFactory.java#L247-L256

const char *bouncy_castle_mlkem_512_priv_expanded_pem_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "uX0nVwQBIwZSB9XN4NgNm6sl7CUnZ/1dK5Tv5Q==\n"
    "-----END PRIVATE KEY-----\n";

const char *bouncy_castle_mlkem_512_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "MIIDMjALBglghkgBZQMEBAEDggMhABGUC5yCDceDLGeFfYoSrNSrWzSzT0kKpP4r\n"
    "hr0bZuuWgQQMbkhqduH7aluLnFdcZ0MnjCwzrHnSDD0DcW0GucPRKCI4A61zt6mU\n"
    "GaV4NVTZo708vujEWR1gYYZKV4mQjgAJG5F6tqBpQZ7VEt34RJ2gzPTAMfenP6CJ\n"
    "Oo5wiJSoHq/2gW3buAcxeliIY2OLArK5D953DTt7Xb7jtw00m/cAEQqMXjpBeIvp\n"
    "S0MAqHwXoRHsJFhqU7tcOCBqCBAToSixMlmitK5Hsj/oshZscJOkEm3VbAT4Z0oA\n"
    "uWCIv0AMuQThCOs0H9Pori8gHfLonWAiYFgxzRAgt6fFVVkhJOfDDXYZtrcpE20m\n"
    "JYxKIDESyquhVhCBcyhLctW6KKalncFoRi2SlSunVWDJYj/zVu5iLmAWMu28ltc5\n"
    "N90qvWVsIi+sFTFKE4jmcINba3JnI6wkJe0LV9nTI5l4VQyFzg2DtAnZXApWHDil\n"
    "Ee7Kgc2HVZJsT688dA3lHS3gSn3bYuTZwHCKwqYIz7D0jyziun1pg3NYAivih/KW\n"
    "LyRQVDiQVbbIQ6G5CbwyPe0LJ3yHb0I2jdXlbhQiYJVyXo1HXixYuzVXGL5LdWF3\n"
    "pLdjpJdrvd28goVDTysUTN2XAkpzr3HKG7EgRdKFBhizmuv1Qxz5u15aog1BnsLR\n"
    "ziBTM1T3I0PwZuB2ngajoMoKRSDUvWBrtNcwcpG5UXT5Sy86zDIgwas1yoezsO0k\n"
    "wRixswpcyyKmMEmDAqdFkGrEvMosxUX4vhFZWRk4Cd/4k8FpHlZBdZmLOCoqtZnY\n"
    "riUpQVHiWGGoSlsipm6hyHhJrz+FAw7rTrGjJRaZyiqgYuIGglPQnjLkowHyG2VL\n"
    "om9XUeiaX2SHHx6gHNfAYl9KBjM4w6rgzpGsstiMKu6KxKTwsgRbTzRiFkoL0DUp\n"
    "IxD8DUqiTqEEp7vHA1qLxqILjIdcJCkhmSRlWJhHGhZ7uycpLVDYLqF2g8BFbE+I\n"
    "KBlkF51phuoYW4bXpZoqCUMhTDnqjb9Q36AIJdp2kU0GBrB9gaFT0He5h2IK5GIn\n"
    "qg50PyZp\n"
    "-----END PUBLIC KEY-----\n";

const char *bouncy_castle_mlkem_768_priv_expanded_str =
    "-----BEGIN PRIVATE KEY-----\n"
    "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\n"
    "drB5C6kc52uVVA3V9jomMufpdKNdVgjqHk4vWA==\n"
    "-----END PRIVATE KEY-----\n";

const char *bouncy_castle_mlkem_768_pub_pem_str =
    "-----BEGIN PUBLIC KEY-----\n"
    "MIIEsjALBglghkgBZQMEBAIDggShAL+iTbEENK8an4t0q47AObdlI0WMOQVxxYBB\n"
    "izFVBdI2oRtSK2fmaYUZZmGUc834TuHJuiNRwKX0wwRwwNPQkZmgGbkZu2wmagby\n"
    "XFRJSdYDq+OVSkSGBFLVeo6YhG3VsLSXQKUCDKLWw0LRx9MEwWThxE0YeH9HEr6U\n"
    "H2rjykEKe3camweMSdW5qwO7Apl2iOigfK1hqb76iVAFibNCE35skD+GCk9oVgMq\n"
    "lJ0oECPVhqFbXf9AP4j4rVxMVcHWaNgzQjKGYahamoK0YlcDYoEMc9USel02uDHo\n"
    "xjejqV6mPNWmE0USfuDMYen3TFAAfW14xxtFcdPKlS4wmnDArB5nGbvsV5vGEyZF\n"
    "sisQph4bJgLID8Y8SUjygZeMmWSmOQ9UB6MrApS2XQKFRcyylj3GGYpmN7UYj09h\n"
    "gqjYLcvpPrjBqrXxXpNgt5DhNyJVGIsDMQsWl6dUw3O4dLOWSgrLgQRyuQlEY8e5\n"
    "szViCcB1YwTZYC1RuofisRQsDTsAhU1JcZsGguJ4c0taObMncfI3mpFiJcirTNuS\n"
    "OlR7oyDcOSA3aKE7puorRPdTbi0FMcD6fOsXgyFzHAOXS2KDvoOLRLUXcq0kTiGJ\n"
    "CTFROT4YeP2Cmn5gIBV1Is+LvUIVEE5wCep3mUDskttsKcl3Rh0awZCRX8hSTuVi\n"
    "T+fJcuTqKNawZntKx1zEEw4wKgtHqnirYvUwzEY7NOkQz6orsYpQhzfbozSJWVkF\n"
    "JCLEH7goz9ZLWGr8BqCKn3WXDnT7XFr7rSZaX/q6mr7aJY3VGAViVDYBxMWFwtYw\n"
    "JMKnRRnQt1X6l+GLgcAGXcsKpRAXmpYzlu7DAsPVQ674mXHBO/VjfqmyQVfkjzrq\n"
    "wys2sAibKayKApJ4rjGSZ+azxI0lPBO5aFvwvdnmJBm7oTSykcAlri9Wn1lxtLiW\n"
    "Zfmci/eWsCgYsy3mvhSimWgESJAwAunsa44YXiWRfVmpxfSjwGWolP8ZAtYlcHnA\n"
    "lrFcJKHwgMvMP0KQEt7hvfRJuMTmF2RquNRCgcDHdwXXu5jVrM0cVvEAFjlCynT1\n"
    "F8GYUww7aIiXsJt5D3TwDNR7JUvgz9IbDbGgFPE3aU/7InBWXaFQcY1pDM/HmAlb\n"
    "WZbwbeKkWshggSgidOTwhMnMjQPVYaxMr0OcQBAYwBGguDJMjwF1tzG5rQerNxIl\n"
    "SjN5euyYBtUJhsgor08AXr4IHExFj/LyFitkvrpXvnOjhNZWrcc3jyB8kGQDEIqy\n"
    "zuFBHS2ZXpulnxkxGTFQO/N5k433ULThg5W4jrWYKZd0l/iVEknYFdWTzQeqRCdS\n"
    "b4UGoGN3ObB6nVXRQM4MkXXmcc9SGRiZxXl0CGwCmAcIxtpCntxgfkJ4UbATNDLi\n"
    "qsOqD42LTtYxo7QpepE0lJh6AiYkYZTbOx1RbzZICV6gJsCWtSRYLGnUaPvZDj80\n"
    "MqZwn/8nRip6pZaJoH1KafsULir7opUjK04GKMvhnLclBtI4lpRSolNrGW/lVfaA\n"
    "n8QLUMqiwEuVCQ6LPpkDk3EXFs/ERtpU8+ZOuHLg4EBAZcbwybrYGDjQ5TAoriVu\n"
    "0KCMcW41\n"
    "-----END PUBLIC KEY-----\n";

struct KEMTestVector {
  int nid;
  const char *public_pem_str;
  const char *private_pem_expanded_str;
  const char *expected_deterministic_pub_pem;
  const char *expected_deterministic_priv_pem;
  size_t public_key_len;
  size_t secret_key_len;
};

static const KEMTestVector kemParameters[] = {
    {NID_MLKEM512, mlkem_512_pub_pem_str, mlkem_512_priv_expanded_pem_str, 
     mlkem_512_pub_pem_str, mlkem_512_priv_expanded_pem_str, 800, 1632},
    {NID_MLKEM768, mlkem_768_pub_pem_str, mlkem_768_priv_expanded_pem_str,
     mlkem_768_pub_pem_str, mlkem_768_priv_expanded_pem_str, 1184, 2400},
    {NID_MLKEM1024, mlkem_1024_pub_pem_str, mlkem_1024_priv_expanded_pem_str,
     mlkem_1024_pub_pem_str, mlkem_1024_priv_expanded_pem_str, 1568, 3168},
    {NID_MLKEM512, bouncy_castle_mlkem_512_pub_pem_str,
     bouncy_castle_mlkem_512_priv_expanded_pem_str, 
     mlkem_512_pub_pem_str, mlkem_512_priv_expanded_pem_str, 800, 1632},
    {NID_MLKEM768, bouncy_castle_mlkem_768_pub_pem_str,
     bouncy_castle_mlkem_768_priv_expanded_str,
     mlkem_768_pub_pem_str, mlkem_768_priv_expanded_pem_str, 1184, 2400},
};


static bssl::UniquePtr<EVP_PKEY> generate_kem_key_pair(int nid) {
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_KEM, nullptr));
  if (!ctx || !EVP_PKEY_CTX_kem_set_params(ctx.get(), nid) ||
      !EVP_PKEY_keygen_init(ctx.get())) {
    return nullptr;
  }
  EVP_PKEY *raw = nullptr;
  if (!EVP_PKEY_keygen(ctx.get(), &raw)) {
    return nullptr;
  }
  return bssl::UniquePtr<EVP_PKEY>(raw);
}

class KEMTest : public testing::TestWithParam<KEMTestVector> {};

INSTANTIATE_TEST_SUITE_P(All, KEMTest, testing::ValuesIn(kemParameters));

TEST_P(KEMTest, MarshalParse) {
  // ---- 1. Setup phase: generate a key ----
  int nid = GetParam().nid;
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(nid));
  ASSERT_TRUE(pkey);

  // ---- 2. Test encode (marshal) and decode (parse) of public key ----
  // The public key must encode properly.
  bssl::ScopedCBB cbb;
  uint8_t *der;
  size_t der_len;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_public_key(cbb.get(), pkey.get()));
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // The public key must parse properly.
  CBS cbs;
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> pub_pkey_from_der(EVP_parse_public_key(&cbs));
  ASSERT_TRUE(pub_pkey_from_der.get());
  EXPECT_EQ(1, EVP_PKEY_cmp(pkey.get(), pub_pkey_from_der.get()));

  // ---- 3. Test encode (marshal) and decode (parse) of private key ----
  // The private key must encode properly.
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), pkey.get()));
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  free_der.reset(der);

  // The private key must parse properly.
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> priv_pkey_from_der(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(priv_pkey_from_der);
  EXPECT_EQ(Bytes(priv_pkey_from_der->pkey.kem_key->secret_key,
                  GetParam().secret_key_len),
            Bytes(pkey->pkey.kem_key->secret_key, GetParam().secret_key_len));
}

// Test that the private key is encoded in expandedKey format
TEST_P(KEMTest, PrivateKeyExpandedFormat) {
  const KEMTestVector &test = GetParam();

  // Generate a key pair
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

  // Encode the private key
  bssl::ScopedCBB cbb;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), pkey.get()));

  uint8_t *der;
  size_t der_len;
  ASSERT_TRUE(CBB_finish(cbb.get(), &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // Parse the PKCS#8 structure to verify the privateKey field contains
  // the expandedKey format - AWS-LC currently only supports expandedKey
  // encoding
  CBS pkcs8, algorithm, private_key;
  uint64_t version;
  CBS_init(&pkcs8, der, der_len);

  ASSERT_TRUE(CBS_get_asn1(&pkcs8, &pkcs8, CBS_ASN1_SEQUENCE));
  ASSERT_TRUE(CBS_get_asn1_uint64(&pkcs8, &version));
  ASSERT_EQ(version, 0u);
  ASSERT_TRUE(CBS_get_asn1(&pkcs8, &algorithm, CBS_ASN1_SEQUENCE));
  ASSERT_TRUE(CBS_get_asn1(&pkcs8, &private_key, CBS_ASN1_OCTETSTRING));

  // The privateKey field should contain the expandedKey as an OCTET STRING
  CBS expanded_key;
  ASSERT_TRUE(CBS_get_asn1(&private_key, &expanded_key, CBS_ASN1_OCTETSTRING));
  ASSERT_EQ(CBS_len(&expanded_key), test.secret_key_len);

  // Verify it matches the original secret key
  EXPECT_EQ(Bytes(CBS_data(&expanded_key), CBS_len(&expanded_key)),
            Bytes(pkey->pkey.kem_key->secret_key, test.secret_key_len));
}

TEST_P(KEMTest, ParsePublicKey) {
  // Test parsing of the draft standard example public keys

  const KEMTestVector &test = GetParam();
  int nid = test.nid;
  size_t public_key_len = test.public_key_len;
  size_t secret_key_len = test.secret_key_len;
  const char *public_pem_str = test.public_pem_str;

  // ---- 1. Convert example PEM to DER ----
  uint8_t *der = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(public_pem_str, &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // ---- 2. Parse the public key ----
  CBS cbs;
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> pkey_from_der(EVP_parse_public_key(&cbs));
  ASSERT_TRUE(pkey_from_der);
  ASSERT_EQ(EVP_PKEY_id(pkey_from_der.get()), EVP_PKEY_KEM);

  // ---- 3. Verify key parameters ----
  KEM_KEY *kem_key = pkey_from_der->pkey.kem_key;
  ASSERT_TRUE(kem_key);
  ASSERT_EQ(kem_key->kem->nid, nid);
  ASSERT_EQ(kem_key->kem->public_key_len, public_key_len);
  ASSERT_EQ(kem_key->kem->secret_key_len, secret_key_len);
}

TEST_P(KEMTest, ParseExamplePrivateKey) {
  // Test parsing of the draft standard example private keys (expanded format)

  const KEMTestVector &test = GetParam();
  int nid = test.nid;
  size_t public_key_len = test.public_key_len;
  size_t secret_key_len = test.secret_key_len;
  const char *private_pem_expanded_str = test.private_pem_expanded_str;

  // ---- 1. Convert example PEM to DER ----
  uint8_t *der = nullptr;
  long der_len = 0;
  ASSERT_TRUE(PEM_to_DER(private_pem_expanded_str, &der, &der_len));
  bssl::UniquePtr<uint8_t> free_der(der);

  // ---- 2. Parse the private key ----
  CBS cbs;
  CBS_init(&cbs, der, der_len);
  bssl::UniquePtr<EVP_PKEY> pkey_from_der(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(pkey_from_der);
  ASSERT_EQ(EVP_PKEY_id(pkey_from_der.get()), EVP_PKEY_KEM);

  // ---- 3. Verify key parameters ----
  KEM_KEY *kem_key = pkey_from_der->pkey.kem_key;
  ASSERT_TRUE(kem_key);
  ASSERT_EQ(kem_key->kem->nid, nid);
  ASSERT_EQ(kem_key->kem->public_key_len, public_key_len);
  ASSERT_EQ(kem_key->kem->secret_key_len, secret_key_len);

  // ---- 4. Verify private key is present ----
  ASSERT_TRUE(kem_key->secret_key);
}

// Invalid length test vectors - truncated DER structures
static const uint8_t mlkem512_public_key_invalid_length[] = {
    0x30, 0x16, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
    0x04, 0x04, 0x01, 0x03, 0x07, 0x00, 0x39, 0x95, 0x5e, 0x59, 0x7d, 0x10};

static const uint8_t mlkem512_private_key_invalid_length[] = {
    0x30, 0x1c, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60,
    0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x01, 0x04, 0x0a,
    0x04, 0x08, 0x70, 0x55, 0x4f, 0xd4, 0x36, 0x34, 0x4f, 0x27};

TEST(KEMTest, ParsePublicKeyInvalidLength) {
  CBS cbs;
  CBS_init(&cbs, mlkem512_public_key_invalid_length,
           sizeof(mlkem512_public_key_invalid_length));
  bssl::UniquePtr<EVP_PKEY> pub_pkey_from_der(EVP_parse_public_key(&cbs));
  ASSERT_FALSE(pub_pkey_from_der.get());
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), EVP_R_INVALID_BUFFER_SIZE);
}

TEST(KEMTest, ParsePrivateKeyInvalidLength) {
  CBS cbs;
  CBS_init(&cbs, mlkem512_private_key_invalid_length,
           sizeof(mlkem512_private_key_invalid_length));
  bssl::UniquePtr<EVP_PKEY> private_pkey_from_der(EVP_parse_private_key(&cbs));
  ASSERT_FALSE(private_pkey_from_der.get());
  ASSERT_EQ(ERR_GET_REASON(ERR_get_error()), EVP_R_INVALID_BUFFER_SIZE);
}


// Verifies that deterministic ML-KEM key generation with the fixed seed from the IETF standard produces keys that exactly
// match the expected PEM strings from the standard. 
// The expected PEM strings from the given seed are fields at the top (mlkem_XXX_pub/priv_pem_str)
// See Appendix C.1 in https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates/ for the seed value
TEST_P(KEMTest, DeterministicKeyMarshaling) {
  const KEMTestVector& test = GetParam();
  
  // ---- 1. Setup phase: create context and set parameters ----
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_KEM, nullptr));
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(EVP_PKEY_keygen_init(ctx.get()));
  ASSERT_TRUE(EVP_PKEY_CTX_kem_set_params(ctx.get(), test.nid));

  // ---- 2. Create deterministic seed: 00 01 02 ... 3f (64 consecutive bytes) ----
  // Seed is specified in Appendix C.1 in https://datatracker.ietf.org/doc/draft-ietf-lamps-kyber-certificates/
  std::vector<uint8_t> keygen_seed(64);
  for (size_t i = 0; i < 64; i++) {
    keygen_seed[i] = static_cast<uint8_t>(i);  // seed is a sequence - 00, 01, 02, ... 3f (from above standard)
  }
  size_t seed_len = keygen_seed.size();

  // ---- 3. Generate deterministic keypair ----
  EVP_PKEY *raw = nullptr;
  ASSERT_TRUE(EVP_PKEY_keygen_deterministic(ctx.get(), &raw,
                                           keygen_seed.data(), &seed_len));
  ASSERT_TRUE(raw);
  bssl::UniquePtr<EVP_PKEY> pkey(raw);

  // ---- 4. Marshal generated public key to DER ----
  bssl::ScopedCBB public_cbb;
  ASSERT_TRUE(CBB_init(public_cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_public_key(public_cbb.get(), pkey.get()));

  uint8_t *generated_pub_der;
  size_t generated_pub_der_len;
  ASSERT_TRUE(CBB_finish(public_cbb.get(), &generated_pub_der, &generated_pub_der_len));
  bssl::UniquePtr<uint8_t> generated_pub_der_ptr(generated_pub_der);

  // ---- 5. Convert expected public PEM to DER ----
  uint8_t *expected_pub_der = nullptr;
  long expected_pub_der_len = 0;
  ASSERT_TRUE(PEM_to_DER(test.expected_deterministic_pub_pem, &expected_pub_der, &expected_pub_der_len));
  bssl::UniquePtr<uint8_t> expected_pub_der_ptr(expected_pub_der);

  // ---- 6. Compare public key DERs ----
  EXPECT_EQ(generated_pub_der_len, static_cast<size_t>(expected_pub_der_len))
      << "Public key DER length mismatch";
  EXPECT_EQ(Bytes(generated_pub_der, generated_pub_der_len),
            Bytes(expected_pub_der, expected_pub_der_len))
      << "Public key DER content mismatch";

  // ---- 7. Marshal generated private key to DER ----
  bssl::ScopedCBB private_cbb;
  ASSERT_TRUE(CBB_init(private_cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(private_cbb.get(), pkey.get()));

  uint8_t *generated_priv_der;
  size_t generated_priv_der_len;
  ASSERT_TRUE(CBB_finish(private_cbb.get(), &generated_priv_der, &generated_priv_der_len));
  bssl::UniquePtr<uint8_t> generated_priv_der_ptr(generated_priv_der);

  // ---- 8. Convert expected private PEM to DER ----
  uint8_t *expected_priv_der = nullptr;
  long expected_priv_der_len = 0;
  ASSERT_TRUE(PEM_to_DER(test.expected_deterministic_priv_pem, &expected_priv_der, &expected_priv_der_len));
  bssl::UniquePtr<uint8_t> expected_priv_der_ptr(expected_priv_der);

  // ---- 9. Compare private key DERs ----
  EXPECT_EQ(generated_priv_der_len, static_cast<size_t>(expected_priv_der_len))
      << "Private key DER length mismatch";
  EXPECT_EQ(Bytes(generated_priv_der, generated_priv_der_len),
            Bytes(expected_priv_der, expected_priv_der_len))
      << "Private key DER content mismatch";

  // ---- 10. Verify private key DER is larger than public key DER ----
  EXPECT_GT(generated_priv_der_len, generated_pub_der_len);
}

// Test KEM public key round-trip serialization using i2d_PUBKEY and d2i_PUBKEY functions.
TEST_P(KEMTest, I2dAndD2iPUBKEYRoundTrip) {
  const KEMTestVector &test = GetParam();
  
  // ---- 1. Generate a keypair ----
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

  // ---- 2. Encode public key using i2d_PUBKEY ----
  uint8_t *encoded_der = nullptr;
  int encoded_der_len = i2d_PUBKEY(pkey.get(), &encoded_der);
  ASSERT_GT(encoded_der_len, 0);
  ASSERT_TRUE(encoded_der);
  bssl::UniquePtr<uint8_t> free_encoded_der(encoded_der);

  // ---- 3. Decode back using d2i_PUBKEY ----
  const uint8_t *encoded_der_ptr = encoded_der;
  bssl::UniquePtr<EVP_PKEY> decoded_pkey(d2i_PUBKEY(nullptr, &encoded_der_ptr, encoded_der_len));
  ASSERT_TRUE(decoded_pkey);
  ASSERT_EQ(EVP_PKEY_id(decoded_pkey.get()), EVP_PKEY_KEM);

  // ---- 4. Verify round-trip correctness ----
  EXPECT_EQ(1, EVP_PKEY_cmp(pkey.get(), decoded_pkey.get()));

  // ---- i2d_PUBKEY output should work with EVP_parse_public_key ----
  CBS cbs;
  CBS_init(&cbs, encoded_der, encoded_der_len);
  bssl::UniquePtr<EVP_PKEY> cross_decoded_pkey(EVP_parse_public_key(&cbs));
  ASSERT_TRUE(cross_decoded_pkey);
  EXPECT_EQ(1, EVP_PKEY_cmp(pkey.get(), cross_decoded_pkey.get()));
}

// Test round-trip encoding/decoding of KEM private keys using PKCS#8 format via EVP_PKEY2PKCS8, i2d_PKCS8_PRIV_KEY_INFO, and d2i_PrivateKey.
TEST_P(KEMTest, PKCS8_PrivateKey_RoundTrip) {
  const KEMTestVector &test = GetParam();
  
  // ---- 1. Generate a keypair ----
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

  // ---- 2. Convert to PKCS8 structure using EVP_PKEY2PKCS8 ----
  bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> pkcs8_info(EVP_PKEY2PKCS8(pkey.get()));
  ASSERT_TRUE(pkcs8_info);

  // ---- 3. Encode PKCS8 to DER using i2d_PKCS8_PRIV_KEY_INFO ----
  uint8_t *encoded_der = nullptr;
  int encoded_der_len = i2d_PKCS8_PRIV_KEY_INFO(pkcs8_info.get(), &encoded_der);
  ASSERT_GT(encoded_der_len, 0);
  ASSERT_TRUE(encoded_der);
  bssl::UniquePtr<uint8_t> free_encoded_der(encoded_der);

  // ---- 4. Decode back using d2i_PrivateKey ----
  const uint8_t *encoded_der_ptr = encoded_der;
  bssl::UniquePtr<EVP_PKEY> decoded_pkey(d2i_PrivateKey(EVP_PKEY_KEM, nullptr, &encoded_der_ptr, encoded_der_len));
  ASSERT_TRUE(decoded_pkey);
  ASSERT_EQ(EVP_PKEY_id(decoded_pkey.get()), EVP_PKEY_KEM);

  // ---- 5. Verify round-trip correctness by comparing secret keys ----
  ASSERT_TRUE(pkey->pkey.kem_key->secret_key);
  ASSERT_TRUE(decoded_pkey->pkey.kem_key->secret_key);
  EXPECT_EQ(Bytes(pkey->pkey.kem_key->secret_key, test.secret_key_len),
            Bytes(decoded_pkey->pkey.kem_key->secret_key, test.secret_key_len));

  // ---- 6. i2d_PKCS8_PRIV_KEY_INFO output should work with EVP_parse_private_key ----
  CBS cbs;
  CBS_init(&cbs, encoded_der, encoded_der_len);
  bssl::UniquePtr<EVP_PKEY> cross_decoded_pkey(EVP_parse_private_key(&cbs));
  ASSERT_TRUE(cross_decoded_pkey);
  EXPECT_EQ(Bytes(pkey->pkey.kem_key->secret_key, test.secret_key_len),
            Bytes(cross_decoded_pkey->pkey.kem_key->secret_key, test.secret_key_len));
}

// Test cross-compatibility between modern EVP_marshal_* encoding functions d2i_* decoding functions
TEST_P(KEMTest, ASN1_Methods_Cross_Compatibility) {
  const KEMTestVector &test = GetParam();
  
  // ---- 1. Generate a keypair ----
  bssl::UniquePtr<EVP_PKEY> pkey(generate_kem_key_pair(test.nid));
  ASSERT_TRUE(pkey);

// ---- 2. Test if the encoded public key using EVP_marshal_public_key can be decoded using d2i_PUBKEY ----
  bssl::ScopedCBB cbb;
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_public_key(cbb.get(), pkey.get()));
  uint8_t *marshal_der;
  size_t marshal_der_len;
  ASSERT_TRUE(CBB_finish(cbb.get(), &marshal_der, &marshal_der_len));
  bssl::UniquePtr<uint8_t> free_marshal_der(marshal_der);

  const uint8_t *marshal_der_ptr = marshal_der;
  bssl::UniquePtr<EVP_PKEY> decoded_from_marshal(d2i_PUBKEY(nullptr, &marshal_der_ptr, marshal_der_len));
  ASSERT_TRUE(decoded_from_marshal);
  EXPECT_EQ(1, EVP_PKEY_cmp(pkey.get(), decoded_from_marshal.get()));

// ---- 3. Test if the encoded private key using EVP_marshal_private_key can be decoded using d2i_PrivateKey ----
  ASSERT_TRUE(CBB_init(cbb.get(), 0));
  ASSERT_TRUE(EVP_marshal_private_key(cbb.get(), pkey.get()));
  uint8_t *marshal_priv_der;
  size_t marshal_priv_der_len;
  ASSERT_TRUE(CBB_finish(cbb.get(), &marshal_priv_der, &marshal_priv_der_len));
  bssl::UniquePtr<uint8_t> free_marshal_priv_der(marshal_priv_der);

  const uint8_t *marshal_priv_der_ptr = marshal_priv_der;
  bssl::UniquePtr<EVP_PKEY> decoded_priv_from_marshal(d2i_PrivateKey(EVP_PKEY_KEM, nullptr, 
                                                      &marshal_priv_der_ptr, marshal_priv_der_len));
  ASSERT_TRUE(decoded_priv_from_marshal);
  EXPECT_EQ(Bytes(pkey->pkey.kem_key->secret_key, test.secret_key_len),
            Bytes(decoded_priv_from_marshal->pkey.kem_key->secret_key, test.secret_key_len));
}

