/* Copyright (c) 2018, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include <openssl/pem.h>

#include <gtest/gtest.h>
#include <signal.h>
#if defined(_WIN32)
#include <io.h>
#define dup _dup
#define dup2 _dup2
#define fileno _fileno
#define close _close
#else
#include <unistd.h>
#endif

#include <openssl/asn1.h>
#include <openssl/bio.h>
#include <openssl/cipher.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>

#include "../test/test_util.h"
#include "internal.h"

const char* SECRET = "test";

static int pem_password_callback(char *buf, int size, int rwflag, void *userdata) {
  char* data = (char *)userdata;
  if(size <= 0) {
    return 0;
  }
  return (int)BUF_strlcpy(buf, data, size);
}

// Test that implausible ciphers, notably an IV-less RC4, aren't allowed in PEM.
// This is a regression test for https://github.com/openssl/openssl/issues/6347,
// though our fix differs from upstream.
TEST(PEMTest, NoRC4) {
  static const char kPEM[] =
      "-----BEGIN RSA PUBLIC KEY-----\n"
      "Proc-Type: 4,ENCRYPTED\n"
      "DEK-Info: RC4 -\n"
      "extra-info\n"
      "router-signature\n"
      "\n"
      "Z1w=\n"
      "-----END RSA PUBLIC KEY-----\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(kPEM, sizeof(kPEM) - 1));
  ASSERT_TRUE(bio);
  bssl::UniquePtr<RSA> rsa(PEM_read_bio_RSAPublicKey(
      bio.get(), nullptr, nullptr, const_cast<char *>("password")));
  EXPECT_FALSE(rsa);
  EXPECT_TRUE(
      ErrorEquals(ERR_get_error(), ERR_LIB_PEM, PEM_R_UNSUPPORTED_ENCRYPTION));
}

static void* d2i_ASN1_INTEGER_void(void ** out, const unsigned char **inp, long len) {
  return d2i_ASN1_INTEGER((ASN1_INTEGER **)out, inp, len);
}

static int i2d_ASN1_INTEGER_void(const void *a, unsigned char **out) {
  return i2d_ASN1_INTEGER((ASN1_INTEGER *)a, out);
}

TEST(PEMTest, WriteReadASN1IntegerPem) {
#if defined(OPENSSL_ANDROID)
  // On Android, when running from an APK, |tmpfile| does not work. See
  // b/36991167#comment8.
  GTEST_SKIP();
#endif
  // Numbers for testing
  std::vector<long> nums = {
      0x00000001L,
      0x00000100L,
      0x00010000L,
      0x01000000L,
      -2L};

  for(long original_value: nums) {
    // Create an ASN1_INTEGER with value
    bssl::UniquePtr<ASN1_INTEGER> asn1_int(ASN1_INTEGER_new());
    ASSERT_TRUE(asn1_int);
    ASSERT_TRUE(ASN1_INTEGER_set(asn1_int.get(), original_value));

    // Create buffer for writing
    TempFILE pem_file = createTempFILE();
    ASSERT_TRUE(pem_file);

    // Write the ASN1_INTEGER to a PEM-formatted string
    ASSERT_TRUE(PEM_ASN1_write(i2d_ASN1_INTEGER_void, "ASN1 INTEGER",
                               pem_file.get(), asn1_int.get(), nullptr, nullptr,
                               0, nullptr, nullptr));

    rewind(pem_file.get());
    // Read the ASN1_INTEGER back from the PEM-formatted string
    bssl::UniquePtr<ASN1_INTEGER> read_integer((ASN1_INTEGER *)PEM_ASN1_read(
        d2i_ASN1_INTEGER_void, "ASN1 INTEGER", pem_file.get(), nullptr,
        nullptr, nullptr));
    ASSERT_TRUE(read_integer);

    // Check if the read ASN1_INTEGER has the same value as the original
    long read_value = ASN1_INTEGER_get(read_integer.get());
    ASSERT_EQ(original_value, read_value);
  }
}

const char* kPemRsaPrivateKey = "-----BEGIN ENCRYPTED PRIVATE KEY-----\n"
    "MIHsMFcGCSqGSIb3DQEFDTBKMCkGCSqGSIb3DQEFDDAcBAhz3vU103jx3wICCAAw\n"
    "DAYIKoZIhvcNAgkFADAdBglghkgBZQMEASoEEA6vMhRLgHZuHFa+eiecYCgEgZDB\n"
    "E8EOzjGQuu4D0TVAjOa3Peb9/MzQz3t09m5pvNBFKrEl96gefpZdni5qQk34ukj9\n"
    "/kryXymP72m4Ch7vbmew08x5x9L69BpfsQLF1yyvAJVtEZ0a1Zqcn5veuoH2WtJT\n"
    "ZTrZtc5Eb+tAjMVzRXPZ80cUwCbbpb9KHUX8spwtG10I1VxJ18X31FVpGORdr0A=\n"
    "-----END ENCRYPTED PRIVATE KEY-----";


TEST(PEMTest, ReadPrivateKeyPem) {
  bssl::UniquePtr<BIO> read_bio(BIO_new_mem_buf(kPemRsaPrivateKey, BUF_strnlen(kPemRsaPrivateKey, 2048)) );
  ASSERT_TRUE(read_bio);
  bssl::UniquePtr<EC_KEY> ec_key(PEM_read_bio_ECPrivateKey(read_bio.get(), nullptr, pem_password_callback, (void*)SECRET));
  ASSERT_TRUE(ec_key);
  const EC_GROUP* p256 = EC_GROUP_new_by_curve_name(NID_X9_62_prime256v1);
  ASSERT_EQ(p256, EC_KEY_get0_group(ec_key.get()));
}


TEST(PEMTest, WriteReadRSAPem) {
  bssl::UniquePtr<RSA> rsa(RSA_new());
  ASSERT_TRUE(rsa);
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  ASSERT_TRUE(bn);
  BN_set_u64(bn.get(), RSA_F4);
#if defined(BORINGSSL_FIPS)
  ASSERT_TRUE(RSA_generate_key_fips(rsa.get(), 2048, nullptr));
#else
  ASSERT_TRUE(RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr));
#endif

  bssl::UniquePtr<BIO> write_bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(write_bio);
  const EVP_CIPHER* cipher = EVP_get_cipherbynid(NID_aes_256_cbc);
  ASSERT_TRUE(cipher);
  ASSERT_TRUE(PEM_write_bio_RSAPrivateKey(write_bio.get(), rsa.get(), cipher, (unsigned char*)SECRET, (int)BUF_strnlen(SECRET, 256), nullptr, nullptr));

  const uint8_t* content;
  size_t content_len;
  BIO_mem_contents(write_bio.get(), &content, &content_len);

  bssl::UniquePtr<BIO> read_bio(BIO_new_mem_buf(content, content_len) );
  ASSERT_TRUE(read_bio);
  bssl::UniquePtr<RSA> rsa_read(PEM_read_bio_RSAPrivateKey(read_bio.get(), nullptr, pem_password_callback, (void*)SECRET));
  ASSERT_TRUE(rsa_read);
  ASSERT_EQ(0, BN_cmp(RSA_get0_n(rsa.get()), RSA_get0_n(rsa_read.get())));
}

TEST(PEMTest, WriteReadECPem) {
  bssl::UniquePtr<EC_KEY> ec_key(EC_KEY_new());
  ASSERT_TRUE(ec_key);
  bssl::UniquePtr<EC_GROUP> ec_group(EC_GROUP_new_by_curve_name(NID_X9_62_prime256v1));
  ASSERT_TRUE(ec_group);
  ASSERT_TRUE(EC_KEY_set_group(ec_key.get(), ec_group.get()));

#if defined(BORINGSSL_FIPS)
  ASSERT_TRUE(EC_KEY_generate_key_fips(ec_key.get()));
#else
  ASSERT_TRUE(EC_KEY_generate_key(ec_key.get()));
#endif

  bssl::UniquePtr<BIO> write_bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(write_bio);
  const EVP_CIPHER* cipher = EVP_get_cipherbynid(NID_aes_256_cbc);
  ASSERT_TRUE(cipher);
  ASSERT_TRUE(PEM_write_bio_ECPrivateKey(write_bio.get(), ec_key.get(), cipher, nullptr, 0, pem_password_callback, (void*)SECRET));

  const uint8_t* content;
  size_t content_len;
  BIO_mem_contents(write_bio.get(), &content, &content_len);

  bssl::UniquePtr<BIO> read_bio(BIO_new_mem_buf(content, content_len) );
  ASSERT_TRUE(read_bio);
  bssl::UniquePtr<EC_KEY> ec_key_read(PEM_read_bio_ECPrivateKey(read_bio.get(), nullptr, pem_password_callback, (void*)"test"));
  ASSERT_TRUE(ec_key_read);
  const BIGNUM* orig_priv_key = EC_KEY_get0_private_key(ec_key.get());
  const BIGNUM* read_priv_key = EC_KEY_get0_private_key(ec_key_read.get());
  ASSERT_EQ(0, BN_cmp(orig_priv_key, read_priv_key));
}

const char *kPemECPARAMETERS =
    "-----BEGIN EC PARAMETERS-----\n"
    "BgUrgQQAIw==\n"
    "-----END EC PARAMETERS-----\n";

const char *kPemExplictECPARAMETERS =
    "-----BEGIN EC PARAMETERS-----\n"
    "MIH3AgEBMCwGByqGSM49AQECIQD/////AAAAAQAAAAAAAAAAAAAAAP//////////"
    "/////zBbBCD/////AAAAAQAAAAAAAAAAAAAAAP///////////////AQgWsY12Ko6"
    "k+ez671VdpiGvGUdBrDMU7D2O848PifSYEsDFQDEnTYIhucEk2pmeOETnSa3gZ9+"
    "kARBBGsX0fLhLEJH+Lzm5WOkQPJ3A32BLeszoPShOUXYmMKWT+NC4v4af5uO5+tK"
    "fA+eFivOM1drMV7Oy7ZAaDe/UfUCIQD/////AAAAAP//////////vOb6racXnoTz"
    "ucrC/GMlUQIBAQ==\n"
    "-----END EC PARAMETERS-----\n";

TEST(PEMTest, WriteReadECPKPem) {
  // Check named curve can be outputted to a PEM file.
  bssl::UniquePtr<EC_GROUP> group(EC_GROUP_new_by_curve_name(NID_secp521r1));
  ASSERT_TRUE(group);
  bssl::UniquePtr<BIO> write_bio(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(write_bio);
  ASSERT_TRUE(PEM_write_bio_ECPKParameters(write_bio.get(), group.get()));

  const uint8_t *content;
  size_t content_len;
  BIO_mem_contents(write_bio.get(), &content, &content_len);
  EXPECT_EQ(Bytes(content, content_len), Bytes(kPemECPARAMETERS));

  // Check named curve of a PEM file can be parsed.
  bssl::UniquePtr<BIO> read_bio(
      BIO_new_mem_buf(kPemECPARAMETERS, strlen(kPemECPARAMETERS)));
  bssl::UniquePtr<EC_GROUP> read_group(
      PEM_read_bio_ECPKParameters(read_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(read_group);
  ASSERT_EQ(EC_GROUP_cmp(EC_group_p521(), read_group.get(), nullptr), 0);


  // Make an arbitrary curve which is identical to P-256.
  static const uint8_t kP[] = {
      0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  };
  static const uint8_t kA[] = {
      0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfc,
  };
  static const uint8_t kB[] = {
      0x5a, 0xc6, 0x35, 0xd8, 0xaa, 0x3a, 0x93, 0xe7, 0xb3, 0xeb, 0xbd,
      0x55, 0x76, 0x98, 0x86, 0xbc, 0x65, 0x1d, 0x06, 0xb0, 0xcc, 0x53,
      0xb0, 0xf6, 0x3b, 0xce, 0x3c, 0x3e, 0x27, 0xd2, 0x60, 0x4b,
  };
  bssl::UniquePtr<BIGNUM> p(BN_bin2bn(kP, sizeof(kP), nullptr)),
      a(BN_bin2bn(kA, sizeof(kA), nullptr)),
      b(BN_bin2bn(kB, sizeof(kB), nullptr));
  ASSERT_TRUE(p && a && b);

  // Writing custom curves, even if the parameters are identical to a named
  // curve, will result in an error
  bssl::UniquePtr<EC_GROUP> custom_group(
      EC_GROUP_new_curve_GFp(p.get(), a.get(), b.get(), nullptr));
  write_bio.reset(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(write_bio);
  EXPECT_FALSE(
      PEM_write_bio_ECPKParameters(write_bio.get(), custom_group.get()));

  // Check that explicitly-encoded versions of namedCurves can be correctly
  // parsed from a PEM file.
  read_bio.reset(BIO_new_mem_buf(
      kPemExplictECPARAMETERS, strlen(kPemExplictECPARAMETERS)));
  read_group.reset(
      PEM_read_bio_ECPKParameters(read_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(read_group);
  ASSERT_EQ(EC_GROUP_cmp(EC_group_p256(), read_group.get(), nullptr), 0);
}

TEST(ParametersTest, PEMReadwrite) {
  // Test |PEM_read/write_bio_Parameters| with |EC_KEY|.
  bssl::UniquePtr<EC_KEY> ec_key(EC_KEY_new());
  ASSERT_TRUE(ec_key);
  bssl::UniquePtr<EC_GROUP> ec_group(EC_GROUP_new_by_curve_name(NID_secp384r1));
  ASSERT_TRUE(ec_group);
  ASSERT_TRUE(EC_KEY_set_group(ec_key.get(), ec_group.get()));
  ASSERT_TRUE(EC_KEY_generate_key(ec_key.get()));

  bssl::UniquePtr<BIO> write_bio(BIO_new(BIO_s_mem()));
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  ASSERT_TRUE(EVP_PKEY_set1_EC_KEY(pkey.get(), ec_key.get()));
  EXPECT_TRUE(PEM_write_bio_Parameters(write_bio.get(), pkey.get()));

  const uint8_t *content;
  size_t content_len;
  BIO_mem_contents(write_bio.get(), &content, &content_len);

  bssl::UniquePtr<BIO> read_bio(BIO_new_mem_buf(content, content_len));
  ASSERT_TRUE(read_bio);
  bssl::UniquePtr<EVP_PKEY> pkey_read(
      PEM_read_bio_Parameters(read_bio.get(), nullptr));
  ASSERT_TRUE(pkey_read);

  EC_KEY *pkey_eckey = EVP_PKEY_get0_EC_KEY(pkey.get());
  ASSERT_TRUE(pkey_eckey);
  const EC_GROUP *orig_params = EC_KEY_get0_group(pkey_eckey);
  ASSERT_TRUE(orig_params);
  const EC_GROUP *read_params = EC_KEY_get0_group(pkey_eckey);
  ASSERT_TRUE(read_params);
  ASSERT_EQ(0, EC_GROUP_cmp(orig_params, read_params, nullptr));

  // Test |PEM_read/write_bio_Parameters| with |DH|.
  bssl::UniquePtr<BIGNUM> p(BN_get_rfc3526_prime_1536(nullptr));
  ASSERT_TRUE(p);
  bssl::UniquePtr<BIGNUM> g(BN_new());
  ASSERT_TRUE(g);
  ASSERT_TRUE(BN_set_u64(g.get(), 2));
  bssl::UniquePtr<DH> dh(DH_new());
  ASSERT_TRUE(dh);
  ASSERT_TRUE(DH_set0_pqg(dh.get(), p.release(), nullptr, g.release()));
  write_bio.reset(BIO_new(BIO_s_mem()));
  pkey.reset(EVP_PKEY_new());
  ASSERT_TRUE(EVP_PKEY_set1_DH(pkey.get(), dh.get()));
  EXPECT_TRUE(PEM_write_bio_Parameters(write_bio.get(), pkey.get()));

  BIO_mem_contents(write_bio.get(), &content, &content_len);
  read_bio.reset(BIO_new_mem_buf(content, content_len));
  ASSERT_TRUE(read_bio);
  pkey_read.reset(PEM_read_bio_Parameters(read_bio.get(), nullptr));
  ASSERT_TRUE(pkey_read);

  DH *pkey_dh = EVP_PKEY_get0_DH(pkey.get());
  ASSERT_TRUE(pkey_dh);
  EXPECT_EQ(0, BN_cmp(DH_get0_p(pkey_dh), DH_get0_p(dh.get())));
  EXPECT_EQ(0, BN_cmp(DH_get0_g(pkey_dh), DH_get0_g(dh.get())));

  // Test |PEM_read/write_bio_Parameters| with |DSA|.
  bssl::UniquePtr<DSA> dsa(DSA_new());
  ASSERT_TRUE(dsa);
  uint8_t seed[20];
  ASSERT_TRUE(RAND_bytes(seed, sizeof(seed)));
  ASSERT_TRUE(DSA_generate_parameters_ex(dsa.get(), 512, seed, sizeof(seed),
                                         nullptr, nullptr, nullptr));
  ASSERT_TRUE(DSA_generate_key(dsa.get()));

  write_bio.reset(BIO_new(BIO_s_mem()));
  pkey.reset(EVP_PKEY_new());
  ASSERT_TRUE(EVP_PKEY_set1_DSA(pkey.get(), dsa.get()));
  EXPECT_TRUE(PEM_write_bio_Parameters(write_bio.get(), pkey.get()));

  BIO_mem_contents(write_bio.get(), &content, &content_len);
  read_bio.reset(BIO_new_mem_buf(content, content_len));
  ASSERT_TRUE(read_bio);
  pkey_read.reset(PEM_read_bio_Parameters(read_bio.get(), nullptr));
  ASSERT_TRUE(pkey_read);

  DSA *pkey_dsa = EVP_PKEY_get0_DSA(pkey.get());
  EXPECT_EQ(0, BN_cmp(DSA_get0_p(pkey_dsa), DSA_get0_p(dsa.get())));
  EXPECT_EQ(0, BN_cmp(DSA_get0_g(pkey_dsa), DSA_get0_g(dsa.get())));
}

const char *kRubyPemDHPARAMETERS =
    "-----BEGIN DH PARAMETERS-----\n"
    "MIIBCAKCAQEA7E6kBrYiyvmKAMzQ7i8WvwVk9Y/+f8S7sCTN712KkK3cqd1jhJDY"
    "JbrYeNV3kUIKhPxWHhObHKpD1R84UpL+s2b55+iMd6GmL7OYmNIT/FccKhTcveab"
    "VBmZT86BZKYyf45hUF9FOuUM9xPzuK3Vd8oJQvfYMCd7LPC0taAEljQLR4Edf8E6"
    "YoaOffgTf5qxiwkjnlVZQc3whgnEt9FpVMvQ9eknyeGB5KHfayAc3+hUAvI3/Cr3"
    "1bNveX5wInh5GDx1FGhKBZ+s1H+aedudCm7sCgRwv8lKWYGiHzObSma8A86KG+MD"
    "7Lo5JquQ3DlBodj3IDyPrxIv96lvRPFtAwIBAg==\n"
    "-----END DH PARAMETERS-----\n";

TEST(ParametersTest, RubyDHFile) {
  bssl::UniquePtr<BIO> read_bio(
      BIO_new_mem_buf(kRubyPemDHPARAMETERS, strlen(kRubyPemDHPARAMETERS)));
  ASSERT_TRUE(read_bio);
  bssl::UniquePtr<EVP_PKEY> pkey_read(
      PEM_read_bio_Parameters(read_bio.get(), nullptr));
  ASSERT_TRUE(pkey_read);
  bssl::UniquePtr<DH> dh(EVP_PKEY_get1_DH(pkey_read.get()));
  EXPECT_TRUE(dh);
  EXPECT_EQ(DH_num_bits(dh.get()), 2048u);
}

TEST(PEMTest, WriteReadTraditionalPem) {
  // Test |PEM_write_bio_PrivateKey_traditional| with |EC_KEY|.
  bssl::UniquePtr<EC_KEY> ec_key(EC_KEY_new());
  ASSERT_TRUE(ec_key);
  bssl::UniquePtr<EC_GROUP> ec_group(EC_GROUP_new_by_curve_name(NID_secp256k1));
  ASSERT_TRUE(ec_group);
  ASSERT_TRUE(EC_KEY_set_group(ec_key.get(), ec_group.get()));
  ASSERT_TRUE(EC_KEY_generate_key(ec_key.get()));

  bssl::UniquePtr<BIO> write_bio(BIO_new(BIO_s_mem()));
  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  ASSERT_TRUE(EVP_PKEY_set1_EC_KEY(pkey.get(), ec_key.get()));
  EXPECT_TRUE(PEM_write_bio_PrivateKey_traditional(
      write_bio.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));

  const uint8_t *content;
  size_t content_len;
  BIO_mem_contents(write_bio.get(), &content, &content_len);

  bssl::UniquePtr<BIO> read_bio(BIO_new_mem_buf(content, content_len));
  ASSERT_TRUE(read_bio);
  bssl::UniquePtr<EVP_PKEY> pkey_read(
      PEM_read_bio_PrivateKey(read_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(pkey_read);

  EC_KEY *pkey_eckey = EVP_PKEY_get0_EC_KEY(pkey.get());
  ASSERT_TRUE(pkey_eckey);
  const BIGNUM *orig_priv_key = EC_KEY_get0_private_key(ec_key.get());
  const BIGNUM *read_priv_key = EC_KEY_get0_private_key(pkey_eckey);
  ASSERT_EQ(0, BN_cmp(orig_priv_key, read_priv_key));

  // Test |PEM_write_bio_PrivateKey_traditional| with |RSA|.
  bssl::UniquePtr<BIGNUM> e(BN_new());
  ASSERT_TRUE(e);
  ASSERT_TRUE(BN_set_word(e.get(), RSA_F4));
  bssl::UniquePtr<RSA> rsa(RSA_new());
  ASSERT_TRUE(rsa);
  ASSERT_TRUE(RSA_generate_key_ex(rsa.get(), 1024, e.get(), nullptr));

  write_bio.reset(BIO_new(BIO_s_mem()));
  pkey.reset(EVP_PKEY_new());
  ASSERT_TRUE(EVP_PKEY_set1_RSA(pkey.get(), rsa.get()));
  EXPECT_TRUE(PEM_write_bio_PrivateKey_traditional(
      write_bio.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));

  BIO_mem_contents(write_bio.get(), &content, &content_len);
  read_bio.reset(BIO_new_mem_buf(content, content_len));
  ASSERT_TRUE(read_bio);
  pkey_read.reset(
      PEM_read_bio_PrivateKey(read_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(pkey_read);

  RSA *pkey_rsa = EVP_PKEY_get0_RSA(pkey.get());
  ASSERT_TRUE(pkey_rsa);
  EXPECT_EQ(0, BN_cmp(RSA_get0_d(pkey_rsa), RSA_get0_d(rsa.get())));
  EXPECT_EQ(0, BN_cmp(RSA_get0_d(pkey_rsa), RSA_get0_d(rsa.get())));

  // Test |PEM_write_bio_PrivateKey_traditional| with |DSA|.
  bssl::UniquePtr<DSA> dsa(DSA_new());
  ASSERT_TRUE(dsa);
  uint8_t seed[20];
  ASSERT_TRUE(RAND_bytes(seed, sizeof(seed)));
  ASSERT_TRUE(DSA_generate_parameters_ex(dsa.get(), 512, seed, sizeof(seed),
                                         nullptr, nullptr, nullptr));
  ASSERT_TRUE(DSA_generate_key(dsa.get()));

  write_bio.reset(BIO_new(BIO_s_mem()));
  pkey.reset(EVP_PKEY_new());
  ASSERT_TRUE(EVP_PKEY_set1_DSA(pkey.get(), dsa.get()));
  EXPECT_TRUE(PEM_write_bio_PrivateKey_traditional(
      write_bio.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));

  BIO_mem_contents(write_bio.get(), &content, &content_len);
  read_bio.reset(BIO_new_mem_buf(content, content_len));
  ASSERT_TRUE(read_bio);
  pkey_read.reset(
      PEM_read_bio_PrivateKey(read_bio.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(pkey_read);

  DSA *pkey_dsa = EVP_PKEY_get0_DSA(pkey.get());
  EXPECT_EQ(0, BN_cmp(DSA_get0_priv_key(pkey_dsa), DSA_get0_priv_key(dsa.get())));

  // Test |PEM_write_bio_PrivateKey_traditional| with |DH|. This should fail,
  // since it's not supported by the API.
  bssl::UniquePtr<BIGNUM> p(BN_get_rfc3526_prime_1536(nullptr));
  ASSERT_TRUE(p);
  bssl::UniquePtr<BIGNUM> g(BN_new());
  ASSERT_TRUE(g);
  ASSERT_TRUE(BN_set_u64(g.get(), 2));
  bssl::UniquePtr<DH> dh(DH_new());
  ASSERT_TRUE(dh);
  ASSERT_TRUE(DH_set0_pqg(dh.get(), p.release(), nullptr, g.release()));
  write_bio.reset(BIO_new(BIO_s_mem()));
  pkey.reset(EVP_PKEY_new());
  ASSERT_TRUE(EVP_PKEY_set1_DH(pkey.get(), dh.get()));
  EXPECT_FALSE(PEM_write_bio_PrivateKey_traditional(
      write_bio.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));
}

// Consolidated password testing
class PemPasswdTest : public testing::Test {
 protected:
  void SetUp() override {
    // Save original file descriptors
    original_stdin = dup(fileno(stdin));
    original_stderr = dup(fileno(stderr));
    
    // Create temporary files
    stdin_file = tmpfile();
    stderr_file = tmpfile();
    ASSERT_TRUE(stdin_file != nullptr);
    ASSERT_TRUE(stderr_file != nullptr);
    
    // Redirect stdin/stderr to our temp files
    ASSERT_NE(-1, dup2(fileno(stdin_file), fileno(stdin)));
    ASSERT_NE(-1, dup2(fileno(stderr_file), fileno(stderr)));
    
    // Initialize console for each test
    ASSERT_TRUE(openssl_console_open());
  }

  void TearDown() override {
    // Close console for each test
    ASSERT_TRUE(openssl_console_close());
    
    // Restore original streams
    ASSERT_NE(-1, dup2(original_stdin, fileno(stdin)));
    ASSERT_NE(-1, dup2(original_stderr, fileno(stderr)));
    close(original_stdin);
    close(original_stderr);
    
    // Close temp files
    if (stdin_file) fclose(stdin_file);
    if (stderr_file) fclose(stderr_file);
  }

  void MockStdinInput(const std::string& input) {
    ftruncate(fileno(stdin_file), 0);
    rewind(stdin_file);
    ASSERT_GT(fwrite(input.c_str(), 1, input.length(), stdin_file), (size_t)0);
    rewind(stdin_file);
  }

  std::string GetStderrOutput() {
    std::string output;
    char buf[1024];
    rewind(stderr_file);
    while (fgets(buf, sizeof(buf), stderr_file) != nullptr) {
      output += buf;
    }

    // Clear the file for next read
    ftruncate(fileno(stderr_file), 0); 
    rewind(stderr_file);
    return output;
  }

  FILE* stdin_file = nullptr;
  FILE* stderr_file = nullptr;
  int original_stdin = -1;
  int original_stderr = -1;
  const char* default_prompt = "Enter password:";
};

// Test basic password functionality with various inputs
TEST_F(PemPasswdTest, PasswordInputVariations) {
  struct TestCase {
    std::string description;
    std::string input;
    int min_size;
    int expected_result;
    std::string expected_output;
  };
  
  std::vector<TestCase> test_cases = {
    // Normal password
    {"Normal password", "test_password\n", 0, 0, "test_password"},
    //
    // // Empty password
    {"Empty password allowed", "\n", 0, 0, ""},
    {"Empty password rejected", "\n", 2, -1, ""},
    
    // Length requirements
    {"Password too short", "short\n", 10, -1, "short"},
    {"Password meets min length", "longenoughpass\n", 10, 0, "longenoughpass"},
    
    // Special characters
    {"Special characters", "!@#$%^&*()\n", 0, 0, "!@#$%^&*()"},
    {"Unicode characters", "パスワード\n", 0, 0, "パスワード"}
  };
  
  for (const auto& tc : test_cases) {
    SCOPED_TRACE(tc.description);
    
    char buf[1024] = {0};
    MockStdinInput(tc.input);

    ASSERT_TRUE(openssl_console_write(default_prompt));
    ASSERT_EQ(openssl_console_read(buf, tc.min_size, sizeof(buf), 0), tc.expected_result);
    
    if (tc.expected_result == 0) {
      ASSERT_STREQ(buf, tc.expected_output.c_str());
    }
    
    // Verify prompt was written
    std::string output = GetStderrOutput();
    ASSERT_TRUE(output.find(default_prompt) != std::string::npos);
  }
}

// Test password verification flow (matching and non-matching)
TEST_F(PemPasswdTest, PasswordVerification) {
  struct TestCase {
    std::string description;
    std::string first_password;
    std::string second_password;
    bool should_match;
  };
  
  std::vector<TestCase> test_cases = {
    {"Matching passwords", "test_password\n", "test_password\n", true},
    {"Non-matching passwords", "password1\n", "password2\n", false}
  };
  
  for (const auto& tc : test_cases) {
    SCOPED_TRACE(tc.description);
    
    char buf1[1024] = {0};
    char buf2[1024] = {0};
    
    // Mock both password inputs
    std::string combined_input = tc.first_password + tc.second_password;
    MockStdinInput(combined_input);
    
    // First password entry
    ASSERT_TRUE(openssl_console_write(default_prompt));
    ASSERT_EQ(0, openssl_console_read(buf1, 0, sizeof(buf1), 0));
    
    // Verification prompt
    ASSERT_TRUE(openssl_console_write("Verifying - "));
    ASSERT_TRUE(openssl_console_write(default_prompt));
    ASSERT_EQ(0, openssl_console_read(buf2, 0, sizeof(buf2), 0));
    
    // Verify match/mismatch as expected
    if (tc.should_match) {
      ASSERT_STREQ(buf1, buf2);
    } else {
      ASSERT_STRNE(buf1, buf2);
    }
    
    // Verify prompts were written
    std::string output = GetStderrOutput();
    ASSERT_TRUE(output.find(default_prompt) != std::string::npos);
    ASSERT_TRUE(output.find("Verifying - ") != std::string::npos);
  }
}

// Test buffer handling (truncation of long passwords)
TEST_F(PemPasswdTest, BufferHandling) {
  // Small buffer to test truncation
  char small_buf[16] = {0};
  
  // Create a password longer than the buffer
  std::string long_password(32, 'a');
  long_password += "\n";
  
  MockStdinInput(long_password);
  ASSERT_TRUE(openssl_console_write(default_prompt));
  ASSERT_EQ(0, openssl_console_read(small_buf, 0, sizeof(small_buf),0));
  
  // Verify the password was truncated to fit the buffer (15 chars + null terminator)
  std::string expected(15, 'a');
  ASSERT_STREQ(small_buf, expected.c_str());
}

// Test echo modes
TEST_F(PemPasswdTest, EchoModes) {
  const char* test_password = "test_password\n";
  char buf_no_echo[1024] = {0};
  char buf_with_echo[1024] = {0};
  
  // Test with echo disabled
  MockStdinInput(test_password);
  ASSERT_TRUE(openssl_console_write(default_prompt));
  ASSERT_EQ(0, openssl_console_read(buf_no_echo, 0, sizeof(buf_no_echo), 0));
  
  // Test with echo enabled
  MockStdinInput(test_password);
  ASSERT_TRUE(openssl_console_write(default_prompt));
  ASSERT_EQ(0, openssl_console_read(buf_with_echo, 0, sizeof(buf_with_echo), 1));
  
  // Both should have the same result
  ASSERT_STREQ(buf_no_echo, "test_password");
  ASSERT_STREQ(buf_with_echo, "test_password");
}

// Test the behavior of the password callback function
TEST(PemPasswordCallbackTest, BasicCallback) {
  // Test normal case - verify the buffer is filled correctly
  {
    char buf[1024] = {0};
    const char* test_secret = "test_secret";
    
    // We don't care about the return value, just the buffer contents
    (void)pem_password_callback(buf, sizeof(buf), 0, (void*)test_secret);
    ASSERT_STREQ(buf, test_secret);
  }
  
  // Test with small buffer - should truncate
  {
    char small_buf[5] = {0};
    const char* test_secret = "test_secret";
    
    (void)pem_password_callback(small_buf, sizeof(small_buf), 0, (void*)test_secret);
    ASSERT_STREQ(small_buf, "test"); // Should be truncated
  }
  
  // Test with zero size buffer - should not modify the buffer
  {
    char zero_buf[1] = {'X'};
    const char* test_secret = "test_secret";
    
    // For zero size, we know it returns 0 per the function definition
    int zero_result = pem_password_callback(zero_buf, 0, 0, (void*)test_secret);
    ASSERT_EQ(zero_result, 0); // Should return 0 for size <= 0
    ASSERT_EQ(zero_buf[0], 'X'); // Buffer should be unchanged
  }
}
