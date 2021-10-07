/* Copyright (c) 2020, Google Inc.
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

#include <openssl/cpucycles.h>
#include <openssl/hpke.h>

#include <cstdint>
#include <limits>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/base.h>
#include <openssl/curve25519.h>

#include <openssl/sike_internal.h>

#include <openssl/digest.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/sha.h>
#include <openssl/span.h>

#include "../test/file_test.h"
#include "../test/test_util.h"


#include <stdint.h>
#include <time.h>

#define SIZE_PLAINTEXT 10000000  // Specify Bytes to be encrypted/decrypted
#define NUMBER_TESTS 100        // Number of tests performed


uint64_t cpucycles(void) {  // Access system counter for benchmarking
  unsigned int hi, lo;
  __asm volatile("rdtsc\n\t" : "=a"(lo), "=d"(hi));
  return ((int64_t)lo) | (((int64_t)hi) << 32);
}


void print_info(int aead, int kdf);

void print_info(int aead, int kdf) {
  printf("\n\n-------------------------------------------------------");
  printf("\nAEAD               ->   ");
  switch (aead) {
    case 0x0001:
      printf("EVP_HPKE_AES_128_GCM");
      break;
    case 0x0002:
      printf("EVP_HPKE_AES_256_GCM");
      break;
    case 0x0003:
      printf("EVP_HPKE_CHACHA20_POLY1305");
      break;
    default:
      printf("Should never happen");
      break;
  }

  printf("\nKDF                ->   ");
  switch (kdf) {
    case 0x0001:
      printf("EVP_HPKE_HKDF_SHA256");
      break;
    default:
      printf("Should never happen");
      break;
  }
  
  printf("\n");
}

void init_plaintext(uint8_t *plaintext, int size);
void init_plaintext(uint8_t *plaintext, int size) {
  for (int i = 0; i < size; i++) {
    plaintext[i] = (uint8_t)((uint8_t)i % 256);
    // printf("%02x", (uint8_t)plaintext[i]);
  }
}

void print_text(std::vector<uint8_t> cleartext, int cleartext_len);
void print_text(std::vector<uint8_t> cleartext, int cleartext_len) {
  for (int i = 0; i < cleartext_len; i++) {
    printf("%02x ", cleartext.at(i));
  }
  printf("\n");
}

namespace bssl {
namespace {

const decltype(&EVP_hpke_aes_128_gcm) kAllAEADs[] = {
    &EVP_hpke_aes_128_gcm,
    &EVP_hpke_aes_256_gcm,
    &EVP_hpke_chacha20_poly1305,
};

const decltype(&EVP_hpke_hkdf_sha256) kAllKDFs[] = {
    &EVP_hpke_hkdf_sha256,
};

// HPKETestVector corresponds to one array member in the published
// test-vectors.json.
class HPKETestVector {
 public:
  explicit HPKETestVector() = default;
  ~HPKETestVector() = default;

  bool ReadFromFileTest(FileTest *t);

  void Verify() const {
    const EVP_HPKE_KEM *kem = EVP_hpke_SIKE_hkdf_sha256();
    const EVP_HPKE_AEAD *aead = GetAEAD();
    ASSERT_TRUE(aead);
    const EVP_HPKE_KDF *kdf = GetKDF();
    ASSERT_TRUE(kdf);

    // Test the sender.
    ScopedEVP_HPKE_CTX sender_ctx;
    uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
    size_t enc_len;
    ASSERT_TRUE(EVP_HPKE_CTX_setup_sender_with_seed_for_testing(
        sender_ctx.get(), enc, &enc_len, sizeof(enc), kem, kdf, aead,
        public_key_r_.data(), public_key_r_.size(), info_.data(), info_.size(),
        secret_key_e_.data(), secret_key_e_.size()));
    EXPECT_EQ(Bytes(enc, enc_len), Bytes(public_key_e_));
    VerifySender(sender_ctx.get());

    // Test the recipient.
    ScopedEVP_HPKE_KEY base_key;
    ASSERT_TRUE(EVP_HPKE_KEY_init(base_key.get(), kem, secret_key_r_.data(),
                                  secret_key_r_.size()));
    for (bool copy : {false, true}) {
      SCOPED_TRACE(copy);
      const EVP_HPKE_KEY *key = base_key.get();
      ScopedEVP_HPKE_KEY key_copy;
      if (copy) {
        ASSERT_TRUE(EVP_HPKE_KEY_copy(key_copy.get(), base_key.get()));
        key = key_copy.get();
      }

      uint8_t public_key[EVP_HPKE_MAX_PUBLIC_KEY_LENGTH];
      size_t public_key_len;
      ASSERT_TRUE(EVP_HPKE_KEY_public_key(key, public_key, &public_key_len,
                                          sizeof(public_key)));
      EXPECT_EQ(Bytes(public_key, public_key_len), Bytes(public_key_r_));

      uint8_t private_key[EVP_HPKE_MAX_PRIVATE_KEY_LENGTH];
      size_t private_key_len;
      ASSERT_TRUE(EVP_HPKE_KEY_private_key(key, private_key, &private_key_len,
                                           sizeof(private_key)));
      EXPECT_EQ(Bytes(private_key, private_key_len), Bytes(secret_key_r_));

      // Set up the recipient.
      ScopedEVP_HPKE_CTX recipient_ctx;
      ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(recipient_ctx.get(), key, kdf,
                                               aead, enc, enc_len, info_.data(),
                                               info_.size()));

      VerifyRecipient(recipient_ctx.get());
    }
  }

 private:
  const EVP_HPKE_AEAD *GetAEAD() const {
    for (const auto aead : kAllAEADs) {
      if (EVP_HPKE_AEAD_id(aead()) == aead_id_) {
        return aead();
      }
    }
    return nullptr;
  }

  const EVP_HPKE_KDF *GetKDF() const {
    for (const auto kdf : kAllKDFs) {
      if (EVP_HPKE_KDF_id(kdf()) == kdf_id_) {
        return kdf();
      }
    }
    return nullptr;
  }

  void VerifySender(EVP_HPKE_CTX *ctx) const {
    for (const Encryption &task : encryptions_) {
      std::vector<uint8_t> encrypted(task.plaintext.size() +
                                     EVP_HPKE_CTX_max_overhead(ctx));
      size_t encrypted_len;
      ASSERT_TRUE(EVP_HPKE_CTX_seal(ctx, encrypted.data(), &encrypted_len,
                                    encrypted.size(), task.plaintext.data(),
                                    task.plaintext.size(), task.aad.data(),
                                    task.aad.size()));

      ASSERT_EQ(Bytes(encrypted.data(), encrypted_len), Bytes(task.ciphertext));
    }
    VerifyExports(ctx);
  }

  void VerifyRecipient(EVP_HPKE_CTX *ctx) const {
    for (const Encryption &task : encryptions_) {
      std::vector<uint8_t> decrypted(task.ciphertext.size());
      size_t decrypted_len;
      ASSERT_TRUE(EVP_HPKE_CTX_open(ctx, decrypted.data(), &decrypted_len,
                                    decrypted.size(), task.ciphertext.data(),
                                    task.ciphertext.size(), task.aad.data(),
                                    task.aad.size()));

      ASSERT_EQ(Bytes(decrypted.data(), decrypted_len), Bytes(task.plaintext));
    }
    VerifyExports(ctx);
  }

  void VerifyExports(EVP_HPKE_CTX *ctx) const {
    for (const Export &task : exports_) {
      std::vector<uint8_t> exported_secret(task.export_length);

      ASSERT_TRUE(EVP_HPKE_CTX_export(
          ctx, exported_secret.data(), exported_secret.size(),
          task.exporter_context.data(), task.exporter_context.size()));
      ASSERT_EQ(Bytes(exported_secret), Bytes(task.exported_value));
    }
  }

  struct Encryption {
    std::vector<uint8_t> aad;
    std::vector<uint8_t> ciphertext;
    std::vector<uint8_t> plaintext;
  };

  struct Export {
    std::vector<uint8_t> exporter_context;
    size_t export_length;
    std::vector<uint8_t> exported_value;
  };

  uint16_t kdf_id_;
  uint16_t aead_id_;
  std::vector<uint8_t> context_;
  std::vector<uint8_t> info_;
  std::vector<uint8_t> public_key_e_;
  std::vector<uint8_t> secret_key_e_;
  std::vector<uint8_t> public_key_r_;
  std::vector<uint8_t> secret_key_r_;
  std::vector<Encryption> encryptions_;
  std::vector<Export> exports_;
};

// Match FileTest's naming scheme for duplicated attribute names.
std::string BuildAttrName(const std::string &name, int iter) {
  return iter == 1 ? name : name + "/" + std::to_string(iter);
}

// Parses |s| as an unsigned integer of type T and writes the value to |out|.
// Returns true on success. If the integer value exceeds the maximum T value,
// returns false.
template <typename T>
bool ParseIntSafe(T *out, const std::string &s) {
  T value = 0;
  for (char c : s) {
    if (c < '0' || c > '9') {
      return false;
    }
    if (value > (std::numeric_limits<T>::max() - (c - '0')) / 10) {
      return false;
    }
    value = 10 * value + (c - '0');
  }
  *out = value;
  return true;
}

// Read the |key| attribute from |file_test| and convert it to an integer.
template <typename T>
bool FileTestReadInt(FileTest *file_test, T *out, const std::string &key) {
  std::string s;
  return file_test->GetAttribute(&s, key) && ParseIntSafe(out, s);
}


bool HPKETestVector::ReadFromFileTest(FileTest *t) {
  uint8_t mode = 0;
  if (!FileTestReadInt(t, &mode, "mode") || mode != 0 /* mode_base */ ||
      !FileTestReadInt(t, &kdf_id_, "kdf_id") ||
      !FileTestReadInt(t, &aead_id_, "aead_id") ||
      !t->GetBytes(&info_, "info") || !t->GetBytes(&secret_key_r_, "skRm") ||
      !t->GetBytes(&public_key_r_, "pkRm") ||
      !t->GetBytes(&secret_key_e_, "skEm") ||
      !t->GetBytes(&public_key_e_, "pkEm")) {
    return false;
  }

  for (int i = 1; t->HasAttribute(BuildAttrName("aad", i)); i++) {
    Encryption encryption;
    if (!t->GetBytes(&encryption.aad, BuildAttrName("aad", i)) ||
        !t->GetBytes(&encryption.ciphertext, BuildAttrName("ciphertext", i)) ||
        !t->GetBytes(&encryption.plaintext, BuildAttrName("plaintext", i))) {
      return false;
    }
    encryptions_.push_back(std::move(encryption));
  }

  for (int i = 1; t->HasAttribute(BuildAttrName("exporter_context", i)); i++) {
    Export exp;
    if (!t->GetBytes(&exp.exporter_context,
                     BuildAttrName("exporter_context", i)) ||
        !FileTestReadInt(t, &exp.export_length, BuildAttrName("L", i)) ||
        !t->GetBytes(&exp.exported_value, BuildAttrName("exported_value", i))) {
      return false;
    }
    exports_.push_back(std::move(exp));
  }
  return true;
}

}  // namespace

TEST(HPKETest, VerifyTestVectors) {
  FileTestGTest("crypto/hpke/hpke_test_vectors.txt", [](FileTest *t) {
    HPKETestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    test_vec.Verify();
  });
}



// The test vectors used fixed sender ephemeral keys, while HPKE itself
// generates new keys for each context. Test this codepath by checking we can
// decrypt our own messages.



TEST(HPKETest, x25519) {
  const uint8_t info_a[] = {1, 1, 2, 3, 5, 8};
  const uint8_t info_b[] = {42, 42, 42};
  const uint8_t ad_a[] = {1, 2, 4, 8, 16};
  const uint8_t ad_b[] = {7};
  Span<const uint8_t> info_values[] = {{nullptr, 0}, info_a, info_b};
  Span<const uint8_t> ad_values[] = {{nullptr, 0}, ad_a, ad_b};
  // Span<const uint8_t> info_values[] = {{nullptr, 0}};
  // Span<const uint8_t> ad_values[] = {{nullptr, 0}};
  unsigned long long cycles_set_up_sender_total = 0,
                     cycles_set_up_recipient_total = 0, cycles_seal_total = 0,
                     cycles_open_total = 0, cycles_protocol_total = 0, clean_protocol = 0;
  unsigned long long cycles_set_up_sender, cycles_set_up_recipient, cycles_seal,
      cycles_open, cycles_protocol;


  // execute Bob keygen
  // pk_B, sk_B << sk_b isn't it so strange that Alice generates Bob's secret
  // key??
  // Actually it is not Alice!! But why they do not have two differnet
  // funcitons?!?!?! In real life how is Alice getting Bob's pk??


  // Generate the recipient's keypair.
  // Benchmarking vars

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), EVP_hpke_x25519_hkdf_sha256()));

  uint8_t public_key_r[X25519_PUBLIC_VALUE_LEN];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));

  for (const auto aead : kAllAEADs) {
    SCOPED_TRACE(EVP_HPKE_AEAD_id(aead()));
    for (const auto kdf : kAllKDFs) {
      SCOPED_TRACE(EVP_HPKE_KDF_id(kdf()));

      print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));

      for (int kk = 1000; kk <= SIZE_PLAINTEXT; kk *= 10) {
        printf("\nPlaintext Bytes    ->   %d\n", kk);
        cycles_set_up_sender_total = 0, cycles_set_up_recipient_total = 0,
        cycles_seal_total = 0, cycles_open_total = 0, cycles_protocol_total = 0, clean_protocol = 0;
        uint8_t *kCleartextPayload = (uint8_t *)malloc(sizeof(uint8_t) * kk);
        init_plaintext(kCleartextPayload, kk);
        for (int jj = 0; jj < NUMBER_TESTS; jj++) {
          // TEST TO CHANGE ALICE'S PK TO SEE IF TEST FAILS
          // public_key_r[X25519_PUBLIC_VALUE_LEN +
          // SIKE_P434_R3_PUBLIC_KEY_BYTES-1]=0;

          for (const Span<const uint8_t> &info : info_values) {
            SCOPED_TRACE(Bytes(info));
            for (const Span<const uint8_t> &ad : ad_values) {
              // print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));

              cycles_protocol = cpucycles();
              //others = cpucycles();
              SCOPED_TRACE(Bytes(ad));
              //others_total += cpucycles() - others;

              // Alice i
              // Set up the sender.
              //others = cpucycles();
              ScopedEVP_HPKE_CTX sender_ctx;
              uint8_t enc[X25519_PUBLIC_VALUE_LEN];
              size_t enc_len;
              //others_total += cpucycles() - others;
              cycles_set_up_sender = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(
                  sender_ctx.get(), enc, &enc_len, sizeof(enc),
                  EVP_hpke_x25519_hkdf_sha256(), kdf(), aead(), public_key_r,
                  public_key_r_len, info.data(), info.size()));
              cycles_set_up_sender_total += cpucycles() - cycles_set_up_sender;


              // Set up the recipient.
              //others = cpucycles();
              ScopedEVP_HPKE_CTX recipient_ctx;
              //others_total += cpucycles() - others;
              cycles_set_up_recipient = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(
                  recipient_ctx.get(), key.get(), kdf(), aead(), enc, enc_len,
                  info.data(), info.size()));
              cycles_set_up_recipient_total +=
                  cpucycles() - cycles_set_up_recipient;


              // const char kCleartextPayload[] = "foobar";


              // Have sender encrypt message for the recipient.
              //others = cpucycles();
              std::vector<uint8_t> ciphertext(
                  kk + EVP_HPKE_CTX_max_overhead(sender_ctx.get()));
              size_t ciphertext_len;
              //others_total += cpucycles() - others;
              cycles_seal = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_seal(
                  sender_ctx.get(), ciphertext.data(), &ciphertext_len,
                  ciphertext.size(),
                  reinterpret_cast<const uint8_t *>(kCleartextPayload),
                  kk, ad.data(), ad.size()));
              cycles_seal_total += cpucycles() - cycles_seal;


              // Have recipient decrypt the message.
              //others = cpucycles();
              std::vector<uint8_t> cleartext(ciphertext.size());
              size_t cleartext_len;
              //others_total += cpucycles() - others;
              cycles_open = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_open(
                  recipient_ctx.get(), cleartext.data(), &cleartext_len,
                  cleartext.size(), ciphertext.data(), ciphertext_len,
                  ad.data(), ad.size()));
              cycles_open_total += cpucycles() - cycles_open;


              // print_text(cleartext, kk);

              cycles_protocol_total += cpucycles() - cycles_protocol;

              // Verify that decrypted message matches the original.
              // ASSERT_EQ(Bytes(cleartext.data(), cleartext_len),
              // Bytes(kCleartextPayload, kk));
            }
          }
        }
        printf("set_up_sender           %llu CCs \n",
               cycles_set_up_sender_total / NUMBER_TESTS / 1000000);
        printf("set_up_recipient        %llu CCs \n",
               cycles_set_up_recipient_total / NUMBER_TESTS / 1000000);
        printf("seal                    %.2f CCs \n",
               (float)(cycles_seal_total / NUMBER_TESTS) / 1000000.0);
        printf("open                    %.2f CCs \n",
               (float)(cycles_open_total / NUMBER_TESTS) / 1000000.0);
        //printf("others            %llu CCs \n",
              // others_total / NUMBER_TESTS / 1000000);
        printf("end protocol            %llu CCs \n",
               cycles_protocol_total / NUMBER_TESTS / 1000000);
        //Print the value of the 4 functions (no overhead for array initialization, etc)
        clean_protocol = cycles_set_up_sender_total + cycles_set_up_recipient_total + cycles_seal_total + cycles_open_total;
        printf("CLEAN protocol          %llu CCs \n",
               clean_protocol / NUMBER_TESTS / 1000000);




        printf("%% set_up_sender         %.3f %% \n",
               ((float)(cycles_set_up_sender_total) /
                ((float)clean_protocol) * 100));
        printf("%% set_up_recipient      %.3f %% \n",
               ((float)cycles_set_up_recipient_total) /
                   ((float)clean_protocol) * 100);
        printf(
            "%% seal                  %.3f %% \n",
            ((float)cycles_seal_total) / ((float)clean_protocol) * 100);
        printf(
            "%% open                  %.3f %% \n",
            ((float)cycles_open_total) / ((float)clean_protocol) * 100);
            //printf(
            //"%% others                  %.3f %% \n",
            //((float)others_total) / ((float)cycles_protocol_total) * 100);
        free(kCleartextPayload);
      }
    }
  }
}



// The test vectors used fixed sender ephemeral keys, while HPKE itself
// generates new keys for each context. Test this codepath by checking we can
// decrypt our own messages.
TEST(HPKETest, SIKE) {
  const uint8_t info_a[] = {1, 1, 2, 3, 5, 8};
  const uint8_t info_b[] = {42, 42, 42};
  const uint8_t ad_a[] = {1, 2, 4, 8, 16};
  const uint8_t ad_b[] = {7};
  Span<const uint8_t> info_values[] = {{nullptr, 0}, info_a, info_b};
  Span<const uint8_t> ad_values[] = {{nullptr, 0}, ad_a, ad_b};
  unsigned long long cycles_set_up_sender_total = 0,
                     cycles_set_up_recipient_total = 0, cycles_seal_total = 0,
                     cycles_open_total = 0, cycles_protocol_total = 0, clean_protocol = 0;
  unsigned long long cycles_set_up_sender, cycles_set_up_recipient, cycles_seal,
      cycles_open, cycles_protocol;

  // execute Bob keygen
  // pk_B, sk_B << sk_b isn't it so strange that Alice generates Bob's secret
  // key??
  // Actually it is not Alice!! But why they do not have two differnet
  // funcitons?!?!?! In real life how is Alice getting Bob's pk??

  // Generate the recipient's keypair.
  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), EVP_hpke_SIKE_hkdf_sha256()));
  uint8_t public_key_r[SIKE_P434_R3_PUBLIC_KEY_BYTES];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));

  // public_key_r[SIKE_P434_R3_PUBLIC_KEY_BYTES-1]=0;
  for (const auto aead : kAllAEADs) {
    SCOPED_TRACE(EVP_HPKE_AEAD_id(aead()));
    for (const auto kdf : kAllKDFs) {
      SCOPED_TRACE(EVP_HPKE_KDF_id(kdf()));

      print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));

      for (int kk = 1000; kk <= SIZE_PLAINTEXT; kk *= 10) {
        printf("\nPlaintext Bytes    ->   %d\n", kk);
        cycles_set_up_sender_total = 0, cycles_set_up_recipient_total = 0,
        cycles_seal_total = 0, cycles_open_total = 0, cycles_protocol_total = 0;
        uint8_t *kCleartextPayload = (uint8_t *)malloc(sizeof(uint8_t) * kk);
        init_plaintext(kCleartextPayload, kk);
        for (int jj = 0; jj < NUMBER_TESTS; jj++) {
          // TEST TO CHANGE ALICE'S PK TO SEE IF TEST FAILS
          // public_key_r[X25519_PUBLIC_VALUE_LEN +
          // SIKE_P434_R3_PUBLIC_KEY_BYTES-1]=0;

          for (const Span<const uint8_t> &info : info_values) {
            SCOPED_TRACE(Bytes(info));
            for (const Span<const uint8_t> &ad : ad_values) {
              // print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));


              cycles_protocol = cpucycles();

              SCOPED_TRACE(Bytes(ad));

              // Set up the sender.
              ScopedEVP_HPKE_CTX sender_ctx;
              uint8_t enc[SIKE_P434_R3_CIPHERTEXT_BYTES];
              size_t enc_len;
              cycles_set_up_sender = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(
                  sender_ctx.get(), enc, &enc_len, sizeof(enc),
                  EVP_hpke_SIKE_hkdf_sha256(), kdf(), aead(), public_key_r,
                  public_key_r_len, info.data(), info.size()));
              cycles_set_up_sender_total += cpucycles() - cycles_set_up_sender;

              // Set up the recipient.
              ScopedEVP_HPKE_CTX recipient_ctx;
              cycles_set_up_recipient = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(
                  recipient_ctx.get(), key.get(), kdf(), aead(), enc, enc_len,
                  info.data(), info.size()));
              cycles_set_up_recipient_total +=
                  cpucycles() - cycles_set_up_recipient;

              // Have sender encrypt message for the recipient.
              std::vector<uint8_t> ciphertext(
                  kk + EVP_HPKE_CTX_max_overhead(sender_ctx.get()));
              size_t ciphertext_len;
              cycles_seal = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_seal(
                  sender_ctx.get(), ciphertext.data(), &ciphertext_len,
                  ciphertext.size(),
                  reinterpret_cast<const uint8_t *>(kCleartextPayload), kk,
                  ad.data(), ad.size()));
              cycles_seal_total += cpucycles() - cycles_seal;

              // Have recipient decrypt the message.
              std::vector<uint8_t> cleartext(ciphertext.size());
              size_t cleartext_len;
              cycles_open = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_open(
                  recipient_ctx.get(), cleartext.data(), &cleartext_len,
                  cleartext.size(), ciphertext.data(), ciphertext_len,
                  ad.data(), ad.size()));
              cycles_open_total += cpucycles() - cycles_open;

              // print_text(cleartext, kk);

              cycles_protocol_total += cpucycles() - cycles_protocol;

              // Verify that decrypted message matches the original.
              // ASSERT_EQ(Bytes(cleartext.data(), cleartext_len),
              // Bytes(kCleartextPayload, kk));
            }
          }
        }
                printf("set_up_sender           %llu CCs \n",
               cycles_set_up_sender_total / NUMBER_TESTS / 1000000);
        printf("set_up_recipient        %llu CCs \n",
               cycles_set_up_recipient_total / NUMBER_TESTS / 1000000);
        printf("seal                    %.2f CCs \n",
               (float)(cycles_seal_total / NUMBER_TESTS) / 1000000.0);
        printf("open                    %.2f CCs \n",
               (float)(cycles_open_total / NUMBER_TESTS) / 1000000.0);
        //printf("others            %llu CCs \n",
              // others_total / NUMBER_TESTS / 1000000);
        printf("end protocol            %llu CCs \n",
               cycles_protocol_total / NUMBER_TESTS / 1000000);
        //Print the value of the 4 functions (no overhead for array initialization, etc)
        clean_protocol = cycles_set_up_sender_total + cycles_set_up_recipient_total + cycles_seal_total + cycles_open_total;
        printf("CLEAN protocol          %llu CCs \n",
               clean_protocol / NUMBER_TESTS / 1000000);




        printf("%% set_up_sender         %.3f %% \n",
               ((float)(cycles_set_up_sender_total) /
                ((float)clean_protocol) * 100));
        printf("%% set_up_recipient      %.3f %% \n",
               ((float)cycles_set_up_recipient_total) /
                   ((float)clean_protocol) * 100);
        printf(
            "%% seal                  %.3f %% \n",
            ((float)cycles_seal_total) / ((float)clean_protocol) * 100);
        printf(
            "%% open                  %.3f %% \n",
            ((float)cycles_open_total) / ((float)clean_protocol) * 100);
            //printf(
            //"%% others                  %.3f %% \n",
            //((float)others_total) / ((float)cycles_protocol_total) * 100);
        free(kCleartextPayload);
      }
    }
  }
}


// The test vectors used fixed sender ephemeral keys, while HPKE itself
// generates new keys for each context. Test this codepath by checking we can
// decrypt our own messages.
TEST(HPKETest, Hybrid) {
  const uint8_t info_a[] = {1, 1, 2, 3, 5, 8};
  const uint8_t info_b[] = {42, 42, 42};
  const uint8_t ad_a[] = {1, 2, 4, 8, 16};
  const uint8_t ad_b[] = {7};
  Span<const uint8_t> info_values[] = {{nullptr, 0}, info_a, info_b};
  Span<const uint8_t> ad_values[] = {{nullptr, 0}, ad_a, ad_b};
  unsigned long long cycles_set_up_sender_total = 0,
                     cycles_set_up_recipient_total = 0, cycles_seal_total = 0,
                     cycles_open_total = 0, cycles_protocol_total = 0, clean_protocol = 0;
  unsigned long long cycles_set_up_sender, cycles_set_up_recipient, cycles_seal,
      cycles_open, cycles_protocol;

  // Generate the recipient's keypair.

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(
      EVP_HPKE_KEY_generate(key.get(), EVP_hpke_x25519_SIKE_hkdf_sha256()));
  uint8_t public_key_r[X25519_PUBLIC_VALUE_LEN + SIKE_P434_R3_PUBLIC_KEY_BYTES];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));
  for (const auto aead : kAllAEADs) {
    SCOPED_TRACE(EVP_HPKE_AEAD_id(aead()));
    for (const auto kdf : kAllKDFs) {
      SCOPED_TRACE(EVP_HPKE_KDF_id(kdf()));

      print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));

      for (int kk = 1000; kk <= SIZE_PLAINTEXT; kk *= 10) {
        printf("\nPlaintext Bytes    ->   %d\n", kk);
        cycles_set_up_sender_total = 0, cycles_set_up_recipient_total = 0,
        cycles_seal_total = 0, cycles_open_total = 0, cycles_protocol_total = 0;
        uint8_t *kCleartextPayload = (uint8_t *)malloc(sizeof(uint8_t) * kk);
        init_plaintext(kCleartextPayload, kk);
        for (int jj = 0; jj < NUMBER_TESTS; jj++) {
          // TEST TO CHANGE ALICE'S PK TO SEE IF TEST FAILS
          // public_key_r[X25519_PUBLIC_VALUE_LEN +
          // SIKE_P434_R3_PUBLIC_KEY_BYTES-1]=0;

          for (const Span<const uint8_t> &info : info_values) {
            SCOPED_TRACE(Bytes(info));
            for (const Span<const uint8_t> &ad : ad_values) {
              // print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));


              cycles_protocol = cpucycles();
              SCOPED_TRACE(Bytes(ad));

              // Set up the sender.
              ScopedEVP_HPKE_CTX sender_ctx;
              uint8_t
                  enc[X25519_PUBLIC_VALUE_LEN + SIKE_P434_R3_CIPHERTEXT_BYTES];
              size_t enc_len;
              cycles_set_up_sender = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(
                  sender_ctx.get(), enc, &enc_len, sizeof(enc),
                  EVP_hpke_x25519_SIKE_hkdf_sha256(), kdf(), aead(),
                  public_key_r, public_key_r_len, info.data(), info.size()));
              cycles_set_up_sender_total += cpucycles() - cycles_set_up_sender;
              // TEST TO CHANGE BOB'S PK/CT TO SEE IF TEST FAILS
              // enc[X25519_PUBLIC_VALUE_LEN + SIKE_P434_R3_CIPHERTEXT_BYTES -
              // 1] = 0;

              // Set up the recipient.
              ScopedEVP_HPKE_CTX recipient_ctx;
              cycles_set_up_recipient = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(
                  recipient_ctx.get(), key.get(), kdf(), aead(), enc, enc_len,
                  info.data(), info.size()));
              cycles_set_up_recipient_total +=
                  cpucycles() - cycles_set_up_recipient;


              // Have sender encrypt message for the recipient.
              std::vector<uint8_t> ciphertext(
                  kk + EVP_HPKE_CTX_max_overhead(sender_ctx.get()));
              size_t ciphertext_len;

              cycles_seal = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_seal(
                  sender_ctx.get(), ciphertext.data(), &ciphertext_len,
                  ciphertext.size(),
                  reinterpret_cast<const uint8_t *>(kCleartextPayload), kk,
                  ad.data(), ad.size()));
              cycles_seal_total += cpucycles() - cycles_seal;

              // TEST TO CHANGE THE CT FROM THE SYMMETRIC ENC TO CHECK IF TEST
              // FAILS ciphertext[ciphertext.size() - 1]=0;

              // Have recipient decrypt the message.
              std::vector<uint8_t> cleartext(ciphertext.size());
              size_t cleartext_len;

              cycles_open = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_open(
                  recipient_ctx.get(), cleartext.data(), &cleartext_len,
                  cleartext.size(), ciphertext.data(), ciphertext_len,
                  ad.data(), ad.size()));

              cycles_open_total += cpucycles() - cycles_open;

              // print_text(cleartext, SIZE_PLAINTEXT);

              cycles_protocol_total += cpucycles() - cycles_protocol;

              // Verify that decrypted message matches the original.
              // ASSERT_EQ(Bytes(cleartext.data(), cleartext_len),
              // Bytes(kCleartextPayload, kk));
            }
          }
        }
                        printf("set_up_sender           %llu CCs \n",
               cycles_set_up_sender_total / NUMBER_TESTS / 1000000);
        printf("set_up_recipient        %llu CCs \n",
               cycles_set_up_recipient_total / NUMBER_TESTS / 1000000);
        printf("seal                    %.2f CCs \n",
               (float)(cycles_seal_total / NUMBER_TESTS) / 1000000.0);
        printf("open                    %.2f CCs \n",
               (float)(cycles_open_total / NUMBER_TESTS) / 1000000.0);
        //printf("others            %llu CCs \n",
              // others_total / NUMBER_TESTS / 1000000);
        printf("end protocol            %llu CCs \n",
               cycles_protocol_total / NUMBER_TESTS / 1000000);
        //Print the value of the 4 functions (no overhead for array initialization, etc)
        clean_protocol = cycles_set_up_sender_total + cycles_set_up_recipient_total + cycles_seal_total + cycles_open_total;
        printf("CLEAN protocol          %llu CCs \n",
               clean_protocol / NUMBER_TESTS / 1000000);




        printf("%% set_up_sender         %.3f %% \n",
               ((float)(cycles_set_up_sender_total) /
                ((float)clean_protocol) * 100));
        printf("%% set_up_recipient      %.3f %% \n",
               ((float)cycles_set_up_recipient_total) /
                   ((float)clean_protocol) * 100);
        printf(
            "%% seal                  %.3f %% \n",
            ((float)cycles_seal_total) / ((float)clean_protocol) * 100);
        printf(
            "%% open                  %.3f %% \n",
            ((float)cycles_open_total) / ((float)clean_protocol) * 100);
            //printf(
            //"%% others                  %.3f %% \n",
            //((float)others_total) / ((float)cycles_protocol_total) * 100);
        free(kCleartextPayload);
      }
    }
  }
}



// The test vectors used fixed sender ephemeral keys, while HPKE itself
// generates new keys for each context. Test this codepath by checking we can
// decrypt our own messages.
TEST(HPKETest, Kyber) {
  const uint8_t info_a[] = {1, 1, 2, 3, 5, 8};
  const uint8_t info_b[] = {42, 42, 42};
  const uint8_t ad_a[] = {1, 2, 4, 8, 16};
  const uint8_t ad_b[] = {7};
  Span<const uint8_t> info_values[] = {{nullptr, 0}, info_a, info_b};
  Span<const uint8_t> ad_values[] = {{nullptr, 0}, ad_a, ad_b};
  unsigned long long cycles_set_up_sender_total = 0,
                     cycles_set_up_recipient_total = 0, cycles_seal_total = 0,
                     cycles_open_total = 0, cycles_protocol_total = 0, clean_protocol = 0;
  unsigned long long cycles_set_up_sender, cycles_set_up_recipient, cycles_seal,
      cycles_open, cycles_protocol;

  // execute Bob keygen
  // pk_B, sk_B << sk_b isn't it so strange that Alice generates Bob's secret
  // key??
  // Actually it is not Alice!! But why they do not have two differnet
  // funcitons?!?!?! In real life how is Alice getting Bob's pk??

  // Generate the recipient's keypair.
  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), EVP_hpke_KYBER_hkdf_sha256()));
  uint8_t public_key_r[KYBER_PUBLICKEYBYTES];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));
  // public_key_r[SIKE_P434_R3_PUBLIC_KEY_BYTES-1]=0;
  for (const auto aead : kAllAEADs) {
    SCOPED_TRACE(EVP_HPKE_AEAD_id(aead()));
    for (const auto kdf : kAllKDFs) {
      SCOPED_TRACE(EVP_HPKE_KDF_id(kdf()));

      print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));

      for (int kk = 1000; kk <= SIZE_PLAINTEXT; kk *= 10) {
        printf("\nPlaintext Bytes    ->   %d\n", kk);
        cycles_set_up_sender_total = 0, cycles_set_up_recipient_total = 0,
        cycles_seal_total = 0, cycles_open_total = 0, cycles_protocol_total = 0;
        uint8_t *kCleartextPayload = (uint8_t *)malloc(sizeof(uint8_t) * kk);
        init_plaintext(kCleartextPayload, kk);
        for (int jj = 0; jj < NUMBER_TESTS; jj++) {
          // TEST TO CHANGE ALICE'S PK TO SEE IF TEST FAILS
          // public_key_r[X25519_PUBLIC_VALUE_LEN +
          // SIKE_P434_R3_PUBLIC_KEY_BYTES-1]=0;

          for (const Span<const uint8_t> &info : info_values) {
            SCOPED_TRACE(Bytes(info));
            for (const Span<const uint8_t> &ad : ad_values) {
              // print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));


              cycles_protocol = cpucycles();

              SCOPED_TRACE(Bytes(ad));

              // Set up the sender.
              ScopedEVP_HPKE_CTX sender_ctx;
              uint8_t enc[KYBER_CIPHERTEXTBYTES];
              size_t enc_len;
              cycles_set_up_sender = cpucycles();
  
              ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(
                  sender_ctx.get(), enc, &enc_len, sizeof(enc),
                  EVP_hpke_KYBER_hkdf_sha256(), kdf(), aead(), public_key_r,
                  public_key_r_len, info.data(), info.size()));
              cycles_set_up_sender_total += cpucycles() - cycles_set_up_sender;

              // Set up the recipient.
              ScopedEVP_HPKE_CTX recipient_ctx;
              cycles_set_up_recipient = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(
                  recipient_ctx.get(), key.get(), kdf(), aead(), enc, enc_len,
                  info.data(), info.size()));
              cycles_set_up_recipient_total +=
                  cpucycles() - cycles_set_up_recipient;

              // Have sender encrypt message for the recipient.
              std::vector<uint8_t> ciphertext(
                  kk + EVP_HPKE_CTX_max_overhead(sender_ctx.get()));
              size_t ciphertext_len;
              cycles_seal = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_seal(
                  sender_ctx.get(), ciphertext.data(), &ciphertext_len,
                  ciphertext.size(),
                  reinterpret_cast<const uint8_t *>(kCleartextPayload), kk,
                  ad.data(), ad.size()));
              cycles_seal_total += cpucycles() - cycles_seal;

              // Have recipient decrypt the message.
              std::vector<uint8_t> cleartext(ciphertext.size());
              size_t cleartext_len;
              cycles_open = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_open(
                  recipient_ctx.get(), cleartext.data(), &cleartext_len,
                  cleartext.size(), ciphertext.data(), ciphertext_len,
                  ad.data(), ad.size()));
              cycles_open_total += cpucycles() - cycles_open;

              // print_text(cleartext, kk);

              cycles_protocol_total += cpucycles() - cycles_protocol;

             // Verify that decrypted message matches the original.
              ASSERT_EQ(Bytes(cleartext.data(), cleartext_len),
              Bytes(kCleartextPayload, kk));
            }
          }
        }
                printf("set_up_sender           %llu CCs \n",
               cycles_set_up_sender_total / NUMBER_TESTS / 1000000);
        printf("set_up_recipient        %llu CCs \n",
               cycles_set_up_recipient_total / NUMBER_TESTS / 1000000);
        printf("seal                    %.2f CCs \n",
               (float)(cycles_seal_total / NUMBER_TESTS) / 1000000.0);
        printf("open                    %.2f CCs \n",
               (float)(cycles_open_total / NUMBER_TESTS) / 1000000.0);
        //printf("others            %llu CCs \n",
              // others_total / NUMBER_TESTS / 1000000);
        printf("end protocol            %llu CCs \n",
               cycles_protocol_total / NUMBER_TESTS / 1000000);
        //Print the value of the 4 functions (no overhead for array initialization, etc)
        clean_protocol = cycles_set_up_sender_total + cycles_set_up_recipient_total + cycles_seal_total + cycles_open_total;
        printf("CLEAN protocol          %llu CCs \n",
               clean_protocol / NUMBER_TESTS / 1000000);




        printf("%% set_up_sender         %.3f %% \n",
               ((float)(cycles_set_up_sender_total) /
                ((float)clean_protocol) * 100));
        printf("%% set_up_recipient      %.3f %% \n",
               ((float)cycles_set_up_recipient_total) /
                   ((float)clean_protocol) * 100);
        printf(
            "%% seal                  %.3f %% \n",
            ((float)cycles_seal_total) / ((float)clean_protocol) * 100);
        printf(
            "%% open                  %.3f %% \n",
            ((float)cycles_open_total) / ((float)clean_protocol) * 100);
            //printf(
            //"%% others                  %.3f %% \n",
            //((float)others_total) / ((float)cycles_protocol_total) * 100);
        free(kCleartextPayload);
      }
    }
  }
}





// The test vectors used fixed sender ephemeral keys, while HPKE itself
// generates new keys for each context. Test this codepath by checking we can
// decrypt our own messages.
TEST(HPKETest, x25519_Kyber) {
  const uint8_t info_a[] = {1, 1, 2, 3, 5, 8};
  const uint8_t info_b[] = {42, 42, 42};
  const uint8_t ad_a[] = {1, 2, 4, 8, 16};
  const uint8_t ad_b[] = {7};
  Span<const uint8_t> info_values[] = {{nullptr, 0}, info_a, info_b};
  Span<const uint8_t> ad_values[] = {{nullptr, 0}, ad_a, ad_b};
  unsigned long long cycles_set_up_sender_total = 0,
                     cycles_set_up_recipient_total = 0, cycles_seal_total = 0,
                     cycles_open_total = 0, cycles_protocol_total = 0, clean_protocol = 0;
  unsigned long long cycles_set_up_sender, cycles_set_up_recipient, cycles_seal,
      cycles_open, cycles_protocol;

  // execute Bob keygen
  // pk_B, sk_B << sk_b isn't it so strange that Alice generates Bob's secret
  // key??
  // Actually it is not Alice!! But why they do not have two differnet
  // funcitons?!?!?! In real life how is Alice getting Bob's pk??

  // Generate the recipient's keypair.
  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), EVP_hpke_x25519_KYBER_hkdf_sha256()));
  uint8_t public_key_r[X25519_PUBLIC_VALUE_LEN + KYBER_PUBLICKEYBYTES];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));
  // public_key_r[SIKE_P434_R3_PUBLIC_KEY_BYTES-1]=0;
  for (const auto aead : kAllAEADs) {
    SCOPED_TRACE(EVP_HPKE_AEAD_id(aead()));
    for (const auto kdf : kAllKDFs) {
      SCOPED_TRACE(EVP_HPKE_KDF_id(kdf()));

      print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));

      for (int kk = 1000; kk <= SIZE_PLAINTEXT; kk *= 10) {
        printf("\nPlaintext Bytes    ->   %d\n", kk);
        cycles_set_up_sender_total = 0, cycles_set_up_recipient_total = 0,
        cycles_seal_total = 0, cycles_open_total = 0, cycles_protocol_total = 0;
        uint8_t *kCleartextPayload = (uint8_t *)malloc(sizeof(uint8_t) * kk);
        init_plaintext(kCleartextPayload, kk);
        for (int jj = 0; jj < NUMBER_TESTS; jj++) {
          // TEST TO CHANGE ALICE'S PK TO SEE IF TEST FAILS
          // public_key_r[X25519_PUBLIC_VALUE_LEN +
          // SIKE_P434_R3_PUBLIC_KEY_BYTES-1]=0;

          for (const Span<const uint8_t> &info : info_values) {
            SCOPED_TRACE(Bytes(info));
            for (const Span<const uint8_t> &ad : ad_values) {
              // print_info(EVP_HPKE_AEAD_id(aead()), EVP_HPKE_KDF_id(kdf()));


              cycles_protocol = cpucycles();

              SCOPED_TRACE(Bytes(ad));

              // Set up the sender.
              ScopedEVP_HPKE_CTX sender_ctx;
              uint8_t enc[KYBER_CIPHERTEXTBYTES + X25519_PUBLIC_VALUE_LEN];
              size_t enc_len;
              cycles_set_up_sender = cpucycles();
  
              ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(
                  sender_ctx.get(), enc, &enc_len, sizeof(enc),
                  EVP_hpke_x25519_KYBER_hkdf_sha256(), kdf(), aead(), public_key_r,
                  public_key_r_len, info.data(), info.size()));
              cycles_set_up_sender_total += cpucycles() - cycles_set_up_sender;

              // Set up the recipient.
              ScopedEVP_HPKE_CTX recipient_ctx;
              cycles_set_up_recipient = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(
                  recipient_ctx.get(), key.get(), kdf(), aead(), enc, enc_len,
                  info.data(), info.size()));
              cycles_set_up_recipient_total +=
                  cpucycles() - cycles_set_up_recipient;

              // Have sender encrypt message for the recipient.
              std::vector<uint8_t> ciphertext(
                  kk + EVP_HPKE_CTX_max_overhead(sender_ctx.get()));
              size_t ciphertext_len;
              cycles_seal = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_seal(
                  sender_ctx.get(), ciphertext.data(), &ciphertext_len,
                  ciphertext.size(),
                  reinterpret_cast<const uint8_t *>(kCleartextPayload), kk,
                  ad.data(), ad.size()));
              cycles_seal_total += cpucycles() - cycles_seal;

              // Have recipient decrypt the message.
              std::vector<uint8_t> cleartext(ciphertext.size());
              size_t cleartext_len;
              cycles_open = cpucycles();
              ASSERT_TRUE(EVP_HPKE_CTX_open(
                  recipient_ctx.get(), cleartext.data(), &cleartext_len,
                  cleartext.size(), ciphertext.data(), ciphertext_len,
                  ad.data(), ad.size()));
              cycles_open_total += cpucycles() - cycles_open;

              // print_text(cleartext, kk);

              cycles_protocol_total += cpucycles() - cycles_protocol;

             // Verify that decrypted message matches the original.
              ASSERT_EQ(Bytes(cleartext.data(), cleartext_len),
              Bytes(kCleartextPayload, kk));
            }
          }
        }
                printf("set_up_sender           %llu CCs \n",
               cycles_set_up_sender_total / NUMBER_TESTS / 1000000);
        printf("set_up_recipient        %llu CCs \n",
               cycles_set_up_recipient_total / NUMBER_TESTS / 1000000);
        printf("seal                    %.2f CCs \n",
               (float)(cycles_seal_total / NUMBER_TESTS) / 1000000.0);
        printf("open                    %.2f CCs \n",
               (float)(cycles_open_total / NUMBER_TESTS) / 1000000.0);
        //printf("others            %llu CCs \n",
              // others_total / NUMBER_TESTS / 1000000);
        printf("end protocol            %llu CCs \n",
               cycles_protocol_total / NUMBER_TESTS / 1000000);
        //Print the value of the 4 functions (no overhead for array initialization, etc)
        clean_protocol = cycles_set_up_sender_total + cycles_set_up_recipient_total + cycles_seal_total + cycles_open_total;
        printf("CLEAN protocol          %llu CCs \n",
               clean_protocol / NUMBER_TESTS / 1000000);




        printf("%% set_up_sender         %.3f %% \n",
               ((float)(cycles_set_up_sender_total) /
                ((float)clean_protocol) * 100));
        printf("%% set_up_recipient      %.3f %% \n",
               ((float)cycles_set_up_recipient_total) /
                   ((float)clean_protocol) * 100);
        printf(
            "%% seal                  %.3f %% \n",
            ((float)cycles_seal_total) / ((float)clean_protocol) * 100);
        printf(
            "%% open                  %.3f %% \n",
            ((float)cycles_open_total) / ((float)clean_protocol) * 100);
            //printf(
            //"%% others                  %.3f %% \n",
            //((float)others_total) / ((float)cycles_protocol_total) * 100);
        free(kCleartextPayload);
      }
    }
  }
}


/*
// Verify that the DH operations inside Encap() and Decap() both fail when the
// public key is on a small-order point in the curve.
TEST(HPKETest, X25519EncapSmallOrderPoint) {
  // Borrowed from X25519Test.SmallOrder.
  static const uint8_t kSmallOrderPoint[32] = {
      0xe0, 0xeb, 0x7a, 0x7c, 0x3b, 0x41, 0xb8, 0xae, 0x16, 0x56, 0xe3,
      0xfa, 0xf1, 0x9f, 0xc4, 0x6a, 0xda, 0x09, 0x8d, 0xeb, 0x9c, 0x32,
      0xb1, 0xfd, 0x86, 0x62, 0x05, 0x16, 0x5f, 0x49, 0xb8,
  };

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), EVP_hpke_x25519_hkdf_sha256()));

  for (const auto kdf : kAllKDFs) {
    SCOPED_TRACE(EVP_HPKE_KDF_id(kdf()));
    for (const auto aead : kAllAEADs) {
      SCOPED_TRACE(EVP_HPKE_AEAD_id(aead()));
      // Set up the sender, passing in kSmallOrderPoint as |peer_public_key|.
      ScopedEVP_HPKE_CTX sender_ctx;
      uint8_t enc[X25519_PUBLIC_VALUE_LEN];
      size_t enc_len;
      ASSERT_FALSE(EVP_HPKE_CTX_setup_sender(
          sender_ctx.get(), enc, &enc_len, sizeof(enc),
          EVP_hpke_x25519_hkdf_sha256(), kdf(), aead(), kSmallOrderPoint,
          sizeof(kSmallOrderPoint), nullptr, 0));

      // Set up the recipient, passing in kSmallOrderPoint as |enc|.
      ScopedEVP_HPKE_CTX recipient_ctx;
      ASSERT_FALSE(EVP_HPKE_CTX_setup_recipient(
          recipient_ctx.get(), key.get(), kdf(), aead(), kSmallOrderPoint,
          sizeof(kSmallOrderPoint), nullptr, 0));
    }
  }
}

// Test that Seal() fails when the context has been initialized as a recipient.
TEST(HPKETest, RecipientInvalidSeal) {
  const uint8_t kMockEnc[X25519_PUBLIC_VALUE_LEN] = {0xff};
  const char kCleartextPayload[] = "foobar";

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), EVP_hpke_x25519_hkdf_sha256()));

  // Set up the recipient.
  ScopedEVP_HPKE_CTX recipient_ctx;
  ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(
      recipient_ctx.get(), key.get(), EVP_hpke_hkdf_sha256(),
      EVP_hpke_aes_128_gcm(), kMockEnc, sizeof(kMockEnc), nullptr, 0));

  // Call Seal() on the recipient.
  size_t ciphertext_len;
  uint8_t ciphertext[100];
  ASSERT_FALSE(EVP_HPKE_CTX_seal(
      recipient_ctx.get(), ciphertext, &ciphertext_len, sizeof(ciphertext),
      reinterpret_cast<const uint8_t *>(kCleartextPayload),
      sizeof(kCleartextPayload), nullptr, 0));
}

// Test that Open() fails when the context has been initialized as a sender.
TEST(HPKETest, SenderInvalidOpen) {
  const uint8_t kMockCiphertext[100] = {0xff};
  const size_t kMockCiphertextLen = 80;

  // Generate the recipient's keypair.
  uint8_t secret_key_r[X25519_PRIVATE_KEY_LEN];
  uint8_t public_key_r[X25519_PUBLIC_VALUE_LEN];
  X25519_keypair(public_key_r, secret_key_r);

  // Set up the sender.
  ScopedEVP_HPKE_CTX sender_ctx;
  uint8_t enc[X25519_PUBLIC_VALUE_LEN];
  size_t enc_len;
  ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(
      sender_ctx.get(), enc, &enc_len, sizeof(enc),
      EVP_hpke_x25519_hkdf_sha256(), EVP_hpke_hkdf_sha256(),
      EVP_hpke_aes_128_gcm(), public_key_r, sizeof(public_key_r), nullptr, 0));

  // Call Open() on the sender.
  uint8_t cleartext[128];
  size_t cleartext_len;
  ASSERT_FALSE(EVP_HPKE_CTX_open(sender_ctx.get(), cleartext, &cleartext_len,
                                 sizeof(cleartext), kMockCiphertext,
                                 kMockCiphertextLen, nullptr, 0));
}

TEST(HPKETest, SetupSenderBufferTooSmall) {
  uint8_t secret_key_r[X25519_PRIVATE_KEY_LEN];
  uint8_t public_key_r[X25519_PUBLIC_VALUE_LEN];
  X25519_keypair(public_key_r, secret_key_r);

  ScopedEVP_HPKE_CTX sender_ctx;
  uint8_t enc[X25519_PUBLIC_VALUE_LEN - 1];
  size_t enc_len;
  ASSERT_FALSE(EVP_HPKE_CTX_setup_sender(
      sender_ctx.get(), enc, &enc_len, sizeof(enc),
      EVP_hpke_x25519_hkdf_sha256(), EVP_hpke_hkdf_sha256(),
      EVP_hpke_aes_128_gcm(), public_key_r, sizeof(public_key_r), nullptr, 0));
  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_EVP, ERR_GET_LIB(err));
  EXPECT_EQ(EVP_R_INVALID_BUFFER_SIZE, ERR_GET_REASON(err));
  ERR_clear_error();
}

TEST(HPKETest, SetupSenderBufferTooLarge) {
  uint8_t secret_key_r[X25519_PRIVATE_KEY_LEN];
  uint8_t public_key_r[X25519_PUBLIC_VALUE_LEN];
  X25519_keypair(public_key_r, secret_key_r);

  // Too large of an output buffer is fine because the function reports the
  // actual length.
  ScopedEVP_HPKE_CTX sender_ctx;
  uint8_t enc[X25519_PUBLIC_VALUE_LEN + 1];
  size_t enc_len;
  EXPECT_TRUE(EVP_HPKE_CTX_setup_sender(
      sender_ctx.get(), enc, &enc_len, sizeof(enc),
      EVP_hpke_x25519_hkdf_sha256(), EVP_hpke_hkdf_sha256(),
      EVP_hpke_aes_128_gcm(), public_key_r, sizeof(public_key_r), nullptr, 0));
  EXPECT_EQ(size_t{X25519_PUBLIC_VALUE_LEN}, enc_len);
}

TEST(HPKETest, SetupRecipientWrongLengthEnc) {
  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), EVP_hpke_x25519_hkdf_sha256()));

  const uint8_t bogus_enc[X25519_PUBLIC_VALUE_LEN + 5] = {0xff};

  ScopedEVP_HPKE_CTX recipient_ctx;
  ASSERT_FALSE(EVP_HPKE_CTX_setup_recipient(
      recipient_ctx.get(), key.get(), EVP_hpke_hkdf_sha256(),
      EVP_hpke_aes_128_gcm(), bogus_enc, sizeof(bogus_enc), nullptr, 0));
  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_EVP, ERR_GET_LIB(err));
  EXPECT_EQ(EVP_R_INVALID_PEER_KEY, ERR_GET_REASON(err));
  ERR_clear_error();
}

TEST(HPKETest, SetupSenderWrongLengthPeerPublicValue) {
  const uint8_t bogus_public_key_r[X25519_PRIVATE_KEY_LEN + 5] = {0xff};
  ScopedEVP_HPKE_CTX sender_ctx;
  uint8_t enc[X25519_PUBLIC_VALUE_LEN];
  size_t enc_len;
  ASSERT_FALSE(EVP_HPKE_CTX_setup_sender(
      sender_ctx.get(), enc, &enc_len, sizeof(enc),
      EVP_hpke_x25519_hkdf_sha256(), EVP_hpke_hkdf_sha256(),
      EVP_hpke_aes_128_gcm(), bogus_public_key_r, sizeof(bogus_public_key_r),
      nullptr, 0));
  uint32_t err = ERR_get_error();
  EXPECT_EQ(ERR_LIB_EVP, ERR_GET_LIB(err));
  EXPECT_EQ(EVP_R_INVALID_PEER_KEY, ERR_GET_REASON(err));
  ERR_clear_error();
}

TEST(HPKETest, InvalidRecipientKey) {
  const uint8_t private_key[X25519_PUBLIC_VALUE_LEN + 5] = {0xff};
  ScopedEVP_HPKE_KEY key;
  EXPECT_FALSE(EVP_HPKE_KEY_init(key.get(), EVP_hpke_x25519_hkdf_sha256(),
                                 private_key, sizeof(private_key)));
}

TEST(HPKETest, InternalParseIntSafe) {
  uint8_t u8 = 0xff;
  ASSERT_FALSE(ParseIntSafe(&u8, "-1"));

  ASSERT_TRUE(ParseIntSafe(&u8, "0"));
  ASSERT_EQ(u8, 0);

  ASSERT_TRUE(ParseIntSafe(&u8, "255"));
  ASSERT_EQ(u8, 255);

  ASSERT_FALSE(ParseIntSafe(&u8, "256"));

  uint16_t u16 = 0xffff;
  ASSERT_TRUE(ParseIntSafe(&u16, "257"));
  ASSERT_EQ(u16, 257);

  ASSERT_TRUE(ParseIntSafe(&u16, "65535"));
  ASSERT_EQ(u16, 65535);

  ASSERT_FALSE(ParseIntSafe(&u16, "65536"));
}
*/

}  // namespace bssl
