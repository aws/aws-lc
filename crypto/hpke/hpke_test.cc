// Copyright (c) 2020, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/hpke.h>

#include <cstdint>
#include <limits>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/base.h>
#include <openssl/curve25519.h>
#include <openssl/digest.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/sha.h>
#include <openssl/span.h>

#include "../test/file_test.h"
#include "../test/test_util.h"


namespace bssl {
namespace {

const decltype(&EVP_hpke_aes_128_gcm) kAllAEADs[] = {
    &EVP_hpke_aes_128_gcm,
    &EVP_hpke_aes_256_gcm,
    &EVP_hpke_chacha20_poly1305,
};

const decltype(&EVP_hpke_hkdf_sha256) kAllKDFs[] = {
    &EVP_hpke_hkdf_sha256,
    &EVP_hpke_hkdf_sha384,
};

// HPKETestVector corresponds to one array member in the published
// test-vectors.json.
class HPKETestVector {
 public:
  explicit HPKETestVector() = default;
  ~HPKETestVector() = default;

  bool ReadFromFileTest(FileTest *t);

  void Verify() const {
    const EVP_HPKE_KEM *kem = EVP_hpke_x25519_hkdf_sha256();
    const EVP_HPKE_AEAD *aead = GetAEAD();
    ASSERT_TRUE(aead);
    const EVP_HPKE_KDF *kdf = GetKDF();
    ASSERT_TRUE(kdf);

    // Test the sender.
    ScopedEVP_HPKE_CTX sender_ctx;
    uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
    size_t enc_len = 0;
    switch (mode_) {
      case Mode::kBase:
        ASSERT_TRUE(EVP_HPKE_CTX_setup_sender_with_seed_for_testing(
            sender_ctx.get(), enc, &enc_len, sizeof(enc), kem, kdf, aead,
            public_key_r_.data(), public_key_r_.size(), info_.data(),
            info_.size(), secret_key_e_.data(), secret_key_e_.size()));
        break;
      case Mode::kAuth: {
        ScopedEVP_HPKE_KEY sender_key;
        ASSERT_TRUE(EVP_HPKE_KEY_init(
            sender_key.get(), kem, secret_key_s_.data(), secret_key_s_.size()));
        ASSERT_TRUE(EVP_HPKE_CTX_setup_auth_sender_with_seed_for_testing(
            sender_ctx.get(), enc, &enc_len, sizeof(enc), sender_key.get(), kdf,
            aead, public_key_r_.data(), public_key_r_.size(), info_.data(),
            info_.size(), secret_key_e_.data(), secret_key_e_.size()));
        break;
      }
    }

    EXPECT_EQ(Bytes(enc, enc_len), Bytes(public_key_e_));
    VerifySender(sender_ctx.get());

    // Test the recipient.
    ScopedEVP_HPKE_KEY base_key;
    ASSERT_TRUE(EVP_HPKE_KEY_init(base_key.get(), kem, secret_key_r_.data(),
                                  secret_key_r_.size()));

    enum class CopyMode { kOriginal, kCopy, kMove };
    for (CopyMode copy :
         {CopyMode::kOriginal, CopyMode::kCopy, CopyMode::kMove}) {
      SCOPED_TRACE(static_cast<int>(copy));
      const EVP_HPKE_KEY *key = base_key.get();
      ScopedEVP_HPKE_KEY key_copy;
      switch (copy) {
        case CopyMode::kOriginal:
          break;
        case CopyMode::kCopy:
          ASSERT_TRUE(EVP_HPKE_KEY_copy(key_copy.get(), base_key.get()));
          key = key_copy.get();
          break;
        case CopyMode::kMove:
          EVP_HPKE_KEY_move(key_copy.get(), base_key.get());
          key = key_copy.get();
          break;
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
      switch (mode_) {
        case Mode::kBase:
          ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(recipient_ctx.get(), key,
                                                   kdf, aead, enc, enc_len,
                                                   info_.data(), info_.size()));
          break;
        case Mode::kAuth:
          ASSERT_TRUE(EVP_HPKE_CTX_setup_auth_recipient(
              recipient_ctx.get(), key, kdf, aead, enc, enc_len, info_.data(),
              info_.size(), public_key_s_.data(), public_key_s_.size()));
          break;
      }

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

  enum class Mode {
    kBase = 0,
    kAuth = 2,
  };

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

  Mode mode_;
  uint16_t kdf_id_;
  uint16_t aead_id_;
  std::vector<uint8_t> context_;
  std::vector<uint8_t> info_;
  std::vector<uint8_t> public_key_e_;
  std::vector<uint8_t> secret_key_e_;
  std::vector<uint8_t> public_key_r_;
  std::vector<uint8_t> secret_key_r_;
  std::vector<uint8_t> public_key_s_;
  std::vector<uint8_t> secret_key_s_;
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
  if (!FileTestReadInt(t, &mode, "mode") ||
      !FileTestReadInt(t, &kdf_id_, "kdf_id") ||
      !FileTestReadInt(t, &aead_id_, "aead_id") ||
      !t->GetBytes(&info_, "info") ||
      !t->GetBytes(&secret_key_r_, "skRm") ||
      !t->GetBytes(&public_key_r_, "pkRm") ||
      !t->GetBytes(&secret_key_e_, "skEm") ||
      !t->GetBytes(&public_key_e_, "pkEm")) {
    return false;
  }

  switch (mode) {
    case static_cast<int>(Mode::kBase):
      mode_ = Mode::kBase;
      break;
    case static_cast<int>(Mode::kAuth):
      mode_ = Mode::kAuth;
      if (!t->GetBytes(&secret_key_s_, "skSm") ||
          !t->GetBytes(&public_key_s_, "pkSm")) {
        return false;
      }
      break;
    default:
      return false;
  }

  for (int i = 1; t->HasAttribute(BuildAttrName("aad", i)); i++) {
    Encryption encryption;
    if (!t->GetBytes(&encryption.aad, BuildAttrName("aad", i)) ||
        !t->GetBytes(&encryption.ciphertext, BuildAttrName("ct", i)) ||
        !t->GetBytes(&encryption.plaintext, BuildAttrName("pt", i))) {
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
TEST(HPKETest, RoundTrip) {
  const uint8_t info_a[] = {1, 1, 2, 3, 5, 8};
  const uint8_t info_b[] = {42, 42, 42};
  const uint8_t ad_a[] = {1, 2, 4, 8, 16};
  const uint8_t ad_b[] = {7};
  Span<const uint8_t> info_values[] = {{nullptr, 0}, info_a, info_b};
  Span<const uint8_t> ad_values[] = {{nullptr, 0}, ad_a, ad_b};

  const EVP_HPKE_KEM *kem = EVP_hpke_x25519_hkdf_sha256();

  // Generate the recipient's keypair.
  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), kem));
  uint8_t public_key_r[EVP_HPKE_MAX_PUBLIC_KEY_LENGTH];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));

  // Generate the sender's keypair, for auth modes.
  ScopedEVP_HPKE_KEY sender_key;
  ASSERT_TRUE(
      EVP_HPKE_KEY_generate(sender_key.get(), kem));
  uint8_t public_key_s[EVP_HPKE_MAX_PUBLIC_KEY_LENGTH];
  size_t public_key_s_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(sender_key.get(), public_key_s,
                                      &public_key_s_len, sizeof(public_key_s)));

  for (const auto kdf : kAllKDFs) {
    SCOPED_TRACE(EVP_HPKE_KDF_id(kdf()));
    for (const auto aead : kAllAEADs) {
      SCOPED_TRACE(EVP_HPKE_AEAD_id(aead()));
      for (const Span<const uint8_t> &info : info_values) {
        SCOPED_TRACE(Bytes(info));
        for (const Span<const uint8_t> &ad : ad_values) {
          SCOPED_TRACE(Bytes(ad));

          auto check_messages = [&](EVP_HPKE_CTX *sender_ctx,
                                    EVP_HPKE_CTX *recipient_ctx) {
            const char kCleartextPayload[] = "foobar";

            // Have sender encrypt message for the recipient.
            std::vector<uint8_t> ciphertext(
                sizeof(kCleartextPayload) +
                EVP_HPKE_CTX_max_overhead(sender_ctx));
            size_t ciphertext_len;
            ASSERT_TRUE(EVP_HPKE_CTX_seal(
                sender_ctx, ciphertext.data(), &ciphertext_len,
                ciphertext.size(),
                reinterpret_cast<const uint8_t *>(kCleartextPayload),
                sizeof(kCleartextPayload), ad.data(), ad.size()));

            // Have recipient decrypt the message.
            std::vector<uint8_t> cleartext(ciphertext.size());
            size_t cleartext_len;
            ASSERT_TRUE(EVP_HPKE_CTX_open(recipient_ctx, cleartext.data(),
                                          &cleartext_len, cleartext.size(),
                                          ciphertext.data(), ciphertext_len,
                                          ad.data(), ad.size()));

            // Verify that decrypted message matches the original.
            ASSERT_EQ(Bytes(cleartext.data(), cleartext_len),
                      Bytes(kCleartextPayload, sizeof(kCleartextPayload)));
          };

          // Test the base mode.
          {
            ScopedEVP_HPKE_CTX sender_ctx;
            uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
            size_t enc_len;
            ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(
                sender_ctx.get(), enc, &enc_len, sizeof(enc), kem, kdf(),
                aead(), public_key_r, public_key_r_len, info.data(),
                info.size()));

            ScopedEVP_HPKE_CTX recipient_ctx;
            ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(
                recipient_ctx.get(), key.get(), kdf(), aead(), enc, enc_len,
                info.data(), info.size()));

            check_messages(sender_ctx.get(), recipient_ctx.get());
          }

          // Test the auth mode.
          {
            ScopedEVP_HPKE_CTX sender_ctx;
            uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
            size_t enc_len;
            ASSERT_TRUE(EVP_HPKE_CTX_setup_auth_sender(
                sender_ctx.get(), enc, &enc_len, sizeof(enc), sender_key.get(),
                kdf(), aead(), public_key_r, public_key_r_len, info.data(),
                info.size()));

            ScopedEVP_HPKE_CTX recipient_ctx;
            ASSERT_TRUE(EVP_HPKE_CTX_setup_auth_recipient(
                recipient_ctx.get(), key.get(), kdf(), aead(), enc, enc_len,
                info.data(), info.size(), public_key_s, public_key_s_len));

            check_messages(sender_ctx.get(), recipient_ctx.get());
          }
        }
      }
    }
  }
}

// Verify that the DH operations inside Encap() and Decap() both fail when the
// public key is on a small-order point in the curve.
TEST(HPKETest, X25519EncapSmallOrderPoint) {
  // Borrowed from X25519Test.SmallOrder.
  static const uint8_t kSmallOrderPoint[32] = {
      0xe0, 0xeb, 0x7a, 0x7c, 0x3b, 0x41, 0xb8, 0xae, 0x16, 0x56, 0xe3,
      0xfa, 0xf1, 0x9f, 0xc4, 0x6a, 0xda, 0x09, 0x8d, 0xeb, 0x9c, 0x32,
      0xb1, 0xfd, 0x86, 0x62, 0x05, 0x16, 0x5f, 0x49, 0xb8,
  };
  static const uint8_t kValidPoint[32] = {
      0xe6, 0xdb, 0x68, 0x67, 0x58, 0x30, 0x30, 0xdb, 0x35, 0x94, 0xc1,
      0xa4, 0x24, 0xb1, 0x5f, 0x7c, 0x72, 0x66, 0x24, 0xec, 0x26, 0xb3,
      0x35, 0x3b, 0x10, 0xa9, 0x03, 0xa6, 0xd0, 0xab, 0x1c, 0x4c,
  };

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), EVP_hpke_x25519_hkdf_sha256()));

  for (const auto kdf : kAllKDFs) {
    SCOPED_TRACE(EVP_HPKE_KDF_id(kdf()));
    for (const auto aead : kAllAEADs) {
      SCOPED_TRACE(EVP_HPKE_AEAD_id(aead()));
      // Set up the sender, passing in kSmallOrderPoint as |peer_public_key|.
      ScopedEVP_HPKE_CTX sender_ctx;
      uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
      size_t enc_len;
      EXPECT_FALSE(EVP_HPKE_CTX_setup_sender(
          sender_ctx.get(), enc, &enc_len, sizeof(enc),
          EVP_hpke_x25519_hkdf_sha256(), kdf(), aead(), kSmallOrderPoint,
          sizeof(kSmallOrderPoint), nullptr, 0));

      // Likewise with auth.
      EXPECT_FALSE(EVP_HPKE_CTX_setup_auth_sender(
          sender_ctx.get(), enc, &enc_len, sizeof(enc), key.get(), kdf(),
          aead(), kSmallOrderPoint, sizeof(kSmallOrderPoint), nullptr, 0));

      // Set up the recipient, passing in kSmallOrderPoint as |enc|.
      ScopedEVP_HPKE_CTX recipient_ctx;
      EXPECT_FALSE(EVP_HPKE_CTX_setup_recipient(
          recipient_ctx.get(), key.get(), kdf(), aead(), kSmallOrderPoint,
          sizeof(kSmallOrderPoint), nullptr, 0));

      // Likewise with auth. With auth, a small-order point could appear as
      // either |enc| or the peer public key.
      EXPECT_FALSE(EVP_HPKE_CTX_setup_auth_recipient(
          recipient_ctx.get(), key.get(), kdf(), aead(), kSmallOrderPoint,
          sizeof(kSmallOrderPoint), nullptr, 0, kValidPoint,
          sizeof(kValidPoint)));
      EXPECT_FALSE(EVP_HPKE_CTX_setup_auth_recipient(
          recipient_ctx.get(), key.get(), kdf(), aead(), kValidPoint,
          sizeof(kValidPoint), nullptr, 0, kSmallOrderPoint,
          sizeof(kSmallOrderPoint)));
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
  uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
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
  EXPECT_TRUE(
      ErrorEquals(ERR_get_error(), ERR_LIB_EVP, EVP_R_INVALID_BUFFER_SIZE));
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
  EXPECT_TRUE(
      ErrorEquals(ERR_get_error(), ERR_LIB_EVP, EVP_R_INVALID_PEER_KEY));
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
  EXPECT_TRUE(
      ErrorEquals(ERR_get_error(), ERR_LIB_EVP, EVP_R_INVALID_PEER_KEY));
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

// ML-KEM HPKE tests.

struct MLKEMTestParam {
  const char *name;
  const EVP_HPKE_KEM *(*kem_func)(void);
  const EVP_HPKE_KDF *(*kdf_func)(void);
  const EVP_HPKE_AEAD *(*aead_func)(void);
};

class HPKEMLKEMTest : public testing::TestWithParam<MLKEMTestParam> {};

TEST_P(HPKEMLKEMTest, RoundTrip) {
  const MLKEMTestParam &param = GetParam();
  const EVP_HPKE_KEM *kem = param.kem_func();
  const EVP_HPKE_KDF *kdf = param.kdf_func();
  const EVP_HPKE_AEAD *aead = param.aead_func();

  // Generate the recipient's keypair.
  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), kem));

  uint8_t public_key_r[EVP_HPKE_MAX_PUBLIC_KEY_LENGTH];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));
  EXPECT_EQ(public_key_r_len, EVP_HPKE_KEM_public_key_len(kem));

  // Sender setup.
  ScopedEVP_HPKE_CTX sender_ctx;
  uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
  size_t enc_len;
  ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(sender_ctx.get(), enc, &enc_len,
                                        sizeof(enc), kem, kdf, aead,
                                        public_key_r, public_key_r_len,
                                        nullptr, 0));
  EXPECT_EQ(enc_len, EVP_HPKE_KEM_enc_len(kem));

  // Seal a message.
  const char kPlaintext[] = "Hello, post-quantum world!";
  const uint8_t kAad[] = {0xde, 0xad, 0xbe, 0xef};
  std::vector<uint8_t> ciphertext(sizeof(kPlaintext) +
                                  EVP_HPKE_CTX_max_overhead(sender_ctx.get()));
  size_t ciphertext_len;
  ASSERT_TRUE(EVP_HPKE_CTX_seal(
      sender_ctx.get(), ciphertext.data(), &ciphertext_len, ciphertext.size(),
      reinterpret_cast<const uint8_t *>(kPlaintext), sizeof(kPlaintext), kAad,
      sizeof(kAad)));

  // Recipient setup.
  ScopedEVP_HPKE_CTX recipient_ctx;
  ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(recipient_ctx.get(), key.get(), kdf,
                                           aead, enc, enc_len, nullptr, 0));

  // Open the message.
  std::vector<uint8_t> plaintext(ciphertext_len);
  size_t plaintext_len;
  ASSERT_TRUE(EVP_HPKE_CTX_open(recipient_ctx.get(), plaintext.data(),
                                &plaintext_len, plaintext.size(),
                                ciphertext.data(), ciphertext_len, kAad,
                                sizeof(kAad)));
  EXPECT_EQ(Bytes(plaintext.data(), plaintext_len),
            Bytes(kPlaintext, sizeof(kPlaintext)));
}

TEST_P(HPKEMLKEMTest, MultiMessage) {
  const MLKEMTestParam &param = GetParam();
  const EVP_HPKE_KEM *kem = param.kem_func();
  const EVP_HPKE_KDF *kdf = param.kdf_func();
  const EVP_HPKE_AEAD *aead = param.aead_func();

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), kem));

  uint8_t public_key_r[EVP_HPKE_MAX_PUBLIC_KEY_LENGTH];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));

  ScopedEVP_HPKE_CTX sender_ctx;
  uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
  size_t enc_len;
  ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(sender_ctx.get(), enc, &enc_len,
                                        sizeof(enc), kem, kdf, aead,
                                        public_key_r, public_key_r_len,
                                        nullptr, 0));

  ScopedEVP_HPKE_CTX recipient_ctx;
  ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(recipient_ctx.get(), key.get(), kdf,
                                           aead, enc, enc_len, nullptr, 0));

  for (int i = 0; i < 10; i++) {
    std::string msg = "message " + std::to_string(i);
    std::vector<uint8_t> ct(msg.size() + EVP_HPKE_CTX_max_overhead(sender_ctx.get()));
    size_t ct_len;
    ASSERT_TRUE(EVP_HPKE_CTX_seal(
        sender_ctx.get(), ct.data(), &ct_len, ct.size(),
        reinterpret_cast<const uint8_t *>(msg.data()), msg.size(), nullptr, 0));

    std::vector<uint8_t> pt(ct_len);
    size_t pt_len;
    ASSERT_TRUE(EVP_HPKE_CTX_open(recipient_ctx.get(), pt.data(), &pt_len,
                                  pt.size(), ct.data(), ct_len, nullptr, 0));
    EXPECT_EQ(Bytes(pt.data(), pt_len),
              Bytes(reinterpret_cast<const uint8_t *>(msg.data()), msg.size()));
  }
}

TEST_P(HPKEMLKEMTest, KeySerializationRoundTrip) {
  const MLKEMTestParam &param = GetParam();
  const EVP_HPKE_KEM *kem = param.kem_func();

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), kem));

  // Export the private key.
  std::vector<uint8_t> priv_key(EVP_HPKE_KEM_private_key_len(kem));
  size_t priv_key_len;
  ASSERT_TRUE(EVP_HPKE_KEY_private_key(key.get(), priv_key.data(),
                                       &priv_key_len, priv_key.size()));
  EXPECT_EQ(priv_key_len, EVP_HPKE_KEM_private_key_len(kem));

  // Export the public key.
  std::vector<uint8_t> pub_key(EVP_HPKE_KEM_public_key_len(kem));
  size_t pub_key_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), pub_key.data(), &pub_key_len,
                                      pub_key.size()));
  EXPECT_EQ(pub_key_len, EVP_HPKE_KEM_public_key_len(kem));

  // Re-import the private key and verify the public key matches.
  ScopedEVP_HPKE_KEY key2;
  ASSERT_TRUE(
      EVP_HPKE_KEY_init(key2.get(), kem, priv_key.data(), priv_key_len));

  std::vector<uint8_t> pub_key2(EVP_HPKE_KEM_public_key_len(kem));
  size_t pub_key2_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key2.get(), pub_key2.data(),
                                      &pub_key2_len, pub_key2.size()));
  EXPECT_EQ(Bytes(pub_key.data(), pub_key_len),
            Bytes(pub_key2.data(), pub_key2_len));
}

TEST_P(HPKEMLKEMTest, KeyCopyAndMove) {
  const MLKEMTestParam &param = GetParam();
  const EVP_HPKE_KEM *kem = param.kem_func();
  const EVP_HPKE_KDF *kdf = param.kdf_func();
  const EVP_HPKE_AEAD *aead = param.aead_func();

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), kem));

  uint8_t public_key_r[EVP_HPKE_MAX_PUBLIC_KEY_LENGTH];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));

  // Test copy.
  {
    ScopedEVP_HPKE_KEY key_copy;
    ASSERT_TRUE(EVP_HPKE_KEY_copy(key_copy.get(), key.get()));

    ScopedEVP_HPKE_CTX sender_ctx;
    uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
    size_t enc_len;
    ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(sender_ctx.get(), enc, &enc_len,
                                          sizeof(enc), kem, kdf, aead,
                                          public_key_r, public_key_r_len,
                                          nullptr, 0));

    const char kPlaintext[] = "copy test";
    std::vector<uint8_t> ct(sizeof(kPlaintext) +
                            EVP_HPKE_CTX_max_overhead(sender_ctx.get()));
    size_t ct_len;
    ASSERT_TRUE(EVP_HPKE_CTX_seal(
        sender_ctx.get(), ct.data(), &ct_len, ct.size(),
        reinterpret_cast<const uint8_t *>(kPlaintext), sizeof(kPlaintext),
        nullptr, 0));

    ScopedEVP_HPKE_CTX recipient_ctx;
    ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(recipient_ctx.get(),
                                             key_copy.get(), kdf, aead, enc,
                                             enc_len, nullptr, 0));

    std::vector<uint8_t> pt(ct_len);
    size_t pt_len;
    ASSERT_TRUE(EVP_HPKE_CTX_open(recipient_ctx.get(), pt.data(), &pt_len,
                                  pt.size(), ct.data(), ct_len, nullptr, 0));
    EXPECT_EQ(Bytes(pt.data(), pt_len), Bytes(kPlaintext, sizeof(kPlaintext)));
  }

  // Test move.
  {
    ScopedEVP_HPKE_KEY key_moved;
    ScopedEVP_HPKE_KEY key_temp;
    ASSERT_TRUE(EVP_HPKE_KEY_copy(key_temp.get(), key.get()));
    EVP_HPKE_KEY_move(key_moved.get(), key_temp.get());

    ScopedEVP_HPKE_CTX sender_ctx;
    uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
    size_t enc_len;
    ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(sender_ctx.get(), enc, &enc_len,
                                          sizeof(enc), kem, kdf, aead,
                                          public_key_r, public_key_r_len,
                                          nullptr, 0));

    const char kPlaintext[] = "move test";
    std::vector<uint8_t> ct(sizeof(kPlaintext) +
                            EVP_HPKE_CTX_max_overhead(sender_ctx.get()));
    size_t ct_len;
    ASSERT_TRUE(EVP_HPKE_CTX_seal(
        sender_ctx.get(), ct.data(), &ct_len, ct.size(),
        reinterpret_cast<const uint8_t *>(kPlaintext), sizeof(kPlaintext),
        nullptr, 0));

    ScopedEVP_HPKE_CTX recipient_ctx;
    ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(recipient_ctx.get(),
                                             key_moved.get(), kdf, aead, enc,
                                             enc_len, nullptr, 0));

    std::vector<uint8_t> pt(ct_len);
    size_t pt_len;
    ASSERT_TRUE(EVP_HPKE_CTX_open(recipient_ctx.get(), pt.data(), &pt_len,
                                  pt.size(), ct.data(), ct_len, nullptr, 0));
    EXPECT_EQ(Bytes(pt.data(), pt_len), Bytes(kPlaintext, sizeof(kPlaintext)));
  }
}

TEST_P(HPKEMLKEMTest, AuthModeNotSupported) {
  const MLKEMTestParam &param = GetParam();
  const EVP_HPKE_KEM *kem = param.kem_func();
  const EVP_HPKE_KDF *kdf = param.kdf_func();
  const EVP_HPKE_AEAD *aead = param.aead_func();

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), kem));

  uint8_t public_key_r[EVP_HPKE_MAX_PUBLIC_KEY_LENGTH];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));

  // Auth sender should fail.
  ScopedEVP_HPKE_CTX sender_ctx;
  uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
  size_t enc_len;
  EXPECT_FALSE(EVP_HPKE_CTX_setup_auth_sender(
      sender_ctx.get(), enc, &enc_len, sizeof(enc), key.get(), kdf, aead,
      public_key_r, public_key_r_len, nullptr, 0));

  // Auth recipient should fail.
  uint8_t fake_enc[EVP_HPKE_MAX_ENC_LENGTH] = {0};
  ScopedEVP_HPKE_CTX recipient_ctx;
  EXPECT_FALSE(EVP_HPKE_CTX_setup_auth_recipient(
      recipient_ctx.get(), key.get(), kdf, aead, fake_enc,
      EVP_HPKE_KEM_enc_len(kem), nullptr, 0, public_key_r, public_key_r_len));
}

TEST_P(HPKEMLKEMTest, WrongCiphertextSize) {
  const MLKEMTestParam &param = GetParam();
  const EVP_HPKE_KEM *kem = param.kem_func();
  const EVP_HPKE_KDF *kdf = param.kdf_func();
  const EVP_HPKE_AEAD *aead = param.aead_func();

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), kem));

  // Attempt to set up recipient with wrong-sized enc.
  uint8_t bogus_enc[100] = {0xff};
  ScopedEVP_HPKE_CTX recipient_ctx;
  EXPECT_FALSE(EVP_HPKE_CTX_setup_recipient(
      recipient_ctx.get(), key.get(), kdf, aead, bogus_enc, sizeof(bogus_enc),
      nullptr, 0));
}

TEST_P(HPKEMLKEMTest, ExportSecret) {
  const MLKEMTestParam &param = GetParam();
  const EVP_HPKE_KEM *kem = param.kem_func();
  const EVP_HPKE_KDF *kdf = param.kdf_func();
  const EVP_HPKE_AEAD *aead = param.aead_func();

  ScopedEVP_HPKE_KEY key;
  ASSERT_TRUE(EVP_HPKE_KEY_generate(key.get(), kem));

  uint8_t public_key_r[EVP_HPKE_MAX_PUBLIC_KEY_LENGTH];
  size_t public_key_r_len;
  ASSERT_TRUE(EVP_HPKE_KEY_public_key(key.get(), public_key_r,
                                      &public_key_r_len, sizeof(public_key_r)));

  ScopedEVP_HPKE_CTX sender_ctx;
  uint8_t enc[EVP_HPKE_MAX_ENC_LENGTH];
  size_t enc_len;
  ASSERT_TRUE(EVP_HPKE_CTX_setup_sender(sender_ctx.get(), enc, &enc_len,
                                        sizeof(enc), kem, kdf, aead,
                                        public_key_r, public_key_r_len,
                                        nullptr, 0));

  ScopedEVP_HPKE_CTX recipient_ctx;
  ASSERT_TRUE(EVP_HPKE_CTX_setup_recipient(recipient_ctx.get(), key.get(), kdf,
                                           aead, enc, enc_len, nullptr, 0));

  const uint8_t kContext[] = {0x01, 0x02, 0x03};
  uint8_t sender_export[32];
  uint8_t recipient_export[32];
  ASSERT_TRUE(EVP_HPKE_CTX_export(sender_ctx.get(), sender_export,
                                  sizeof(sender_export), kContext,
                                  sizeof(kContext)));
  ASSERT_TRUE(EVP_HPKE_CTX_export(recipient_ctx.get(), recipient_export,
                                  sizeof(recipient_export), kContext,
                                  sizeof(kContext)));
  EXPECT_EQ(Bytes(sender_export), Bytes(recipient_export));
}

static const MLKEMTestParam kMLKEMTestParams[] = {
    {"MLKEM512_SHA256_AES128GCM", &EVP_hpke_mlkem512, &EVP_hpke_hkdf_sha256,
     &EVP_hpke_aes_128_gcm},
    {"MLKEM768_SHA256_AES256GCM", &EVP_hpke_mlkem768, &EVP_hpke_hkdf_sha256,
     &EVP_hpke_aes_256_gcm},
    {"MLKEM1024_SHA384_AES256GCM", &EVP_hpke_mlkem1024, &EVP_hpke_hkdf_sha384,
     &EVP_hpke_aes_256_gcm},
    {"MLKEM1024_SHA256_AES256GCM", &EVP_hpke_mlkem1024, &EVP_hpke_hkdf_sha256,
     &EVP_hpke_aes_256_gcm},
    {"MLKEM1024_SHA384_ChaCha20Poly1305", &EVP_hpke_mlkem1024,
     &EVP_hpke_hkdf_sha384, &EVP_hpke_chacha20_poly1305},
};

INSTANTIATE_TEST_SUITE_P(HPKEMLKEM, HPKEMLKEMTest,
                         testing::ValuesIn(kMLKEMTestParams),
                         [](const testing::TestParamInfo<MLKEMTestParam> &info) {
                           return info.param.name;
                         });


}  // namespace bssl
