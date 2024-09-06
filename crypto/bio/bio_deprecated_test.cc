#include <gtest/gtest.h>

#include <openssl/bytestring.h>
#include <openssl/crypto.h>
#include <openssl/mem.h>
#include <openssl/pem.h>
#include <openssl/pkcs7.h>
#include <openssl/rand.h>
#include <openssl/stack.h>
#include <openssl/x509.h>

#include "../bytestring/internal.h"
#include "../internal.h"
#include "../test/test_util.h"

// NOTE: need to keep these in sync with cipher BIO source file
#define ENC_MIN_CHUNK_SIZE 256
#define ENC_BLOCK_SIZE 1024 * 4

#define BIO_get_cipher_status(bio) \
  BIO_ctrl(bio, BIO_C_GET_CIPHER_STATUS, 0, NULL)

struct CipherParams {
  const char name[40];
  const EVP_CIPHER *(*cipher)(void);
};

static const struct CipherParams Ciphers[] = {
    {"AES_128_CTR", EVP_aes_128_ctr},
    {"AES_128_GCM", EVP_aes_128_gcm},
    {"AES_128_OFB", EVP_aes_128_ofb},
    {"AES_256_CTR", EVP_aes_256_ctr},
    {"AES_256_GCM", EVP_aes_256_gcm},
    {"AES_256_OFB", EVP_aes_256_ofb},
    {"ChaCha20Poly1305", EVP_chacha20_poly1305},
};

class DeprecatedTest : public testing::TestWithParam<CipherParams> {};

INSTANTIATE_TEST_SUITE_P(BIOTest, DeprecatedTest, testing::ValuesIn(Ciphers),
                         [](const testing::TestParamInfo<CipherParams> &params)
                             -> std::string { return params.param.name; });

TEST_P(DeprecatedTest, Cipher) {
  uint8_t key[EVP_MAX_KEY_LENGTH];
  uint8_t iv[EVP_MAX_IV_LENGTH];
  uint8_t pt[8 * ENC_BLOCK_SIZE];
  uint8_t pt_decrypted[sizeof(pt)];
  uint8_t ct[sizeof(pt) + 2*EVP_MAX_BLOCK_LENGTH];  // pt + pad + tag
  bssl::UniquePtr<BIO> bio_cipher;
  bssl::UniquePtr<BIO> bio_mem;
  std::vector<uint8_t> pt_vec, ct_vec, decrypted_pt_vec;
  uint8_t buff[2 * sizeof(pt)];
  OPENSSL_memset(buff, 'A', sizeof(buff));

  const EVP_CIPHER *cipher = GetParam().cipher();
  ASSERT_TRUE(cipher);

  OPENSSL_memset(pt, 'A', sizeof(pt));
  ASSERT_TRUE(RAND_bytes(key, sizeof(key)));
  ASSERT_TRUE(RAND_bytes(iv, sizeof(iv)));

  // Unsupported or unimplemented CTRL flags and cipher(s)
  bio_cipher.reset(BIO_new(BIO_f_cipher()));
  ASSERT_TRUE(bio_cipher);
  EXPECT_FALSE(BIO_ctrl(bio_cipher.get(), BIO_CTRL_DUP, 0, NULL));
  EXPECT_FALSE(BIO_ctrl(bio_cipher.get(), BIO_CTRL_GET_CALLBACK, 0, NULL));
  EXPECT_FALSE(BIO_ctrl(bio_cipher.get(), BIO_CTRL_SET_CALLBACK, 0, NULL));
  EXPECT_FALSE(BIO_ctrl(bio_cipher.get(), BIO_C_DO_STATE_MACHINE, 0, NULL));
  EXPECT_FALSE(BIO_ctrl(bio_cipher.get(), BIO_C_GET_CIPHER_CTX, 0, NULL));
  EXPECT_FALSE(BIO_ctrl(bio_cipher.get(), BIO_C_SSL_MODE, 0, NULL));
  EXPECT_FALSE(BIO_set_cipher(bio_cipher.get(), EVP_rc4(), key, iv, /*enc*/ 1));

  // Round-trip using only |BIO_read|, backing mem buffer with pt/ct. Fixed size
  // IO.
  bio_cipher.reset(BIO_new(BIO_f_cipher()));
  ASSERT_TRUE(bio_cipher);
  EXPECT_TRUE(BIO_set_cipher(bio_cipher.get(), cipher, key, iv, /*enc*/ 1));
  bio_mem.reset(BIO_new_mem_buf(pt, sizeof(pt)));
  ASSERT_TRUE(bio_mem);
  ASSERT_TRUE(BIO_push(bio_cipher.get(), bio_mem.get()));
  bio_mem.release();  // |bio_cipher| will take ownership
  // Copy |pt| contents to |ct| so we can detect that |ct| gets overwritten
  OPENSSL_memcpy(ct, pt, sizeof(pt));
  OPENSSL_cleanse(pt_decrypted, sizeof(pt_decrypted));
  EXPECT_FALSE(BIO_eof(bio_cipher.get()));
  EXPECT_LT(0UL, BIO_pending(bio_cipher.get()));
  EXPECT_TRUE(BIO_read(bio_cipher.get(), ct, sizeof(ct)));
  EXPECT_TRUE(BIO_eof(bio_cipher.get()));
  EXPECT_EQ(0UL, BIO_pending(bio_cipher.get()));
  EXPECT_TRUE(BIO_get_cipher_status(bio_cipher.get()));
  // only consider first |sizeof(pt)| bytes of |ct|, exclude pad block
  EXPECT_NE(Bytes(pt, sizeof(pt)), Bytes(ct, sizeof(pt)));
  // Reset both BIOs and decrypt
  bio_cipher.reset(BIO_new(BIO_f_cipher()));
  ASSERT_TRUE(bio_cipher);
  EXPECT_TRUE(BIO_set_cipher(bio_cipher.get(), cipher, key, iv, /*enc*/ 0));
  bio_mem.reset(BIO_new_mem_buf((const uint8_t *)ct, sizeof(ct)));
  ASSERT_TRUE(bio_mem);
  ASSERT_TRUE(BIO_push(bio_cipher.get(), bio_mem.get()));
  bio_mem.release();  // |bio_cipher| will take ownership
  EXPECT_TRUE(BIO_read(bio_cipher.get(), pt_decrypted, sizeof(pt_decrypted)));
  EXPECT_TRUE(BIO_get_cipher_status(bio_cipher.get()));
  EXPECT_EQ(Bytes(pt, sizeof(pt)), Bytes(pt_decrypted, sizeof(pt_decrypted)));

  // Round-trip using |BIO_write| for encryption with same BIOs, reset between
  // encryption/decryption using |BIO_reset|. Fixed size IO.
  bio_cipher.reset(BIO_new(BIO_f_cipher()));
  ASSERT_TRUE(bio_cipher);
  EXPECT_TRUE(BIO_set_cipher(bio_cipher.get(), cipher, key, iv, /*enc*/ 1));
  bio_mem.reset(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(bio_mem);
  ASSERT_TRUE(BIO_push(bio_cipher.get(), bio_mem.get()));
  // Copy |pt| contents to |ct| so we can detect that |ct| gets overwritten
  OPENSSL_memcpy(ct, pt, sizeof(pt));
  OPENSSL_cleanse(pt_decrypted, sizeof(pt_decrypted));
  EXPECT_TRUE(BIO_eof(bio_cipher.get()));
  EXPECT_EQ(0UL, BIO_wpending(bio_cipher.get()));
  EXPECT_TRUE(BIO_write(bio_cipher.get(), pt, sizeof(pt)));
  EXPECT_FALSE(BIO_eof(bio_cipher.get()));
  EXPECT_EQ(0UL, BIO_wpending(bio_cipher.get()));
  EXPECT_TRUE(BIO_flush(bio_cipher.get()));
  EXPECT_FALSE(BIO_eof(bio_cipher.get()));
  EXPECT_EQ(0UL, BIO_wpending(bio_cipher.get()));
  EXPECT_TRUE(BIO_get_cipher_status(bio_cipher.get()));
  EXPECT_TRUE(BIO_read(bio_mem.get(), ct, sizeof(ct)));
  // only consider first |sizeof(pt)| bytes of |ct|, exclude pad block
  EXPECT_NE(Bytes(pt, sizeof(pt)), Bytes(ct, sizeof(pt)));
  // Reset both BIOs and decrypt
  EXPECT_TRUE(BIO_reset(bio_cipher.get()));  // also resets owned |bio_mem|
  EXPECT_TRUE(BIO_write(bio_mem.get(), ct, sizeof(ct)));
  bio_mem.release();  // |bio_cipher| took ownership
  EXPECT_TRUE(BIO_set_cipher(bio_cipher.get(), cipher, key, iv, /*enc*/ 0));
  EXPECT_TRUE(BIO_read(bio_cipher.get(), pt_decrypted, sizeof(pt_decrypted)));
  EXPECT_TRUE(BIO_get_cipher_status(bio_cipher.get()));
  EXPECT_EQ(Bytes(pt, sizeof(pt)), Bytes(pt_decrypted, sizeof(pt_decrypted)));

  // Test a number of different IO sizes around byte, word, cipher block,
  // BIO internal buffer size, and other boundaries.
  int io_sizes[] = {1,
                    3,
                    7,
                    8,
                    9,
                    64,
                    923,
                    2 * ENC_BLOCK_SIZE,
                    15,
                    16,
                    17,
                    31,
                    32,
                    33,
                    511,
                    512,
                    513,
                    1023,
                    1024,
                    1025,
                    ENC_MIN_CHUNK_SIZE - 1,
                    ENC_MIN_CHUNK_SIZE,
                    ENC_MIN_CHUNK_SIZE + 1,
                    ENC_BLOCK_SIZE - 1,
                    ENC_BLOCK_SIZE,
                    ENC_BLOCK_SIZE + 1};

  // Round-trip encryption/decryption with successive IOs of different sizes.
  bio_cipher.reset(BIO_new(BIO_f_cipher()));
  ASSERT_TRUE(bio_cipher);
  EXPECT_TRUE(BIO_set_cipher(bio_cipher.get(), cipher, key, iv, /*enc*/ 1));
  bio_mem.reset(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(bio_mem);
  ASSERT_TRUE(BIO_push(bio_cipher.get(), bio_mem.get()));
  for (size_t wsize : io_sizes) {
    pt_vec.insert(pt_vec.end(), buff, buff + wsize);
    EXPECT_TRUE(BIO_write(bio_cipher.get(), buff, wsize));
  }
  EXPECT_TRUE(BIO_flush(bio_cipher.get()));
  EXPECT_TRUE(BIO_get_cipher_status(bio_cipher.get()));
  while (!BIO_eof(bio_mem.get())) {
    size_t bytes_read = BIO_read(bio_mem.get(), buff, sizeof(buff));
    ct_vec.insert(ct_vec.end(), buff, buff + bytes_read);
  }
  EXPECT_TRUE(BIO_reset(bio_cipher.get()));  // also resets owned |bio_mem|
  EXPECT_TRUE(
      BIO_write(bio_mem.get(), ct_vec.data(), ct_vec.size()));  // replace ct
  bio_mem.release();  // |bio_cipher| took ownership
  EXPECT_TRUE(BIO_set_cipher(bio_cipher.get(), cipher, key, iv, /*enc*/ 0));
  for (size_t rsize : io_sizes) {
    EXPECT_TRUE(BIO_read(bio_cipher.get(), buff, rsize));
    decrypted_pt_vec.insert(decrypted_pt_vec.end(), buff, buff + rsize);
  }
  EXPECT_TRUE(BIO_get_cipher_status(bio_cipher.get()));
  EXPECT_EQ(pt_vec.size(), decrypted_pt_vec.size());
  EXPECT_EQ(Bytes(pt_vec.data(), pt_vec.size()),
            Bytes(decrypted_pt_vec.data(), decrypted_pt_vec.size()));

  // Induce IO failures in the underlying BIO between subsequent same-size
  // operations. The flow os this test is to, for each IO size:
  //
  // 1. Write/encrypt a chunk of plaintext.
  // 2. Disable writes in the underlying BIO and try to write the same plaintext
  //    chunk again. depending on how large the write size relative to cipher
  //    BIO's internal buffer size, the write may partially or fully succeed if
  //    it can be buffered.
  // 3. Enable writes in the underlying BIO and complete 2.'s chunk by writing
  //    any remaining bytes in the chunk
  // 4. Flush the cipher BIO to complete the encryption, reset the cipher BIO in
  //    decrypt mode with the underlying BIO containing the ciphertext.
  // 5. Similar to 1., read/decrypt a chunk of ciphertext.
  // 6. Similar to 2., disable reads in the underlying BIO. As with 2., this may
  //    partially or fully succeed depending on how large the read is relative
  //    to internal buffer sizes.
  // 7. Enable reads in the underlying BIO and decrypt the rest of the
  //    ciphertext.
  // 8. Compare original and decrypted plaintexts.
  int rsize, wsize;
  uint8_t *pos;
  for (int io_size : io_sizes) {
    pt_vec.clear();
    decrypted_pt_vec.clear();
    bio_cipher.reset(BIO_new(BIO_f_cipher()));
    ASSERT_TRUE(bio_cipher);
    EXPECT_TRUE(BIO_set_cipher(bio_cipher.get(), cipher, key, iv, /*enc*/ 1));
    bio_mem.reset(BIO_new(BIO_s_mem()));
    ASSERT_TRUE(bio_mem);
    ASSERT_TRUE(BIO_push(bio_cipher.get(), bio_mem.get()));
    // Initial write should fully succeed
    pos = &pt[0];
    wsize = BIO_write(bio_cipher.get(), pos, io_size);
    if (wsize > 0) {
      pt_vec.insert(pt_vec.end(), pos, pos + wsize);
      pos += wsize;
    }
    EXPECT_EQ(io_size, wsize);
    // All data should have been flushed
    EXPECT_EQ(0UL, BIO_wpending(bio_cipher.get()));
    // Set underlying BIO to r/o to induce buffering in |bio_cipher|
    auto disable_writes = [](BIO *bio, int oper, const char *argp, size_t len,
                             int argi, long argl, int bio_ret,
                             size_t *processed) -> long {
      return (oper & BIO_CB_RETURN) || !(oper & BIO_CB_WRITE);
    };
    BIO_set_callback_ex(bio_mem.get(), disable_writes);
    BIO_set_retry_write(bio_mem.get());
    // Write to |bio_cipher| should still succeed in writing up to
    // ENC_BLOCK_SIZE bytes by buffering them
    wsize = BIO_write(bio_cipher.get(), buff, io_size);
    if (wsize > 0) {
      pt_vec.insert(pt_vec.end(), pos, pos + wsize);
      pos += wsize;
    }
    EXPECT_GT(wsize, 0);
    EXPECT_LE(wsize, ENC_BLOCK_SIZE);
    // Now that there's buffered data, |BIO_wpending| should match
    EXPECT_EQ((size_t)wsize, BIO_wpending(bio_cipher.get()));
    // Renable writes
    BIO_set_callback_ex(bio_mem.get(), nullptr);
    BIO_clear_retry_flags(bio_mem.get());
    if (wsize < io_size) {
      const int remaining = io_size - wsize;
      ASSERT_EQ(remaining,
                BIO_write(bio_cipher.get(), buff + wsize, remaining));
      pt_vec.insert(pt_vec.end(), pos, pos + remaining);
      pos += wsize;
    }
    // Flush should empty the buffered encrypted data
    EXPECT_TRUE(BIO_flush(bio_cipher.get()));
    EXPECT_EQ(0UL, BIO_wpending(bio_cipher.get()));
    EXPECT_TRUE(BIO_get_cipher_status(bio_cipher.get()));
    EXPECT_TRUE(BIO_set_cipher(bio_cipher.get(), cipher, key, iv, /*enc*/ 0));
    // Reset BIOs, hydrate ciphertext for decryption
    ct_vec.clear();
    while ((rsize = BIO_read(bio_mem.get(), buff, io_size)) > 0) {
      ct_vec.insert(ct_vec.end(), buff, buff + rsize);
    }
    EXPECT_TRUE(BIO_reset(bio_cipher.get()));  // also resets owned |bio_mem|
    ASSERT_EQ((int)ct_vec.size(), BIO_write(bio_mem.get(), ct_vec.data(),
                                            ct_vec.size()));  // replace ct
    EXPECT_LE(pt_vec.size(), BIO_pending(bio_cipher.get()));
    // First read should fully succeed
    rsize = BIO_read(bio_cipher.get(), buff, io_size);
    ASSERT_EQ(io_size, rsize);
    decrypted_pt_vec.insert(decrypted_pt_vec.end(), buff, buff + rsize);
    // Disable reads from underlying BIO
    auto disable_reads = [](BIO *bio, int oper, const char *argp, size_t len,
                            int argi, long argl, int bio_ret,
                            size_t *processed) -> long {
      return (oper & BIO_CB_RETURN) || !(oper & BIO_CB_READ);
    };
    BIO_set_callback_ex(bio_mem.get(), disable_reads);
    // Set retry flags so |cipher_bio| doesn't give up when the read fails
    BIO_set_retry_read(bio_mem.get());
    rsize = BIO_read(bio_cipher.get(), buff, io_size);
    decrypted_pt_vec.insert(decrypted_pt_vec.end(), buff, buff + rsize);
    EXPECT_EQ(0UL, BIO_pending(bio_cipher.get()));
    // Re-enable reads from underlying BIO
    BIO_set_callback_ex(bio_mem.get(), nullptr);
    BIO_clear_retry_flags(bio_mem.get());
    while ((rsize = BIO_read(bio_cipher.get(), buff, io_size)) > 0) {
      decrypted_pt_vec.insert(decrypted_pt_vec.end(), buff, buff + rsize);
    }
    EXPECT_TRUE(BIO_eof(bio_cipher.get()));
    EXPECT_EQ(0UL, BIO_pending(bio_cipher.get()));
    EXPECT_TRUE(BIO_get_cipher_status(bio_cipher.get()));
    EXPECT_EQ(pt_vec.size(), decrypted_pt_vec.size());
    EXPECT_EQ(Bytes(pt_vec.data(), pt_vec.size()),
              Bytes(decrypted_pt_vec.data(), decrypted_pt_vec.size()));
    bio_mem.release();  // |bio_cipher| took ownership
  }
}
