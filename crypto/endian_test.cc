#include <gtest/gtest.h>
#include "internal.h"
#include "openssl/aes.h"
#include "openssl/bn.h"
#include "test/test_util.h"


TEST(EndianTest, u32Operations) {
  uint8_t buffer[4];
  uint32_t val = 0x12345678;
  uint8_t expected_be[4] = {0x12, 0x34, 0x56, 0x78};
  uint8_t expected_le[4] = {0x78, 0x56, 0x34, 0x12};


  CRYPTO_store_u32_le(buffer, val);
  EXPECT_EQ(Bytes(expected_le), Bytes(buffer));
  EXPECT_EQ(val, CRYPTO_load_u32_le(buffer));

  CRYPTO_store_u32_be(buffer, val);
  EXPECT_EQ(Bytes(expected_be), Bytes(buffer));
  EXPECT_EQ(val, CRYPTO_load_u32_be(buffer));
}

TEST(EndianTest, u64Operations) {
  uint8_t buffer[8];
  uint64_t val = 0x123456789abcdef0;
  uint8_t expected_be[8] = {0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0};
  uint8_t expected_le[8] = {0xf0, 0xde, 0xbc, 0x9a, 0x78, 0x56, 0x34, 0x12};

  CRYPTO_store_u64_le(buffer, val);
  EXPECT_EQ(Bytes(expected_le), Bytes(buffer));
  EXPECT_EQ(val, CRYPTO_load_u64_le(buffer));

  CRYPTO_store_u64_be(buffer, val);
  EXPECT_EQ(Bytes(expected_be), Bytes(buffer));
  EXPECT_EQ(val, CRYPTO_load_u64_be(buffer));
}

TEST(EndianTest, wordOperations) {
  uint8_t buffer[sizeof(crypto_word_t)];
#if defined(OPENSSL_64_BIT)
  size_t val = 0x123456789abcdef0;
  uint8_t expected_le[8] = {0xf0, 0xde, 0xbc, 0x9a, 0x78, 0x56, 0x34, 0x12};
#else
size_t val = 0x12345678;
uint8_t expected_le[4] = {0x78, 0x56, 0x34, 0x12};
#endif

  CRYPTO_store_word_le(buffer, val);
  EXPECT_EQ(Bytes(expected_le), Bytes(buffer));
  EXPECT_EQ(val, CRYPTO_load_word_le(buffer));
}

TEST(EndianTest, TestRotate32) {
  uint32_t value = 0b00000010000000000000000000000;
  uint32_t expected = 0b00100000000000000000000000000;

  uint32_t rotl_by = 4;
  uint32_t rotr_by = 32 - rotl_by;

  uint32_t rotl_value = CRYPTO_rotl_u32(value, rotl_by);
  uint32_t rotr_value = CRYPTO_rotr_u32(value, rotr_by);

  ASSERT_EQ(rotl_value, rotr_value);
  EXPECT_EQ(expected, rotl_value);
  ASSERT_EQ(CRYPTO_rotr_u32(rotl_value, rotl_by), value);
}

TEST(EndianTest, TestRotate64) {
  uint64_t value = 0b0000001000000000000000000000000000010000000000000000000000;
  uint64_t expected = 0b0010000000000000000000000000000100000000000000000000000000;

  uint64_t rotl_by = 4;
  uint64_t rotr_by = 64 - rotl_by;

  uint64_t rotl_value = CRYPTO_rotl_u64(value, rotl_by);
  uint64_t rotr_value = CRYPTO_rotr_u64(value, rotr_by);

  ASSERT_EQ(rotl_value, rotr_value);
  EXPECT_EQ(expected, rotl_value);
  ASSERT_EQ(CRYPTO_rotr_u64(rotl_value, rotl_by), value);
}

union test_union {
  uint16_t big[2];
  uint8_t small[4];
};

struct test_struct {
  test_union union_val;
};

TEST(EndianTest, TestStructUnion) {
  struct test_struct val = {{{0}}};
  val.union_val.big[0] = 0x1234;
  val.union_val.big[1] = 0x5678;


#if defined(OPENSSL_BIG_ENDIAN)
  ASSERT_EQ(val.union_val.small[0], 0x12);
  ASSERT_EQ(val.union_val.small[1], 0x34);
  ASSERT_EQ(val.union_val.small[2], 0x56);
  ASSERT_EQ(val.union_val.small[3], 0x78);
#else
  ASSERT_EQ(val.union_val.small[0], 0x34);
  ASSERT_EQ(val.union_val.small[1], 0x12);
  ASSERT_EQ(val.union_val.small[2], 0x78);
  ASSERT_EQ(val.union_val.small[3], 0x56);
#endif
}

// Shift left is increasing value/significance
// shift right decreases value/drops values
TEST(EndianTest, Shifting) {
  uint32_t test = 0b1010000000010001;
  ASSERT_EQ(test << 4, (uint32_t)0b10100000000100010000);
  ASSERT_EQ(test >> 4, (uint32_t)0b101000000001);
}

TEST(EndianTest, Swap) {
  EXPECT_EQ(0x3412, CRYPTO_bswap2(0x1234));
  EXPECT_EQ((uint32_t)0x78563412, CRYPTO_bswap4(0x12345678));
  EXPECT_EQ(0xf0debc9a78563412, CRYPTO_bswap8(0x123456789abcdef0));
}

TEST(EndianTest, BN_bin2bn) {
  bssl::UniquePtr<BIGNUM> x(BN_new());
  uint8_t input[256];
  OPENSSL_memset(input, 0, sizeof(input));
  input[0] = 0xaa;
  input[1] = 0x01;
  input[254] = 0x01;
  input[255] = 0x02;
  ASSERT_NE(nullptr, BN_bin2bn(input, sizeof(input), x.get()));
  EXPECT_FALSE(BN_is_zero(x.get()));
  for (int i = 1; i < (256*8/BN_BITS2) - 1; i++) {
    SCOPED_TRACE(i);
    EXPECT_EQ((uint64_t)0, x.get()->d[i]);
  }
  EXPECT_EQ((uint64_t)0x0102, x.get()->d[0]);
  EXPECT_EQ((uint64_t)0xaa01 << (BN_BITS2-16), x.get()->d[(256*8/BN_BITS2)-1]);
}

TEST(EndianTest, BN_le2bn) {
  bssl::UniquePtr<BIGNUM> x(BN_new());
  uint8_t input[256];
  OPENSSL_memset(input, 0, sizeof(input));
  input[0] = 0xaa;
  input[1] = 0x01;
  input[254] = 0x01;
  input[255] = 0x02;
  ASSERT_NE(nullptr, BN_le2bn(input, sizeof(input), x.get()));
  EXPECT_FALSE(BN_is_zero(x.get()));
  for (int i = 1; i < (256*8/BN_BITS2) - 1; i++) {
    SCOPED_TRACE(i);
    EXPECT_EQ((uint64_t)0, x.get()->d[i]);
  }
  EXPECT_EQ((uint64_t)0x01aa, x.get()->d[0]);
  EXPECT_EQ((uint64_t)0x0201 << (BN_BITS2-16), x.get()->d[(256*8/BN_BITS2)-1]);
}

TEST(EndianTest, BN_bn2bin) {
  bssl::UniquePtr<BIGNUM> x(BN_new());
  uint8_t input[256];
  OPENSSL_memset(input, 0, sizeof(input));
  input[0] = 0xaa;
  input[1] = 0x01;
  input[254] = 0x01;
  input[255] = 0x02;
  ASSERT_NE(nullptr, BN_bin2bn(input, sizeof(input), x.get()));

  uint8_t out[256];
  OPENSSL_memset(out, 0, sizeof(out));
  EXPECT_EQ((size_t)256, BN_bn2bin(x.get(), out));
  EXPECT_EQ(Bytes(input), Bytes(out));
}

TEST(EndianTest, BN_bn2le_padded) {
  bssl::UniquePtr<BIGNUM> x(BN_new());
  uint8_t input[256];
  OPENSSL_memset(input, 0, sizeof(input));
  input[0] = 0xaa;
  input[1] = 0x01;
  input[254] = 0x01;
  input[255] = 0x02;
  ASSERT_NE(nullptr, BN_le2bn(input, sizeof(input), x.get()));

  uint8_t out[256];
  OPENSSL_memset(out, 0, sizeof(out));
  EXPECT_EQ(1, BN_bn2le_padded(out, sizeof(out), x.get()));
  EXPECT_EQ(Bytes(input), Bytes(out));
}

TEST(EndianTest, BN_bn2bin_padded) {
  bssl::UniquePtr<BIGNUM> x(BN_new());
  uint8_t input[256];
  OPENSSL_memset(input, 0, sizeof(input));
  input[0] = 0xaa;
  input[1] = 0x01;
  input[254] = 0x01;
  input[255] = 0x02;
  ASSERT_NE(nullptr, BN_bin2bn(input, sizeof(input), x.get()));

  uint8_t out[256];
  OPENSSL_memset(out, 0, sizeof(out));
  EXPECT_EQ(1, BN_bn2bin_padded(out, sizeof(out), x.get()));
  EXPECT_EQ(Bytes(input), Bytes(out));
}

TEST(EndianTest, AES) {
  // Initialize the key and message buffers with zeros
  uint8_t key[AES_BLOCK_SIZE] = {0};
  key[0] = 0xaa;
  key[0] = 0xbb;
  uint8_t message[AES_BLOCK_SIZE] = {0};
  message[0] = 0xcc;
  message[1] = 0xdd;

  // Allocate buffer to store the encrypted message
  uint8_t encrypted_message[AES_BLOCK_SIZE];

  // Create an AES_KEY struct
  AES_KEY aes_key = {{0}, 0};
  ASSERT_EQ(0, AES_set_encrypt_key(key, 128, &aes_key));

  AES_encrypt(message, encrypted_message, &aes_key);

  const uint8_t known_value_bytes[AES_BLOCK_SIZE] = {
      0x15, 0x81, 0x0f, 0xf3, 0x0d, 0x23, 0x08, 0x71, 0x96, 0x05, 0x94, 0x12, 0x14, 0xb7, 0xd6, 0x69
  };
  EXPECT_EQ(Bytes(known_value_bytes), Bytes(encrypted_message));
}

TEST(EndianTest, memcpy) {
  uint8_t buffer[2] = {0xab, 0xcd};
  uint16_t out = 0;
  memcpy(&out, buffer, 2);
#if defined(OPENSSL_BIG_ENDIAN)
  EXPECT_EQ(out, 0xabcd);
#else
  EXPECT_EQ(out, 0xcdab);
#endif
}

TEST(EndianTest, masking) {
  uint16_t value = 0xabcd;
  uint16_t mask = 0xf00f;
  uint16_t result = value & mask;
  EXPECT_EQ(result, 0xa00d);
}
