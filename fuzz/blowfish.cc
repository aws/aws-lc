// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/blowfish.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include "../crypto/internal.h"

static uint8_t bf_key[16] = {
    0x7f, 0x63, 0xd3, 0xf1, 0xe9, 0x6d, 0x05, 0xb0,
    0x48, 0x0c, 0x5f, 0x52, 0x27, 0x4e, 0x4d, 0xcc,
};

static uint8_t bf_iv[16] = {0xca, 0xe4, 0xed, 0xe7, 0x25, 0xc9, 0xc1, 0x8b,
                            0x93, 0x07, 0xbe, 0x30, 0xf5, 0x84, 0x10, 0xc3};

static uint8_t padding[BF_BLOCK - 1] = {0x00, 0x00, 0x00, 0x00,
                                        0x00, 0x00, 0x00};

static int blowfish_ecb(const uint8_t *buf, size_t len);
static int blowfish_cbc(const uint8_t *buf, size_t len);
static int blowfish_cfb(const uint8_t *buf, size_t len);
static int blowfish_ofb(const uint8_t *buf, size_t len);

using ossl_uint8_t_ptr = std::unique_ptr<uint8_t, decltype(&OPENSSL_free)>;

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  if (!blowfish_ecb(buf, len)) {
    abort();
  }
  if (!blowfish_cbc(buf, len)) {
    abort();
  }
  if (!blowfish_cfb(buf, len)) {
    abort();
  }
  if (!blowfish_ofb(buf, len)) {
    abort();
  }
  return 0;
}

static int blowfish_ecb(const uint8_t *buf, size_t len) {
  if (len == 0) {
    return 1;
  }
  size_t padded_len = (len + BF_BLOCK - 1) & ~(BF_BLOCK - 1);
  ossl_uint8_t_ptr in_padded((uint8_t *)OPENSSL_zalloc(padded_len),
                             OPENSSL_free);
  ossl_uint8_t_ptr out((uint8_t *)OPENSSL_zalloc(padded_len), OPENSSL_free);

  OPENSSL_memcpy(in_padded.get(), buf, len);

  int out_bytes = 0, final_bytes = 0;

  bssl::ScopedEVP_CIPHER_CTX ctx;
  if (!EVP_EncryptInit_ex(ctx.get(), EVP_bf_ecb(), nullptr, bf_key, nullptr) ||
      !EVP_CIPHER_CTX_set_padding(ctx.get(), 0 /* no padding */) ||
      !EVP_EncryptUpdate(ctx.get(), out.get(), &out_bytes, in_padded.get(),
                         padded_len) ||
      !EVP_EncryptFinal_ex(ctx.get(), out.get() + out_bytes, &final_bytes) ||
      (size_t)(out_bytes + final_bytes) != padded_len ||
      OPENSSL_memcmp(in_padded.get(), out.get(), padded_len) == 0) {
    return 0;
  }

  OPENSSL_cleanse(in_padded.get(), padded_len);

  bssl::ScopedEVP_CIPHER_CTX decrypt_ctx;
  if (!EVP_DecryptInit_ex(decrypt_ctx.get(), EVP_bf_ecb(), nullptr, bf_key,
                          nullptr) ||
      !EVP_CIPHER_CTX_set_padding(decrypt_ctx.get(), 0 /* no padding */) ||
      !EVP_DecryptUpdate(decrypt_ctx.get(), in_padded.get(), &out_bytes,
                         out.get(), padded_len) ||
      !EVP_DecryptFinal_ex(decrypt_ctx.get(), in_padded.get() + out_bytes,
                           &final_bytes) ||
      (size_t)(out_bytes + final_bytes) != padded_len ||
      !(OPENSSL_memcmp(in_padded.get(), buf, len) == 0 &&
        OPENSSL_memcmp(in_padded.get() + len, padding, padded_len - len) ==
            0)) {
    return 0;
  }

  return 1;
}

static int blowfish_cbc(const uint8_t *buf, size_t len) {
  size_t padding = BF_BLOCK - (len & (BF_BLOCK - 1));
  // Make in to be the same size as out buffer for later decrypt
  ossl_uint8_t_ptr in((uint8_t *)OPENSSL_zalloc(len + padding), OPENSSL_free);
  ossl_uint8_t_ptr out((uint8_t *)OPENSSL_zalloc(len + padding), OPENSSL_free);

  OPENSSL_memcpy(in.get(), buf, len);

  int out_bytes = 0, final_bytes = 0;

  bssl::ScopedEVP_CIPHER_CTX ctx;
  if (!EVP_EncryptInit_ex(ctx.get(), EVP_bf_cbc(), nullptr, bf_key, bf_iv) ||
      !EVP_EncryptUpdate(ctx.get(), out.get(), &out_bytes, in.get(), len) ||
      !EVP_EncryptFinal_ex(ctx.get(), out.get() + out_bytes, &final_bytes) ||
      (size_t)(out_bytes + final_bytes) != (len + padding) ||
      OPENSSL_memcmp(in.get(), out.get(), len + padding) == 0) {
    return 0;
  }

  OPENSSL_cleanse(in.get(), len + padding);

  bssl::ScopedEVP_CIPHER_CTX decrypt_ctx;
  if (!EVP_DecryptInit_ex(decrypt_ctx.get(), EVP_bf_cbc(), nullptr, bf_key,
                          bf_iv) ||
      !EVP_DecryptUpdate(decrypt_ctx.get(), in.get(), &out_bytes, out.get(),
                         len + padding) ||
      !EVP_DecryptFinal_ex(decrypt_ctx.get(), in.get() + out_bytes,
                           &final_bytes) ||
      (size_t)(out_bytes + final_bytes) != len ||
      OPENSSL_memcmp(in.get(), buf, len) != 0) {
    return 0;
  }

  return 1;
}

static int blowfish_cfb(const uint8_t *buf, size_t len) {
  if (len == 0) {
    return 1;
  }
  ossl_uint8_t_ptr in((uint8_t *)OPENSSL_zalloc(len), OPENSSL_free);
  ossl_uint8_t_ptr out((uint8_t *)OPENSSL_zalloc(len), OPENSSL_free);

  OPENSSL_memcpy(in.get(), buf, len);

  int out_bytes = 0, final_bytes = 0;

  bssl::ScopedEVP_CIPHER_CTX ctx;
  if (!EVP_EncryptInit_ex(ctx.get(), EVP_bf_cfb(), nullptr, bf_key, bf_iv) ||
      !EVP_EncryptUpdate(ctx.get(), out.get(), &out_bytes, in.get(), len) ||
      !EVP_EncryptFinal_ex(ctx.get(), out.get() + out_bytes, &final_bytes) ||
      (size_t)(out_bytes + final_bytes) != len ||
      OPENSSL_memcmp(in.get(), out.get(), len) == 0) {
    return 0;
  }

  OPENSSL_cleanse(in.get(), len);

  bssl::ScopedEVP_CIPHER_CTX decrypt_ctx;
  if (!EVP_DecryptInit_ex(decrypt_ctx.get(), EVP_bf_cfb(), nullptr, bf_key,
                          bf_iv) ||
      !EVP_DecryptUpdate(decrypt_ctx.get(), in.get(), &out_bytes, out.get(),
                         len) ||
      !EVP_DecryptFinal_ex(decrypt_ctx.get(), in.get() + out_bytes,
                           &final_bytes) ||
      (size_t)(out_bytes + final_bytes) != len ||
      OPENSSL_memcmp(in.get(), buf, len) != 0) {
    return 0;
  }

  return 1;
}

static int blowfish_ofb(const uint8_t *buf, size_t len) {
  if (len == 0) {
    return 1;
  }
  ossl_uint8_t_ptr in((uint8_t *)OPENSSL_zalloc(len), OPENSSL_free);
  ossl_uint8_t_ptr out((uint8_t *)OPENSSL_zalloc(len), OPENSSL_free);

  OPENSSL_memcpy(in.get(), buf, len);

  int out_bytes = 0, final_bytes = 0;

  bssl::ScopedEVP_CIPHER_CTX ctx;
  if (!EVP_EncryptInit_ex(ctx.get(), EVP_bf_ofb(), nullptr, bf_key, bf_iv) ||
      !EVP_EncryptUpdate(ctx.get(), out.get(), &out_bytes, in.get(), len) ||
      !EVP_EncryptFinal_ex(ctx.get(), out.get() + out_bytes, &final_bytes) ||
      (size_t)(out_bytes + final_bytes) != len ||
      OPENSSL_memcmp(in.get(), out.get(), len) == 0) {
    return 0;
  }

  OPENSSL_cleanse(in.get(), len);

  bssl::ScopedEVP_CIPHER_CTX decrypt_ctx;
  if (!EVP_DecryptInit_ex(decrypt_ctx.get(), EVP_bf_ofb(), nullptr, bf_key,
                          bf_iv) ||
      !EVP_DecryptUpdate(decrypt_ctx.get(), in.get(), &out_bytes, out.get(),
                         len) ||
      !EVP_DecryptFinal_ex(decrypt_ctx.get(), in.get() + out_bytes,
                           &final_bytes) ||
      (size_t)(out_bytes + final_bytes) != len ||
      OPENSSL_memcmp(in.get(), buf, len) != 0) {
    return 0;
  }

  return 1;
}
