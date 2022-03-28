/*
 * Copyright 2013-2016 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#include <openssl/opensslconf.h>

#include <stdio.h>
#include <string.h>


#include <openssl/aes.h>
#include <openssl/cipher.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/objects.h>
#include <openssl/rand.h>
#include <openssl/sha.h>
#include "../fipsmodule/aes/internal.h"
#include "internal.h"

#if defined(AES_CBC_HMAC_SHA_STITCH)

typedef struct {
  AES_KEY ks;
  // Used to compute(init, update and final) HMAC-SHA256.
  SHA256_CTX head, tail, md;
  // In encrypt case, it's eiv_len + plaintext_len. eiv is explicit iv(required
  // TLS 1.1+). In decrypt case, it's |EVP_AEAD_TLS1_AAD_LEN(13)|.
  size_t payload_length;
  union {
    unsigned int tls_ver;
    // In encrypt case, it's not set.
    // In decrypt case, it stores |additional_data|.
    // additional_data = seq_num + content_type + protocol_version +
    // payload_eiv_len seq_num: 8 octets long. content_type: 1 octets long.
    // protocol_version: 2 octets long.
    // payload_eiv_len: 2 octets long. eiv is explicit iv required by TLS 1.1+.
    unsigned char tls_aad[EVP_AEAD_TLS1_AAD_LEN];
  } aux;
} EVP_AES_HMAC_SHA256;

#define data(ctx) ((EVP_AES_HMAC_SHA256 *)EVP_CIPHER_CTX_get_cipher_data(ctx))

int aesni_cbc_sha256_enc(const void *inp, void *out, size_t blocks,
                         const AES_KEY *key, unsigned char iv[16],
                         SHA256_CTX *ctx, const void *in0);


static int aesni_cbc_hmac_sha256_init_key(EVP_CIPHER_CTX *ctx,
                                          const unsigned char *inkey,
                                          const unsigned char *iv, int enc) {
  EVP_AES_HMAC_SHA256 *key = data(ctx);
  int ret;

  int key_bits = EVP_CIPHER_CTX_key_length(ctx) * 8;
  if (enc) {
    ret = aes_hw_set_encrypt_key(inkey, key_bits, &key->ks);
  } else {
    ret = aes_hw_set_decrypt_key(inkey, key_bits, &key->ks);
  }

  SHA256_Init(&key->head);
  key->tail = key->head;
  key->md = key->head;

  key->payload_length = NO_PAYLOAD_LENGTH;

  return ret < 0 ? 0 : 1;
}

void sha256_block_data_order(void *c, const void *p, size_t len);

static int aesni_cbc_hmac_sha256_cipher(EVP_CIPHER_CTX *ctx, unsigned char *out,
                                        const unsigned char *in, size_t len) {
  EVP_AES_HMAC_SHA256 *key = data(ctx);
  unsigned int l;
  size_t plen = key->payload_length, iv = 0;
  size_t aes_off = 0, blocks;

  size_t sha_off = SHA256_CBLOCK - key->md.num;

  key->payload_length = NO_PAYLOAD_LENGTH;

  if (len % AES_BLOCK_SIZE) {
    OPENSSL_PUT_ERROR(CIPHER, CIPHER_R_DATA_NOT_MULTIPLE_OF_BLOCK_LENGTH);
    return 0;
  }

  if (EVP_CIPHER_CTX_encrypting(ctx)) {
    // NOTE: Difference between openssl and aws-lc:
    // In encrypt case, |plen| is set in the call |EVP_CIPHER_CTX_ctrl| with
    // |EVP_CTRL_AEAD_TLS1_AAD| operation.
    // When |plen == NO_PAYLOAD_LENGTH|, it means the call did not happen.
    // In this case, aws-lc returns error(0) but openssl supports that with
    // below explanation.
    // https://mta.openssl.org/pipermail/openssl-users/2019-November/011458.html
    // -- These stitched ciphers are specifically targeted at use by libssl
    //    and are designed for use in SSL/TLS only.
    if (plen == NO_PAYLOAD_LENGTH) {
      // |EVP_CIPHER_CTX_ctrl| with |EVP_CTRL_AEAD_TLS1_AAD| operation is not
      // performed.
      OPENSSL_PUT_ERROR(CIPHER, CIPHER_R_INVALID_OPERATION);
      return 0;
    }
    if (len !=
        ((plen + SHA256_DIGEST_LENGTH + AES_BLOCK_SIZE) & -AES_BLOCK_SIZE)) {
      OPENSSL_PUT_ERROR(CIPHER, CIPHER_R_UNSUPPORTED_INPUT_SIZE);
      return 0;
    } else if (key->aux.tls_ver >= TLS1_1_VERSION) {
      iv = AES_BLOCK_SIZE;
    }

    /*
     * Assembly stitch handles AVX-capable processors, but its
     * performance is not optimal on AMD Jaguar, ~40% worse, for
     * unknown reasons. Incidentally processor in question supports
     * AVX, but not AMD-specific XOP extension, which can be used
     * to identify it and avoid stitch invocation. So that after we
     * establish that current CPU supports AVX, we even see if it's
     * either even XOP-capable Bulldozer-based or GenuineIntel one.
     * But SHAEXT-capable go ahead...
     */
    if (((OPENSSL_ia32cap_P[2] & (1 << 29)) ||         /* SHAEXT? */
         ((OPENSSL_ia32cap_P[1] & (1 << (60 - 32))) && /* AVX? */
          ((OPENSSL_ia32cap_P[1] & (1 << (43 - 32)))   /* XOP? */
           | (OPENSSL_ia32cap_P[0] & (1 << 30))))) &&  /* "Intel CPU"? */
        plen > (sha_off + iv) &&
        (blocks = (plen - (sha_off + iv)) / SHA256_CBLOCK)) {
      SHA256_Update(&key->md, in + iv, sha_off);

      (void)aesni_cbc_sha256_enc(in, out, blocks, &key->ks,
                                 EVP_CIPHER_CTX_iv_noconst(ctx), &key->md,
                                 in + iv + sha_off);
      blocks *= SHA256_CBLOCK;
      aes_off += blocks;
      sha_off += blocks;
      key->md.Nh += blocks >> 29;
      key->md.Nl += blocks <<= 3;
      if (key->md.Nl < (unsigned int)blocks)
        key->md.Nh++;
    } else {
      sha_off = 0;
    }
    sha_off += iv;
    SHA256_Update(&key->md, in + sha_off, plen - sha_off);

    if (in != out)
      OPENSSL_memcpy(out + aes_off, in + aes_off, plen - aes_off);

    /* calculate HMAC and append it to payload */
    SHA256_Final(out + plen, &key->md);
    key->md = key->tail;
    SHA256_Update(&key->md, out + plen, SHA256_DIGEST_LENGTH);
    SHA256_Final(out + plen, &key->md);

    /* pad the payload|hmac */
    plen += SHA256_DIGEST_LENGTH;
    for (l = len - plen - 1; plen < len; plen++)
      out[plen] = l;
    /* encrypt HMAC|padding at once */
    aes_hw_cbc_encrypt(out + aes_off, out + aes_off, len - aes_off, &key->ks,
                       EVP_CIPHER_CTX_iv_noconst(ctx), 1);
  } else {
    if (plen != EVP_AEAD_TLS1_AAD_LEN) {
      // |EVP_CIPHER_CTX_ctrl| with |EVP_CTRL_AEAD_TLS1_AAD| operation is not
      // performed.
      OPENSSL_PUT_ERROR(CIPHER, CIPHER_R_INVALID_OPERATION);
      return 0;
    }
    union {
      unsigned int u[SHA256_DIGEST_LENGTH / sizeof(unsigned int)];
      unsigned char c[64 + SHA256_DIGEST_LENGTH];
    } mac, *pmac;

    /* arrange cache line alignment */
    pmac = align_pointer(mac.c, 64);

    /* decrypt HMAC|padding at once */
    aes_hw_cbc_encrypt(in, out, len, &key->ks, EVP_CIPHER_CTX_iv_noconst(ctx),
                       0);

    size_t inp_len, mask, j, i;
    unsigned int res, maxpad, pad, bitlen;
    int ret = 1;
    union {
      unsigned int u[SHA_LBLOCK];
      unsigned char c[SHA256_CBLOCK];
    } *data = (void *)key->md.data;

    if ((key->aux.tls_aad[plen - 4] << 8 | key->aux.tls_aad[plen - 3]) >=
        TLS1_1_VERSION)
      iv = AES_BLOCK_SIZE;

    if (len < (iv + SHA256_DIGEST_LENGTH + 1)) {
      OPENSSL_PUT_ERROR(CIPHER, CIPHER_R_UNSUPPORTED_INPUT_SIZE);
      return 0;
    }

    /* omit explicit iv */
    out += iv;
    len -= iv;

    /* figure out payload length */
    pad = out[len - 1];
    maxpad = len - (SHA256_DIGEST_LENGTH + 1);
    maxpad |= (255 - maxpad) >> (sizeof(maxpad) * 8 - 8);
    maxpad &= 255;

    mask = constant_time_ge_8(maxpad, pad);
    ret &= mask;
    /*
     * If pad is invalid then we will fail the above test but we must
     * continue anyway because we are in constant time code. However,
     * we'll use the maxpad value instead of the supplied pad to make
     * sure we perform well defined pointer arithmetic.
     */
    pad = constant_time_select_8(mask, pad, maxpad);

    inp_len = len - (SHA256_DIGEST_LENGTH + pad + 1);

    key->aux.tls_aad[plen - 2] = inp_len >> 8;
    key->aux.tls_aad[plen - 1] = inp_len;

    /* calculate HMAC */
    key->md = key->head;
    SHA256_Update(&key->md, key->aux.tls_aad, plen);

    len -= SHA256_DIGEST_LENGTH; /* amend mac */
    if (len >= (256 + SHA256_CBLOCK)) {
      j = (len - (256 + SHA256_CBLOCK)) & (0 - SHA256_CBLOCK);
      j += SHA256_CBLOCK - key->md.num;
      SHA256_Update(&key->md, out, j);
      out += j;
      len -= j;
      inp_len -= j;
    }

    /* but pretend as if we hashed padded payload */
    bitlen = key->md.Nl + (inp_len << 3); /* at most 18 bits */
    bitlen = CRYPTO_bswap4(bitlen);

    pmac->u[0] = 0;
    pmac->u[1] = 0;
    pmac->u[2] = 0;
    pmac->u[3] = 0;
    pmac->u[4] = 0;
    pmac->u[5] = 0;
    pmac->u[6] = 0;
    pmac->u[7] = 0;

    for (res = key->md.num, j = 0; j < len; j++) {
      size_t c = out[j];
      mask = (j - inp_len) >> (sizeof(j) * 8 - 8);
      c &= mask;
      c |= 0x80 & ~mask & ~((inp_len - j) >> (sizeof(j) * 8 - 8));
      data->c[res++] = (unsigned char)c;

      if (res != SHA256_CBLOCK)
        continue;

      /* j is not incremented yet */
      mask = 0 - ((inp_len + 7 - j) >> (sizeof(j) * 8 - 1));
      data->u[SHA_LBLOCK - 1] |= bitlen & mask;
      sha256_block_data_order(&key->md, data, 1);
      mask &= 0 - ((j - inp_len - 72) >> (sizeof(j) * 8 - 1));
      pmac->u[0] |= key->md.h[0] & mask;
      pmac->u[1] |= key->md.h[1] & mask;
      pmac->u[2] |= key->md.h[2] & mask;
      pmac->u[3] |= key->md.h[3] & mask;
      pmac->u[4] |= key->md.h[4] & mask;
      pmac->u[5] |= key->md.h[5] & mask;
      pmac->u[6] |= key->md.h[6] & mask;
      pmac->u[7] |= key->md.h[7] & mask;
      res = 0;
    }

    for (i = res; i < SHA256_CBLOCK; i++, j++)
      data->c[i] = 0;

    if (res > SHA256_CBLOCK - 8) {
      mask = 0 - ((inp_len + 8 - j) >> (sizeof(j) * 8 - 1));
      data->u[SHA_LBLOCK - 1] |= bitlen & mask;
      sha256_block_data_order(&key->md, data, 1);
      mask &= 0 - ((j - inp_len - 73) >> (sizeof(j) * 8 - 1));
      pmac->u[0] |= key->md.h[0] & mask;
      pmac->u[1] |= key->md.h[1] & mask;
      pmac->u[2] |= key->md.h[2] & mask;
      pmac->u[3] |= key->md.h[3] & mask;
      pmac->u[4] |= key->md.h[4] & mask;
      pmac->u[5] |= key->md.h[5] & mask;
      pmac->u[6] |= key->md.h[6] & mask;
      pmac->u[7] |= key->md.h[7] & mask;

      OPENSSL_memset(data, 0, SHA256_CBLOCK);
      j += 64;
    }
    data->u[SHA_LBLOCK - 1] = bitlen;
    sha256_block_data_order(&key->md, data, 1);
    mask = 0 - ((j - inp_len - 73) >> (sizeof(j) * 8 - 1));
    pmac->u[0] |= key->md.h[0] & mask;
    pmac->u[1] |= key->md.h[1] & mask;
    pmac->u[2] |= key->md.h[2] & mask;
    pmac->u[3] |= key->md.h[3] & mask;
    pmac->u[4] |= key->md.h[4] & mask;
    pmac->u[5] |= key->md.h[5] & mask;
    pmac->u[6] |= key->md.h[6] & mask;
    pmac->u[7] |= key->md.h[7] & mask;

    pmac->u[0] = CRYPTO_bswap4(pmac->u[0]);
    pmac->u[1] = CRYPTO_bswap4(pmac->u[1]);
    pmac->u[2] = CRYPTO_bswap4(pmac->u[2]);
    pmac->u[3] = CRYPTO_bswap4(pmac->u[3]);
    pmac->u[4] = CRYPTO_bswap4(pmac->u[4]);
    pmac->u[5] = CRYPTO_bswap4(pmac->u[5]);
    pmac->u[6] = CRYPTO_bswap4(pmac->u[6]);
    pmac->u[7] = CRYPTO_bswap4(pmac->u[7]);
    len += SHA256_DIGEST_LENGTH;
    key->md = key->tail;
    SHA256_Update(&key->md, pmac->c, SHA256_DIGEST_LENGTH);
    SHA256_Final(pmac->c, &key->md);

    /* verify HMAC */
    out += inp_len;
    len -= inp_len;
    {
      unsigned char *p = out + len - 1 - maxpad - SHA256_DIGEST_LENGTH;
      size_t off = out - p;
      unsigned int c, cmask;

      maxpad += SHA256_DIGEST_LENGTH;
      for (res = 0, i = 0, j = 0; j < maxpad; j++) {
        c = p[j];
        cmask =
            ((int)(j - off - SHA256_DIGEST_LENGTH)) >> (sizeof(int) * 8 - 1);
        res |= (c ^ pad) & ~cmask; /* ... and padding */
        cmask &= ((int)(off - 1 - j)) >> (sizeof(int) * 8 - 1);
        res |= (c ^ pmac->c[i]) & cmask;
        i += 1 & cmask;
      }
      maxpad -= SHA256_DIGEST_LENGTH;

      res = 0 - ((0 - res) >> (sizeof(res) * 8 - 1));
      ret &= (int)~res;
    }
    return ret;
  }

  return 1;
}

static int aesni_cbc_hmac_sha256_ctrl(EVP_CIPHER_CTX *ctx, int type, int arg,
                                      void *ptr) {
  EVP_AES_HMAC_SHA256 *key = data(ctx);
  unsigned int u_arg = (unsigned int)arg;

  switch (type) {
    case EVP_CTRL_AEAD_SET_MAC_KEY: {
      unsigned int i;
      unsigned char hmac_key[64];

      OPENSSL_memset(hmac_key, 0, sizeof(hmac_key));

      if (arg < 0)
        return -1;

      if (u_arg > sizeof(hmac_key)) {
        SHA256_Init(&key->head);
        SHA256_Update(&key->head, ptr, arg);
        SHA256_Final(hmac_key, &key->head);
      } else {
        OPENSSL_memcpy(hmac_key, ptr, arg);
      }

      for (i = 0; i < sizeof(hmac_key); i++)
        hmac_key[i] ^= 0x36; /* ipad */
      SHA256_Init(&key->head);
      SHA256_Update(&key->head, hmac_key, sizeof(hmac_key));

      for (i = 0; i < sizeof(hmac_key); i++)
        hmac_key[i] ^= 0x36 ^ 0x5c; /* opad */
      SHA256_Init(&key->tail);
      SHA256_Update(&key->tail, hmac_key, sizeof(hmac_key));

      OPENSSL_cleanse(hmac_key, sizeof(hmac_key));

      return 1;
    }
    case EVP_CTRL_AEAD_TLS1_AAD: {
      unsigned char *p = ptr;
      unsigned int len;

      if (arg != EVP_AEAD_TLS1_AAD_LEN)
        return -1;

      len = p[arg - 2] << 8 | p[arg - 1];

      if (EVP_CIPHER_CTX_encrypting(ctx)) {
        key->payload_length = len;
        if ((key->aux.tls_ver = p[arg - 4] << 8 | p[arg - 3]) >=
            TLS1_1_VERSION) {
          if (len < AES_BLOCK_SIZE)
            return 0;
          len -= AES_BLOCK_SIZE;
          p[arg - 2] = len >> 8;
          p[arg - 1] = len;
        }
        key->md = key->head;
        SHA256_Update(&key->md, p, arg);

        return (int)(((len + SHA256_DIGEST_LENGTH + AES_BLOCK_SIZE) &
                      -AES_BLOCK_SIZE) -
                     len);
      } else {
        OPENSSL_memcpy(key->aux.tls_aad, ptr, arg);
        key->payload_length = arg;

        return SHA256_DIGEST_LENGTH;
      }
    }
    default:
      return -1;
  }
}

static const EVP_CIPHER aesni_128_cbc_hmac_sha256_cipher = {
    NID_aes_128_cbc_hmac_sha256 /* nid */,
    AES_BLOCK_SIZE /* block size */,
    16 /* key len */,
    AES_BLOCK_SIZE /* iv len */,
    sizeof(EVP_AES_HMAC_SHA256) /* ctx_size */,
    EVP_CIPH_CBC_MODE | EVP_CIPH_FLAG_AEAD_CIPHER /* flags */,
    NULL /* app_data */,
    aesni_cbc_hmac_sha256_init_key,
    aesni_cbc_hmac_sha256_cipher,
    NULL /* cleanup */,
    aesni_cbc_hmac_sha256_ctrl};

static const EVP_CIPHER aesni_256_cbc_hmac_sha256_cipher = {
    NID_aes_256_cbc_hmac_sha256 /* nid */,
    AES_BLOCK_SIZE /* block size */,
    32 /* key len */,
    AES_BLOCK_SIZE /* iv len */,
    sizeof(EVP_AES_HMAC_SHA256) /* ctx_size */,
    EVP_CIPH_CBC_MODE | EVP_CIPH_FLAG_AEAD_CIPHER /* flags */,
    NULL /* app_data */,
    aesni_cbc_hmac_sha256_init_key,
    aesni_cbc_hmac_sha256_cipher,
    NULL /* cleanup */,
    aesni_cbc_hmac_sha256_ctrl};

const EVP_CIPHER *EVP_aes_128_cbc_hmac_sha256(void) {
  return (hwaes_capable() &&
                  aesni_cbc_sha256_enc(NULL, NULL, 0, NULL, NULL, NULL, NULL)
              ? &aesni_128_cbc_hmac_sha256_cipher
              : NULL);
}

const EVP_CIPHER *EVP_aes_256_cbc_hmac_sha256(void) {
  return (hwaes_capable() &&
                  aesni_cbc_sha256_enc(NULL, NULL, 0, NULL, NULL, NULL, NULL)
              ? &aesni_256_cbc_hmac_sha256_cipher
              : NULL);
}
#else
const EVP_CIPHER *EVP_aes_128_cbc_hmac_sha256(void) { return NULL; }

const EVP_CIPHER *EVP_aes_256_cbc_hmac_sha256(void) { return NULL; }
#endif /* AES_CBC_HMAC_SHA_STITCH */
