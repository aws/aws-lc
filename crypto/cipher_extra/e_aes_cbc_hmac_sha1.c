/*
 * Copyright 2011-2016 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#include <openssl/opensslconf.h>

#include <stdio.h>
#include <string.h>

#include <openssl/evp.h>
// TODO: check circuit of include.
#include <openssl/cipher.h>
#include <openssl/err.h>
#include <openssl/objects.h>
#include <openssl/aes.h>
#include <openssl/sha.h>
#include <openssl/rand.h>
#include "internal.h"
#include "../fipsmodule/aes/internal.h"

#if defined(AESNI_ASM)

typedef struct {
    AES_KEY ks;
    SHA_CTX head, tail, md;
    size_t payload_length;      /* AAD length in decrypt case */
    union {
        unsigned int tls_ver;
        unsigned char tls_aad[16]; /* 13 used */
    } aux;
} EVP_AES_HMAC_SHA1;

#define NO_PAYLOAD_LENGTH       ((size_t)-1)

void aesni_cbc_sha1_enc(const void *inp, void *out, size_t blocks,
                        const AES_KEY *key, unsigned char iv[16],
                        SHA_CTX *ctx, const void *in0);

void aesni256_cbc_sha1_dec(const void *inp, void *out, size_t blocks,
                           const AES_KEY *key, unsigned char iv[16],
                           SHA_CTX *ctx, const void *in0);

# define data(ctx) ((EVP_AES_HMAC_SHA1 *)EVP_CIPHER_CTX_get_cipher_data(ctx))

static int aesni_cbc_hmac_sha1_init_key(EVP_CIPHER_CTX *ctx,
                                        const unsigned char *inkey,
                                        const unsigned char *iv, int enc)
{
    EVP_AES_HMAC_SHA1 *key = data(ctx);
    int ret;

    if (enc)
        ret = aes_hw_set_encrypt_key(inkey,
                                    EVP_CIPHER_CTX_key_length(ctx) * 8,
                                    &key->ks);
    else
        ret = aes_hw_set_decrypt_key(inkey,
                                    EVP_CIPHER_CTX_key_length(ctx) * 8,
                                    &key->ks);

    SHA1_Init(&key->head); /* handy when benchmarking */
    key->tail = key->head;
    key->md = key->head;

    key->payload_length = NO_PAYLOAD_LENGTH;

    return ret < 0 ? 0 : 1;
}

static void printa(const uint8_t *ticket_key, size_t len) {
//   printf("================================================ \n");
//   for (size_t i = 0; i < len; i++) {
//     printf("%02x", ticket_key[i]);
//   }
}

static void printd(const uint8_t *ticket_key, size_t len) {
//   printf("================================================ \n");
//   for (size_t i = 0; i < len; i++) {
//     printf("%02x", ticket_key[i]);
//   }
//   printf("\n");
}

void sha1_block_data_order(void *c, const void *p, size_t len);

static int aesni_cbc_hmac_sha1_cipher(EVP_CIPHER_CTX *ctx, unsigned char *out,
                                      const unsigned char *in, size_t len)
{
    EVP_AES_HMAC_SHA1 *key = data(ctx);
    size_t plen = key->payload_length, iv = 0, /* explicit IV in TLS 1.1 and
                                                * later */
        sha_off = 0;
    size_t aes_off = 0, blocks;

    sha_off = SHA_CBLOCK - key->md.num;

    key->payload_length = NO_PAYLOAD_LENGTH;

    if (len % AES_BLOCK_SIZE) {
        OPENSSL_PUT_ERROR(CIPHER, CIPHER_R_INVALID_1);
        return 0;
    }

    // TODO: check if the TLS operation should ensure the payload <= RECORD_MAX_SIZE?
    if (EVP_CIPHER_CTX_encrypting(ctx)) {
        if (plen == NO_PAYLOAD_LENGTH) {
            plen = len;
        } else if (len != ((plen + SHA_DIGEST_LENGTH + AES_BLOCK_SIZE) & -AES_BLOCK_SIZE)) {
            printf("aloha len %zu plen %zu\n", len, plen);
            // TODO[Addressed]: why the len should include plen + sha_digest_len + aes_block_size?
            // Looks like this is a API implicit constraint: the input len should have space of
            // iv + plaintext + digest + padding.
            OPENSSL_PUT_ERROR(CIPHER, CIPHER_R_UNSUPPORTED_INPUT_SIZE);
            return 0;
        } else if (key->aux.tls_ver >= TLS1_1_VERSION) {
            iv = AES_BLOCK_SIZE;
        }

        printf("aloha iv %zu sha_off %zu plen %zu\n", iv, sha_off, plen);

        if (plen > (sha_off + iv) && (blocks = (plen - (sha_off + iv)) / SHA_CBLOCK)) {
            SHA1_Update(&key->md, in + iv, sha_off);

            aesni_cbc_sha1_enc(in, out, blocks, &key->ks,
                               EVP_CIPHER_CTX_iv_noconst(ctx),
                               &key->md, in + iv + sha_off);
            blocks *= SHA_CBLOCK;
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
        SHA1_Update(&key->md, in + sha_off, plen - sha_off);

        if (plen != len) {      /* "TLS" mode of operation */
            if (in != out) {
                OPENSSL_memcpy(out + aes_off, in + aes_off, plen - aes_off);
            }

            /* calculate HMAC and append it to payload */
            SHA1_Final(out + plen, &key->md);
            key->md = key->tail;
            SHA1_Update(&key->md, out + plen, SHA_DIGEST_LENGTH);
            SHA1_Final(out + plen, &key->md);

            /* pad the payload|hmac */
            plen += SHA_DIGEST_LENGTH;
            for (unsigned int l = len - plen - 1; plen < len; plen++) {
                out[plen] = l;
            }
            // TODO(DONE): investigate if |len - aes_off| includes partial of payload.
            // In other words, if/why |aes_off| covers all bytes of payload.
            // if not, what ensures ONLY HMAC|padding is encrytped.
            // DONE: below does include some payload. This may not matter because aes is blocker cipher.
            /* encrypt HMAC|padding at once */
            printa(EVP_CIPHER_CTX_iv_noconst(ctx), 16);
            printa(out + aes_off, len - aes_off);
            aes_hw_cbc_encrypt(out + aes_off, out + aes_off, len - aes_off,
                              &key->ks, EVP_CIPHER_CTX_iv_noconst(ctx), 1);
            printa(EVP_CIPHER_CTX_iv_noconst(ctx), 16);
            printa(out + aes_off, len - aes_off);
        } else {
            aes_hw_cbc_encrypt(in + aes_off, out + aes_off, len - aes_off,
                              &key->ks, EVP_CIPHER_CTX_iv_noconst(ctx), 1);
        }
    } else {
        union {
            unsigned int u[SHA_DIGEST_LENGTH / sizeof(unsigned int)];
            unsigned char c[32 + SHA_DIGEST_LENGTH];
        } mac, *pmac;

        // TODO: 32 still makes sense today?
        /* arrange cache line alignment */
        pmac = (void *)(((size_t)mac.c + 31) & ((size_t)0 - 32));

        if (plen != NO_PAYLOAD_LENGTH) { /* "TLS" mode of operation */
            size_t inp_len, mask, j, i;
            unsigned int res, maxpad, pad, bitlen;
            int ret = 1;
            union {
                unsigned int u[SHA_LBLOCK];
                unsigned char c[SHA_CBLOCK];
            } *data = (void *)key->md.data;

            if ((key->aux.tls_aad[plen - 4] << 8 | key->aux.tls_aad[plen - 3])
                >= TLS1_1_VERSION) {
                // TODO: check input len >= RECORD_MAX_LENGTH + AES_BLOCK_SIZE + SHA_DIGEST_LENGTH + 256?
                if (len < (AES_BLOCK_SIZE + SHA_DIGEST_LENGTH + 1)) {
                    OPENSSL_PUT_ERROR(CIPHER, CIPHER_R_UNSUPPORTED_INPUT_SIZE);
                    return 0;
                }

                /* omit explicit iv */
                OPENSSL_memcpy(EVP_CIPHER_CTX_iv_noconst(ctx), in, AES_BLOCK_SIZE);

                in += AES_BLOCK_SIZE;
                out += AES_BLOCK_SIZE;
                len -= AES_BLOCK_SIZE;
            } else if (len < (SHA_DIGEST_LENGTH + 1)) {
                OPENSSL_PUT_ERROR(CIPHER, CIPHER_R_UNSUPPORTED_INPUT_SIZE);
                return 0;
            }
            // TODO: in decryption, use the encrypted iv?
            // TODO: continue: The encrypted iv is treated as normal block and decrypted with |ks|?
                /* decrypt HMAC|padding at once */
                aes_hw_cbc_encrypt(in, out, len, &key->ks,
                                  EVP_CIPHER_CTX_iv_noconst(ctx), 0);

            /* figure out payload length */
            pad = out[len - 1];
            // Below three lines of code is to get the min of maxpad.
            // maxpad = min(len - (SHA_DIGEST_LENGTH + 1), 255);
            maxpad = len - (SHA_DIGEST_LENGTH + 1);
            // TODO: 256 is the max padding length from RFC5652?
            // https://datatracker.ietf.org/doc/html/rfc5652
            // "This padding method is well defined if and only if k is less than 256."
            // TODO: what below two lines code are doing?
            maxpad |= (255 - maxpad) >> (sizeof(maxpad) * 8 - 8);
            maxpad &= 255;

            mask = constant_time_ge_8(maxpad, pad);
            ret &= mask;
            printf("ret is %d\n", ret);
            /*
             * If pad is invalid then we will fail the above test but we must
             * continue anyway because we are in constant time code. However,
             * we'll use the maxpad value instead of the supplied pad to make
             * sure we perform well defined pointer arithmetic.
             */
            pad = constant_time_select_8(mask, pad, maxpad);

            inp_len = len - (SHA_DIGEST_LENGTH + pad + 1);
            printf("aloha pad %u maxpad %u mask %zu inp_len %zu\n", pad, maxpad, mask, inp_len);

            printd(key->aux.tls_aad, 13);
            key->aux.tls_aad[plen - 2] = inp_len >> 8;
            key->aux.tls_aad[plen - 1] = inp_len;

            printd(key->aux.tls_aad, 13);

            /* calculate HMAC */
            key->md = key->head;
            SHA1_Update(&key->md, key->aux.tls_aad, plen);

            len -= SHA_DIGEST_LENGTH; /* amend mac */
            // TODO: why below if special case?
            if (len >= (256 + SHA_CBLOCK)) {
                j = (len - (256 + SHA_CBLOCK)) & (0 - SHA_CBLOCK);
                j += SHA_CBLOCK - key->md.num;
                SHA1_Update(&key->md, out, j);
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

            for (res = key->md.num, j = 0; j < len; j++) {
                // preprocess partial block https://en.wikipedia.org/wiki/SHA-1
                // When j is within the payload, out[j] is kept.
                // when j is out of the payload, out[j] is appended with 0x80 and 0 until the SHA_CBLOCK.
                // TODO: size_t here is quite confusing.
                size_t c = out[j];
                mask = (j - inp_len) >> (sizeof(j) * 8 - 8);
                c &= mask;
                c |= 0x80 & ~mask & ~((inp_len - j) >> (sizeof(j) * 8 - 8));
                data->c[res++] = (unsigned char)c;

                if (res != SHA_CBLOCK) {
                    continue;
                }

                /* j is not incremented yet */
                mask = 0 - ((inp_len + 7 - j) >> (sizeof(j) * 8 - 1));
                data->u[SHA_LBLOCK - 1] |= bitlen & mask;
                sha1_block_data_order(&key->md, data, 1);
                mask &= 0 - ((j - inp_len - 72) >> (sizeof(j) * 8 - 1));
                pmac->u[0] |= key->md.h[0] & mask;
                pmac->u[1] |= key->md.h[1] & mask;
                pmac->u[2] |= key->md.h[2] & mask;
                pmac->u[3] |= key->md.h[3] & mask;
                pmac->u[4] |= key->md.h[4] & mask;
                res = 0;
            }

            for (i = res; i < SHA_CBLOCK; i++, j++) {
                data->c[i] = 0;
            }

            printf("res %u bitlen %u j %zu\n", res, bitlen, j);

            if (res > SHA_CBLOCK - 8) {
                mask = 0 - ((inp_len + 8 - j) >> (sizeof(j) * 8 - 1));
                printf("mask %zu j %zu\n", mask, j);
                data->u[SHA_LBLOCK - 1] |= bitlen & mask;
                sha1_block_data_order(&key->md, data, 1);
                mask &= 0 - ((j - inp_len - 73) >> (sizeof(j) * 8 - 1));
                printf("mask2 %zu j %zu\n", mask, j);
                pmac->u[0] |= key->md.h[0] & mask;
                pmac->u[1] |= key->md.h[1] & mask;
                pmac->u[2] |= key->md.h[2] & mask;
                pmac->u[3] |= key->md.h[3] & mask;
                pmac->u[4] |= key->md.h[4] & mask;

                OPENSSL_memset(data, 0, SHA_CBLOCK);
                j += 64;
            }
            data->u[SHA_LBLOCK - 1] = bitlen;
            sha1_block_data_order(&key->md, data, 1);
            mask = 0 - ((j - inp_len - 73) >> (sizeof(j) * 8 - 1));
            printf("mask3 %zu j %zu\n", mask, j);
            pmac->u[0] |= key->md.h[0] & mask;
            pmac->u[1] |= key->md.h[1] & mask;
            pmac->u[2] |= key->md.h[2] & mask;
            pmac->u[3] |= key->md.h[3] & mask;
            pmac->u[4] |= key->md.h[4] & mask;

            pmac->u[0] = CRYPTO_bswap4(pmac->u[0]);
            pmac->u[1] = CRYPTO_bswap4(pmac->u[1]);
            pmac->u[2] = CRYPTO_bswap4(pmac->u[2]);
            pmac->u[3] = CRYPTO_bswap4(pmac->u[3]);
            pmac->u[4] = CRYPTO_bswap4(pmac->u[4]);
            len += SHA_DIGEST_LENGTH;
            key->md = key->tail;
            SHA1_Update(&key->md, pmac->c, SHA_DIGEST_LENGTH);
            SHA1_Final(pmac->c, &key->md);
            printd(pmac->c, 20);

            /* verify HMAC */
            out += inp_len;
            len -= inp_len;
            {
                unsigned char *p = out + len - 1 - maxpad - SHA_DIGEST_LENGTH;
                size_t off = out - p;
                printf("len %zu off %zu\n", len, off);
                unsigned int c, cmask;

                maxpad += SHA_DIGEST_LENGTH;
                for (res = 0, i = 0, j = 0; j < maxpad; j++) {
                    c = p[j];
                    cmask =
                        ((int)(j - off - SHA_DIGEST_LENGTH)) >> (sizeof(int) *
                                                                 8 - 1);
                    res |= (c ^ pad) & ~cmask; /* ... and padding */
                    cmask &= ((int)(off - 1 - j)) >> (sizeof(int) * 8 - 1);
                    res |= (c ^ pmac->c[i]) & cmask;
                    i += 1 & cmask;
                }
                maxpad -= SHA_DIGEST_LENGTH;

                res = 0 - ((0 - res) >> (sizeof(res) * 8 - 1));
                ret &= (int)~res;
            }
            return ret;
        } else {
                /* decrypt HMAC|padding at once */
                aes_hw_cbc_encrypt(in, out, len, &key->ks,
                                  EVP_CIPHER_CTX_iv_noconst(ctx), 0);

            // TODO: why this call at the end of decryption!?
            SHA1_Update(&key->md, out, len);
        }
    }

    return 1;
}

static int aesni_cbc_hmac_sha1_ctrl(EVP_CIPHER_CTX *ctx, int type, int arg,
                                    void *ptr)
{
    EVP_AES_HMAC_SHA1 *key = data(ctx);

    switch (type) {
    case EVP_CTRL_AEAD_SET_MAC_KEY:
        {
            unsigned int i;
            unsigned char hmac_key[64];

            OPENSSL_memset(hmac_key, 0, sizeof(hmac_key));

            if (arg > (int)sizeof(hmac_key)) {
                SHA1_Init(&key->head);
                SHA1_Update(&key->head, ptr, arg);
                SHA1_Final(hmac_key, &key->head);
            } else {
                OPENSSL_memcpy(hmac_key, ptr, arg);
            }

            for (i = 0; i < sizeof(hmac_key); i++) {
                hmac_key[i] ^= 0x36; /* ipad */
            }
            SHA1_Init(&key->head);
            SHA1_Update(&key->head, hmac_key, sizeof(hmac_key));

            for (i = 0; i < sizeof(hmac_key); i++) {
                hmac_key[i] ^= 0x36 ^ 0x5c; /* opad */
            }
            SHA1_Init(&key->tail);
            SHA1_Update(&key->tail, hmac_key, sizeof(hmac_key));

            OPENSSL_cleanse(hmac_key, sizeof(hmac_key));

            return 1;
        }
    case EVP_CTRL_AEAD_TLS1_AAD:
        {
            // p is 
            // additional_data = seq_num + content_type + protocol_version + payload_eiv_len
            // seq_num: 8 octets long.
            // content_type: 1 octets long.
            // protocol_version: 2 octets long.
            // payload_eiv_len: 2 octets long. eiv is explicit iv required by TLS 1.1+
            unsigned char *p = ptr;
            unsigned int len;

            if (arg != EVP_AEAD_TLS1_AAD_LEN)
                return -1;

            len = p[arg - 2] << 8 | p[arg - 1];
            // printf("aloha EVP_CTRL_AEAD_TLS1_AAD add\n");
            // printd(p, 13);

            if (EVP_CIPHER_CTX_encrypting(ctx)) {
                key->payload_length = len;
                if ((key->aux.tls_ver =
                     p[arg - 4] << 8 | p[arg - 3]) >= TLS1_1_VERSION) {
                    if (len < AES_BLOCK_SIZE)
                        return 0;
                    len -= AES_BLOCK_SIZE;
                    p[arg - 2] = len >> 8;
                    p[arg - 1] = len;
                }
                key->md = key->head;
                SHA1_Update(&key->md, p, arg);

                return (int)(((len + SHA_DIGEST_LENGTH +
                               AES_BLOCK_SIZE) & -AES_BLOCK_SIZE)
                             - len);
            } else {
                OPENSSL_memcpy(key->aux.tls_aad, ptr, arg);
                key->payload_length = arg;

                return SHA_DIGEST_LENGTH;
            }
        }
    default:
        return -1;
    }
}

static const EVP_CIPHER aesni_128_cbc_hmac_sha1_cipher = {
    NID_aes_128_cbc_hmac_sha1 /* nid */,
    AES_BLOCK_SIZE /* block size */, 
    16 /* key len */,
    AES_BLOCK_SIZE /* iv len */,
    sizeof(EVP_AES_HMAC_SHA1) /* ctx_size */,
    EVP_CIPH_CBC_MODE | EVP_CIPH_FLAG_AEAD_CIPHER /* flags */,
    NULL /* app_data */,
    aesni_cbc_hmac_sha1_init_key,
    aesni_cbc_hmac_sha1_cipher,
    NULL /* cleanup */,
    aesni_cbc_hmac_sha1_ctrl
};

static const EVP_CIPHER aesni_256_cbc_hmac_sha1_cipher = {
    NID_aes_256_cbc_hmac_sha1 /* nid */,
    AES_BLOCK_SIZE /* block size */,
    32 /* key len */,
    AES_BLOCK_SIZE /* iv len */,
    sizeof(EVP_AES_HMAC_SHA1) /* ctx_size */,
    EVP_CIPH_CBC_MODE | EVP_CIPH_FLAG_AEAD_CIPHER /* flags */,
    NULL /* app_data */,
    aesni_cbc_hmac_sha1_init_key,
    aesni_cbc_hmac_sha1_cipher,
    NULL,
    aesni_cbc_hmac_sha1_ctrl
};

const EVP_CIPHER *EVP_aes_128_cbc_hmac_sha1(void)
{
    return (hwaes_capable() ? &aesni_128_cbc_hmac_sha1_cipher : NULL);
}

const EVP_CIPHER *EVP_aes_256_cbc_hmac_sha1(void)
{
    return (hwaes_capable() ? &aesni_256_cbc_hmac_sha1_cipher : NULL);
}
#else
const EVP_CIPHER *EVP_aes_128_cbc_hmac_sha1(void)
{
    return NULL;
}

const EVP_CIPHER *EVP_aes_256_cbc_hmac_sha1(void)
{
    return NULL;
}
#endif
