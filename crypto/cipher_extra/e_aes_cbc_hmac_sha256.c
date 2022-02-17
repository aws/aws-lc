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


#include <openssl/evp.h>
#include <openssl/objects.h>
#include <openssl/aes.h>
#include <openssl/sha.h>
#include <openssl/rand.h>
#include "internal.h"
#include "../fipsmodule/aes/internal.h"

#if defined(AESNI_ASM)

typedef struct {
    AES_KEY ks;
    SHA256_CTX head, tail, md;
    size_t payload_length;      /* AAD length in decrypt case */
    union {
        unsigned int tls_ver;
        unsigned char tls_aad[16]; /* 13 used */
    } aux;
} EVP_AES_HMAC_SHA256;

# define NO_PAYLOAD_LENGTH       ((size_t)-1)

int aesni_cbc_sha256_enc(const void *inp, void *out, size_t blocks,
                         const AES_KEY *key, unsigned char iv[16],
                         SHA256_CTX *ctx, const void *in0);

# define data(ctx) ((EVP_AES_HMAC_SHA256 *)EVP_CIPHER_CTX_get_cipher_data(ctx))

static int aesni_cbc_hmac_sha256_init_key(EVP_CIPHER_CTX *ctx,
                                          const unsigned char *inkey,
                                          const unsigned char *iv, int enc)
{
    EVP_AES_HMAC_SHA256 *key = data(ctx);
    int ret;

    if (enc)
        ret = aes_hw_set_encrypt_key(inkey,
                                    EVP_CIPHER_CTX_key_length(ctx) * 8,
                                    &key->ks);
    else
        ret = aes_hw_set_decrypt_key(inkey,
                                    EVP_CIPHER_CTX_key_length(ctx) * 8,
                                    &key->ks);

    SHA256_Init(&key->head);    /* handy when benchmarking */
    key->tail = key->head;
    key->md = key->head;

    key->payload_length = NO_PAYLOAD_LENGTH;

    return ret < 0 ? 0 : 1;
}

void sha256_block_data_order(void *c, const void *p, size_t len);

static void sha256_update(SHA256_CTX *c, const void *data, size_t len)
{
    const unsigned char *ptr = data;
    size_t res;

    if ((res = c->num)) {
        res = SHA256_CBLOCK - res;
        if (len < res)
            res = len;
        SHA256_Update(c, ptr, res);
        ptr += res;
        len -= res;
    }

    res = len % SHA256_CBLOCK;
    len -= res;

    if (len) {
        sha256_block_data_order(c, ptr, len / SHA256_CBLOCK);

        ptr += len;
        c->Nh += len >> 29;
        c->Nl += len <<= 3;
        if (c->Nl < (unsigned int)len)
            c->Nh++;
    }

    if (res)
        SHA256_Update(c, ptr, res);
}

static int aesni_cbc_hmac_sha256_cipher(EVP_CIPHER_CTX *ctx,
                                        unsigned char *out,
                                        const unsigned char *in, size_t len)
{
    EVP_AES_HMAC_SHA256 *key = data(ctx);
    unsigned int l;
    size_t plen = key->payload_length, iv = 0, /* explicit IV in TLS 1.1 and
                                                * later */
        sha_off = 0;
    size_t aes_off = 0, blocks;

    sha_off = SHA256_CBLOCK - key->md.num;

    key->payload_length = NO_PAYLOAD_LENGTH;

    if (len % AES_BLOCK_SIZE)
        return 0;

    if (EVP_CIPHER_CTX_encrypting(ctx)) {
        if (plen == NO_PAYLOAD_LENGTH)
            plen = len;
        else if (len !=
                 ((plen + SHA256_DIGEST_LENGTH +
                   AES_BLOCK_SIZE) & -AES_BLOCK_SIZE))
            return 0;
        else if (key->aux.tls_ver >= TLS1_1_VERSION)
            iv = AES_BLOCK_SIZE;

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
            sha256_update(&key->md, in + iv, sha_off);

            (void)aesni_cbc_sha256_enc(in, out, blocks, &key->ks,
                                       EVP_CIPHER_CTX_iv_noconst(ctx),
                                       &key->md, in + iv + sha_off);
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
        sha256_update(&key->md, in + sha_off, plen - sha_off);

        if (plen != len) {      /* "TLS" mode of operation */
            if (in != out)
                memcpy(out + aes_off, in + aes_off, plen - aes_off);

            /* calculate HMAC and append it to payload */
            SHA256_Final(out + plen, &key->md);
            key->md = key->tail;
            sha256_update(&key->md, out + plen, SHA256_DIGEST_LENGTH);
            SHA256_Final(out + plen, &key->md);

            /* pad the payload|hmac */
            plen += SHA256_DIGEST_LENGTH;
            for (l = len - plen - 1; plen < len; plen++)
                out[plen] = l;
            /* encrypt HMAC|padding at once */
            aes_hw_cbc_encrypt(out + aes_off, out + aes_off, len - aes_off,
                              &key->ks, EVP_CIPHER_CTX_iv_noconst(ctx), 1);
        } else {
            aes_hw_cbc_encrypt(in + aes_off, out + aes_off, len - aes_off,
                              &key->ks, EVP_CIPHER_CTX_iv_noconst(ctx), 1);
        }
    } else {
        union {
            unsigned int u[SHA256_DIGEST_LENGTH / sizeof(unsigned int)];
            unsigned char c[64 + SHA256_DIGEST_LENGTH];
        } mac, *pmac;

        /* arrange cache line alignment */
        pmac = (void *)(((size_t)mac.c + 63) & ((size_t)0 - 64));

        /* decrypt HMAC|padding at once */
        aes_hw_cbc_encrypt(in, out, len, &key->ks,
                          EVP_CIPHER_CTX_iv_noconst(ctx), 0);

        if (plen != NO_PAYLOAD_LENGTH) { /* "TLS" mode of operation */
            size_t inp_len, mask, j, i;
            unsigned int res, maxpad, pad, bitlen;
            int ret = 1;
            union {
                unsigned int u[SHA_LBLOCK];
                unsigned char c[SHA256_CBLOCK];
            } *data = (void *)key->md.data;

            if ((key->aux.tls_aad[plen - 4] << 8 | key->aux.tls_aad[plen - 3])
                >= TLS1_1_VERSION)
                iv = AES_BLOCK_SIZE;

            if (len < (iv + SHA256_DIGEST_LENGTH + 1))
                return 0;

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
            sha256_update(&key->md, key->aux.tls_aad, plen);

# if 1      /* see original reference version in #else */
            len -= SHA256_DIGEST_LENGTH; /* amend mac */
            if (len >= (256 + SHA256_CBLOCK)) {
                j = (len - (256 + SHA256_CBLOCK)) & (0 - SHA256_CBLOCK);
                j += SHA256_CBLOCK - key->md.num;
                sha256_update(&key->md, out, j);
                out += j;
                len -= j;
                inp_len -= j;
            }

            /* but pretend as if we hashed padded payload */
            bitlen = key->md.Nl + (inp_len << 3); /* at most 18 bits */
#  ifdef BSWAP4
            bitlen = BSWAP4(bitlen);
#  else
            mac.c[0] = 0;
            mac.c[1] = (unsigned char)(bitlen >> 16);
            mac.c[2] = (unsigned char)(bitlen >> 8);
            mac.c[3] = (unsigned char)bitlen;
            bitlen = mac.u[0];
#  endif

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

                memset(data, 0, SHA256_CBLOCK);
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

#  ifdef BSWAP4
            pmac->u[0] = BSWAP4(pmac->u[0]);
            pmac->u[1] = BSWAP4(pmac->u[1]);
            pmac->u[2] = BSWAP4(pmac->u[2]);
            pmac->u[3] = BSWAP4(pmac->u[3]);
            pmac->u[4] = BSWAP4(pmac->u[4]);
            pmac->u[5] = BSWAP4(pmac->u[5]);
            pmac->u[6] = BSWAP4(pmac->u[6]);
            pmac->u[7] = BSWAP4(pmac->u[7]);
#  else
            for (i = 0; i < 8; i++) {
                res = pmac->u[i];
                pmac->c[4 * i + 0] = (unsigned char)(res >> 24);
                pmac->c[4 * i + 1] = (unsigned char)(res >> 16);
                pmac->c[4 * i + 2] = (unsigned char)(res >> 8);
                pmac->c[4 * i + 3] = (unsigned char)res;
            }
#  endif
            len += SHA256_DIGEST_LENGTH;
# else
            sha256_update(&key->md, out, inp_len);
            res = key->md.num;
            SHA256_Final(pmac->c, &key->md);

            {
                unsigned int inp_blocks, pad_blocks;

                /* but pretend as if we hashed padded payload */
                inp_blocks =
                    1 + ((SHA256_CBLOCK - 9 - res) >> (sizeof(res) * 8 - 1));
                res += (unsigned int)(len - inp_len);
                pad_blocks = res / SHA256_CBLOCK;
                res %= SHA256_CBLOCK;
                pad_blocks +=
                    1 + ((SHA256_CBLOCK - 9 - res) >> (sizeof(res) * 8 - 1));
                for (; inp_blocks < pad_blocks; inp_blocks++)
                    sha1_block_data_order(&key->md, data, 1);
            }
# endif      /* pre-lucky-13 reference version of above */
            key->md = key->tail;
            sha256_update(&key->md, pmac->c, SHA256_DIGEST_LENGTH);
            SHA256_Final(pmac->c, &key->md);

            /* verify HMAC */
            out += inp_len;
            len -= inp_len;
# if 1      /* see original reference version in #else */
            {
                unsigned char *p =
                    out + len - 1 - maxpad - SHA256_DIGEST_LENGTH;
                size_t off = out - p;
                unsigned int c, cmask;

                maxpad += SHA256_DIGEST_LENGTH;
                for (res = 0, i = 0, j = 0; j < maxpad; j++) {
                    c = p[j];
                    cmask =
                        ((int)(j - off - SHA256_DIGEST_LENGTH)) >>
                        (sizeof(int) * 8 - 1);
                    res |= (c ^ pad) & ~cmask; /* ... and padding */
                    cmask &= ((int)(off - 1 - j)) >> (sizeof(int) * 8 - 1);
                    res |= (c ^ pmac->c[i]) & cmask;
                    i += 1 & cmask;
                }
                maxpad -= SHA256_DIGEST_LENGTH;

                res = 0 - ((0 - res) >> (sizeof(res) * 8 - 1));
                ret &= (int)~res;
            }
# else      /* pre-lucky-13 reference version of above */
            for (res = 0, i = 0; i < SHA256_DIGEST_LENGTH; i++)
                res |= out[i] ^ pmac->c[i];
            res = 0 - ((0 - res) >> (sizeof(res) * 8 - 1));
            ret &= (int)~res;

            /* verify padding */
            pad = (pad & ~res) | (maxpad & res);
            out = out + len - 1 - pad;
            for (res = 0, i = 0; i < pad; i++)
                res |= out[i] ^ pad;

            res = (0 - res) >> (sizeof(res) * 8 - 1);
            ret &= (int)~res;
# endif
            return ret;
        } else {
            sha256_update(&key->md, out, len);
        }
    }

    return 1;
}

static int aesni_cbc_hmac_sha256_ctrl(EVP_CIPHER_CTX *ctx, int type, int arg,
                                      void *ptr)
{
    EVP_AES_HMAC_SHA256 *key = data(ctx);
    unsigned int u_arg = (unsigned int)arg;

    switch (type) {
    case EVP_CTRL_AEAD_SET_MAC_KEY:
        {
            unsigned int i;
            unsigned char hmac_key[64];

            memset(hmac_key, 0, sizeof(hmac_key));

            if (arg < 0)
                return -1;

            if (u_arg > sizeof(hmac_key)) {
                SHA256_Init(&key->head);
                sha256_update(&key->head, ptr, arg);
                SHA256_Final(hmac_key, &key->head);
            } else {
                memcpy(hmac_key, ptr, arg);
            }

            for (i = 0; i < sizeof(hmac_key); i++)
                hmac_key[i] ^= 0x36; /* ipad */
            SHA256_Init(&key->head);
            sha256_update(&key->head, hmac_key, sizeof(hmac_key));

            for (i = 0; i < sizeof(hmac_key); i++)
                hmac_key[i] ^= 0x36 ^ 0x5c; /* opad */
            SHA256_Init(&key->tail);
            sha256_update(&key->tail, hmac_key, sizeof(hmac_key));

            OPENSSL_cleanse(hmac_key, sizeof(hmac_key));

            return 1;
        }
    case EVP_CTRL_AEAD_TLS1_AAD:
        {
            unsigned char *p = ptr;
            unsigned int len;

            if (arg != EVP_AEAD_TLS1_AAD_LEN)
                return -1;

            len = p[arg - 2] << 8 | p[arg - 1];

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
                sha256_update(&key->md, p, arg);

                return (int)(((len + SHA256_DIGEST_LENGTH +
                               AES_BLOCK_SIZE) & -AES_BLOCK_SIZE)
                             - len);
            } else {
                memcpy(key->aux.tls_aad, ptr, arg);
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
    aesni_cbc_hmac_sha256_ctrl
};

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
    aesni_cbc_hmac_sha256_ctrl
};

const EVP_CIPHER *EVP_aes_128_cbc_hmac_sha256(void)
{
    return (hwaes_capable() &&
            aesni_cbc_sha256_enc(NULL, NULL, 0, NULL, NULL, NULL, NULL) ?
            &aesni_128_cbc_hmac_sha256_cipher : NULL);
}

const EVP_CIPHER *EVP_aes_256_cbc_hmac_sha256(void)
{
    return (hwaes_capable() &&
            aesni_cbc_sha256_enc(NULL, NULL, 0, NULL, NULL, NULL, NULL) ?
            &aesni_256_cbc_hmac_sha256_cipher : NULL);
}
#else
const EVP_CIPHER *EVP_aes_128_cbc_hmac_sha256(void)
{
    return NULL;
}

const EVP_CIPHER *EVP_aes_256_cbc_hmac_sha256(void)
{
    return NULL;
}
#endif  /* AESNI_ASM */
