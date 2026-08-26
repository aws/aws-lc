// Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com) All rights reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/x509.h>

#include <limits.h>

#include <openssl/asn1.h>
#include <openssl/bytestring.h>
#include <openssl/digest.h>
#include <openssl/dsa.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/rsa.h>
#include <openssl/stack.h>

#include "../asn1/internal.h"
#include "../ocsp/internal.h"
#include "internal.h"


static int x509_view_range(const X509 *x509, AWSLC_X509_DER_RANGE range,
                           const uint8_t **out_data, size_t *out_len) {
  const size_t buffer_len = CRYPTO_BUFFER_len(x509->buf);
  if (range.offset > buffer_len || range.length > buffer_len - range.offset) {
    OPENSSL_PUT_ERROR(X509, ERR_R_INTERNAL_ERROR);
    return 0;
  }
  *out_data = CRYPTO_BUFFER_data(x509->buf) + range.offset;
  *out_len = range.length;
  return 1;
}

static int x509_verify_view_signature(const X509_ALGOR *sigalg,
                                      const uint8_t *signature,
                                      size_t signature_len, const uint8_t *data,
                                      size_t data_len, EVP_PKEY *pkey) {
  if (pkey == NULL) {
    OPENSSL_PUT_ERROR(X509, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  }

  EVP_MD_CTX ctx;
  EVP_MD_CTX_init(&ctx);
  int ret = 0;
  if (x509_digest_verify_init(&ctx, sigalg, pkey) &&
      EVP_DigestVerify(&ctx, signature, signature_len, data, data_len)) {
    ret = 1;
  } else if (ctx.pctx != NULL) {
    OPENSSL_PUT_ERROR(X509, ERR_R_EVP_LIB);
  }
  EVP_MD_CTX_cleanup(&ctx);
  return ret;
}

static int x509_verify_view(X509 *x509, EVP_PKEY *pkey, int *out_handled) {
  *out_handled = 0;
  if (x509 == NULL || x509->buf == NULL) {
    return 0;
  }

  const uint8_t *tbs_data = NULL, *tbs_alg_data = NULL, *signature_data = NULL;
  size_t tbs_len = 0, tbs_alg_len = 0, signature_len = 0;
  CRYPTO_MUTEX_lock_read(&x509->lock);
  if (x509->view_state == X509_VIEW_STATE_EAGER) {
    CRYPTO_MUTEX_unlock_read(&x509->lock);
    return 0;
  }
  *out_handled = 1;
  if (!x509_view_range(x509, x509->view.tbs_certificate, &tbs_data, &tbs_len) ||
      !x509_view_range(x509, x509->view.tbs_signature_algorithm, &tbs_alg_data,
                       &tbs_alg_len) ||
      !x509_view_range(x509, x509->view.signature, &signature_data,
                       &signature_len)) {
    CRYPTO_MUTEX_unlock_read(&x509->lock);
    return 0;
  }
  CRYPTO_MUTEX_unlock_read(&x509->lock);

  if (tbs_alg_len > LONG_MAX) {
    OPENSSL_PUT_ERROR(X509, ERR_R_OVERFLOW);
    return 0;
  }
  const uint8_t *tbs_alg_cursor = tbs_alg_data;
  X509_ALGOR *tbs_alg =
      d2i_X509_ALGOR(NULL, &tbs_alg_cursor, (long)tbs_alg_len);
  X509_ALGOR *outer_alg = x509_get_cached_signature_algorithm(x509);
  if (tbs_alg == NULL || outer_alg == NULL ||
      tbs_alg_cursor != tbs_alg_data + tbs_alg_len) {
    // These are allocation failures or an internal inconsistency rather than a
    // verdict on the signature, so defer to the legacy path instead of
    // reporting failure.
    X509_ALGOR_free(tbs_alg);
    *out_handled = 0;
    return 0;
  }
  const int algorithms_match = X509_ALGOR_cmp(outer_alg, tbs_alg) == 0;
  X509_ALGOR_free(tbs_alg);
  if (!algorithms_match) {
    OPENSSL_PUT_ERROR(X509, X509_R_SIGNATURE_ALGORITHM_MISMATCH);
    return 0;
  }

  CBS encoded_signature, signature;
  CBS_init(&encoded_signature, signature_data, signature_len);
  uint8_t padding_bits = 0;
  if (!CBS_get_asn1(&encoded_signature, &signature, CBS_ASN1_BITSTRING) ||
      CBS_len(&encoded_signature) != 0 ||
      !CBS_get_u8(&signature, &padding_bits)) {
    OPENSSL_PUT_ERROR(X509, X509_R_INVALID_BIT_STRING_BITS_LEFT);
    return 0;
  }
  if (padding_bits != 0) {
    // ASN1_item_verify historically ignores unused signature bits. Preserve
    // that behavior for unusual certificates by using the legacy path.
    *out_handled = 0;
    return 0;
  }

  return x509_verify_view_signature(outer_alg, CBS_data(&signature),
                                    CBS_len(&signature), tbs_data, tbs_len,
                                    pkey);
}

int X509_verify(X509 *x509, EVP_PKEY *pkey) {
  int handled = 0;
  const int view_result = x509_verify_view(x509, pkey, &handled);
  if (handled) {
    return view_result;
  }
  if (!x509_ensure_legacy(x509)) {
    return 0;
  }
  if (X509_ALGOR_cmp(x509->sig_alg, x509->cert_info->signature)) {
    OPENSSL_PUT_ERROR(X509, X509_R_SIGNATURE_ALGORITHM_MISMATCH);
    return 0;
  }
  return ASN1_item_verify(ASN1_ITEM_rptr(X509_CINF), x509->sig_alg,
                          x509->signature, x509->cert_info, pkey);
}

int X509_REQ_verify(X509_REQ *req, EVP_PKEY *pkey) {
  return ASN1_item_verify(ASN1_ITEM_rptr(X509_REQ_INFO), req->sig_alg,
                          req->signature, req->req_info, pkey);
}

int X509_sign(X509 *x, EVP_PKEY *pkey, const EVP_MD *md) {
  if (!x509_ensure_legacy(x)) {
    return 0;
  }
  asn1_encoding_clear(&x->cert_info->enc);
  return (ASN1_item_sign(ASN1_ITEM_rptr(X509_CINF), x->cert_info->signature,
                         x->sig_alg, x->signature, x->cert_info, pkey, md));
}

int X509_sign_ctx(X509 *x, EVP_MD_CTX *ctx) {
  if (!x509_ensure_legacy(x)) {
    return 0;
  }
  asn1_encoding_clear(&x->cert_info->enc);
  return ASN1_item_sign_ctx(ASN1_ITEM_rptr(X509_CINF), x->cert_info->signature,
                            x->sig_alg, x->signature, x->cert_info, ctx);
}

int X509_REQ_sign(X509_REQ *x, EVP_PKEY *pkey, const EVP_MD *md) {
  asn1_encoding_clear(&x->req_info->enc);
  return (ASN1_item_sign(ASN1_ITEM_rptr(X509_REQ_INFO), x->sig_alg, NULL,
                         x->signature, x->req_info, pkey, md));
}

int X509_REQ_sign_ctx(X509_REQ *x, EVP_MD_CTX *ctx) {
  asn1_encoding_clear(&x->req_info->enc);
  return ASN1_item_sign_ctx(ASN1_ITEM_rptr(X509_REQ_INFO), x->sig_alg, NULL,
                            x->signature, x->req_info, ctx);
}

int X509_CRL_sign(X509_CRL *x, EVP_PKEY *pkey, const EVP_MD *md) {
  asn1_encoding_clear(&x->crl->enc);
  return (ASN1_item_sign(ASN1_ITEM_rptr(X509_CRL_INFO), x->crl->sig_alg,
                         x->sig_alg, x->signature, x->crl, pkey, md));
}

int X509_CRL_sign_ctx(X509_CRL *x, EVP_MD_CTX *ctx) {
  asn1_encoding_clear(&x->crl->enc);
  return ASN1_item_sign_ctx(ASN1_ITEM_rptr(X509_CRL_INFO), x->crl->sig_alg,
                            x->sig_alg, x->signature, x->crl, ctx);
}

int X509_CRL_http_nbio(OCSP_REQ_CTX *rctx, X509_CRL **pcrl) {
  return OCSP_REQ_CTX_nbio_d2i(rctx, (ASN1_VALUE **)pcrl,
                               ASN1_ITEM_rptr(X509_CRL));
}

int NETSCAPE_SPKI_sign(NETSCAPE_SPKI *x, EVP_PKEY *pkey, const EVP_MD *md) {
  return (ASN1_item_sign(ASN1_ITEM_rptr(NETSCAPE_SPKAC), x->sig_algor, NULL,
                         x->signature, x->spkac, pkey, md));
}

int NETSCAPE_SPKI_verify(NETSCAPE_SPKI *spki, EVP_PKEY *pkey) {
  return (ASN1_item_verify(ASN1_ITEM_rptr(NETSCAPE_SPKAC), spki->sig_algor,
                           spki->signature, spki->spkac, pkey));
}

X509 *d2i_X509_fp(FILE *fp, X509 **x509) {
  return ASN1_item_d2i_fp(ASN1_ITEM_rptr(X509), fp, x509);
}

static int i2d_x509_void(const void *x509, unsigned char **out) {
  return i2d_X509((X509 *)x509, out);
}

int i2d_X509_fp(FILE *fp, X509 *x509) {
  BIO *bio = BIO_new_fp(fp, BIO_NOCLOSE);
  if (bio == NULL) {
    OPENSSL_PUT_ERROR(ASN1, ERR_R_BUF_LIB);
    return 0;
  }
  const int ret = ASN1_i2d_bio(i2d_x509_void, bio, x509);
  BIO_free(bio);
  return ret;
}

X509 *d2i_X509_bio(BIO *bp, X509 **x509) {
  return ASN1_item_d2i_bio(ASN1_ITEM_rptr(X509), bp, x509);
}

int i2d_X509_bio(BIO *bp, X509 *x509) {
  return ASN1_i2d_bio(i2d_x509_void, bp, x509);
}

X509_CRL *d2i_X509_CRL_fp(FILE *fp, X509_CRL **crl) {
  return ASN1_item_d2i_fp(ASN1_ITEM_rptr(X509_CRL), fp, crl);
}

int i2d_X509_CRL_fp(FILE *fp, X509_CRL *crl) {
  return ASN1_item_i2d_fp(ASN1_ITEM_rptr(X509_CRL), fp, crl);
}

X509_CRL *d2i_X509_CRL_bio(BIO *bp, X509_CRL **crl) {
  return ASN1_item_d2i_bio(ASN1_ITEM_rptr(X509_CRL), bp, crl);
}

int i2d_X509_CRL_bio(BIO *bp, X509_CRL *crl) {
  return ASN1_item_i2d_bio(ASN1_ITEM_rptr(X509_CRL), bp, crl);
}

X509_REQ *d2i_X509_REQ_fp(FILE *fp, X509_REQ **req) {
  return ASN1_item_d2i_fp(ASN1_ITEM_rptr(X509_REQ), fp, req);
}

int i2d_X509_REQ_fp(FILE *fp, X509_REQ *req) {
  return ASN1_item_i2d_fp(ASN1_ITEM_rptr(X509_REQ), fp, req);
}

X509_REQ *d2i_X509_REQ_bio(BIO *bp, X509_REQ **req) {
  return ASN1_item_d2i_bio(ASN1_ITEM_rptr(X509_REQ), bp, req);
}

int i2d_X509_REQ_bio(BIO *bp, X509_REQ *req) {
  return ASN1_item_i2d_bio(ASN1_ITEM_rptr(X509_REQ), bp, req);
}


#define IMPLEMENT_D2I_FP(type, name, bio_func) \
  type *name(FILE *fp, type **obj) {           \
    BIO *bio = BIO_new_fp(fp, BIO_NOCLOSE);    \
    if (bio == NULL) {                         \
      return NULL;                             \
    }                                          \
    type *ret = bio_func(bio, obj);            \
    BIO_free(bio);                             \
    return ret;                                \
  }

#define IMPLEMENT_I2D_FP(type, name, bio_func) \
  int name(FILE *fp, type *obj) {              \
    BIO *bio = BIO_new_fp(fp, BIO_NOCLOSE);    \
    if (bio == NULL) {                         \
      return 0;                                \
    }                                          \
    int ret = bio_func(bio, obj);              \
    BIO_free(bio);                             \
    return ret;                                \
  }

IMPLEMENT_D2I_FP(RSA, d2i_RSAPrivateKey_fp, d2i_RSAPrivateKey_bio)
IMPLEMENT_I2D_FP(RSA, i2d_RSAPrivateKey_fp, i2d_RSAPrivateKey_bio)

IMPLEMENT_D2I_FP(RSA, d2i_RSAPublicKey_fp, d2i_RSAPublicKey_bio)
IMPLEMENT_I2D_FP(RSA, i2d_RSAPublicKey_fp, i2d_RSAPublicKey_bio)

IMPLEMENT_D2I_FP(RSA, d2i_RSA_PUBKEY_fp, d2i_RSA_PUBKEY_bio)
IMPLEMENT_I2D_FP(RSA, i2d_RSA_PUBKEY_fp, i2d_RSA_PUBKEY_bio)

#define IMPLEMENT_D2I_BIO(type, name, d2i_func)         \
  type *name(BIO *bio, type **obj) {                    \
    uint8_t *data;                                      \
    size_t len;                                         \
    if (!BIO_read_asn1(bio, &data, &len, 100 * 1024)) { \
      return NULL;                                      \
    }                                                   \
    const uint8_t *ptr = data;                          \
    type *ret = d2i_func(obj, &ptr, (long)len);         \
    OPENSSL_free(data);                                 \
    return ret;                                         \
  }

#define IMPLEMENT_I2D_BIO(type, name, i2d_func) \
  int name(BIO *bio, type *obj) {               \
    uint8_t *data = NULL;                       \
    int len = i2d_func(obj, &data);             \
    if (len < 0) {                              \
      return 0;                                 \
    }                                           \
    int ret = BIO_write_all(bio, data, len);    \
    OPENSSL_free(data);                         \
    return ret;                                 \
  }

IMPLEMENT_D2I_BIO(RSA, d2i_RSAPrivateKey_bio, d2i_RSAPrivateKey)
IMPLEMENT_I2D_BIO(RSA, i2d_RSAPrivateKey_bio, i2d_RSAPrivateKey)

IMPLEMENT_D2I_BIO(RSA, d2i_RSAPublicKey_bio, d2i_RSAPublicKey)
IMPLEMENT_I2D_BIO(RSA, i2d_RSAPublicKey_bio, i2d_RSAPublicKey)

IMPLEMENT_D2I_BIO(RSA, d2i_RSA_PUBKEY_bio, d2i_RSA_PUBKEY)
IMPLEMENT_I2D_BIO(RSA, i2d_RSA_PUBKEY_bio, i2d_RSA_PUBKEY)

IMPLEMENT_D2I_FP(DSA, d2i_DSAPrivateKey_fp, d2i_DSAPrivateKey_bio)
IMPLEMENT_I2D_FP(DSA, i2d_DSAPrivateKey_fp, i2d_DSAPrivateKey_bio)

IMPLEMENT_D2I_FP(DSA, d2i_DSA_PUBKEY_fp, d2i_DSA_PUBKEY_bio)
IMPLEMENT_I2D_FP(DSA, i2d_DSA_PUBKEY_fp, i2d_DSA_PUBKEY_bio)

IMPLEMENT_D2I_BIO(DSA, d2i_DSAPrivateKey_bio, d2i_DSAPrivateKey)
IMPLEMENT_I2D_BIO(DSA, i2d_DSAPrivateKey_bio, i2d_DSAPrivateKey)

IMPLEMENT_D2I_BIO(DSA, d2i_DSA_PUBKEY_bio, d2i_DSA_PUBKEY)
IMPLEMENT_I2D_BIO(DSA, i2d_DSA_PUBKEY_bio, i2d_DSA_PUBKEY)

IMPLEMENT_D2I_FP(EC_KEY, d2i_ECPrivateKey_fp, d2i_ECPrivateKey_bio)
IMPLEMENT_I2D_FP(EC_KEY, i2d_ECPrivateKey_fp, i2d_ECPrivateKey_bio)

IMPLEMENT_D2I_FP(EC_KEY, d2i_EC_PUBKEY_fp, d2i_EC_PUBKEY_bio)
IMPLEMENT_I2D_FP(EC_KEY, i2d_EC_PUBKEY_fp, i2d_EC_PUBKEY_bio)

IMPLEMENT_D2I_BIO(EC_KEY, d2i_ECPrivateKey_bio, d2i_ECPrivateKey)
IMPLEMENT_I2D_BIO(EC_KEY, i2d_ECPrivateKey_bio, i2d_ECPrivateKey)

IMPLEMENT_D2I_BIO(EC_KEY, d2i_EC_PUBKEY_bio, d2i_EC_PUBKEY)
IMPLEMENT_I2D_BIO(EC_KEY, i2d_EC_PUBKEY_bio, i2d_EC_PUBKEY)

int X509_pubkey_digest(const X509 *data, const EVP_MD *type, unsigned char *md,
                       unsigned int *len) {
  ASN1_BIT_STRING *key;
  key = X509_get0_pubkey_bitstr(data);
  if (!key) {
    return 0;
  }
  return EVP_Digest(key->data, key->length, md, len, type, NULL);
}

int X509_digest(const X509 *data, const EVP_MD *type, unsigned char *md,
                unsigned int *len) {
  if (data != NULL && data->buf != NULL) {
    CRYPTO_MUTEX_lock_read((CRYPTO_MUTEX *)&data->lock);
    if (data->view_state == X509_VIEW_STATE_PARSED) {
      const uint8_t *encoded = NULL;
      size_t encoded_len = 0;
      const int ret = x509_view_range(data, data->view.certificate, &encoded,
                                      &encoded_len) &&
                      EVP_Digest(encoded, encoded_len, md, len, type, NULL);
      CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&data->lock);
      return ret;
    }
    CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&data->lock);
  }
  return (ASN1_item_digest(ASN1_ITEM_rptr(X509), type, (char *)data, md, len));
}

int X509_CRL_digest(const X509_CRL *data, const EVP_MD *type, unsigned char *md,
                    unsigned int *len) {
  return (
      ASN1_item_digest(ASN1_ITEM_rptr(X509_CRL), type, (char *)data, md, len));
}

int X509_REQ_digest(const X509_REQ *data, const EVP_MD *type, unsigned char *md,
                    unsigned int *len) {
  return (
      ASN1_item_digest(ASN1_ITEM_rptr(X509_REQ), type, (char *)data, md, len));
}

int X509_NAME_digest(const X509_NAME *data, const EVP_MD *type,
                     unsigned char *md, unsigned int *len) {
  return (
      ASN1_item_digest(ASN1_ITEM_rptr(X509_NAME), type, (char *)data, md, len));
}

IMPLEMENT_D2I_FP(X509_SIG, d2i_PKCS8_fp, d2i_PKCS8_bio)
IMPLEMENT_I2D_FP(X509_SIG, i2d_PKCS8_fp, i2d_PKCS8_bio)

IMPLEMENT_D2I_BIO(X509_SIG, d2i_PKCS8_bio, d2i_X509_SIG)
IMPLEMENT_I2D_BIO(X509_SIG, i2d_PKCS8_bio, i2d_X509_SIG)

IMPLEMENT_D2I_FP(PKCS8_PRIV_KEY_INFO, d2i_PKCS8_PRIV_KEY_INFO_fp,
                 d2i_PKCS8_PRIV_KEY_INFO_bio)
IMPLEMENT_I2D_FP(PKCS8_PRIV_KEY_INFO, i2d_PKCS8_PRIV_KEY_INFO_fp,
                 i2d_PKCS8_PRIV_KEY_INFO_bio)

int i2d_PKCS8PrivateKeyInfo_fp(FILE *fp, EVP_PKEY *key) {
  PKCS8_PRIV_KEY_INFO *p8inf;
  int ret;
  p8inf = EVP_PKEY2PKCS8(key);
  if (!p8inf) {
    return 0;
  }
  ret = i2d_PKCS8_PRIV_KEY_INFO_fp(fp, p8inf);
  PKCS8_PRIV_KEY_INFO_free(p8inf);
  return ret;
}

IMPLEMENT_D2I_FP(EVP_PKEY, d2i_PrivateKey_fp, d2i_PrivateKey_bio)
IMPLEMENT_I2D_FP(EVP_PKEY, i2d_PrivateKey_fp, i2d_PrivateKey_bio)

IMPLEMENT_D2I_FP(EVP_PKEY, d2i_PUBKEY_fp, d2i_PUBKEY_bio)
IMPLEMENT_I2D_FP(EVP_PKEY, i2d_PUBKEY_fp, i2d_PUBKEY_bio)

IMPLEMENT_D2I_BIO(PKCS8_PRIV_KEY_INFO, d2i_PKCS8_PRIV_KEY_INFO_bio,
                  d2i_PKCS8_PRIV_KEY_INFO)
IMPLEMENT_I2D_BIO(PKCS8_PRIV_KEY_INFO, i2d_PKCS8_PRIV_KEY_INFO_bio,
                  i2d_PKCS8_PRIV_KEY_INFO)

int i2d_PKCS8PrivateKeyInfo_bio(BIO *bp, EVP_PKEY *key) {
  PKCS8_PRIV_KEY_INFO *p8inf;
  int ret;
  p8inf = EVP_PKEY2PKCS8(key);
  if (!p8inf) {
    return 0;
  }
  ret = i2d_PKCS8_PRIV_KEY_INFO_bio(bp, p8inf);
  PKCS8_PRIV_KEY_INFO_free(p8inf);
  return ret;
}

IMPLEMENT_D2I_BIO(EVP_PKEY, d2i_PrivateKey_bio, d2i_AutoPrivateKey)
IMPLEMENT_I2D_BIO(EVP_PKEY, i2d_PrivateKey_bio, i2d_PrivateKey)

IMPLEMENT_D2I_BIO(EVP_PKEY, d2i_PUBKEY_bio, d2i_PUBKEY)
IMPLEMENT_I2D_BIO(EVP_PKEY, i2d_PUBKEY_bio, i2d_PUBKEY)

IMPLEMENT_D2I_BIO(DH, d2i_DHparams_bio, d2i_DHparams)
IMPLEMENT_I2D_BIO(const DH, i2d_DHparams_bio, i2d_DHparams)
