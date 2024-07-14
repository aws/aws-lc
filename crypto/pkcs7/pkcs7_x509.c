/* Copyright (c) 2017, Google Inc.
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

#include <openssl/pkcs7.h>

#include <assert.h>
#include <limits.h>

#include <openssl/asn1.h>
#include <openssl/asn1t.h>
#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/obj.h>
#include <openssl/pem.h>
#include <openssl/pool.h>
#include <openssl/stack.h>
#include <openssl/x509.h>

#include "internal.h"
#include "../internal.h"


int PKCS7_get_certificates(STACK_OF(X509) *out_certs, CBS *cbs) {
  int ret = 0;
  const size_t initial_certs_len = sk_X509_num(out_certs);
  STACK_OF(CRYPTO_BUFFER) *raw = sk_CRYPTO_BUFFER_new_null();
  if (raw == NULL ||
      !PKCS7_get_raw_certificates(raw, cbs, NULL)) {
    goto err;
  }

  for (size_t i = 0; i < sk_CRYPTO_BUFFER_num(raw); i++) {
    CRYPTO_BUFFER *buf = sk_CRYPTO_BUFFER_value(raw, i);
    X509 *x509 = X509_parse_from_buffer(buf);
    if (x509 == NULL ||
        !sk_X509_push(out_certs, x509)) {
      X509_free(x509);
      goto err;
    }
  }

  ret = 1;

err:
  sk_CRYPTO_BUFFER_pop_free(raw, CRYPTO_BUFFER_free);
  if (!ret) {
    while (sk_X509_num(out_certs) != initial_certs_len) {
      X509 *x509 = sk_X509_pop(out_certs);
      X509_free(x509);
    }
  }

  return ret;
}

int PKCS7_get_CRLs(STACK_OF(X509_CRL) *out_crls, CBS *cbs) {
  CBS signed_data, crls;
  uint8_t *der_bytes = NULL;
  int ret = 0, has_crls;
  const size_t initial_crls_len = sk_X509_CRL_num(out_crls);

  // See https://tools.ietf.org/html/rfc2315#section-9.1
  if (!pkcs7_parse_header(&der_bytes, &signed_data, cbs) ||
      // Even if only CRLs are included, there may be an empty certificates
      // block. OpenSSL does this, for example.
      !CBS_get_optional_asn1(
          &signed_data, NULL, NULL,
          CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0) ||
      !CBS_get_optional_asn1(
          &signed_data, &crls, &has_crls,
          CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 1)) {
    goto err;
  }

  if (!has_crls) {
    CBS_init(&crls, NULL, 0);
  }

  while (CBS_len(&crls) > 0) {
    CBS crl_data;
    X509_CRL *crl;
    const uint8_t *inp;

    if (!CBS_get_asn1_element(&crls, &crl_data, CBS_ASN1_SEQUENCE)) {
      goto err;
    }

    if (CBS_len(&crl_data) > LONG_MAX) {
      goto err;
    }
    inp = CBS_data(&crl_data);
    crl = d2i_X509_CRL(NULL, &inp, (long)CBS_len(&crl_data));
    if (!crl) {
      goto err;
    }

    assert(inp == CBS_data(&crl_data) + CBS_len(&crl_data));

    if (sk_X509_CRL_push(out_crls, crl) == 0) {
      X509_CRL_free(crl);
      goto err;
    }
  }

  ret = 1;

err:
  OPENSSL_free(der_bytes);

  if (!ret) {
    while (sk_X509_CRL_num(out_crls) != initial_crls_len) {
      X509_CRL_free(sk_X509_CRL_pop(out_crls));
    }
  }

  return ret;
}

int PKCS7_get_PEM_certificates(STACK_OF(X509) *out_certs, BIO *pem_bio) {
  uint8_t *data;
  long len;
  int ret;

  // Even though we pass PEM_STRING_PKCS7 as the expected PEM type here, PEM
  // internally will actually allow several other values too, including
  // "CERTIFICATE".
  if (!PEM_bytes_read_bio(&data, &len, NULL /* PEM type output */,
                          PEM_STRING_PKCS7, pem_bio,
                          NULL /* password callback */,
                          NULL /* password callback argument */)) {
    return 0;
  }

  CBS cbs;
  CBS_init(&cbs, data, len);
  ret = PKCS7_get_certificates(out_certs, &cbs);
  OPENSSL_free(data);
  return ret;
}

int PKCS7_get_PEM_CRLs(STACK_OF(X509_CRL) *out_crls, BIO *pem_bio) {
  uint8_t *data;
  long len;
  int ret;

  // Even though we pass PEM_STRING_PKCS7 as the expected PEM type here, PEM
  // internally will actually allow several other values too, including
  // "CERTIFICATE".
  if (!PEM_bytes_read_bio(&data, &len, NULL /* PEM type output */,
                          PEM_STRING_PKCS7, pem_bio,
                          NULL /* password callback */,
                          NULL /* password callback argument */)) {
    return 0;
  }

  CBS cbs;
  CBS_init(&cbs, data, len);
  ret = PKCS7_get_CRLs(out_crls, &cbs);
  OPENSSL_free(data);
  return ret;
}

static int pkcs7_bundle_certificates_cb(CBB *out, const void *arg) {
  const STACK_OF(X509) *certs = arg;
  size_t i;
  CBB certificates;

  // See https://tools.ietf.org/html/rfc2315#section-9.1
  if (!CBB_add_asn1(out, &certificates,
                    CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0)) {
    return 0;
  }

  for (i = 0; i < sk_X509_num(certs); i++) {
    X509 *x509 = sk_X509_value(certs, i);
    uint8_t *buf;
    int len = i2d_X509(x509, NULL);

    if (len < 0 ||
        !CBB_add_space(&certificates, &buf, len) ||
        i2d_X509(x509, &buf) < 0) {
      return 0;
    }
  }

  // |certificates| is a implicitly-tagged SET OF.
  return CBB_flush_asn1_set_of(&certificates) && CBB_flush(out);
}

int PKCS7_bundle_certificates(CBB *out, const STACK_OF(X509) *certs) {
  return pkcs7_add_signed_data(out, /*digest_algos_cb=*/NULL,
                               pkcs7_bundle_certificates_cb,
                               /*signer_infos_cb=*/NULL, certs);
}

static int pkcs7_bundle_crls_cb(CBB *out, const void *arg) {
  const STACK_OF(X509_CRL) *crls = arg;
  size_t i;
  CBB crl_data;

  // See https://tools.ietf.org/html/rfc2315#section-9.1
  if (!CBB_add_asn1(out, &crl_data,
                    CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 1)) {
    return 0;
  }

  for (i = 0; i < sk_X509_CRL_num(crls); i++) {
    X509_CRL *crl = sk_X509_CRL_value(crls, i);
    uint8_t *buf;
    int len = i2d_X509_CRL(crl, NULL);

    if (len < 0 ||
        !CBB_add_space(&crl_data, &buf, len) ||
        i2d_X509_CRL(crl, &buf) < 0) {
      return 0;
    }
  }

  // |crl_data| is a implicitly-tagged SET OF.
  return CBB_flush_asn1_set_of(&crl_data) && CBB_flush(out);
}

int PKCS7_bundle_CRLs(CBB *out, const STACK_OF(X509_CRL) *crls) {
  return pkcs7_add_signed_data(out, /*digest_algos_cb=*/NULL,
                               pkcs7_bundle_crls_cb,
                               /*signer_infos_cb=*/NULL, crls);
}

static PKCS7 *pkcs7_new(CBS *cbs) {
  PKCS7 *ret = OPENSSL_zalloc(sizeof(PKCS7));
  if (ret == NULL) {
    return NULL;
  }
  ret->type = OBJ_nid2obj(NID_pkcs7_signed);
  ret->d.sign = OPENSSL_malloc(sizeof(PKCS7_SIGNED));
  if (ret->d.sign == NULL) {
    goto err;
  }
  ret->d.sign->cert = sk_X509_new_null();
  ret->d.sign->crl = sk_X509_CRL_new_null();
  CBS copy = *cbs, copy2 = *cbs;
  if (ret->d.sign->cert == NULL || ret->d.sign->crl == NULL ||
      !PKCS7_get_certificates(ret->d.sign->cert, &copy) ||
      !PKCS7_get_CRLs(ret->d.sign->crl, cbs)) {
    goto err;
  }

  if (sk_X509_num(ret->d.sign->cert) == 0) {
    sk_X509_free(ret->d.sign->cert);
    ret->d.sign->cert = NULL;
  }

  if (sk_X509_CRL_num(ret->d.sign->crl) == 0) {
    sk_X509_CRL_free(ret->d.sign->crl);
    ret->d.sign->crl = NULL;
  }

  ret->ber_len = CBS_len(&copy2) - CBS_len(cbs);
  ret->ber_bytes = OPENSSL_memdup(CBS_data(&copy2), ret->ber_len);
  if (ret->ber_bytes == NULL) {
    goto err;
  }

  return ret;

err:
  PKCS7_free(ret);
  return NULL;
}

PKCS7 *d2i_PKCS7(PKCS7 **out, const uint8_t **inp,
                 size_t len) {
  CBS cbs;
  CBS_init(&cbs, *inp, len);
  PKCS7 *ret = pkcs7_new(&cbs);
  if (ret == NULL) {
    return NULL;
  }
  *inp = CBS_data(&cbs);
  if (out != NULL) {
    PKCS7_free(*out);
    *out = ret;
  }
  return ret;
}

PKCS7 *d2i_PKCS7_bio(BIO *bio, PKCS7 **out) {
  // Use a generous bound, to allow for PKCS#7 files containing large root sets.
  static const size_t kMaxSize = 4 * 1024 * 1024;
  uint8_t *data;
  size_t len;
  if (!BIO_read_asn1(bio, &data, &len, kMaxSize)) {
    return NULL;
  }

  CBS cbs;
  CBS_init(&cbs, data, len);
  PKCS7 *ret = pkcs7_new(&cbs);
  OPENSSL_free(data);
  if (out != NULL && ret != NULL) {
    PKCS7_free(*out);
    *out = ret;
  }
  return ret;
}

int i2d_PKCS7(const PKCS7 *p7, uint8_t **out) {
  if (p7->ber_len > INT_MAX) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_OVERFLOW);
    return -1;
  }

  if (out == NULL) {
    return (int)p7->ber_len;
  }

  if (*out == NULL) {
    *out = OPENSSL_memdup(p7->ber_bytes, p7->ber_len);
    if (*out == NULL) {
      return -1;
    }
  } else {
    OPENSSL_memcpy(*out, p7->ber_bytes, p7->ber_len);
    *out += p7->ber_len;
  }
  return (int)p7->ber_len;
}

int i2d_PKCS7_bio(BIO *bio, const PKCS7 *p7) {
  return BIO_write_all(bio, p7->ber_bytes, p7->ber_len);
}


PKCS7 *PKCS7_new(void) {
  PKCS7 *ret = OPENSSL_zalloc(sizeof(PKCS7));
  ret->ber_bytes = NULL;
  ret->ber_len = 0;
  ret->type = NULL;
  return ret;
}

void PKCS7_free(PKCS7 *p7) {
  if (p7 == NULL) {
    return;
  }

  OPENSSL_free(p7->ber_bytes);
  ASN1_OBJECT_free(p7->type);
  // We only supported signed data.
  if (p7->d.sign != NULL) {
    sk_X509_pop_free(p7->d.sign->cert, X509_free);
    sk_X509_CRL_pop_free(p7->d.sign->crl, X509_CRL_free);
    OPENSSL_free(p7->d.sign);
  }
  OPENSSL_free(p7);
}

// We only support signed data, so these getters are no-ops.
int PKCS7_type_is_data(const PKCS7 *p7) { return 0; }
int PKCS7_type_is_digest(const PKCS7 *p7) { return 0; }
int PKCS7_type_is_encrypted(const PKCS7 *p7) { return 0; }
int PKCS7_type_is_enveloped(const PKCS7 *p7) { return 0; }
int PKCS7_type_is_signed(const PKCS7 *p7) { return 1; }
int PKCS7_type_is_signedAndEnveloped(const PKCS7 *p7) { return 0; }

// write_sha256_ai writes an AlgorithmIdentifier for SHA-256 to
// |digest_algos_set|.
static int write_sha256_ai(CBB *digest_algos_set, const void *arg) {
  CBB seq;
  return CBB_add_asn1(digest_algos_set, &seq, CBS_ASN1_SEQUENCE) &&
         OBJ_nid2cbb(&seq, NID_sha256) &&  //
         // https://datatracker.ietf.org/doc/html/rfc5754#section-2
         // "Implementations MUST generate SHA2 AlgorithmIdentifiers with absent
         //  parameters."
         CBB_flush(digest_algos_set);
}

// sign_sha256 writes at most |max_out_sig| bytes of the signature of |data| by
// |pkey| to |out_sig| and sets |*out_sig_len| to the number of bytes written.
// It returns one on success or zero on error.
static int sign_sha256(uint8_t *out_sig, size_t *out_sig_len,
                       size_t max_out_sig, EVP_PKEY *pkey, BIO *data) {
  static const size_t kBufSize = 4096;
  uint8_t *buffer = OPENSSL_malloc(kBufSize);
  if (!buffer) {
    return 0;
  }

  EVP_MD_CTX ctx;
  EVP_MD_CTX_init(&ctx);

  int ret = 0;
  if (!EVP_DigestSignInit(&ctx, NULL, EVP_sha256(), NULL, pkey)) {
    goto out;
  }

  for (;;) {
    const int n = BIO_read(data, buffer, kBufSize);
    if (n == 0) {
      break;
    } else if (n < 0 || !EVP_DigestSignUpdate(&ctx, buffer, n)) {
      goto out;
    }
  }

  *out_sig_len = max_out_sig;
  if (!EVP_DigestSignFinal(&ctx, out_sig, out_sig_len)) {
    goto out;
  }

  ret = 1;

out:
  EVP_MD_CTX_cleanup(&ctx);
  OPENSSL_free(buffer);
  return ret;
}

struct signer_info_data {
  const X509 *sign_cert;
  uint8_t *signature;
  size_t signature_len;
};

// write_signer_info writes the SignerInfo structure from
// https://datatracker.ietf.org/doc/html/rfc2315#section-9.2 to |out|. It
// returns one on success or zero on error.
static int write_signer_info(CBB *out, const void *arg) {
  const struct signer_info_data *const si_data = arg;

  int ret = 0;
  uint8_t *subject_bytes = NULL;
  uint8_t *serial_bytes = NULL;

  const int subject_len =
      i2d_X509_NAME(X509_get_subject_name(si_data->sign_cert), &subject_bytes);
  const int serial_len = i2d_ASN1_INTEGER(
      (ASN1_INTEGER *)X509_get0_serialNumber(si_data->sign_cert),
      &serial_bytes);

  CBB seq, issuer_and_serial, signing_algo, null, signature;
  if (subject_len < 0 ||
      serial_len < 0 ||
      !CBB_add_asn1(out, &seq, CBS_ASN1_SEQUENCE) ||
      // version
      !CBB_add_asn1_uint64(&seq, 1) ||
      !CBB_add_asn1(&seq, &issuer_and_serial, CBS_ASN1_SEQUENCE) ||
      !CBB_add_bytes(&issuer_and_serial, subject_bytes, subject_len) ||
      !CBB_add_bytes(&issuer_and_serial, serial_bytes, serial_len) ||
      !write_sha256_ai(&seq, NULL) ||
      !CBB_add_asn1(&seq, &signing_algo, CBS_ASN1_SEQUENCE) ||
      !OBJ_nid2cbb(&signing_algo, NID_rsaEncryption) ||
      !CBB_add_asn1(&signing_algo, &null, CBS_ASN1_NULL) ||
      !CBB_add_asn1(&seq, &signature, CBS_ASN1_OCTETSTRING) ||
      !CBB_add_bytes(&signature, si_data->signature, si_data->signature_len) ||
      !CBB_flush(out)) {
    goto out;
  }

  ret = 1;

out:
  OPENSSL_free(subject_bytes);
  OPENSSL_free(serial_bytes);
  return ret;
}

PKCS7 *PKCS7_sign(X509 *sign_cert, EVP_PKEY *pkey, STACK_OF(X509) *certs,
                  BIO *data, int flags) {
  CBB cbb;
  if (!CBB_init(&cbb, 2048)) {
    return NULL;
  }

  uint8_t *der = NULL;
  size_t len;
  PKCS7 *ret = NULL;

  if (sign_cert == NULL && pkey == NULL && flags == PKCS7_DETACHED) {
    // Caller just wants to bundle certificates.
    if (!PKCS7_bundle_certificates(&cbb, certs)) {
      goto out;
    }
  } else if (sign_cert != NULL && pkey != NULL && certs == NULL &&
             data != NULL &&
             flags == (PKCS7_NOATTR | PKCS7_BINARY | PKCS7_NOCERTS |
                       PKCS7_DETACHED) &&
             EVP_PKEY_id(pkey) == NID_rsaEncryption) {
    // sign-file.c from the Linux kernel.
    const size_t signature_max_len = EVP_PKEY_size(pkey);
    struct signer_info_data si_data = {
      .sign_cert = sign_cert,
      .signature = OPENSSL_malloc(signature_max_len),
    };

    if (!si_data.signature ||
        !sign_sha256(si_data.signature, &si_data.signature_len,
                     signature_max_len, pkey, data) ||
        !pkcs7_add_signed_data(&cbb, write_sha256_ai, /*cert_crl_cb=*/NULL,
                               write_signer_info, &si_data)) {
      OPENSSL_free(si_data.signature);
      goto out;
    }
    OPENSSL_free(si_data.signature);
  } else {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
    goto out;
  }

  if (!CBB_finish(&cbb, &der, &len)) {
    goto out;
  }

  CBS cbs;
  CBS_init(&cbs, der, len);
  ret = pkcs7_new(&cbs);

out:
  CBB_cleanup(&cbb);
  OPENSSL_free(der);
  return ret;
}

int PKCS7_add_certificate(PKCS7 *p7, X509 *x509)
{
    int i;
    STACK_OF(X509) *sk;

    i = OBJ_obj2nid(p7->type);
    switch (i) {
    case NID_pkcs7_signed:
        sk = p7->d.sign->cert;
        break;
    case NID_pkcs7_signedAndEnveloped:
        sk = p7->d.signed_and_enveloped->cert;
        break;
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_WRONG_CONTENT_TYPE);
        return 0;
    }

    if (sk == NULL) {
        OPENSSL_PUT_ERROR(X509, ERR_R_INTERNAL_ERROR);
        return 0;
    }
    if (!sk_X509_insert(sk, x509, 0)) {
        OPENSSL_PUT_ERROR(X509, ERR_R_CRYPTO_LIB);
        return 0;
    }
    X509_up_ref(x509);
    return 1;
}

int PKCS7_add_crl(PKCS7 *p7, X509_CRL *crl)
{
    int i;
    STACK_OF(X509_CRL) **sk;

    i = OBJ_obj2nid(p7->type);
    switch (i) {
    case NID_pkcs7_signed:
        sk = &(p7->d.sign->crl);
        break;
    case NID_pkcs7_signedAndEnveloped:
        sk = &(p7->d.signed_and_enveloped->crl);
        break;
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_WRONG_CONTENT_TYPE);
        return 0;
    }

    if (*sk == NULL)
        *sk = sk_X509_CRL_new_null();
    if (*sk == NULL) {
        OPENSSL_PUT_ERROR(PKCS7, ERR_R_CRYPTO_LIB);
        return 0;
    }

    X509_CRL_up_ref(crl);
    if (!sk_X509_CRL_push(*sk, crl)) {
        X509_CRL_free(crl);
        return 0;
    }
    return 1;
}

int PKCS7_set_type(PKCS7 *p7, int type)
{
    ASN1_OBJECT *obj;

    obj = OBJ_nid2obj(type);    /* will not fail */

    switch (type) {
    case NID_pkcs7_signed:
      p7->type = obj;
      p7->d.sign->cert = sk_X509_new_null();
      p7->d.sign->crl = sk_X509_CRL_new_null();
      if (p7->d.sign->cert == NULL || p7->d.sign->crl == NULL) {
        goto err;
      }
      break;
    case NID_pkcs7_signedAndEnveloped:
      p7->type = obj;
      p7->d.signed_and_enveloped->cert = sk_X509_new_null();
      p7->d.signed_and_enveloped->crl = sk_X509_CRL_new_null();
      if (p7->d.signed_and_enveloped->cert == NULL
              || p7->d.signed_and_enveloped->crl == NULL) {
        goto err;
      }
      break;
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_UNSUPPORTED_CONTENT_TYPE);
        goto err;
    }
    return 1;
 err:
    return 0;
}

int PKCS7_set_cipher(PKCS7 *p7, const EVP_CIPHER *cipher)
{
    int i;
    PKCS7_ENC_CONTENT *ec;

    i = OBJ_obj2nid(p7->type);
    switch (i) {
    case NID_pkcs7_signedAndEnveloped:
        ec = p7->d.signed_and_enveloped->enc_data;
        break;
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_WRONG_CONTENT_TYPE);
        return 0;
    }

    /* Check cipher OID exists and has data in it */
    if (EVP_get_cipherbynid(EVP_CIPHER_nid(cipher)) == NULL) {
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_CIPHER_HAS_NO_OBJECT_IDENTIFIER);
        return 0;
    }

    ec->cipher = cipher;
    return 1;
}

static int PKCS7_set_content(PKCS7 *p7, PKCS7 *p7_data)
{
    int i;

    i = OBJ_obj2nid(p7->type);
    switch (i) {
    case NID_pkcs7_signed:
        // TODO [childw] need to free p7->d.sign?
        p7->d.sign = p7_data->d.sign;
        break;
    case NID_pkcs7_signedAndEnveloped:
        // TODO [childw] need to free p7->d.signed_and_enveloped?
        p7->d.signed_and_enveloped = p7_data->d.signed_and_enveloped;
        break;
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_UNSUPPORTED_CONTENT_TYPE);
        goto err;
    }
    return 1;
 err:
    return 0;
}



// TODO [childw] de-indent down to 2 spaces

// TODO [childw] implement this dup
PKCS7 *PKCS7_dup(PKCS7 * p7) {
    uint8_t *buf = NULL;
    int len = i2d_PKCS7(p7, &buf);
    return d2i_PKCS7(NULL, (const uint8_t **) &buf, len);
}

int PKCS7_content_new(PKCS7 *p7, int type)
{
    PKCS7 *ret = NULL;

    if ((ret = PKCS7_new()) == NULL)
        goto err;
    if (!PKCS7_set_type(ret, type))
        goto err;
    if (!PKCS7_set_content(p7, ret))
        goto err;

    return 1;
 err:
    PKCS7_free(ret);
    return 0;
}

ASN1_SEQUENCE(PKCS7_ISSUER_AND_SERIAL) = {
        ASN1_SIMPLE(PKCS7_ISSUER_AND_SERIAL, issuer, X509_NAME),
        ASN1_SIMPLE(PKCS7_ISSUER_AND_SERIAL, serial, ASN1_INTEGER)
} ASN1_SEQUENCE_END(PKCS7_ISSUER_AND_SERIAL)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7_ISSUER_AND_SERIAL)

ASN1_SEQUENCE(PKCS7_RECIP_INFO) = {
        ASN1_SIMPLE(PKCS7_RECIP_INFO, version, ASN1_INTEGER),
        ASN1_SIMPLE(PKCS7_RECIP_INFO, issuer_and_serial, PKCS7_ISSUER_AND_SERIAL),
        ASN1_SIMPLE(PKCS7_RECIP_INFO, key_enc_algor, X509_ALGOR),
        ASN1_SIMPLE(PKCS7_RECIP_INFO, enc_key, ASN1_OCTET_STRING)
} ASN1_SEQUENCE_END(PKCS7_RECIP_INFO)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7_RECIP_INFO)

ASN1_SEQUENCE(PKCS7_SIGNER_INFO) = {
        ASN1_SIMPLE(PKCS7_SIGNER_INFO, version, ASN1_INTEGER),
        ASN1_SIMPLE(PKCS7_SIGNER_INFO, issuer_and_serial, PKCS7_ISSUER_AND_SERIAL),
        ASN1_SIMPLE(PKCS7_SIGNER_INFO, digest_alg, X509_ALGOR),
        /* NB this should be a SET OF but we use a SEQUENCE OF so the
         * original order * is retained when the structure is reencoded.
         * Since the attributes are implicitly tagged this will not affect
         * the encoding.
         */
        ASN1_IMP_SEQUENCE_OF_OPT(PKCS7_SIGNER_INFO, auth_attr, X509_ATTRIBUTE, 0),
        ASN1_SIMPLE(PKCS7_SIGNER_INFO, digest_enc_alg, X509_ALGOR),
        ASN1_SIMPLE(PKCS7_SIGNER_INFO, enc_digest, ASN1_OCTET_STRING),
        ASN1_IMP_SET_OF_OPT(PKCS7_SIGNER_INFO, unauth_attr, X509_ATTRIBUTE, 1)
} ASN1_SEQUENCE_END(PKCS7_SIGNER_INFO)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7_SIGNER_INFO)

int PKCS7_add_recipient_info(PKCS7 *p7, PKCS7_RECIP_INFO *ri) {
    int i;
    STACK_OF(PKCS7_RECIP_INFO) *sk;

    i = OBJ_obj2nid(p7->type);
    switch (i) {
    case NID_pkcs7_signedAndEnveloped:
        sk = p7->d.signed_and_enveloped->recipientinfo;
        break;
    case NID_pkcs7_enveloped:
        sk = p7->d.enveloped->recipientinfo;
        break;
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_WRONG_CONTENT_TYPE);
        return 0;
    }

    if (!sk_PKCS7_RECIP_INFO_push(sk, ri))
        return 0;
    return 1;
}

int PKCS7_add_signer(PKCS7 *p7, PKCS7_SIGNER_INFO *p7i) {
    int i;
    STACK_OF(PKCS7_SIGNER_INFO) *signer_sk;

    i = OBJ_obj2nid(p7->type);
    switch (i) {
    case NID_pkcs7_signed:
        signer_sk = p7->d.sign->signer_info;
        break;
    case NID_pkcs7_signedAndEnveloped:
        signer_sk = p7->d.signed_and_enveloped->signer_info;
        break;
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_WRONG_CONTENT_TYPE);
        return 0;
    }

    if (!sk_PKCS7_SIGNER_INFO_push(signer_sk, p7i)) {
        return 0;
    }
    return 1;
}

ASN1_TYPE *PKCS7_get_signed_attribute(const PKCS7_SIGNER_INFO *si, int nid) {
    return 0;
}

STACK_OF(PKCS7_SIGNER_INFO) *PKCS7_get_signer_info(PKCS7 *p7) {
    // TODO [childw] impl. the no-ops. can can we look at p7->type?
    if (p7 == NULL || p7->d.ptr == NULL)
        return NULL;
    if (PKCS7_type_is_signed(p7)) {
        return p7->d.sign->signer_info;
    } else if (PKCS7_type_is_signedAndEnveloped(p7)) {
        return p7->d.signed_and_enveloped->signer_info;
    } else
        return NULL;
}

int PKCS7_SIGNER_INFO_set(PKCS7_SIGNER_INFO *p7i, X509 *x509, EVP_PKEY *pkey,
                          const EVP_MD *dgst) {
    return 0;
}

int PKCS7_RECIP_INFO_set(PKCS7_RECIP_INFO *p7i, X509 *x509) {
    return 0;
}
