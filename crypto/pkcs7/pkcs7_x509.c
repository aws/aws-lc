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

ASN1_ADB_TEMPLATE(p7default) = ASN1_EXP_OPT(PKCS7, d.other, ASN1_ANY, 0);

ASN1_ADB(PKCS7) = {
        ADB_ENTRY(NID_pkcs7_data, ASN1_EXP_OPT(PKCS7, d.data, ASN1_OCTET_STRING, 0)),
        ADB_ENTRY(NID_pkcs7_signed, ASN1_EXP_OPT(PKCS7, d.sign, PKCS7_SIGNED, 0)),
        ADB_ENTRY(NID_pkcs7_enveloped, ASN1_EXP_OPT(PKCS7, d.enveloped, PKCS7_ENVELOPE, 0)),
        ADB_ENTRY(NID_pkcs7_signedAndEnveloped, ASN1_EXP_OPT(PKCS7, d.signed_and_enveloped, PKCS7_SIGN_ENVELOPE, 0)),
        ADB_ENTRY(NID_pkcs7_digest, ASN1_EXP_OPT(PKCS7, d.digest, PKCS7_DIGEST, 0)),
        ADB_ENTRY(NID_pkcs7_encrypted, ASN1_EXP_OPT(PKCS7, d.encrypted, PKCS7_ENCRYPT, 0))
} ASN1_ADB_END(PKCS7, 0, type, 0, &p7default_tt, NULL);

ASN1_SEQUENCE(PKCS7) = {
    ASN1_SIMPLE(PKCS7, type, ASN1_OBJECT),
    ASN1_ADB_OBJECT(PKCS7)
} ASN1_SEQUENCE_END(PKCS7)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7)
IMPLEMENT_ASN1_DUP_FUNCTION(PKCS7)

ASN1_SEQUENCE(PKCS7_SIGNED) = {
        ASN1_SIMPLE(PKCS7_SIGNED, version, ASN1_INTEGER),
        ASN1_SET_OF(PKCS7_SIGNED, md_algs, X509_ALGOR),
        ASN1_SIMPLE(PKCS7_SIGNED, contents, PKCS7),
        ASN1_IMP_SEQUENCE_OF_OPT(PKCS7_SIGNED, cert, X509, 0),
        ASN1_IMP_SET_OF_OPT(PKCS7_SIGNED, crl, X509_CRL, 1),
        ASN1_SET_OF(PKCS7_SIGNED, signer_info, PKCS7_SIGNER_INFO)
} ASN1_SEQUENCE_END(PKCS7_SIGNED)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7_SIGNED)

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

ASN1_SEQUENCE(PKCS7_ENC_CONTENT) = {
        ASN1_SIMPLE(PKCS7_ENC_CONTENT, content_type, ASN1_OBJECT),
        ASN1_SIMPLE(PKCS7_ENC_CONTENT, algorithm, X509_ALGOR),
        ASN1_IMP_OPT(PKCS7_ENC_CONTENT, enc_data, ASN1_OCTET_STRING, 0)
} ASN1_SEQUENCE_END(PKCS7_ENC_CONTENT)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7_ENC_CONTENT)

ASN1_SEQUENCE(PKCS7_SIGN_ENVELOPE) = {
        ASN1_SIMPLE(PKCS7_SIGN_ENVELOPE, version, ASN1_INTEGER),
        ASN1_SET_OF(PKCS7_SIGN_ENVELOPE, recipientinfo, PKCS7_RECIP_INFO),
        ASN1_SET_OF(PKCS7_SIGN_ENVELOPE, md_algs, X509_ALGOR),
        ASN1_SIMPLE(PKCS7_SIGN_ENVELOPE, enc_data, PKCS7_ENC_CONTENT),
        ASN1_IMP_SET_OF_OPT(PKCS7_SIGN_ENVELOPE, cert, X509, 0),
        ASN1_IMP_SET_OF_OPT(PKCS7_SIGN_ENVELOPE, crl, X509_CRL, 1),
        ASN1_SET_OF(PKCS7_SIGN_ENVELOPE, signer_info, PKCS7_SIGNER_INFO)
} ASN1_SEQUENCE_END(PKCS7_SIGN_ENVELOPE)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7_SIGN_ENVELOPE)

ASN1_SEQUENCE(PKCS7_ENCRYPT) = {
        ASN1_SIMPLE(PKCS7_ENCRYPT, version, ASN1_INTEGER),
        ASN1_SIMPLE(PKCS7_ENCRYPT, enc_data, PKCS7_ENC_CONTENT)
} ASN1_SEQUENCE_END(PKCS7_ENCRYPT)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7_ENCRYPT)

ASN1_SEQUENCE(PKCS7_DIGEST) = {
        ASN1_SIMPLE(PKCS7_DIGEST, version, ASN1_INTEGER),
        ASN1_SIMPLE(PKCS7_DIGEST, md, X509_ALGOR),
        ASN1_SIMPLE(PKCS7_DIGEST, contents, PKCS7),
        ASN1_SIMPLE(PKCS7_DIGEST, digest, ASN1_OCTET_STRING)
} ASN1_SEQUENCE_END(PKCS7_DIGEST)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7_DIGEST)

ASN1_SEQUENCE(PKCS7_ENVELOPE) = {
        ASN1_SIMPLE(PKCS7_ENVELOPE, version, ASN1_INTEGER),
        ASN1_SET_OF(PKCS7_ENVELOPE, recipientinfo, PKCS7_RECIP_INFO),
        ASN1_SIMPLE(PKCS7_ENVELOPE, enc_data, PKCS7_ENC_CONTENT)
} ASN1_SEQUENCE_END(PKCS7_ENVELOPE)

IMPLEMENT_ASN1_FUNCTIONS(PKCS7_ENVELOPE)


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

PKCS7 *d2i_PKCS7_bio(BIO *bio, PKCS7 **out) {
  if (out == NULL) {
      return NULL;
  }
  return ASN1_item_d2i_bio(ASN1_ITEM_rptr(PKCS7), bio, (void *) *out);
}

int i2d_PKCS7_bio(BIO *bio, const PKCS7 *p7) {
  return ASN1_item_i2d_bio(ASN1_ITEM_rptr(PKCS7), bio, (void *) p7);
}

int PKCS7_type_is_data(const PKCS7 *p7) {
    return OBJ_obj2nid(p7->type) == NID_pkcs7_data;
}

int PKCS7_type_is_digest(const PKCS7 *p7) {
    return OBJ_obj2nid(p7->type) == NID_pkcs7_digest;
}

int PKCS7_type_is_encrypted(const PKCS7 *p7) {
    return OBJ_obj2nid(p7->type) == NID_pkcs7_encrypted;
}

int PKCS7_type_is_enveloped(const PKCS7 *p7) {
    return OBJ_obj2nid(p7->type) == NID_pkcs7_enveloped;
}

int PKCS7_type_is_signed(const PKCS7 *p7) {
    return OBJ_obj2nid(p7->type) == NID_pkcs7_signed;
}

int PKCS7_type_is_signedAndEnveloped(const PKCS7 *p7) {
    return OBJ_obj2nid(p7->type) == NID_pkcs7_signedAndEnveloped;
}

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

  const uint8_t *const_der = der;
  ret = d2i_PKCS7(NULL, &const_der, len);

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
        if ((p7->d.sign = PKCS7_SIGNED_new()) == NULL)
            return 0;
        if (!ASN1_INTEGER_set(p7->d.sign->version, 1)) {
            PKCS7_SIGNED_free(p7->d.sign);
            p7->d.sign = NULL;
            return 0;
        }
        break;
    case NID_pkcs7_digest:
        p7->type = obj;
        if ((p7->d.digest = PKCS7_DIGEST_new()) == NULL)
            return 0;
        if (!ASN1_INTEGER_set(p7->d.digest->version, 0))
            return 0;
        break;
    case NID_pkcs7_data:
        p7->type = obj;
        if ((p7->d.data = ASN1_OCTET_STRING_new()) == NULL)
            return 0;
        break;
    case NID_pkcs7_signedAndEnveloped:
        p7->type = obj;
        if ((p7->d.signed_and_enveloped = PKCS7_SIGN_ENVELOPE_new()) == NULL)
            return 0;
        if (!ASN1_INTEGER_set(p7->d.signed_and_enveloped->version, 1))
            return 0;
        p7->d.signed_and_enveloped->enc_data->content_type = OBJ_nid2obj(NID_pkcs7_data);
        break;
    case NID_pkcs7_enveloped:
        p7->type = obj;
        if ((p7->d.enveloped = PKCS7_ENVELOPE_new()) == NULL)
            return 0;
        if (!ASN1_INTEGER_set(p7->d.enveloped->version, 0))
            return 0;
        p7->d.enveloped->enc_data->content_type = OBJ_nid2obj(NID_pkcs7_data);
        break;
    case NID_pkcs7_encrypted:
        p7->type = obj;
        if ((p7->d.encrypted = PKCS7_ENCRYPT_new()) == NULL)
            return 0;
        if (!ASN1_INTEGER_set(p7->d.encrypted->version, 0))
            return 0;
        p7->d.encrypted->enc_data->content_type = OBJ_nid2obj(NID_pkcs7_data);
        break;
    // TODO [childw] https://github.com/openssl/openssl/blob/c86d37cec919caf6ca71d093cff3e05ade1212fe/crypto/pkcs7/pk7_lib.c#L339
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_UNSUPPORTED_CONTENT_TYPE);
        return 0;
    }
    return 1;
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
    case NID_pkcs7_enveloped:
        ec = p7->d.enveloped->enc_data;
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

int PKCS7_set_content(PKCS7 *p7, PKCS7 *p7_data)
{
    int i = OBJ_obj2nid(p7->type);
    switch (i) {
    case NID_pkcs7_signed:
        PKCS7_free(p7->d.sign->contents);
        p7->d.sign->contents = p7_data;
        break;
    case NID_pkcs7_digest:
        PKCS7_free(p7->d.digest->contents);
        p7->d.digest->contents = p7_data;
        break;
    case NID_pkcs7_data:
    case NID_pkcs7_enveloped:
    case NID_pkcs7_signedAndEnveloped:
    case NID_pkcs7_encrypted:
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_UNSUPPORTED_CONTENT_TYPE);
        return 0;
    }
    return 1;
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
    int j;
    ASN1_OBJECT *obj;
    X509_ALGOR *alg;
    STACK_OF(PKCS7_SIGNER_INFO) *signer_sk;
    STACK_OF(X509_ALGOR) *md_sk;

    switch (OBJ_obj2nid(p7->type)) {
    case NID_pkcs7_signed:
        signer_sk = p7->d.sign->signer_info;
        md_sk = p7->d.sign->md_algs;
        break;
    case NID_pkcs7_signedAndEnveloped:
        signer_sk = p7->d.signed_and_enveloped->signer_info;
        md_sk = p7->d.signed_and_enveloped->md_algs;
        break;
    default:
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_WRONG_CONTENT_TYPE);
        return 0;
    }


    obj = p7i->digest_alg->algorithm;
    /* If the digest is not currently listed, add it */
    j = 0;
    for (size_t i = 0; i < sk_X509_ALGOR_num(md_sk); i++) {
        alg = sk_X509_ALGOR_value(md_sk, i);
        if (OBJ_cmp(obj, alg->algorithm) == 0) {
            j = 1;
            break;
        }
    }
    if (!j) {                   /* we need to add another algorithm */
        int nid;

        if ((alg = X509_ALGOR_new()) == NULL
            || (alg->parameter = ASN1_TYPE_new()) == NULL) {
            X509_ALGOR_free(alg);
            OPENSSL_PUT_ERROR(PKCS7, ERR_R_ASN1_LIB);
            return 0;
        }
        /*
         * If there is a constant copy of the ASN1 OBJECT in libcrypto, then
         * use that.  Otherwise, use a dynamically duplicated copy
         */
        if ((nid = OBJ_obj2nid(obj)) != NID_undef)
            alg->algorithm = OBJ_nid2obj(nid);
        else
            alg->algorithm = OBJ_dup(obj);
        alg->parameter->type = V_ASN1_NULL;
        if (alg->algorithm == NULL || !sk_X509_ALGOR_push(md_sk, alg)) {
            X509_ALGOR_free(alg);
            return 0;
        }
    }

    if (!sk_PKCS7_SIGNER_INFO_push(signer_sk, p7i)) {
        return 0;
    }
    return 1;
}

ASN1_TYPE *PKCS7_get_signed_attribute(const PKCS7_SIGNER_INFO *si, int nid) {
    for (size_t i = 0; i < sk_X509_ATTRIBUTE_num(si->auth_attr); i++) {
        X509_ATTRIBUTE *attr = sk_X509_ATTRIBUTE_value(si->auth_attr, i);
        ASN1_OBJECT *obj = X509_ATTRIBUTE_get0_object(attr);
        if (OBJ_obj2nid(obj) == nid) {
            return X509_ATTRIBUTE_get0_type(attr, 0);
        }
    }
    return NULL;
}

STACK_OF(PKCS7_SIGNER_INFO) *PKCS7_get_signer_info(PKCS7 *p7) {
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
    /* We now need to add another PKCS7_SIGNER_INFO entry */
    if (!ASN1_INTEGER_set(p7i->version, 1))
        return 0;
    if (!X509_NAME_set(&p7i->issuer_and_serial->issuer,
                       X509_get_issuer_name(x509)))
        return 0;

    /*
     * because ASN1_INTEGER_set is used to set a 'long' we will do things the
     * ugly way.
     */
    ASN1_INTEGER_free(p7i->issuer_and_serial->serial);
    if (!(p7i->issuer_and_serial->serial =
          ASN1_INTEGER_dup(X509_get0_serialNumber(x509))))
        return 0;

    /* lets keep the pkey around for a while */
    EVP_PKEY_up_ref(pkey);
    p7i->pkey = pkey;

    /* Set the algorithms */

    if (!X509_ALGOR_set0(p7i->digest_alg, OBJ_nid2obj(EVP_MD_pkey_type(dgst)),
                         V_ASN1_NULL, NULL))
        return 0;

    if (EVP_PKEY_id(pkey) == EVP_PKEY_EC || EVP_PKEY_id(pkey) == EVP_PKEY_DH) {
        int snid, hnid;
        X509_ALGOR *alg1, *alg2;

        PKCS7_SIGNER_INFO_get0_algs(p7i, NULL, &alg1, &alg2);
        if (alg1 == NULL || alg1->algorithm == NULL)
            return 0;
        hnid = OBJ_obj2nid(alg1->algorithm);
        if (hnid == NID_undef)
            return 0;
        if (!OBJ_find_sigid_by_algs(&snid, hnid, EVP_PKEY_id(pkey)))
            return 0;
        if (!X509_ALGOR_set0(alg2, OBJ_nid2obj(snid), V_ASN1_UNDEF, NULL))
            return 0;
    } else if (EVP_PKEY_id(pkey) == EVP_PKEY_RSA || EVP_PKEY_id(pkey) == EVP_PKEY_RSA_PSS) {
        X509_ALGOR *alg = NULL;

        PKCS7_SIGNER_INFO_get0_algs(p7i, NULL, NULL, &alg);
        if (alg != NULL)
            // TODO [childw] why the hell does this set encryption instead of sig/PSS?
            return X509_ALGOR_set0(alg, OBJ_nid2obj(NID_rsaEncryption),
                                   V_ASN1_NULL, NULL);
    } else {
        OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_SIGNING_NOT_SUPPORTED_FOR_THIS_KEY_TYPE);
        return 0;
    }

    return 1;
}

int PKCS7_RECIP_INFO_set(PKCS7_RECIP_INFO *p7i, X509 *x509) {
    EVP_PKEY *pkey = NULL;
    if (!ASN1_INTEGER_set(p7i->version, 0))
        return 0;
    if (!X509_NAME_set(&p7i->issuer_and_serial->issuer,
                       X509_get_issuer_name(x509)))
        return 0;

    ASN1_INTEGER_free(p7i->issuer_and_serial->serial);
    if (!(p7i->issuer_and_serial->serial =
          ASN1_INTEGER_dup(X509_get0_serialNumber(x509))))
        return 0;

    pkey = X509_get0_pubkey(x509);
    if (pkey == NULL)
        return 0;

    if (EVP_PKEY_id(pkey) == EVP_PKEY_RSA_PSS) {
        return 0;
    } else if (EVP_PKEY_id(pkey) == EVP_PKEY_RSA) {
        X509_ALGOR *alg;
        PKCS7_RECIP_INFO_get0_alg(p7i, &alg);
        if (!X509_ALGOR_set0(alg, OBJ_nid2obj(NID_rsaEncryption),
                                   V_ASN1_NULL, NULL)) {
            return 0;
        }
    }

    X509_up_ref(x509);
    p7i->cert = x509;

    return 1;
}

void PKCS7_SIGNER_INFO_get0_algs(PKCS7_SIGNER_INFO *si, EVP_PKEY **pk,
                                 X509_ALGOR **pdig, X509_ALGOR **psig)
{
    if (pk)
        *pk = si->pkey;
    if (pdig)
        *pdig = si->digest_alg;
    if (psig)
        *psig = si->digest_enc_alg;
}

void PKCS7_RECIP_INFO_get0_alg(PKCS7_RECIP_INFO *ri, X509_ALGOR **penc)
{
    if (penc)
        *penc = ri->key_enc_algor;
}
