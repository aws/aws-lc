/* Copyright (c) 2014, Google Inc.
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

#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/obj.h>
#include <openssl/pem.h>
#include <openssl/pool.h>
#include <openssl/stack.h>

#include "../bytestring/internal.h"
#include "../internal.h"
#include "internal.h"


// 1.2.840.113549.1.7.1
static const uint8_t kPKCS7Data[] = {0x2a, 0x86, 0x48, 0x86, 0xf7,
                                     0x0d, 0x01, 0x07, 0x01};

// 1.2.840.113549.1.7.2
static const uint8_t kPKCS7SignedData[] = {0x2a, 0x86, 0x48, 0x86, 0xf7,
                                           0x0d, 0x01, 0x07, 0x02};

// pkcs7_parse_header reads the non-certificate/non-CRL prefix of a PKCS#7
// SignedData blob from |cbs| and sets |*out| to point to the rest of the
// input. If the input is in BER format, then |*der_bytes| will be set to a
// pointer that needs to be freed by the caller once they have finished
// processing |*out| (which will be pointing into |*der_bytes|).
//
// It returns one on success or zero on error. On error, |*der_bytes| is
// NULL.
int pkcs7_parse_header(uint8_t **der_bytes, CBS *out, CBS *cbs) {
  CBS in, content_info, content_type, wrapped_signed_data, signed_data;
  uint64_t version;

  // The input may be in BER format.
  *der_bytes = NULL;
  if (!CBS_asn1_ber_to_der(cbs, &in, der_bytes) ||
      // See https://tools.ietf.org/html/rfc2315#section-7
      !CBS_get_asn1(&in, &content_info, CBS_ASN1_SEQUENCE) ||
      !CBS_get_asn1(&content_info, &content_type, CBS_ASN1_OBJECT)) {
    goto err;
  }

  if (!CBS_mem_equal(&content_type, kPKCS7SignedData,
                     sizeof(kPKCS7SignedData))) {
    OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_NOT_PKCS7_SIGNED_DATA);
    goto err;
  }

  // See https://tools.ietf.org/html/rfc2315#section-9.1
  if (!CBS_get_asn1(&content_info, &wrapped_signed_data,
                    CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0) ||
      !CBS_get_asn1(&wrapped_signed_data, &signed_data, CBS_ASN1_SEQUENCE) ||
      !CBS_get_asn1_uint64(&signed_data, &version) ||
      !CBS_get_asn1(&signed_data, NULL /* digests */, CBS_ASN1_SET) ||
      !CBS_get_asn1(&signed_data, NULL /* content */, CBS_ASN1_SEQUENCE)) {
    goto err;
  }

  if (version < 1) {
    OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_BAD_PKCS7_VERSION);
    goto err;
  }

  CBS_init(out, CBS_data(&signed_data), CBS_len(&signed_data));
  return 1;

err:
  OPENSSL_free(*der_bytes);
  *der_bytes = NULL;
  return 0;
}

int PKCS7_get_raw_certificates(STACK_OF(CRYPTO_BUFFER) *out_certs, CBS *cbs,
                               CRYPTO_BUFFER_POOL *pool) {
  CBS signed_data, certificates;
  uint8_t *der_bytes = NULL;
  int ret = 0, has_certificates;
  const size_t initial_certs_len = sk_CRYPTO_BUFFER_num(out_certs);

  // See https://tools.ietf.org/html/rfc2315#section-9.1
  if (!pkcs7_parse_header(&der_bytes, &signed_data, cbs) ||
      !CBS_get_optional_asn1(
          &signed_data, &certificates, &has_certificates,
          CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0)) {
    goto err;
  }

  if (!has_certificates) {
    CBS_init(&certificates, NULL, 0);
  }

  while (CBS_len(&certificates) > 0) {
    CBS cert;
    if (!CBS_get_asn1_element(&certificates, &cert, CBS_ASN1_SEQUENCE)) {
      goto err;
    }

    CRYPTO_BUFFER *buf = CRYPTO_BUFFER_new_from_CBS(&cert, pool);
    if (buf == NULL || !sk_CRYPTO_BUFFER_push(out_certs, buf)) {
      CRYPTO_BUFFER_free(buf);
      goto err;
    }
  }

  ret = 1;

err:
  OPENSSL_free(der_bytes);

  if (!ret) {
    while (sk_CRYPTO_BUFFER_num(out_certs) != initial_certs_len) {
      CRYPTO_BUFFER *buf = sk_CRYPTO_BUFFER_pop(out_certs);
      CRYPTO_BUFFER_free(buf);
    }
  }

  return ret;
}

static int pkcs7_bundle_raw_certificates_cb(CBB *out, const void *arg) {
  const STACK_OF(CRYPTO_BUFFER) *certs = arg;
  CBB certificates;

  // See https://tools.ietf.org/html/rfc2315#section-9.1
  if (!CBB_add_asn1(out, &certificates,
                    CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0)) {
    return 0;
  }

  for (size_t i = 0; i < sk_CRYPTO_BUFFER_num(certs); i++) {
    CRYPTO_BUFFER *cert = sk_CRYPTO_BUFFER_value(certs, i);
    if (!CBB_add_bytes(&certificates, CRYPTO_BUFFER_data(cert),
                       CRYPTO_BUFFER_len(cert))) {
      return 0;
    }
  }

  // |certificates| is a implicitly-tagged SET OF.
  return CBB_flush_asn1_set_of(&certificates) && CBB_flush(out);
}

int PKCS7_bundle_raw_certificates(CBB *out,
                                  const STACK_OF(CRYPTO_BUFFER) *certs) {
  return pkcs7_add_signed_data(out, /*digest_algos_cb=*/NULL,
                               pkcs7_bundle_raw_certificates_cb,
                               /*signer_infos_cb=*/NULL, certs);
}

int pkcs7_add_signed_data(CBB *out,
                          int (*digest_algos_cb)(CBB *out, const void *arg),
                          int (*cert_crl_cb)(CBB *out, const void *arg),
                          int (*signer_infos_cb)(CBB *out, const void *arg),
                          const void *arg) {
  CBB outer_seq, oid, wrapped_seq, seq, version_bytes, digest_algos_set,
      content_info, signer_infos;

  // See https://tools.ietf.org/html/rfc2315#section-7
  if (!CBB_add_asn1(out, &outer_seq, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1(&outer_seq, &oid, CBS_ASN1_OBJECT) ||
      !CBB_add_bytes(&oid, kPKCS7SignedData, sizeof(kPKCS7SignedData)) ||
      !CBB_add_asn1(&outer_seq, &wrapped_seq,
                    CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0) ||
      // See https://tools.ietf.org/html/rfc2315#section-9.1
      !CBB_add_asn1(&wrapped_seq, &seq, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1(&seq, &version_bytes, CBS_ASN1_INTEGER) ||
      !CBB_add_u8(&version_bytes, 1) ||
      !CBB_add_asn1(&seq, &digest_algos_set, CBS_ASN1_SET) ||
      (digest_algos_cb != NULL && !digest_algos_cb(&digest_algos_set, arg)) ||
      !CBB_add_asn1(&seq, &content_info, CBS_ASN1_SEQUENCE) ||
      !CBB_add_asn1(&content_info, &oid, CBS_ASN1_OBJECT) ||
      !CBB_add_bytes(&oid, kPKCS7Data, sizeof(kPKCS7Data)) ||
      (cert_crl_cb != NULL && !cert_crl_cb(&seq, arg)) ||
      !CBB_add_asn1(&seq, &signer_infos, CBS_ASN1_SET) ||
      (signer_infos_cb != NULL && !signer_infos_cb(&signer_infos, arg))) {
    return 0;
  }

  return CBB_flush(out);
}

int PKCS7_set_type(PKCS7 *p7, int type) {
  if (p7 == NULL) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  }
  ASN1_OBJECT *obj = OBJ_nid2obj(type);
  if (obj == NULL) {
    OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_UNSUPPORTED_CONTENT_TYPE);
    return 0;
  }

  switch (type) {
    case NID_pkcs7_signed:
      p7->type = obj;
      PKCS7_SIGNED_free(p7->d.sign);
      p7->d.sign = PKCS7_SIGNED_new();
      if (p7->d.sign == NULL) {
        return 0;
      }
      if (!ASN1_INTEGER_set(p7->d.sign->version, 1)) {
        PKCS7_SIGNED_free(p7->d.sign);
        p7->d.sign = NULL;
        return 0;
      }
      break;
    case NID_pkcs7_digest:
      p7->type = obj;
      PKCS7_DIGEST_free(p7->d.digest);
      p7->d.digest = PKCS7_DIGEST_new();
      if (p7->d.digest == NULL) {
        return 0;
      }
      if (!ASN1_INTEGER_set(p7->d.digest->version, 0)) {
        PKCS7_DIGEST_free(p7->d.digest);
        p7->d.digest = NULL;
        return 0;
      }
      break;
    case NID_pkcs7_data:
      p7->type = obj;
      ASN1_OCTET_STRING_free(p7->d.data);
      p7->d.data = ASN1_OCTET_STRING_new();
      if (p7->d.data == NULL) {
        return 0;
      }
      break;
    case NID_pkcs7_signedAndEnveloped:
      p7->type = obj;
      PKCS7_SIGN_ENVELOPE_free(p7->d.signed_and_enveloped);
      p7->d.signed_and_enveloped = PKCS7_SIGN_ENVELOPE_new();
      if (p7->d.signed_and_enveloped == NULL) {
        return 0;
      }
      if (!ASN1_INTEGER_set(p7->d.signed_and_enveloped->version, 1)) {
        PKCS7_SIGN_ENVELOPE_free(p7->d.signed_and_enveloped);
        p7->d.signed_and_enveloped = NULL;
        return 0;
      }
      p7->d.signed_and_enveloped->enc_data->content_type =
          OBJ_nid2obj(NID_pkcs7_data);
      break;
    case NID_pkcs7_enveloped:
      p7->type = obj;
      PKCS7_ENVELOPE_free(p7->d.enveloped);
      p7->d.enveloped = PKCS7_ENVELOPE_new();
      if (p7->d.enveloped == NULL) {
        return 0;
      }
      if (!ASN1_INTEGER_set(p7->d.enveloped->version, 0)) {
        PKCS7_ENVELOPE_free(p7->d.enveloped);
        p7->d.enveloped = NULL;
        return 0;
      }
      p7->d.enveloped->enc_data->content_type = OBJ_nid2obj(NID_pkcs7_data);
      break;
    case NID_pkcs7_encrypted:
      p7->type = obj;
      PKCS7_ENCRYPT_free(p7->d.encrypted);
      p7->d.encrypted = PKCS7_ENCRYPT_new();
      if (p7->d.encrypted == NULL) {
        return 0;
      }
      if (!ASN1_INTEGER_set(p7->d.encrypted->version, 0)) {
        PKCS7_ENCRYPT_free(p7->d.encrypted);
        p7->d.encrypted = NULL;
        return 0;
      }
      p7->d.encrypted->enc_data->content_type = OBJ_nid2obj(NID_pkcs7_data);
      break;
    default:
      OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_UNSUPPORTED_CONTENT_TYPE);
      return 0;
  }
  return 1;
}

int PKCS7_set_cipher(PKCS7 *p7, const EVP_CIPHER *cipher) {
  if (p7 == NULL || cipher == NULL) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  }
  if (EVP_get_cipherbynid(EVP_CIPHER_nid(cipher)) == NULL) {
    OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_CIPHER_HAS_NO_OBJECT_IDENTIFIER);
    return 0;
  }

  PKCS7_ENC_CONTENT *ec;
  switch (OBJ_obj2nid(p7->type)) {
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

  ec->cipher = cipher;
  return 1;
}

int PKCS7_set_content(PKCS7 *p7, PKCS7 *p7_data) {
  if (p7 == NULL) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  }

  switch (OBJ_obj2nid(p7->type)) {
    case NID_pkcs7_signed:
      PKCS7_free(p7->d.sign->contents);
      p7->d.sign->contents = p7_data;
      break;
    case NID_pkcs7_digest:
      PKCS7_free(p7->d.digest->contents);
      p7->d.digest->contents = p7_data;
      break;
    default:
      OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_UNSUPPORTED_CONTENT_TYPE);
      return 0;
  }
  return 1;
}

int PKCS7_content_new(PKCS7 *p7, int type) {
  PKCS7 *ret = PKCS7_new();
  if (ret == NULL) {
    goto err;
  }
  if (!PKCS7_set_type(ret, type)) {
    goto err;
  }
  if (!PKCS7_set_content(p7, ret)) {
    goto err;
  }
  return 1;
err:
  PKCS7_free(ret);
  return 0;
}

int PKCS7_add_recipient_info(PKCS7 *p7, PKCS7_RECIP_INFO *ri) {
  STACK_OF(PKCS7_RECIP_INFO) *sk;

  if (p7 == NULL || ri == NULL) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  }

  switch (OBJ_obj2nid(p7->type)) {
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

  if (!sk_PKCS7_RECIP_INFO_push(sk, ri)) {
    return 0;
  }
  return 1;
}

int PKCS7_add_signer(PKCS7 *p7, PKCS7_SIGNER_INFO *p7i) {
  ASN1_OBJECT *obj;
  X509_ALGOR *alg;
  STACK_OF(PKCS7_SIGNER_INFO) *signer_sk;
  STACK_OF(X509_ALGOR) *md_sk;

  if (p7 == NULL || p7i == NULL) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  }

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
  // If the digest is not currently listed, add it
  int alg_found = 0;
  for (size_t i = 0; i < sk_X509_ALGOR_num(md_sk); i++) {
    alg = sk_X509_ALGOR_value(md_sk, i);
    if (OBJ_cmp(obj, alg->algorithm) == 0) {
      alg_found = 1;
      break;
    }
  }
  if (!alg_found) {
    if ((alg = X509_ALGOR_new()) == NULL ||
        (alg->parameter = ASN1_TYPE_new()) == NULL) {
      X509_ALGOR_free(alg);
      OPENSSL_PUT_ERROR(PKCS7, ERR_R_ASN1_LIB);
      return 0;
    }
    // If there is a constant copy of the ASN1 OBJECT in libcrypto, then
    // use that.  Otherwise, use a dynamically duplicated copy.
    int nid = OBJ_obj2nid(obj);
    if (nid != NID_undef) {
      alg->algorithm = OBJ_nid2obj(nid);
    } else {
      alg->algorithm = OBJ_dup(obj);
    }
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
  if (si == NULL) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_PASSED_NULL_PARAMETER);
    return NULL;
  }
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
  if (p7 == NULL || p7->d.ptr == NULL) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_PASSED_NULL_PARAMETER);
    return NULL;
  }

  switch (OBJ_obj2nid(p7->type)) {
    case NID_pkcs7_signed:
      return p7->d.sign->signer_info;
    case NID_pkcs7_signedAndEnveloped:
      return p7->d.signed_and_enveloped->signer_info;
    default:
      return NULL;
  }
}

int PKCS7_SIGNER_INFO_set(PKCS7_SIGNER_INFO *p7i, X509 *x509, EVP_PKEY *pkey,
                          const EVP_MD *dgst) {
  if (!p7i || !x509 || !pkey || !dgst) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  } else if (!ASN1_INTEGER_set(p7i->version, 1)) {
    return 0;
  } else if (!X509_NAME_set(&p7i->issuer_and_serial->issuer,
                            X509_get_issuer_name(x509))) {
    return 0;
  }

  ASN1_INTEGER_free(p7i->issuer_and_serial->serial);
  if (!(p7i->issuer_and_serial->serial =
            ASN1_INTEGER_dup(X509_get0_serialNumber(x509)))) {
    return 0;
  }

  // NOTE: OpenSSL does not free |p7i->pkey| before setting it. we do so here
  // to avoid potential memory leaks.
  EVP_PKEY_free(p7i->pkey);
  EVP_PKEY_up_ref(pkey);
  p7i->pkey = pkey;

  if (!X509_ALGOR_set0(p7i->digest_alg, OBJ_nid2obj(EVP_MD_type(dgst)),
                       V_ASN1_NULL, NULL)) {
    return 0;
  }

  switch (EVP_PKEY_id(pkey)) {
    case EVP_PKEY_EC:
    case EVP_PKEY_DH: {
      int snid, hnid;
      X509_ALGOR *alg1, *alg2;
      PKCS7_SIGNER_INFO_get0_algs(p7i, NULL, &alg1, &alg2);
      if (alg1 == NULL || alg1->algorithm == NULL) {
        return 0;
      }
      hnid = OBJ_obj2nid(alg1->algorithm);
      if (hnid == NID_undef ||
          !OBJ_find_sigid_by_algs(&snid, hnid, EVP_PKEY_id(pkey)) ||
          !X509_ALGOR_set0(alg2, OBJ_nid2obj(snid), V_ASN1_UNDEF, NULL)) {
        return 0;
      }
      break;
    }
    case EVP_PKEY_RSA:
    case EVP_PKEY_RSA_PSS: {
      X509_ALGOR *alg = NULL;
      PKCS7_SIGNER_INFO_get0_algs(p7i, NULL, NULL, &alg);
      if (alg != NULL) {
        return X509_ALGOR_set0(alg, OBJ_nid2obj(NID_rsaEncryption), V_ASN1_NULL,
                               NULL);
      }
      break;
    }
    default:
      OPENSSL_PUT_ERROR(PKCS7, PKCS7_R_SIGNING_NOT_SUPPORTED_FOR_THIS_KEY_TYPE);
      return 0;
  }

  return 1;
}

int PKCS7_RECIP_INFO_set(PKCS7_RECIP_INFO *p7i, X509 *x509) {
  if (!p7i || !x509) {
    OPENSSL_PUT_ERROR(PKCS7, ERR_R_PASSED_NULL_PARAMETER);
    return 0;
  }
  if (!ASN1_INTEGER_set(p7i->version, 0)) {
    return 0;
  } else if (!X509_NAME_set(&p7i->issuer_and_serial->issuer,
                            X509_get_issuer_name(x509))) {
    return 0;
  }

  ASN1_INTEGER_free(p7i->issuer_and_serial->serial);
  if (!(p7i->issuer_and_serial->serial =
            ASN1_INTEGER_dup(X509_get0_serialNumber(x509)))) {
    return 0;
  }

  EVP_PKEY *pkey = X509_get0_pubkey(x509);
  if (pkey == NULL) {
    return 0;
  }

  if (EVP_PKEY_id(pkey) == EVP_PKEY_RSA_PSS) {
    return 0;
  } else if (EVP_PKEY_id(pkey) == EVP_PKEY_RSA) {
    X509_ALGOR *alg;
    PKCS7_RECIP_INFO_get0_alg(p7i, &alg);
    if (!X509_ALGOR_set0(alg, OBJ_nid2obj(NID_rsaEncryption), V_ASN1_NULL,
                         NULL)) {
      return 0;
    }
  }

  // NOTE: OpenSSL does not free |p7i->cert| before setting it. we do so here
  // to avoid potential memory leaks.
  X509_free(p7i->cert);
  X509_up_ref(x509);
  p7i->cert = x509;

  return 1;
}

void PKCS7_SIGNER_INFO_get0_algs(PKCS7_SIGNER_INFO *si, EVP_PKEY **pk,
                                 X509_ALGOR **pdig, X509_ALGOR **psig) {
  if (!si) {
    return;
  }
  if (pk) {
    *pk = si->pkey;
  }
  if (pdig) {
    *pdig = si->digest_alg;
  }
  if (psig) {
    *psig = si->digest_enc_alg;
  }
}

void PKCS7_RECIP_INFO_get0_alg(PKCS7_RECIP_INFO *ri, X509_ALGOR **penc) {
  if (!ri) {
    return;
  }
  if (penc) {
    *penc = ri->key_enc_algor;
  }
}
