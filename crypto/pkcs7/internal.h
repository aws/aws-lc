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

#ifndef OPENSSL_HEADER_PKCS7_INTERNAL_H
#define OPENSSL_HEADER_PKCS7_INTERNAL_H

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif


typedef struct pkcs7_issuer_and_serial_st PKCS7_ISSUER_AND_SERIAL;
typedef struct pkcs7_enc_content_st PKCS7_ENC_CONTENT;

DECLARE_ASN1_FUNCTIONS(PKCS7_ISSUER_AND_SERIAL)
DECLARE_ASN1_FUNCTIONS(PKCS7_SIGNED)
DECLARE_ASN1_FUNCTIONS(PKCS7_ENC_CONTENT)
DECLARE_ASN1_FUNCTIONS(PKCS7_ENCRYPT)
DECLARE_ASN1_FUNCTIONS(PKCS7_ENVELOPE)
DECLARE_ASN1_FUNCTIONS(PKCS7_DIGEST)
DECLARE_ASN1_FUNCTIONS(PKCS7_SIGN_ENVELOPE)

DEFINE_STACK_OF(PKCS7)

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-11.1
//
//   SignedAndEnvelopedData ::= SEQUENCE {
//     version Version,
//     recipientInfos RecipientInfos,
//     digestAlgorithms DigestAlgorithmIdentifiers,
//     encryptedContentInfo EncryptedContentInfo,
//     certificates
//        [0] IMPLICIT ExtendedCertificatesAndCertificates
//          OPTIONAL,
//     crls
//       [1] IMPLICIT CertificateRevocationLists OPTIONAL,
//     signerInfos SignerInfos }
struct pkcs7_sign_envelope_st {
  ASN1_INTEGER *version;
  STACK_OF(PKCS7_RECIP_INFO) *recipientinfo;
  STACK_OF(X509_ALGOR) *md_algs;
  PKCS7_ENC_CONTENT *enc_data;
  STACK_OF(X509) *cert;
  STACK_OF(X509_CRL) *crl;
  STACK_OF(PKCS7_SIGNER_INFO) *signer_info;
};

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-6.7
//
//   IssuerAndSerialNumber ::= SEQUENCE {
//     issuer Name,
//     serialNumber CertificateSerialNumber }
struct pkcs7_issuer_and_serial_st {
  X509_NAME *issuer;
  ASN1_INTEGER *serial;
};

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-9.2
//
//   SignerInfo ::= SEQUENCE {
//     version Version,
//     issuerAndSerialNumber IssuerAndSerialNumber,
//     digestAlgorithm DigestAlgorithmIdentifier,
//     authenticatedAttributes
//       [0] IMPLICIT Attributes OPTIONAL,
//     digestEncryptionAlgorithm
//       DigestEncryptionAlgorithmIdentifier,
//     encryptedDigest EncryptedDigest,
//     unauthenticatedAttributes
//       [1] IMPLICIT Attributes OPTIONAL }
//
//   EncryptedDigest ::= OCTET STRING
struct pkcs7_signer_info_st {
  ASN1_INTEGER *version;
  PKCS7_ISSUER_AND_SERIAL *issuer_and_serial;
  X509_ALGOR *digest_alg;
  STACK_OF(X509_ATTRIBUTE) *auth_attr;
  X509_ALGOR *digest_enc_alg;
  ASN1_OCTET_STRING *enc_digest;
  STACK_OF(X509_ATTRIBUTE) *unauth_attr;
  EVP_PKEY *pkey;  // NOTE: |pkey| is not seriliazed.
};

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-10.2
//
//   RecipientInfo ::= SEQUENCE {
//     version Version,
//     issuerAndSerialNumber IssuerAndSerialNumber,
//     keyEncryptionAlgorithm
//
//       KeyEncryptionAlgorithmIdentifier,
//     encryptedKey EncryptedKey }
//
//   EncryptedKey ::= OCTET STRING
struct pkcs7_recip_info_st {
  ASN1_INTEGER *version;
  PKCS7_ISSUER_AND_SERIAL *issuer_and_serial;
  X509_ALGOR *key_enc_algor;
  ASN1_OCTET_STRING *enc_key;
  X509 *cert;  // NOTE: |cert| is not serialized
};

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-10.1
//
//   EncryptedContentInfo ::= SEQUENCE {
//     contentType ContentType,
//     contentEncryptionAlgorithm
//       ContentEncryptionAlgorithmIdentifier,
//     encryptedContent
//       [0] IMPLICIT EncryptedContent OPTIONAL }
//
//   EncryptedContent ::= OCTET STRING
struct pkcs7_enc_content_st {
  ASN1_OBJECT *content_type;
  X509_ALGOR *algorithm;
  ASN1_OCTET_STRING *enc_data;
  const EVP_CIPHER *cipher;  // NOTE: |cipher| is not serialized
};

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-10.1
//
//    EnvelopedData ::= SEQUENCE {
//      version Version,
//      recipientInfos RecipientInfos,
//      encryptedContentInfo EncryptedContentInfo }
//
//    RecipientInfos ::= SET OF RecipientInfo
struct pkcs7_envelope_st {
  ASN1_INTEGER *version;
  PKCS7_ENC_CONTENT *enc_data;
  STACK_OF(PKCS7_RECIP_INFO) *recipientinfo;
};

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-12
//
//   DigestedData ::= SEQUENCE {
//     version Version,
//     digestAlgorithm DigestAlgorithmIdentifier,
//     contentInfo ContentInfo,
//     digest Digest }
//
//   Digest ::= OCTET STRING
struct pkcs7_digest_st {
  ASN1_INTEGER *version;
  X509_ALGOR *digest_alg;
  PKCS7 *contents;
  ASN1_OCTET_STRING *digest;
  const EVP_MD *md;  // NOTE: |md| is not serialized
};

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-13
//
//   EncryptedData ::= SEQUENCE {
//     version Version,
//     encryptedContentInfo EncryptedContentInfo }
struct pkcs7_encrypt_st {
  ASN1_INTEGER *version;
  PKCS7_ENC_CONTENT *enc_data;
};

// pkcs7_parse_header reads the non-certificate/non-CRL prefix of a PKCS#7
// SignedData blob from |cbs| and sets |*out| to point to the rest of the
// input. If the input is in BER format, then |*der_bytes| will be set to a
// pointer that needs to be freed by the caller once they have finished
// processing |*out| (which will be pointing into |*der_bytes|).
//
// It returns one on success or zero on error. On error, |*der_bytes| is
// NULL.
int pkcs7_parse_header(uint8_t **der_bytes, CBS *out, CBS *cbs);

// pkcs7_add_signed_data writes a PKCS#7, SignedData structure to |out|. While
// doing so it makes callbacks to let the caller fill in parts of the structure.
// All callbacks are ignored if NULL and return one on success or zero on error.
//
//   digest_algos_cb: may write AlgorithmIdentifiers into the given CBB, which
//       is a SET of digest algorithms.
//   cert_crl_cb: may write the |certificates| or |crls| fields.
//       (See https://datatracker.ietf.org/doc/html/rfc2315#section-9.1)
//   signer_infos_cb: may write the contents of the |signerInfos| field.
//       (See https://datatracker.ietf.org/doc/html/rfc2315#section-9.1)
//
// pkcs7_add_signed_data returns one on success or zero on error.
int pkcs7_add_signed_data(CBB *out,
                          int (*digest_algos_cb)(CBB *out, const void *arg),
                          int (*cert_crl_cb)(CBB *out, const void *arg),
                          int (*signer_infos_cb)(CBB *out, const void *arg),
                          const void *arg);


#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_PKCS7_INTERNAL_H
