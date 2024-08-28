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

#ifndef OPENSSL_HEADER_PKCS7_H
#define OPENSSL_HEADER_PKCS7_H

#include <openssl/asn1.h>
#include <openssl/base.h>

#include <openssl/stack.h>

#if defined(__cplusplus)
extern "C" {
#endif


// PKCS#7.
//
// This library contains functions for extracting information from PKCS#7
// structures (RFC 2315).

DECLARE_STACK_OF(CRYPTO_BUFFER)
DECLARE_STACK_OF(X509)
DECLARE_STACK_OF(X509_CRL)

// PKCS7_get_raw_certificates parses a PKCS#7, SignedData structure from |cbs|
// and appends the included certificates to |out_certs|. It returns one on
// success and zero on error. |cbs| is advanced passed the structure.
//
// Note that a SignedData structure may contain no certificates, in which case
// this function succeeds but does not append any certificates. Additionally,
// certificates in SignedData structures are unordered. Callers should not
// assume a particular order in |*out_certs| and may need to search for matches
// or run path-building algorithms.
OPENSSL_EXPORT int PKCS7_get_raw_certificates(
    STACK_OF(CRYPTO_BUFFER) *out_certs, CBS *cbs, CRYPTO_BUFFER_POOL *pool);

// PKCS7_get_certificates behaves like |PKCS7_get_raw_certificates| but parses
// them into |X509| objects.
OPENSSL_EXPORT int PKCS7_get_certificates(STACK_OF(X509) *out_certs, CBS *cbs);

// PKCS7_bundle_raw_certificates appends a PKCS#7, SignedData structure
// containing |certs| to |out|. It returns one on success and zero on error.
// Note that certificates in SignedData structures are unordered. The order in
// |certs| will not be preserved.
OPENSSL_EXPORT int PKCS7_bundle_raw_certificates(
    CBB *out, const STACK_OF(CRYPTO_BUFFER) *certs);

// PKCS7_bundle_certificates behaves like |PKCS7_bundle_raw_certificates| but
// takes |X509| objects as input.
OPENSSL_EXPORT int PKCS7_bundle_certificates(CBB *out,
                                             const STACK_OF(X509) *certs);

// PKCS7_get_CRLs parses a PKCS#7, SignedData structure from |cbs| and appends
// the included CRLs to |out_crls|. It returns one on success and zero on error.
// |cbs| is advanced passed the structure.
//
// Note that a SignedData structure may contain no CRLs, in which case this
// function succeeds but does not append any CRLs. Additionally, CRLs in
// SignedData structures are unordered. Callers should not assume an order in
// |*out_crls| and may need to search for matches.
OPENSSL_EXPORT int PKCS7_get_CRLs(STACK_OF(X509_CRL) *out_crls, CBS *cbs);

// PKCS7_bundle_CRLs appends a PKCS#7, SignedData structure containing
// |crls| to |out|. It returns one on success and zero on error. Note that CRLs
// in SignedData structures are unordered. The order in |crls| will not be
// preserved.
OPENSSL_EXPORT int PKCS7_bundle_CRLs(CBB *out, const STACK_OF(X509_CRL) *crls);

// PKCS7_get_PEM_certificates reads a PEM-encoded, PKCS#7, SignedData structure
// from |pem_bio| and appends the included certificates to |out_certs|. It
// returns one on success and zero on error.
//
// Note that a SignedData structure may contain no certificates, in which case
// this function succeeds but does not append any certificates. Additionally,
// certificates in SignedData structures are unordered. Callers should not
// assume a particular order in |*out_certs| and may need to search for matches
// or run path-building algorithms.
OPENSSL_EXPORT int PKCS7_get_PEM_certificates(STACK_OF(X509) *out_certs,
                                              BIO *pem_bio);

// PKCS7_get_PEM_CRLs reads a PEM-encoded, PKCS#7, SignedData structure from
// |pem_bio| and appends the included CRLs to |out_crls|. It returns one on
// success and zero on error.
//
// Note that a SignedData structure may contain no CRLs, in which case this
// function succeeds but does not append any CRLs. Additionally, CRLs in
// SignedData structures are unordered. Callers should not assume an order in
// |*out_crls| and may need to search for matches.
OPENSSL_EXPORT int PKCS7_get_PEM_CRLs(STACK_OF(X509_CRL) *out_crls,
                                      BIO *pem_bio);


// Deprecated functions.
//
// These functions are a compatibility layer over a subset of OpenSSL's PKCS#7
// API. It intentionally does not implement the whole thing, only the minimum
// needed to build cryptography.io and CRuby.

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-7
//
//   ContentInfo ::= SEQUENCE {
//     contentType ContentType,
//     content
//       [0] EXPLICIT ANY DEFINED BY contentType OPTIONAL }
//
//   ContentType ::= OBJECT IDENTIFIER
struct pkcs7_st {
  // Unlike OpenSSL, the following fields are immutable. They filled in when the
  // object is parsed and ignored in serialization.
  ASN1_OBJECT *type;
  union {
    char *ptr;
    ASN1_OCTET_STRING *data;
    PKCS7_SIGNED *sign;
    PKCS7_ENVELOPE *enveloped;
    PKCS7_SIGN_ENVELOPE *signed_and_enveloped;
    PKCS7_DIGEST *digest;
    PKCS7_ENCRYPT *encrypted;
    ASN1_TYPE *other;
  } d;
};

// ASN.1 defined here https://datatracker.ietf.org/doc/html/rfc2315#section-9.1
//
//   SignedData ::= SEQUENCE {
//     version Version,
//     digestAlgorithms DigestAlgorithmIdentifiers,
//     contentInfo ContentInfo,
//     certificates
//        [0] IMPLICIT ExtendedCertificatesAndCertificates
//          OPTIONAL,
//     crls
//       [1] IMPLICIT CertificateRevocationLists OPTIONAL,
//     signerInfos SignerInfos }
//
//   DigestAlgorithmIdentifiers ::=
//
//     SET OF DigestAlgorithmIdentifier
//
//   SignerInfos ::= SET OF SignerInfo
struct pkcs7_signed_st {
  ASN1_INTEGER *version;
  STACK_OF(X509_ALGOR) *md_algs;
  PKCS7 *contents;
  STACK_OF(X509) *cert;
  STACK_OF(X509_CRL) *crl;
  STACK_OF(PKCS7_SIGNER_INFO) *signer_info;
};

// Only declare ASN1 functions or define stacks publibly if needed by supported
// projects that depend on them.
DECLARE_ASN1_FUNCTIONS(PKCS7)
DECLARE_ASN1_FUNCTIONS(PKCS7_RECIP_INFO)
DECLARE_ASN1_FUNCTIONS(PKCS7_SIGNER_INFO)

DEFINE_STACK_OF(PKCS7_RECIP_INFO)
DEFINE_STACK_OF(PKCS7_SIGNER_INFO)

// PKCS7_dup returns a newly allocated copy of |p7| without deep-copying
// internal references.
OPENSSL_EXPORT PKCS7 *PKCS7_dup(PKCS7 * p7);

// d2i_PKCS7_bio behaves like |d2i_PKCS7| but reads the input from |bio|.  If
// the length of the object is indefinite the full contents of |bio| are read.
//
// If the function fails then some unknown amount of data may have been read
// from |bio|.
OPENSSL_EXPORT PKCS7 *d2i_PKCS7_bio(BIO *bio, PKCS7 **out);

// i2d_PKCS7_bio writes |p7| to |bio|. It returns one on success and zero on
// error.
OPENSSL_EXPORT int i2d_PKCS7_bio(BIO *bio, const PKCS7 *p7);

// PKCS7_type_is_data returns 1 if |p7| is of type data
OPENSSL_EXPORT int PKCS7_type_is_data(const PKCS7 *p7);

// PKCS7_type_is_digest returns 1 if |p7| is of type digest
OPENSSL_EXPORT int PKCS7_type_is_digest(const PKCS7 *p7);

// PKCS7_type_is_encrypted returns 1 if |p7| is of type encrypted
OPENSSL_EXPORT int PKCS7_type_is_encrypted(const PKCS7 *p7);

// PKCS7_type_is_enveloped returns 1 if |p7| is of type enveloped
OPENSSL_EXPORT int PKCS7_type_is_enveloped(const PKCS7 *p7);

// PKCS7_type_is_signed returns 1 if |p7| is of type signed
OPENSSL_EXPORT int PKCS7_type_is_signed(const PKCS7 *p7);

// PKCS7_type_is_signedAndEnveloped returns 1 if |p7| is of type
// signedAndEnveloped
OPENSSL_EXPORT int PKCS7_type_is_signedAndEnveloped(const PKCS7 *p7);


// PKCS7_sign [Deprecated]
//
// Only |PKCS7_DETACHED| and a combination of
// "PKCS7_DETACHED|PKCS7_BINARY|PKCS7_NOATTR|PKCS7_PARTIAL" is supported.
// See |PKCS7_sign| for more details.

// PKCS7_DETACHED indicates that the PKCS#7 file specifies its data externally.
#define PKCS7_DETACHED 0x40

// PKCS7_BINARY disables the default translation to MIME canonical format (as
// required by the S/MIME specifications).
// Must be used as "PKCS7_DETACHED|PKCS7_BINARY|PKCS7_NOATTR|PKCS7_PARTIAL".
#define PKCS7_BINARY 0x80

// PKCS7_NOATTR disables usage of authenticatedAttributes.
// Must be used as "PKCS7_DETACHED|PKCS7_BINARY|PKCS7_NOATTR|PKCS7_PARTIAL".
#define PKCS7_NOATTR 0x100

// PKCS7_PARTIAL outputs a partial PKCS7 structure which additional signers and
// capabilities can be added before finalization.
// Must be used as "PKCS7_DETACHED|PKCS7_BINARY|PKCS7_NOATTR|PKCS7_PARTIAL".
#define PKCS7_PARTIAL 0x4000

// PKCS7_TEXT prepends MIME headers for type text/plain to the data. Using this
// will fail |PKCS7_sign|.
#define PKCS7_TEXT 0x1

// PKCS7_NOCERTS excludes the signer's certificate and the extra certs defined
// from the PKCS7 structure. Using this will fail |PKCS7_sign|.
#define PKCS7_NOCERTS 0x2

// PKCS7_NOSMIMECAP omits SMIMECapabilities. Using this will fail |PKCS7_sign|.
#define PKCS7_NOSMIMECAP 0x200

// PKCS7_STREAM returns a PKCS7 structure just initialized to perform the
// signing operation. Signing is not performed yet. Using this will fail
// |PKCS7_sign|.
#define PKCS7_STREAM 0x1000

// The following flags are used with |PKCS7_verify| (not implemented).
#define PKCS7_NOSIGS 0x4
#define PKCS7_NOCHAIN 0x8
#define PKCS7_NOINTERN 0x10
#define PKCS7_NOVERIFY 0x20

// PKCS7_sign can operate in two modes to provide some backwards compatibility:
//
// The first mode assembles |certs| into a PKCS#7 signed data ContentInfo with
// external data and no signatures. It returns a newly-allocated |PKCS7| on
// success or NULL on error. |sign_cert| and |pkey| must be NULL. |data| is
// ignored. |flags| must be equal to |PKCS7_DETACHED|. Additionally,
// certificates in SignedData structures are unordered. The order of |certs|
// will not be preserved.
//
// The second mode generates a detached RSA SHA-256 signature of |data| using
// |pkey| and produces a PKCS#7 SignedData structure containing it. |certs|
// must be NULL and |flags| must be exactly |PKCS7_NOATTR | PKCS7_BINARY |
// PKCS7_NOCERTS | PKCS7_DETACHED|.
//
// Note this function only implements a subset of the corresponding OpenSSL
// function. It is provided for backwards compatibility only.
OPENSSL_EXPORT OPENSSL_DEPRECATED PKCS7 *PKCS7_sign(X509 *sign_cert,
                                                    EVP_PKEY *pkey,
                                                    STACK_OF(X509) *certs,
                                                    BIO *data, int flags);


#if defined(__cplusplus)
}  // extern C

extern "C++" {
BSSL_NAMESPACE_BEGIN

BORINGSSL_MAKE_DELETER(PKCS7, PKCS7_free)

BSSL_NAMESPACE_END
}  // extern C++
#endif

#define PKCS7_R_BAD_PKCS7_VERSION 100
#define PKCS7_R_NOT_PKCS7_SIGNED_DATA 101
#define PKCS7_R_NO_CERTIFICATES_INCLUDED 102
#define PKCS7_R_NO_CRLS_INCLUDED 103

#endif  // OPENSSL_HEADER_PKCS7_H
