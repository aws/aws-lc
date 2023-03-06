/*
 * Copyright 2015-2021 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the Apache License 2.0 (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#ifndef AWSLC_OCSP_H
#define AWSLC_OCSP_H

#include <openssl/asn1t.h>
#include <openssl/safestack.h>
#include <openssl/x509.h>
#include <openssl/x509v3.h>

#ifdef __cplusplus
extern "C" {
#endif

// Various OCSP flags and values
//
// OCSP_NOCERTS is for |OCSP_request_sign| if no certificates are included
// in the |OCSP_REQUEST|. Certificates are optional.
#define OCSP_NOCERTS 0x1
// OCSP_NOINTERN is for |OCSP_basic_verify|. Searches for certificates the
// responder may have included in |bs| will be done, unless the flags contain
// OCSP_NOINTERN.
#define OCSP_NOINTERN 0x2
// OCSP_NOCHAIN is for |OCSP_basic_verify|. All certificates in |certs| and in
// |bs| are considered as untrusted certificates for the construction of the
// validation path for the signer certificate unless the OCSP_NOCHAIN flag is
// set.
#define OCSP_NOCHAIN 0x8
// OCSP_NOINTERN is for |OCSP_basic_verify|. We will check for explicit trust
// for OCSP signing in the root CA certificate, unless the flags contain
// OCSP_NOEXPLICIT.
#define OCSP_NOEXPLICIT 0x20


typedef struct ocsp_cert_id_st OCSP_CERTID;
typedef struct ocsp_one_request_st OCSP_ONEREQ;
typedef struct ocsp_req_info_st OCSP_REQINFO;
typedef struct ocsp_req_ctx_st OCSP_REQ_CTX;
typedef struct ocsp_signature_st OCSP_SIGNATURE;
typedef struct ocsp_request_st OCSP_REQUEST;
typedef struct ocsp_resp_bytes_st OCSP_RESPBYTES;
typedef struct ocsp_revoked_info_st OCSP_REVOKEDINFO;
typedef struct ocsp_cert_status_st OCSP_CERTSTATUS;
typedef struct ocsp_single_response_st OCSP_SINGLERESP;
typedef struct ocsp_response_data_st OCSP_RESPDATA;
typedef struct ocsp_response_st OCSP_RESPONSE;
typedef struct ocsp_responder_id_st OCSP_RESPID;
typedef struct ocsp_basic_response_st OCSP_BASICRESP;

DEFINE_STACK_OF(OCSP_CERTID)
DEFINE_STACK_OF(OCSP_ONEREQ)
DEFINE_STACK_OF(OCSP_RESPID)
DEFINE_STACK_OF(OCSP_SINGLERESP)

DECLARE_ASN1_FUNCTIONS(OCSP_BASICRESP)
DECLARE_ASN1_FUNCTIONS(OCSP_RESPONSE)
DECLARE_ASN1_FUNCTIONS(OCSP_CERTID)
DECLARE_ASN1_FUNCTIONS(OCSP_REQUEST)

// OCSP_sendreq_bio is a blocking OCSP request handler which is a special case
// of non-blocking I/O.
// |OCSP_sendreq_bio| combines |OCSP_sendreq_new| with as many calls of
// |OCSP_sendreq_nbio| as needed and then |OCSP_REQ_CTX_free|, with a response
// header maximum line length of 4k. It waits indefinitely on a response, if
// |BIO_should_retry| is true and the |BIO| persists.
//
// WARNING: This is retained only for compatibility. This does not support
// setting a timeout or adding your own HTTP headers.
// Use |OCSP_sendreq_nbio| and handle the timeout accordingly to the |BIO| type.
// You can also use |OCSP_REQ_CTX_add1_header| to add your own HTTP headers.
OPENSSL_EXPORT OCSP_RESPONSE *OCSP_sendreq_bio(BIO *b, const char *path,
                                               OCSP_REQUEST *req);

// OCSP_sendreq_new returns an |OCSP_REQ_CTX| structure using the responder io,
// the URL path, the |OCSP_REQUEST| req to be sent, and with a response header
// maximum line length of maxline. If maxline is zero or less, a default value
// of 4k is used. The |OCSP_REQUEST| req may be set to NULL and provided later
// if required.
OPENSSL_EXPORT OCSP_REQ_CTX *OCSP_sendreq_new(BIO *io, const char *path,
                                              OCSP_REQUEST *req, int maxline);

// OCSP_sendreq_nbio attempts to send the request prepared in |rctx| and to
// gather the response via HTTP, using the |BIO| io and path that were given
// when calling |OCSP_sendreq_new|.
OPENSSL_EXPORT int OCSP_sendreq_nbio(OCSP_RESPONSE **presp, OCSP_REQ_CTX *rctx);

// OCSP_REQ_CTX_new creates a new |OCSP_REQ_CTX|. |OCSP_REQ_CTX| is used to
// contain the information to send the OCSP request and gather the response
// over HTTP.
OPENSSL_EXPORT OCSP_REQ_CTX *OCSP_REQ_CTX_new(BIO *io, int maxline);

// OCSP_REQ_CTX_free frees the memory allocated by |OCSP_REQ_CTX|.
OPENSSL_EXPORT void OCSP_REQ_CTX_free(OCSP_REQ_CTX *rctx);

// OCSP_set_max_response_length sets the maximum response length for an OCSP
// request over HTTP to |len|. If a custom max response length is needed, this
// should be set before |OCSP_REQ_CTX| is sent out to retrieve the OCSP
// response.
OPENSSL_EXPORT void OCSP_set_max_response_length(OCSP_REQ_CTX *rctx,
                                                 unsigned long len);

// OCSP_REQ_CTX_http adds the HTTP request line to the context.
OPENSSL_EXPORT int OCSP_REQ_CTX_http(OCSP_REQ_CTX *rctx, const char *op,
                                     const char *path);

// OCSP_REQ_CTX_set1_req finalizes the HTTP request context. It is needed if
// an ASN.1-encoded request should be sent.
OPENSSL_EXPORT int OCSP_REQ_CTX_set1_req(OCSP_REQ_CTX *rctx, OCSP_REQUEST *req);

// OCSP_REQ_CTX_add1_header adds header name with value |value| to the
// context |rctx|. It can be called  more than once to add multiple header
// lines.
OPENSSL_EXPORT int OCSP_REQ_CTX_add1_header(OCSP_REQ_CTX *rctx,
                                            const char *name,
                                            const char *value);

// OCSP_request_add0_id adds |cid| to |req|. Returns the new |OCSP_ONEREQ|
// pointer allocated on the stack within |req|. This is useful if we want to
// add extensions.
// WARNING: This allocates a new |OCSP_ONEREQ| and assigns the  pointer to |cid|
// to it. It then adds the newly allocated |OCSP_ONEREQ| to the stack within
// |req|. |req| now takes ownership of |cid|, and also maintains ownership of
// the pointer to |OCSP_ONEREQ|.
OPENSSL_EXPORT OCSP_ONEREQ *OCSP_request_add0_id(OCSP_REQUEST *req,
                                                 OCSP_CERTID *cid);

// OCSP_request_set1_name sets |requestorName| from an |X509_NAME| structure.
OPENSSL_EXPORT int OCSP_request_set1_name(OCSP_REQUEST *req, X509_NAME *nm);

// OCSP_request_add1_cert adds a certificate to an |OCSP_REQUEST|.
OPENSSL_EXPORT int OCSP_request_add1_cert(OCSP_REQUEST *req, X509 *cert);

// OCSP_request_sign signs an |OCSP_REQUEST|. Signing also sets the
// |requestorName| to the subject name of an optional signers certificate and
// includes one or more optional certificates in the request.
// This will fail if a signature in the |OCSP_REQUEST| already exists.
OPENSSL_EXPORT int OCSP_request_sign(OCSP_REQUEST *req, X509 *signer,
                                     EVP_PKEY *key, const EVP_MD *dgst,
                                     STACK_OF(X509) *certs,
                                     unsigned long flags);

// OCSP_response_status returns response status from |OCSP_RESPONSE|.
OPENSSL_EXPORT int OCSP_response_status(OCSP_RESPONSE *resp);

// OCSP_response_get1_basic returns |OCSP_BASICRESP| from |OCSP_RESPONSE|.
OPENSSL_EXPORT OCSP_BASICRESP *OCSP_response_get1_basic(OCSP_RESPONSE *resp);

// OCSP_resp_find_status looks up a cert id and extract the update time and
// revocation status of  certificate sent back from OCSP responder if found.
// Returns 1 on success.
//
// Note: 1. Revocation status code is passed into |*status| parameter. Status
//          code will not be passed if |*status| is NULL.
OPENSSL_EXPORT int OCSP_resp_find_status(OCSP_BASICRESP *bs, OCSP_CERTID *id,
                                         int *status, int *reason,
                                         ASN1_GENERALIZEDTIME **revtime,
                                         ASN1_GENERALIZEDTIME **thisupd,
                                         ASN1_GENERALIZEDTIME **nextupd);

// OCSP_check_validity checks the validity of |thisUpdate| and |nextUpdate|
// fields from an |OCSP_SINGLERESP|.
//
// Note: It is possible that the request will take a few
// seconds to process and/or the time won't be totally accurate. Therefore,
// to avoid rejecting otherwise valid time we allow the times to be within
// |nsec| of the current time. Also, to avoid accepting very old responses
// without a |nextUpdate| field an optional |maxsec| parameter specifies the
// maximum age the |thisUpdate| field can be. |maxsec| should be set to "-1",
// if the maximum age should not be checked.
OPENSSL_EXPORT int OCSP_check_validity(ASN1_GENERALIZEDTIME *thisupd,
                                       ASN1_GENERALIZEDTIME *nextupd, long nsec,
                                       long maxsec);

// OCSP_basic_verify verifies a basic response message. Returns 1 if the
// response is valid, 0 if the signature cannot be verified, or -1 on fatal
// errors such as malloc failure.
//
// Note: 1. Checks that OCSP response CAN be verified, not that it has been
//          verified.
OPENSSL_EXPORT int OCSP_basic_verify(OCSP_BASICRESP *bs, STACK_OF(X509) *certs,
                                     X509_STORE *st, unsigned long flags);

// OCSP_cert_to_id returns a |OCSP_CERTID| converted from a certificate and
// its issuer.
//
// Note: 1. If subject is NULL, we get the subject name from the issuer and set
//          the serial number is NULL.
//       2. OpenSSL's legacy OCSP code decided to make sha1 as default hash
//          algorithm when the digest is set as NULL. We keep this to maintain
//          backwards compatibility, but strongly advise to set a digest when
//          using this function.
OPENSSL_EXPORT OCSP_CERTID *OCSP_cert_to_id(const EVP_MD *dgst,
                                            const X509 *subject,
                                            const X509 *issuer);

// OCSP_parse_url parses an OCSP responder URL and returns its component parts.
// |url| argument must be a null-terminated string containing the URL to be
// parsed. The other arguments are pointers to variables that will be set to the
// parsed components of the URL. When |OCSP_parse_url| returns 1, these
// arguments will allocate new memory with a copy of value. It is the caller's
// responsibility to free these.
//
//  |phost|: A pointer to a char pointer that will be set to the host component
//           of the URL. If the URL does not contain a host component, this will
//           be set to an empty string.
//  |pport|: A pointer to an int that will be set to the port number specified
//           in the URL, or to the default port (80 for HTTP, 443 for HTTPS)
//           if no port number is specified.
//  |ppath|: A pointer to a char pointer that will be set to the path component
//           of the URL. If the URL does not contain a path component, this
//           will be set to "/".
//  |pssl|:  A pointer to an int that will be set to 1 if the URL specifies the
//           HTTPS protocol, or 0 if HTTP.
//
// Note: |OCSP_parse_url| does not perform any validation of the URL or its
//        components beyond basic parsing. It is the responsibility of the
//        caller to ensure that the URL is well-formed and valid.
OPENSSL_EXPORT int OCSP_parse_url(const char *url, char **phost, char **pport,
                                  char **ppath, int *pssl);

// OCSP_response_status_str prints OCSP response status in a string.
OPENSSL_EXPORT const char *OCSP_response_status_str(long s);

// OCSP_cert_status_str prints OCSP cert status in a string.
OPENSSL_EXPORT const char *OCSP_cert_status_str(long s);


#ifdef __cplusplus
}
#endif

#if !defined(BORINGSSL_NO_CXX)
extern "C++" {

BSSL_NAMESPACE_BEGIN

BORINGSSL_MAKE_DELETER(OCSP_REQUEST, OCSP_REQUEST_free)
BORINGSSL_MAKE_DELETER(OCSP_REQ_CTX, OCSP_REQ_CTX_free)
BORINGSSL_MAKE_DELETER(OCSP_RESPONSE, OCSP_RESPONSE_free)
BORINGSSL_MAKE_DELETER(OCSP_BASICRESP, OCSP_BASICRESP_free)
BORINGSSL_MAKE_DELETER(OCSP_CERTID, OCSP_CERTID_free)

BSSL_NAMESPACE_END

}  // extern C++
#endif  // !BORINGSSL_NO_CXX

#define OCSP_RESPONSE_STATUS_SUCCESSFUL 0
#define OCSP_RESPONSE_STATUS_MALFORMEDREQUEST 1
#define OCSP_RESPONSE_STATUS_INTERNALERROR 2
#define OCSP_RESPONSE_STATUS_TRYLATER 3
#define OCSP_RESPONSE_STATUS_SIGREQUIRED 5
#define OCSP_RESPONSE_STATUS_UNAUTHORIZED 6

#define V_OCSP_RESPID_NAME 0
#define V_OCSP_RESPID_KEY 1

#define V_OCSP_CERTSTATUS_GOOD 0
#define V_OCSP_CERTSTATUS_REVOKED 1
#define V_OCSP_CERTSTATUS_UNKNOWN 2

#define OCSP_R_CERTIFICATE_VERIFY_ERROR 101
#define OCSP_R_DIGEST_ERR 102
#define OCSP_R_MISSING_OCSPSIGNING_USAGE 103
#define OCSP_R_NOT_BASIC_RESPONSE 104
#define OCSP_R_NO_CERTIFICATES_IN_CHAIN 105
#define OCSP_R_NO_RESPONSE_DATA 108
#define OCSP_R_PRIVATE_KEY_DOES_NOT_MATCH_CERTIFICATE 110
#define OCSP_R_RESPONSE_CONTAINS_NO_REVOCATION_DATA 111
#define OCSP_R_ROOT_CA_NOT_TRUSTED 112
#define OCSP_R_SERVER_RESPONSE_PARSE_ERROR 115
#define OCSP_R_SIGNATURE_FAILURE 117
#define OCSP_R_SIGNER_CERTIFICATE_NOT_FOUND 118
#define OCSP_R_UNKNOWN_MESSAGE_DIGEST 119
#define OCSP_R_UNKNOWN_NID 120
#define OCSP_R_ERROR_PARSING_URL 121
#define OCSP_R_ERROR_IN_NEXTUPDATE_FIELD 122
#define OCSP_R_ERROR_IN_THISUPDATE_FIELD 123
#define OCSP_R_NEXTUPDATE_BEFORE_THISUPDATE 124
#define OCSP_R_STATUS_EXPIRED 125
#define OCSP_R_STATUS_NOT_YET_VALID 126
#define OCSP_R_STATUS_TOO_OLD 127
#define OCSP_R_NO_SIGNER_KEY 130
#define OCSP_R_OCSP_REQUEST_DUPLICATE_SIGNATURE 131

#endif  // AWSLC_OCSP_H
