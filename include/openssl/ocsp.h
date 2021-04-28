/*
 * Copyright 2000-2020 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the Apache License 2.0 (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

//
// Created by Chiang, Samuel on 4/22/21.
//

#ifndef AWSLC_OCSP_H
#define AWSLC_OCSP_H

# pragma once

#  include <openssl/asn1t.h>
#  include <openssl/x509.h>
#  include <openssl/x509v3.h>
#  include <openssl/safestack.h>

/*-
 *   CRLReason ::= ENUMERATED {
 *        unspecified             (0),
 *        keyCompromise           (1),
 *        cACompromise            (2),
 *        affiliationChanged      (3),
 *        superseded              (4),
 *        cessationOfOperation    (5),
 *        certificateHold         (6),
 *        -- value 7 is not used
 *        removeFromCRL           (8),
 *        privilegeWithdrawn      (9),
 *        aACompromise           (10) }
 */
# define OCSP_REVOKED_STATUS_NOSTATUS                -1
# define OCSP_REVOKED_STATUS_UNSPECIFIED             0
# define OCSP_REVOKED_STATUS_KEYCOMPROMISE           1
# define OCSP_REVOKED_STATUS_CACOMPROMISE            2
# define OCSP_REVOKED_STATUS_AFFILIATIONCHANGED      3
# define OCSP_REVOKED_STATUS_SUPERSEDED              4
# define OCSP_REVOKED_STATUS_CESSATIONOFOPERATION    5
# define OCSP_REVOKED_STATUS_CERTIFICATEHOLD         6
# define OCSP_REVOKED_STATUS_REMOVEFROMCRL           8
# define OCSP_REVOKED_STATUS_PRIVILEGEWITHDRAWN      9
# define OCSP_REVOKED_STATUS_AACOMPROMISE            10


/* Various flags and values */
#  define OCSP_NOCERTS                    0x1
#  define OCSP_NOINTERN                   0x2
#  define OCSP_NOSIGS                     0x4
#  define OCSP_NOCHAIN                    0x8
#  define OCSP_NOVERIFY                   0x10
#  define OCSP_NOEXPLICIT                 0x20
#  define OCSP_NOCASIGN                   0x40
#  define OCSP_NODELEGATED                0x80
#  define OCSP_NOCHECKS                   0x100
#  define OCSP_TRUSTOTHER                 0x200
#  define OCSP_RESPID_KEY                 0x400
#  define OCSP_NOTIME                     0x800

/* Time used by default for nextUpdate if none provided in OCSP: 1 hour since thisUpdate. */
#define DEFAULT_OCSP_NEXT_UPDATE_PERIOD 3600000000000

typedef struct ocsp_cert_id_st OCSP_CERTID;
typedef struct ocsp_responder_id_st OCSP_RESPID;
typedef struct ocsp_signature_st OCSP_SIGNATURE;
typedef struct ocsp_resp_bytes_st OCSP_RESPBYTES;
typedef struct ocsp_revoked_info_st OCSP_REVOKEDINFO;
typedef struct ocsp_cert_status_st OCSP_CERTSTATUS;
typedef struct ocsp_single_response_st OCSP_SINGLERESP;
typedef struct ocsp_response_data_st OCSP_RESPDATA;
typedef struct ocsp_response_st OCSP_RESPONSE;
typedef struct ocsp_basic_response_st OCSP_BASICRESP;

DEFINE_STACK_OF(OCSP_CERTID)
DEFINE_STACK_OF(OCSP_RESPID)
DEFINE_STACK_OF(OCSP_SINGLERESP)

/* return values to support s2n */
#define S2N_CERT_OK 0
#define S2N_CERT_ERR_UNTRUSTED -1
#define S2N_CERT_ERR_REVOKED -2
#define S2N_CERT_ERR_EXPIRED -3
#define S2N_CERT_ERR_TYPE_UNSUPPORTED -4
#define S2N_CERT_ERR_INVALID -5
#define S2N_CERT_ERR_MAX_CHAIN_DEPTH_EXCEEDED -6

/* for ocsp resp status */
#  define OCSP_RESPONSE_STATUS_SUCCESSFUL           0
#  define OCSP_RESPONSE_STATUS_MALFORMEDREQUEST     1
#  define OCSP_RESPONSE_STATUS_INTERNALERROR        2
#  define OCSP_RESPONSE_STATUS_TRYLATER             3
#  define OCSP_RESPONSE_STATUS_SIGREQUIRED          5
#  define OCSP_RESPONSE_STATUS_UNAUTHORIZED         6

/* for ocsp resp id  */
#  define V_OCSP_RESPID_NAME 0
#  define V_OCSP_RESPID_KEY  1

/* for certificate status */
#  define V_OCSP_CERTSTATUS_GOOD    0
#  define V_OCSP_CERTSTATUS_REVOKED 1
#  define V_OCSP_CERTSTATUS_UNKNOWN 2


/* DECLARE_ASN1_DUP_FUNCTION_name(OCSP_CERTID)  */
DECLARE_ASN1_FUNCTIONS(OCSP_SINGLERESP)
DECLARE_ASN1_FUNCTIONS(OCSP_CERTSTATUS)
DECLARE_ASN1_FUNCTIONS(OCSP_REVOKEDINFO)
DECLARE_ASN1_FUNCTIONS(OCSP_BASICRESP)
DECLARE_ASN1_FUNCTIONS(OCSP_RESPDATA)
DECLARE_ASN1_FUNCTIONS(OCSP_RESPID)
DECLARE_ASN1_FUNCTIONS(OCSP_RESPONSE)
DECLARE_ASN1_FUNCTIONS(OCSP_RESPBYTES)
DECLARE_ASN1_FUNCTIONS(OCSP_CERTID)
DECLARE_ASN1_FUNCTIONS(OCSP_SIGNATURE)


/* wrapper functions for entire OCSP functionality */
/* we take time in nanoseconds */
int s2n_ocsp_validate_ocsp_response(const uint8_t *ocsp_response_raw,
                                    uint32_t ocsp_response_length,
                                    STACK_OF(X509) *cert_chain,
                                    X509_STORE *trust_store,
                                    uint64_t *current_time);


/* FUNCTIONS FOR OCSP_RESPONSE */

/* get OCSP_RESPONSE's response status */
int OCSP_response_status(OCSP_RESPONSE *resp, int64_t *resp_status);

/* extract OCSP_BASICRESP in OCSP_RESPONSE */
int OCSP_response_get1_basic(OCSP_RESPONSE *resp, OCSP_BASICRESP **basic_resp);



/* FUNCTIONS FOR OCSP_BASICRESP */

/* get number of OCSP_SINGLERESPs in OCSP_BASICRESP */
int OCSP_resp_count(OCSP_BASICRESP *bs, int *count);

/* extract OCSP_SINGLERESP in the index of OCSP_BASICRESP */
int OCSP_resp_get0(OCSP_BASICRESP *bs, int idx, OCSP_SINGLERESP **single_resp);

/* extracts stack of X509 certificates from OCSP_BASICRESP */
int OCSP_resp_get0_certs(const OCSP_BASICRESP *bs, STACK_OF(X509) **bs_certs);

/* OCSP basic crypto checks on OCSP_BASICRESP */
int OCSP_basic_verify(OCSP_BASICRESP *bs, STACK_OF(X509) *certs,
                      X509_STORE *st, unsigned long flags);

/* adds an X509 certificate to OCSP_BASICRESP  */
int OCSP_basic_add1_cert(OCSP_BASICRESP *bs, X509 *cert);



/* FUNCTIONS FOR OCSP_SINGLERESP */

/* get OCSP_SINGLERESP's status */
int OCSP_single_get0_status(OCSP_SINGLERESP *single,int *status, int *reason,
                            ASN1_GENERALIZEDTIME **revtime,
                            ASN1_GENERALIZEDTIME **thisupd,
                            ASN1_GENERALIZEDTIME **nextupd);



/* FUNCTIONS FOR OTHER OCSP DATA STRUCTURES */
int OCSP_cert_to_id(const EVP_MD *dgst, X509 *subject, X509 *issuer, OCSP_CERTID **new_certid);

int OCSP_cert_id_new(const EVP_MD *dgst,
                     const X509_NAME *issuerName,
                     const ASN1_BIT_STRING *issuerKey,
                     const ASN1_INTEGER *serialNumber,
                     OCSP_CERTID **new_certid);

/* compares id issuer name hash and key hash */
int OCSP_id_issuer_cmp(const OCSP_CERTID *a, const OCSP_CERTID *b);


/* the functions below are not used in current version of s2n, but were found in new ocsp revision code */
int OCSP_resp_find_status(OCSP_BASICRESP *bs, OCSP_CERTID *id, int *status,
                          int *reason,
                          ASN1_GENERALIZEDTIME **revtime,
                          ASN1_GENERALIZEDTIME **thisupd,
                          ASN1_GENERALIZEDTIME **nextupd);

int OCSP_resp_find(OCSP_BASICRESP *bs, OCSP_CERTID *id, int last, int *found_idx);
int OCSP_id_cmp(const OCSP_CERTID *a, const OCSP_CERTID *b);


#endif  // AWSLC_OCSP_H
