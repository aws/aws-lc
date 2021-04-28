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

#pragma once

#include <openssl/asn1t.h>
#include <openssl/x509.h>
#include <openssl/x509v3.h>
#include <openssl/safestack.h>


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


/* get OCSP_RESPONSE's response status */
int OCSP_response_status(OCSP_RESPONSE *resp);

/* extract OCSP_BASICRESP in OCSP_RESPONSE */
OCSP_BASICRESP *OCSP_response_get1_basic(OCSP_RESPONSE *resp);


#endif  // AWSLC_OCSP_H
