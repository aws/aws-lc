/*
 * Copyright 2001-2017 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

// SPDX-License-Identifier: Apache-2.0 OR ISC
// Modifications Copyright Amazon.com, Inc. or its affiliates.

#include "../internal.h"
#include "internal.h"

int OCSP_request_onereq_count(OCSP_REQUEST *req) {
  GUARD_PTR(req);
  GUARD_PTR(req->tbsRequest);
  return (int)sk_OCSP_ONEREQ_num(req->tbsRequest->requestList);
}

OCSP_ONEREQ *OCSP_request_onereq_get0(OCSP_REQUEST *req, int i) {
  GUARD_PTR(req);
  return sk_OCSP_ONEREQ_value(req->tbsRequest->requestList, i);
}

int OCSP_id_get0_info(ASN1_OCTET_STRING **nameHash, ASN1_OBJECT **algor,
                      ASN1_OCTET_STRING **keyHash, ASN1_INTEGER **serial,
                      OCSP_CERTID *cid) {
  if (cid == NULL) {
    return 0;
  }
  if (algor != NULL) {
    *algor = cid->hashAlgorithm->algorithm;
  }
  if (nameHash != NULL) {
    *nameHash = cid->issuerNameHash;
  }
  if (keyHash != NULL) {
    *keyHash = cid->issuerKeyHash;
  }
  if (serial != NULL) {
    *serial = cid->serialNumber;
  }
  return 1;
}

int OCSP_request_is_signed(OCSP_REQUEST *req) {
  GUARD_PTR(req);
  if (req->optionalSignature != NULL) {
    return 1;
  }
  return 0;
}

OCSP_CERTID *OCSP_onereq_get0_id(OCSP_ONEREQ *one) {
  GUARD_PTR(one);
  return one->reqCert;
}

int OCSP_basic_add1_cert(OCSP_BASICRESP *resp, X509 *cert) {
  if (resp->certs == NULL && (resp->certs = sk_X509_new_null()) == NULL) {
    return 0;
  }

  if (!sk_X509_push(resp->certs, cert)) {
    return 0;
  }
  X509_up_ref(cert);
  return 1;
}
