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
  GUARD_PTR(req->tbsRequest);
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

OCSP_SINGLERESP *OCSP_basic_add1_status(OCSP_BASICRESP *resp, OCSP_CERTID *cid,
                                        int status, int revoked_reason,
                                        ASN1_TIME *revoked_time,
                                        ASN1_TIME *this_update,
                                        ASN1_TIME *next_update) {
  GUARD_PTR(resp);
  GUARD_PTR(cid);
  GUARD_PTR(this_update);
  // Ambiguous status values are not allowed.
  if (status < V_OCSP_CERTSTATUS_GOOD || status > V_OCSP_CERTSTATUS_UNKNOWN) {
    OPENSSL_PUT_ERROR(OCSP, OCSP_R_UNKNOWN_FIELD_VALUE);
    return NULL;
  }

  OCSP_SINGLERESP *single = OCSP_SINGLERESP_new();
  if (single == NULL) {
    goto err;
  }

  // Init |resp->tbsResponseData->responses| if NULL.
  if (resp->tbsResponseData->responses == NULL) {
    resp->tbsResponseData->responses = sk_OCSP_SINGLERESP_new_null();
    if (resp->tbsResponseData->responses == NULL) {
      goto err;
    }
  }

  if (!ASN1_TIME_to_generalizedtime(this_update, &single->thisUpdate)) {
    goto err;
  }
  if (next_update != NULL) {
    // |next_update| is allowed to be NULL. Only set |single->nextUpdate| if
    // |next_update| is non-NULL.
    if (!ASN1_TIME_to_generalizedtime(next_update, &single->nextUpdate)) {
      goto err;
    }
  }

  // Reset |single->certId|.
  OCSP_CERTID_free(single->certId);
  single->certId = OCSP_CERTID_dup(cid);
  if (single->certId == NULL) {
    goto err;
  }

  single->certStatus->type = status;
  switch (single->certStatus->type) {
    case V_OCSP_CERTSTATUS_REVOKED:
      if (revoked_time == NULL) {
        OPENSSL_PUT_ERROR(OCSP, OCSP_R_NO_REVOKED_TIME);
        goto err;
      }

      single->certStatus->value.revoked = OCSP_REVOKEDINFO_new();
      if (single->certStatus->value.revoked == NULL) {
        goto err;
      }

      // Start assigning values to |info| once initialized successfully.
      OCSP_REVOKEDINFO *info = single->certStatus->value.revoked;
      if (!ASN1_TIME_to_generalizedtime(revoked_time, &info->revocationTime)) {
        goto err;
      }
      // https://www.rfc-editor.org/rfc/rfc5280#section-5.3.1 specifies the only
      // valid reason codes are 0-10. Value 7 is not used.
      if (revoked_reason < OCSP_REVOKED_STATUS_UNSPECIFIED ||
          revoked_reason > OCSP_REVOKED_STATUS_AACOMPROMISE ||
          revoked_reason == 7) {
        OPENSSL_PUT_ERROR(OCSP, OCSP_R_UNKNOWN_FIELD_VALUE);
        goto err;
      }
      info->revocationReason = ASN1_ENUMERATED_new();
      if (info->revocationReason == NULL ||
          !ASN1_ENUMERATED_set(info->revocationReason, revoked_reason)) {
        goto err;
      }

      break;

    case V_OCSP_CERTSTATUS_GOOD:
      single->certStatus->value.good = ASN1_NULL_new();
      if (single->certStatus->value.good == NULL) {
        goto err;
      }
      break;

    case V_OCSP_CERTSTATUS_UNKNOWN:
      single->certStatus->value.unknown = ASN1_NULL_new();
      if (single->certStatus->value.unknown == NULL) {
        goto err;
      }
      break;

    default:
      goto err;
  }

  // Finally add the |OCSP_SINGLERESP| we were working with to |resp|.
  if (!sk_OCSP_SINGLERESP_push(resp->tbsResponseData->responses, single)) {
    goto err;
  }
  return single;

err:
  OCSP_SINGLERESP_free(single);
  return NULL;
}

OCSP_RESPONSE *OCSP_response_create(int status, OCSP_BASICRESP *bs) {
  if (status < OCSP_RESPONSE_STATUS_SUCCESSFUL ||
      status > OCSP_RESPONSE_STATUS_UNAUTHORIZED ||
      // 4 is not a valid response status code.
      status == 4) {
    OPENSSL_PUT_ERROR(OCSP, OCSP_R_UNKNOWN_FIELD_VALUE);
    return NULL;
  }

  OCSP_RESPONSE *rsp = OCSP_RESPONSE_new();
  if (rsp == NULL) {
    goto err;
  }
  if (!ASN1_ENUMERATED_set(rsp->responseStatus, status)) {
    goto err;
  }
  if (bs == NULL) {
    // |bs| is allowed to be NULL.
    return rsp;
  }

  rsp->responseBytes = OCSP_RESPBYTES_new();
  if (rsp->responseBytes == NULL) {
    goto err;
  }
  rsp->responseBytes->responseType = OBJ_nid2obj(NID_id_pkix_OCSP_basic);
  if (!ASN1_item_pack(bs, ASN1_ITEM_rptr(OCSP_BASICRESP),
                      &rsp->responseBytes->response)) {
    goto err;
  }
  return rsp;

err:
  OCSP_RESPONSE_free(rsp);
  return NULL;
}
