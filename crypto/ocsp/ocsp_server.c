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

static int OCSP_RESPID_set_by_name(OCSP_RESPID *respid, X509 *cert) {
  GUARD_PTR(respid);
  GUARD_PTR(cert);
  if (!X509_NAME_set(&respid->value.byName, X509_get_subject_name(cert))) {
    return 0;
  }

  respid->type = V_OCSP_RESPID_NAME;
  return 1;
}

static int OCSP_RESPID_set_by_key(OCSP_RESPID *respid, X509 *cert) {
  GUARD_PTR(respid);
  GUARD_PTR(cert);

  // RFC2560 requires SHA1.
  unsigned char digest[SHA_DIGEST_LENGTH];
  if (!X509_pubkey_digest(cert, EVP_sha1(), digest, NULL)) {
    return 0;
  }

  ASN1_OCTET_STRING *byKey = ASN1_OCTET_STRING_new();
  if (byKey == NULL) {
    return 0;
  }

  if (!ASN1_OCTET_STRING_set(byKey, digest, SHA_DIGEST_LENGTH)) {
    ASN1_OCTET_STRING_free(byKey);
    return 0;
  }
  respid->type = V_OCSP_RESPID_KEY;
  respid->value.byKey = byKey;

  return 1;
}


// OCSP_basic_sign_ctx does the actual signing operation for |OCSP_basic_sign|,
// but with an initialized |EVP_MD_CTX|.
static int OCSP_basic_sign_ctx(OCSP_BASICRESP *resp, X509 *signer,
                               EVP_MD_CTX *ctx, STACK_OF(X509) *certs,
                               unsigned long flags) {
  GUARD_PTR(resp);
  GUARD_PTR(signer);

  if (ctx == NULL || ctx->pctx == NULL) {
    OPENSSL_PUT_ERROR(OCSP, OCSP_R_NO_SIGNER_KEY);
    return 0;
  }

  EVP_PKEY *pkey = EVP_PKEY_CTX_get0_pkey(ctx->pctx);
  if (pkey == NULL || !X509_check_private_key(signer, pkey)) {
    OPENSSL_PUT_ERROR(OCSP, OCSP_R_PRIVATE_KEY_DOES_NOT_MATCH_CERTIFICATE);
    return 0;
  }

  // Add relevant certificates to the response. This is optional according to
  // the RFC.
  if (!IS_OCSP_FLAG_SET(flags, OCSP_NOCERTS)) {
    if (!OCSP_basic_add1_cert(resp, signer)) {
      return 0;
    }
    for (size_t i = 0; i < sk_X509_num(certs); i++) {
      X509 *tmpcert = sk_X509_value(certs, i);
      if (!OCSP_basic_add1_cert(resp, tmpcert)) {
        return 0;
      }
    }
  }

  // Set |responderId| of response.
  OCSP_RESPID *rid = resp->tbsResponseData->responderId;
  if (IS_OCSP_FLAG_SET(flags, OCSP_RESPID_KEY)) {
    if (!OCSP_RESPID_set_by_key(rid, signer)) {
      return 0;
    }
  } else if (!OCSP_RESPID_set_by_name(rid, signer)) {
    // The OCSP responder is identified by name by default.
    return 0;
  }

  // Set |producedAt| time field of response. Although this can be
  // excluded with |OCSP_NOTIME|, a definitive response should include
  // the generation time.
  if (!IS_OCSP_FLAG_SET(flags, OCSP_NOTIME)) {
    if (!X509_gmtime_adj(resp->tbsResponseData->producedAt, 0)) {
      return 0;
    }
  }

  // Do the actual signing. This is mandatory according to the RFC.
  if (!ASN1_item_sign_ctx(ASN1_ITEM_rptr(OCSP_RESPDATA),
                          resp->signatureAlgorithm, NULL, resp->signature,
                          resp->tbsResponseData, ctx)) {
    return 0;
  }

  return 1;
}

int OCSP_basic_sign(OCSP_BASICRESP *resp, X509 *signer, EVP_PKEY *key,
                    const EVP_MD *dgst, STACK_OF(X509) *certs,
                    unsigned long flags) {
  GUARD_PTR(resp);
  GUARD_PTR(signer);
  GUARD_PTR(key);
  GUARD_PTR(dgst);

  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  if (ctx == NULL) {
    return 0;
  }

  if (!EVP_DigestSignInit(ctx, NULL, dgst, NULL, key)) {
    EVP_MD_CTX_free(ctx);
    return 0;
  }
  int ret = OCSP_basic_sign_ctx(resp, signer, ctx, certs, flags);
  EVP_MD_CTX_free(ctx);
  return ret;
}
