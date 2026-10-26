// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bytestring.h>
#include <openssl/digest.h>
#include <openssl/nid.h>
#include <openssl/obj.h>

#include "backend/operations/rsa.h"
#include "boundary/operations/rsa.h"

int awslc_prov_rsa_marshal_pss_params(CBB *cbb, const EVP_MD *md,
                                      const EVP_MD *mgf1_md, int64_t saltlen) {
  CBB params, field, mgf1;

  // RFC 4055 section 3.1, where DER omits each field equal to its DEFAULT:
  //
  //   RSASSA-PSS-params ::= SEQUENCE {
  //     hashAlgorithm     [0] HashAlgorithm    DEFAULT sha1Identifier,
  //     maskGenAlgorithm  [1] MaskGenAlgorithm DEFAULT mgf1SHA1Identifier,
  //     saltLength        [2] INTEGER          DEFAULT 20,
  //     trailerField      [3] INTEGER          DEFAULT 1 }
  //
  // The tags are EXPLICIT. HashAlgorithm is an AlgorithmIdentifier, and
  // MaskGenAlgorithm is one naming id-mgf1 whose parameters are the MGF1
  // HashAlgorithm. trailerField is always 1, so it never appears.
  if (!CBB_add_asn1(cbb, &params, CBS_ASN1_SEQUENCE)) {
    return 0;
  }
  if (EVP_MD_type(md) != NID_sha1 &&
      (!CBB_add_asn1(&params, &field,
                     CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 0) ||
       !EVP_marshal_digest_algorithm(&field, md))) {
    return 0;
  }
  if (EVP_MD_type(mgf1_md) != NID_sha1 &&
      (!CBB_add_asn1(&params, &field,
                     CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 1) ||
       !CBB_add_asn1(&field, &mgf1, CBS_ASN1_SEQUENCE) ||
       !OBJ_nid2cbb(&mgf1, NID_mgf1) ||
       !EVP_marshal_digest_algorithm(&mgf1, mgf1_md))) {
    return 0;
  }
  if (saltlen != AWSLC_PROV_RSA_PSS_DEFAULT_SALTLEN &&
      (!CBB_add_asn1(&params, &field,
                     CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 2) ||
       !CBB_add_asn1_int64(&field, saltlen))) {
    return 0;
  }
  return CBB_flush(cbb);
}
