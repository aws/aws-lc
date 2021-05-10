// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>
#include "ocsp_internal.h"

/* supporting internal static functions for OCSP_basic_verify */
#define IS_OCSP_FLAG_SET(flags, query) (flags & query)
static int ocsp_find_signer(X509 **psigner, OCSP_BASICRESP *bs, STACK_OF(X509) *certs, unsigned long flags);
static X509 *ocsp_find_signer_sk(STACK_OF(X509) *certs, OCSP_RESPID *id);
static int ocsp_check_issuer(OCSP_BASICRESP *bs, STACK_OF(X509) *chain);
static int ocsp_check_ids(STACK_OF(OCSP_SINGLERESP) *sresp, OCSP_CERTID **ret)


int OCSP_basic_verify(OCSP_BASICRESP *bs, STACK_OF(X509) *certs, X509_STORE *st, unsigned long flags)
{
  if (bs == NULL || certs == NULL || st == NULL) {
    OPENSSL_PUT_ERROR(OCSP, ERR_R_PASSED_NULL_PARAMETER);
    return -1;
  }

  X509 *signer, *x;
  STACK_OF(X509) *chain = NULL;
  STACK_OF(X509) *untrusted = NULL;
  int ret = ocsp_find_signer(&signer, bs, certs, flags);

  if (ret == 0) {
    OPENSSL_PUT_ERROR(OCSP, OCSP_R_SIGNER_CERTIFICATE_NOT_FOUND);
    goto end;
  }
  if ((ret == 2) && (flags & OCSP_TRUSTOTHER) != 0) {
    flags |= OCSP_NOVERIFY;
  }

  if ((ret = ocsp_verify(NULL, bs, signer, flags)) <= 0) {
    goto end;
  }
  if (IS_OCSP_FLAG_SET(flags, OCSP_NOVERIFY) == 0) {
    ret = -1;
    if (IS_OCSP_FLAG_SET(flags, OCSP_NOCHAIN) == 0) {
      if ((untrusted = sk_X509_dup(bs->certs)) == NULL) {
        goto end;
      }
      for (size_t i = 0; i < sk_X509_num(certs); i++) {
        if (!sk_X509_push(untrusted, sk_X509_value(certs, i))) {
          OPENSSL_PUT_ERROR(OCSP, ERR_R_MALLOC_FAILURE);
          goto end;
        }
      }
    }
    ret = ocsp_verify_signer(signer, 1, st, flags, untrusted, &chain);
    if (ret <= 0) {
      goto end;
    }
    if (IS_OCSP_FLAG_SET(flags, OCSP_NOCHECKS) != 0) {
      ret = 1;
      goto end;
    }
    /*
     * At this point we have a valid certificate chain need to verify it
     * against the OCSP issuer criteria.
     */
    ret = ocsp_check_issuer(bs, chain);

    /* If fatal error or valid match then finish */
    if (ret != 0) {
      goto end;
    }

    /* Easy case: explicitly trusted. Get root CA and check for explicit trust */
    if (IS_OCSP_FLAG_SET(flags, OCSP_NOEXPLICIT) != 0) {
      goto end;
    }
    x = sk_X509_value(chain, sk_X509_num(chain) - 1);
    if (X509_check_trust(x, NID_OCSP_sign, 0) != X509_TRUST_TRUSTED) {
      OPENSSL_PUT_ERROR(OCSP, OCSP_R_ROOT_CA_NOT_TRUSTED);
      ret = 0;
      goto end;
    }
    ret = 1;
  }

  end:
  sk_X509_pop_free(chain, X509_free);
  sk_X509_free(untrusted);
  return ret;
}

static int ocsp_find_signer(X509 **psigner, OCSP_BASICRESP *bs,
                            STACK_OF(X509) *certs, unsigned long flags)
{
  X509 *signer;
  OCSP_RESPID *rid = bs->tbsResponseData->responderId;

  if ((signer = ocsp_find_signer_sk(certs, rid)) != NULL) {
    *psigner = signer;
    return 2;
  }
  if ((flags & OCSP_NOINTERN) == 0 &&
      (signer = ocsp_find_signer_sk(bs->certs, rid))) {
    *psigner = signer;
    return 1;
  }
  /* Maybe lookup from store if by subject name */

  *psigner = NULL;
  return 0;
}

static X509 *ocsp_find_signer_sk(STACK_OF(X509) *certs, OCSP_RESPID *id)
{
  unsigned char tmphash[SHA_DIGEST_LENGTH], *keyhash;
  X509 *x;

  /* Easy if lookup by name */
  if (id->type == V_OCSP_RESPID_NAME) {
    return X509_find_by_subject(certs, id->value.byName);
  }

  /* Lookup by key hash */

  /* If key hash isn't SHA1 length then forget it */
  if (id->value.byKey->length != SHA_DIGEST_LENGTH) {
    return NULL;
  }
  keyhash = id->value.byKey->data;
  /* Calculate hash of each key and compare */
  for (size_t i = 0; i < sk_X509_num(certs); i++) {
    x = sk_X509_value(certs, i);
    X509_pubkey_digest(x, EVP_sha1(), tmphash, NULL);
    if (!memcmp(keyhash, tmphash, SHA_DIGEST_LENGTH)) {
      return x;
    }
  }
  return NULL;
}

static int ocsp_check_issuer(OCSP_BASICRESP *bs, STACK_OF(X509) *chain)
{
  STACK_OF(OCSP_SINGLERESP) *sresp = bs->tbsResponseData.responses;
  X509 *signer, *sca;
  OCSP_CERTID *caid = NULL;
  int ret;

  if (sk_X509_num(chain) <= 0) {
    OPENSSL_PUT_ERROR(OCSP, OCSP_R_NO_CERTIFICATES_IN_CHAIN);
    return -1;
  }

  /* See if the issuer IDs match. */
  ret = ocsp_check_ids(sresp, &caid);

  /* If ID mismatch or other error then return */
  if (ret <= 0) {
    return ret;
  }

  signer = sk_X509_value(chain, 0);
  /* Check to see if OCSP responder CA matches request CA */
  if (sk_X509_num(chain) > 1) {
    sca = sk_X509_value(chain, 1);
    ret = ocsp_match_issuerid(sca, caid, sresp);
    if (ret < 0) {
      return ret;
    }
    if (ret != 0) {
      /* We have a match, if extensions OK then success */
      if (ocsp_check_delegated(signer)) {
        return 1;
      }
      return 0;
    }
  }

  /* Otherwise check if OCSP request signed directly by request CA */
  return ocsp_match_issuerid(signer, caid, sresp);
}

/*
 * Check the issuer certificate IDs for equality. If there is a mismatch with
 * the same algorithm then there's no point trying to match any certificates
 * against the issuer. If the issuer IDs all match then we just need to check
 * equality against one of them.
 */
static int ocsp_check_ids(STACK_OF(OCSP_SINGLERESP) *sresp, OCSP_CERTID **ret)
{
  OCSP_CERTID *tmpid, *cid;
  size_t idcount;

  idcount = sk_OCSP_SINGLERESP_num(sresp);
  if (idcount <= 0) {
    OPENSSL_PUT_ERROR(OCSP, OCSP_R_RESPONSE_CONTAINS_NO_REVOCATION_DATA);
    return -1;
  }

  cid = sk_OCSP_SINGLERESP_value(sresp, 0)->certId;

  *ret = NULL;
  for (size_t i = 1; i < idcount; i++) {
    tmpid = sk_OCSP_SINGLERESP_value(sresp, i)->certId;
    /* Check to see if IDs match */
    if (OCSP_id_issuer_cmp(cid, tmpid) != 0) {
      /* If algorithm mismatch let caller deal with it */
      if (OBJ_cmp(tmpid->hashAlgorithm->algorithm, cid->hashAlgorithm->algorithm) != 0) {
        return 2;
      }
      /* Else mismatch */
      return 0;
    }
  }

  /* All IDs match: only need to check one ID */
  *ret = cid;
  return 1;
}
