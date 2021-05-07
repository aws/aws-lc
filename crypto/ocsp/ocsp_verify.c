// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include "ocsp_internal.h"

#define IS_OCSP_FLAG_SET(flags, query) (flags & query)

/* Verify a basic response message */
int OCSP_basic_verify(OCSP_BASICRESP *bs, STACK_OF(X509) *certs, X509_STORE *st, unsigned long flags)
{
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
