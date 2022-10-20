// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Based on OpenSSL 3.x SSHKDF().

#include <openssl/digest.h>
#include <openssl/mem.h>

#include "../service_indicator/internal.h"
#include "../../internal.h"

int SSHKDF(const EVP_MD *evp_md,
           const uint8_t *key, size_t key_len,
           const uint8_t *xcghash, size_t xcghash_len,
           const uint8_t *session_id, size_t session_id_len,
           char type,
           uint8_t *out, size_t out_len)
{
  EVP_MD_CTX *md = NULL;
  uint8_t digest[EVP_MAX_MD_SIZE];
  size_t digest_size = 0;
  size_t cursize = 0;
  int ret = 0;

  // Sanity-check.
  if (type < EVP_KDF_SSHKDF_TYPE_INITIAL_IV_CLI_TO_SRV ||
      type > EVP_KDF_SSHKDF_TYPE_INTEGRITY_KEY_SRV_TO_CLI) {
    return 0;
  }

  FIPS_service_indicator_lock_state();

  md = EVP_MD_CTX_new();
  if (md == NULL) {
    return 0;
  }

  if (!EVP_DigestInit_ex(md, evp_md, NULL)) {
    goto out;
  }

  if (!EVP_DigestUpdate(md, key, key_len)) {
    goto out;
  }

  if (!EVP_DigestUpdate(md, xcghash, xcghash_len)) {
    goto out;
  }

  if (!EVP_DigestUpdate(md, &type, 1)) {
    goto out;
  }

  if (!EVP_DigestUpdate(md, session_id, session_id_len)) {
    goto out;
  }

  if (!EVP_DigestFinal_ex(md, digest, (unsigned int *)&digest_size)) {
    goto out;
  }

  if (out_len < digest_size) {
    memcpy(out, digest, out_len);
    ret = 1;
    goto out;
  }

  memcpy(out, digest, digest_size);

  for (cursize = digest_size; cursize < out_len; cursize += digest_size) {
    if (!EVP_DigestInit_ex(md, evp_md, NULL)) {
      goto out;
    }

    if (!EVP_DigestUpdate(md, key, key_len)) {
      goto out;
    }

    if (!EVP_DigestUpdate(md, xcghash, xcghash_len)) {
      goto out;
    }

    if (!EVP_DigestUpdate(md, out, cursize)) {
      goto out;
    }

    if (!EVP_DigestFinal_ex(md, digest, (unsigned int *)&digest_size)) {
      goto out;
    }

    if (out_len < cursize + digest_size) {
      memcpy(out + cursize, digest, out_len - cursize);
      ret = 1;
      goto out;
    }

    memcpy(out + cursize, digest, digest_size);
  }

  ret = 1;

out:
  EVP_MD_CTX_free(md);
  OPENSSL_cleanse(digest, EVP_MAX_MD_SIZE);

  FIPS_service_indicator_unlock_state();
  if (ret) {
    SSHKDF_verify_service_indicator(evp_md);
  }

  return ret;
}
