// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bytestring.h>
#include <openssl/digest.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/nid.h>
#include <openssl/obj.h>
#include <openssl/rsa.h>

#include "backend/operations/rsa.h"
#include "backend/utils.h"
#include "boundary/operations/rsa.h"

typedef struct {
  EVP_PKEY *pkey;
  // Set for the digest operations, which own |pctx| through it.
  EVP_MD_CTX *md_ctx;
  EVP_PKEY_CTX *pctx;
  AWSLC_PROV_RSA_SIG_OPERATION operation;
  int saltlen;
} AWSLC_PROV_RSA_SIG;

static int awslc_prov_rsa_sig_is_verify(const AWSLC_PROV_RSA_SIG *sig) {
  return sig->operation == AWSLC_PROV_RSA_SIG_VERIFY ||
         sig->operation == AWSLC_PROV_RSA_SIG_DIGEST_VERIFY;
}

static int awslc_prov_rsa_sig_is_pss(const AWSLC_PROV_RSA_SIG *sig) {
  int padding = 0;

  return EVP_PKEY_CTX_get_rsa_padding(sig->pctx, &padding) &&
         padding == RSA_PKCS1_PSS_PADDING;
}

// What AWS-LC's RSA_PSS_SALTLEN_AUTO resolves to when signing.
static int awslc_prov_rsa_sig_max_saltlen(const AWSLC_PROV_RSA_SIG *sig,
                                          const EVP_MD *md) {
  int max = EVP_PKEY_size(sig->pkey) - (int)EVP_MD_size(md) - 2;

  if (((EVP_PKEY_bits(sig->pkey) - 1) & 0x7) == 0) {
    max--;
  }
  return max;
}

// |sig->saltlen| in AWS-LC's terms, where only DIGEST and AUTO are special.
static int awslc_prov_rsa_sig_awslc_saltlen(const AWSLC_PROV_RSA_SIG *sig,
                                            const EVP_MD *md) {
  const int verify = awslc_prov_rsa_sig_is_verify(sig);

  switch (sig->saltlen) {
    case AWSLC_PROV_RSA_PSS_SALTLEN_DIGEST:
      return RSA_PSS_SALTLEN_DIGEST;
    case AWSLC_PROV_RSA_PSS_SALTLEN_AUTO:
      return RSA_PSS_SALTLEN_AUTO;
    case AWSLC_PROV_RSA_PSS_SALTLEN_MAX:
      return verify ? awslc_prov_rsa_sig_max_saltlen(sig, md)
                    : RSA_PSS_SALTLEN_AUTO;
    case AWSLC_PROV_RSA_PSS_SALTLEN_AUTO_DIGEST_MAX: {
      if (verify) {
        return RSA_PSS_SALTLEN_AUTO;
      }
      const int max = awslc_prov_rsa_sig_max_saltlen(sig, md);
      return max < (int)EVP_MD_size(md) ? max : RSA_PSS_SALTLEN_DIGEST;
    }
    default:
      return sig->saltlen;
  }
}

// Resolves |sig->saltlen| against the current digest, which MAX and
// AUTO_DIGEST_MAX depend on, so it reruns whenever padding or digest change.
// With no digest yet it does nothing, and setting one resolves it.
static int awslc_prov_rsa_sig_apply_saltlen(AWSLC_PROV_RSA_SIG *sig) {
  const EVP_MD *md = NULL;

  if (!awslc_prov_rsa_sig_is_pss(sig)) {
    return 1;
  }
  if (!EVP_PKEY_CTX_get_signature_md(sig->pctx, &md)) {
    return 0;
  }
  return md == NULL || EVP_PKEY_CTX_set_rsa_pss_saltlen(
                           sig->pctx, awslc_prov_rsa_sig_awslc_saltlen(sig, md));
}

void awslc_prov_rsa_sig_free(void *sig_ptr) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;

  if (sig == NULL) {
    return;
  }
  if (sig->md_ctx != NULL) {
    EVP_MD_CTX_free(sig->md_ctx);
  } else {
    EVP_PKEY_CTX_free(sig->pctx);
  }
  EVP_PKEY_free(sig->pkey);
  OPENSSL_free(sig);
}

static int awslc_prov_rsa_sig_init(AWSLC_PROV_RSA_SIG *sig, const EVP_MD *md) {
  switch (sig->operation) {
    case AWSLC_PROV_RSA_SIG_DIGEST_SIGN:
    case AWSLC_PROV_RSA_SIG_DIGEST_VERIFY:
      sig->md_ctx = EVP_MD_CTX_new();
      if (sig->md_ctx == NULL) {
        return 0;
      }
      return sig->operation == AWSLC_PROV_RSA_SIG_DIGEST_SIGN
                 ? EVP_DigestSignInit(sig->md_ctx, &sig->pctx, md, NULL,
                                      sig->pkey)
                 : EVP_DigestVerifyInit(sig->md_ctx, &sig->pctx, md, NULL,
                                        sig->pkey);
    case AWSLC_PROV_RSA_SIG_SIGN:
    case AWSLC_PROV_RSA_SIG_VERIFY:
    case AWSLC_PROV_RSA_SIG_VERIFY_RECOVER: {
      int ok = 0;

      sig->pctx = EVP_PKEY_CTX_new(sig->pkey, NULL);
      if (sig->pctx == NULL) {
        return 0;
      }
      if (sig->operation == AWSLC_PROV_RSA_SIG_SIGN) {
        ok = EVP_PKEY_sign_init(sig->pctx);
      } else if (sig->operation == AWSLC_PROV_RSA_SIG_VERIFY) {
        ok = EVP_PKEY_verify_init(sig->pctx);
      } else {
        ok = EVP_PKEY_verify_recover_init(sig->pctx);
      }
      return ok && (md == NULL || EVP_PKEY_CTX_set_signature_md(sig->pctx, md));
    }
  }
  return 0;
}

void *awslc_prov_rsa_sig_new(void *rsa, int pss_key, int restricted,
                             AWSLC_PROV_RSA_SIG_OPERATION operation,
                             const char *digest) {
  AWSLC_PROV_RSA_SIG *sig = NULL;
  const EVP_MD *md = NULL;

  if (rsa == NULL ||
      (digest != NULL && (md = awslc_prov_digest_md(digest)) == NULL)) {
    return NULL;
  }
  sig = OPENSSL_zalloc(sizeof(*sig));
  if (sig == NULL) {
    return NULL;
  }
  sig->operation = operation;
  sig->saltlen = AWSLC_PROV_RSA_PSS_SALTLEN_AUTO_DIGEST_MAX;
  sig->pkey = EVP_PKEY_new();
  if (sig->pkey == NULL || !RSA_up_ref((RSA *)rsa)) {
    awslc_prov_rsa_sig_free(sig);
    return NULL;
  }
  if (!EVP_PKEY_assign(sig->pkey, pss_key ? EVP_PKEY_RSA_PSS : EVP_PKEY_RSA,
                       rsa)) {
    RSA_free((RSA *)rsa);
    awslc_prov_rsa_sig_free(sig);
    return NULL;
  }
  if (!awslc_prov_rsa_sig_init(sig, md) ||
      (restricted &&
       !EVP_PKEY_CTX_get_rsa_pss_saltlen(sig->pctx, &sig->saltlen)) ||
      !awslc_prov_rsa_sig_apply_saltlen(sig)) {
    awslc_prov_rsa_sig_free(sig);
    return NULL;
  }
  return sig;
}

void *awslc_prov_rsa_sig_dup(const void *sig_ptr) {
  const AWSLC_PROV_RSA_SIG *sig = (const AWSLC_PROV_RSA_SIG *)sig_ptr;
  AWSLC_PROV_RSA_SIG *copy = NULL;

  if (sig == NULL) {
    return NULL;
  }
  copy = OPENSSL_zalloc(sizeof(*copy));
  if (copy == NULL) {
    return NULL;
  }
  copy->operation = sig->operation;
  copy->saltlen = sig->saltlen;
  if (!EVP_PKEY_up_ref(sig->pkey)) {
    OPENSSL_free(copy);
    return NULL;
  }
  copy->pkey = sig->pkey;
  if (sig->md_ctx != NULL) {
    copy->md_ctx = EVP_MD_CTX_new();
    if (copy->md_ctx == NULL ||
        !EVP_MD_CTX_copy_ex(copy->md_ctx, sig->md_ctx)) {
      awslc_prov_rsa_sig_free(copy);
      return NULL;
    }
    copy->pctx = EVP_MD_CTX_get_pkey_ctx(copy->md_ctx);
  } else {
    copy->pctx = EVP_PKEY_CTX_dup(sig->pctx);
  }
  if (copy->pctx == NULL) {
    awslc_prov_rsa_sig_free(copy);
    return NULL;
  }
  return copy;
}

int awslc_prov_rsa_sig_set_padding(void *sig_ptr,
                                   AWSLC_PROV_RSA_PADDING padding) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  int mode = 0;

  switch (padding) {
    case AWSLC_PROV_RSA_PADDING_PKCS1:
      mode = RSA_PKCS1_PADDING;
      break;
    case AWSLC_PROV_RSA_PADDING_NONE:
      mode = RSA_NO_PADDING;
      break;
    case AWSLC_PROV_RSA_PADDING_PSS:
      mode = RSA_PKCS1_PSS_PADDING;
      break;
    default:
      return 0;
  }
  return sig != NULL && EVP_PKEY_CTX_set_rsa_padding(sig->pctx, mode) &&
         awslc_prov_rsa_sig_apply_saltlen(sig);
}

int awslc_prov_rsa_sig_set_digest(void *sig_ptr, const char *digest) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  const EVP_MD *md = awslc_prov_digest_md(digest);

  return sig != NULL && sig->md_ctx == NULL && md != NULL &&
         EVP_PKEY_CTX_set_signature_md(sig->pctx, md) &&
         awslc_prov_rsa_sig_apply_saltlen(sig);
}

int awslc_prov_rsa_sig_set_mgf1_digest(void *sig_ptr, const char *digest) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  const EVP_MD *md = awslc_prov_digest_md(digest);

  return sig != NULL && md != NULL &&
         EVP_PKEY_CTX_set_rsa_mgf1_md(sig->pctx, md);
}

int awslc_prov_rsa_sig_set_pss_saltlen(void *sig_ptr, int saltlen) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  const int previous = sig == NULL ? 0 : sig->saltlen;

  if (sig == NULL || saltlen < AWSLC_PROV_RSA_PSS_SALTLEN_AUTO_DIGEST_MAX) {
    return 0;
  }
  // Without PSS padding AWS-LC refuses any salt length; it raises the error.
  if (!awslc_prov_rsa_sig_is_pss(sig)) {
    return EVP_PKEY_CTX_set_rsa_pss_saltlen(sig->pctx, RSA_PSS_SALTLEN_DIGEST);
  }
  sig->saltlen = saltlen;
  if (!awslc_prov_rsa_sig_apply_saltlen(sig)) {
    sig->saltlen = previous;
    return 0;
  }
  return 1;
}

int awslc_prov_rsa_sig_padding(const void *sig_ptr) {
  const AWSLC_PROV_RSA_SIG *sig = (const AWSLC_PROV_RSA_SIG *)sig_ptr;
  int mode = 0;

  if (sig == NULL || !EVP_PKEY_CTX_get_rsa_padding(sig->pctx, &mode)) {
    return 0;
  }
  switch (mode) {
    case RSA_PKCS1_PADDING:
      return AWSLC_PROV_RSA_PADDING_PKCS1;
    case RSA_NO_PADDING:
      return AWSLC_PROV_RSA_PADDING_NONE;
    case RSA_PKCS1_PSS_PADDING:
      return AWSLC_PROV_RSA_PADDING_PSS;
    default:
      return 0;
  }
}

static const EVP_MD *awslc_prov_rsa_sig_md(const AWSLC_PROV_RSA_SIG *sig) {
  const EVP_MD *md = NULL;

  if (sig == NULL || !EVP_PKEY_CTX_get_signature_md(sig->pctx, &md)) {
    return NULL;
  }
  return md;
}

static const EVP_MD *awslc_prov_rsa_sig_mgf1_md(const AWSLC_PROV_RSA_SIG *sig) {
  const EVP_MD *md = NULL;

  if (sig == NULL || !awslc_prov_rsa_sig_is_pss(sig)) {
    return awslc_prov_rsa_sig_md(sig);
  }
  return EVP_PKEY_CTX_get_rsa_mgf1_md(sig->pctx, &md) ? md : NULL;
}

const char *awslc_prov_rsa_sig_digest(const void *sig) {
  return awslc_prov_digest_md_name(
      awslc_prov_rsa_sig_md((const AWSLC_PROV_RSA_SIG *)sig));
}

const char *awslc_prov_rsa_sig_mgf1_digest(const void *sig) {
  return awslc_prov_digest_md_name(
      awslc_prov_rsa_sig_mgf1_md((const AWSLC_PROV_RSA_SIG *)sig));
}

int awslc_prov_rsa_sig_pss_saltlen(const void *sig) {
  return sig == NULL ? 0 : ((const AWSLC_PROV_RSA_SIG *)sig)->saltlen;
}

// PKCS#1 v1.5 signature OIDs AWS-LC has no NID for: RFC 8017
// sha512-224WithRSAEncryption and sha512-256WithRSAEncryption, and the NIST
// id-rsassa-pkcs1-v1_5-with-sha3-* arc.
static const struct {
  int md_nid;
  uint8_t oid[9];
} awslc_prov_rsa_sig_pkcs1_oids[] = {
    {NID_sha512_224, {0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0f}},
    {NID_sha512_256, {0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x10}},
    {NID_sha3_224, {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x0d}},
    {NID_sha3_256, {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x0e}},
    {NID_sha3_384, {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x0f}},
    {NID_sha3_512, {0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x10}},
};

static int awslc_prov_rsa_sig_add_pkcs1_oid(CBB *cbb, const EVP_MD *md) {
  int sig_nid = NID_undef;
  CBB oid;

  if (OBJ_find_sigid_by_algs(&sig_nid, EVP_MD_type(md), EVP_PKEY_RSA)) {
    return OBJ_nid2cbb(cbb, sig_nid);
  }
  for (size_t i = 0; i < sizeof(awslc_prov_rsa_sig_pkcs1_oids) /
                             sizeof(awslc_prov_rsa_sig_pkcs1_oids[0]);
       i++) {
    if (awslc_prov_rsa_sig_pkcs1_oids[i].md_nid == EVP_MD_type(md)) {
      return CBB_add_asn1(cbb, &oid, CBS_ASN1_OBJECT) &&
             CBB_add_bytes(&oid, awslc_prov_rsa_sig_pkcs1_oids[i].oid,
                           sizeof(awslc_prov_rsa_sig_pkcs1_oids[i].oid)) &&
             CBB_flush(cbb);
    }
  }
  return 0;
}

int awslc_prov_rsa_sig_algorithm_id(const void *sig_ptr, unsigned char *out,
                                    size_t out_size, size_t *out_len) {
  const AWSLC_PROV_RSA_SIG *sig = (const AWSLC_PROV_RSA_SIG *)sig_ptr;
  const EVP_MD *md = awslc_prov_rsa_sig_md(sig);
  const int padding = awslc_prov_rsa_sig_padding(sig);
  CBB cbb, algorithm;
  int ok = 0;

  if (md == NULL || out == NULL || out_len == NULL ||
      !CBB_init_fixed(&cbb, out, out_size)) {
    return 0;
  }
  if (padding == AWSLC_PROV_RSA_PADDING_PKCS1) {
    CBB null;

    ok = CBB_add_asn1(&cbb, &algorithm, CBS_ASN1_SEQUENCE) &&
         awslc_prov_rsa_sig_add_pkcs1_oid(&algorithm, md) &&
         CBB_add_asn1(&algorithm, &null, CBS_ASN1_NULL);
  } else if (padding == AWSLC_PROV_RSA_PADDING_PSS) {
    const EVP_MD *mgf1_md = awslc_prov_rsa_sig_mgf1_md(sig);
    int saltlen = 0;

    ok = mgf1_md != NULL &&
         EVP_PKEY_CTX_get_rsa_pss_saltlen(sig->pctx, &saltlen);
    if (saltlen == RSA_PSS_SALTLEN_DIGEST) {
      saltlen = (int)EVP_MD_size(md);
    } else if (saltlen == RSA_PSS_SALTLEN_AUTO) {
      saltlen = awslc_prov_rsa_sig_max_saltlen(sig, md);
    }
    ok = ok && saltlen >= 0 &&
         CBB_add_asn1(&cbb, &algorithm, CBS_ASN1_SEQUENCE) &&
         OBJ_nid2cbb(&algorithm, NID_rsassaPss) &&
         awslc_prov_rsa_marshal_pss_params(&algorithm, md, mgf1_md, saltlen);
  }
  ok = ok && CBB_finish(&cbb, NULL, out_len);
  if (!ok) {
    CBB_cleanup(&cbb);
  }
  return ok;
}

int awslc_prov_rsa_sig_update(void *sig_ptr, const unsigned char *data,
                              size_t len) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;

  if (sig == NULL || sig->md_ctx == NULL) {
    return 0;
  }
  return sig->operation == AWSLC_PROV_RSA_SIG_DIGEST_SIGN
             ? EVP_DigestSignUpdate(sig->md_ctx, data, len)
             : EVP_DigestVerifyUpdate(sig->md_ctx, data, len);
}

int awslc_prov_rsa_sig_sign_final(void *sig_ptr, unsigned char *out,
                                  size_t *out_len, size_t out_size) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  size_t len = out_size;

  if (sig == NULL || out_len == NULL ||
      sig->operation != AWSLC_PROV_RSA_SIG_DIGEST_SIGN ||
      !EVP_DigestSignFinal(sig->md_ctx, out, &len)) {
    return 0;
  }
  *out_len = len;
  return 1;
}

int awslc_prov_rsa_sig_verify_final(void *sig_ptr, const unsigned char *in,
                                    size_t in_len) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;

  return sig != NULL && sig->operation == AWSLC_PROV_RSA_SIG_DIGEST_VERIFY &&
         EVP_DigestVerifyFinal(sig->md_ctx, in, in_len) == 1;
}

int awslc_prov_rsa_sig_sign(void *sig_ptr, unsigned char *out, size_t *out_len,
                            size_t out_size, const unsigned char *tbs,
                            size_t tbs_len) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  size_t len = out_size;

  if (sig == NULL || out_len == NULL ||
      sig->operation != AWSLC_PROV_RSA_SIG_SIGN ||
      !EVP_PKEY_sign(sig->pctx, out, &len, tbs, tbs_len)) {
    return 0;
  }
  *out_len = len;
  return 1;
}

int awslc_prov_rsa_sig_verify(void *sig_ptr, const unsigned char *in,
                              size_t in_len, const unsigned char *tbs,
                              size_t tbs_len) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;

  return sig != NULL && sig->operation == AWSLC_PROV_RSA_SIG_VERIFY &&
         EVP_PKEY_verify(sig->pctx, in, in_len, tbs, tbs_len) == 1;
}

int awslc_prov_rsa_sig_verify_recover(void *sig_ptr, unsigned char *out,
                                      size_t *out_len, size_t out_size,
                                      const unsigned char *in, size_t in_len) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  size_t len = out_size;

  if (sig == NULL || out_len == NULL ||
      sig->operation != AWSLC_PROV_RSA_SIG_VERIFY_RECOVER ||
      !EVP_PKEY_verify_recover(sig->pctx, out, &len, in, in_len)) {
    return 0;
  }
  *out_len = len;
  return 1;
}
