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
  // The key, shared by duplicates.
  EVP_PKEY *pkey;
  // Digest-sign/verify only: hashes the message and holds the EVP_PKEY_CTX.
  // NULL otherwise.
  EVP_MD_CTX *message_digest_ctx;
  // The operation over |pkey|, for plain sign/verify/recover only. NULL
  // otherwise.
  EVP_PKEY_CTX *pkey_ctx;
  AWSLC_PROV_RSA_SIG_OPERATION operation;
  int saltlen;
} AWSLC_PROV_RSA_SIG;

// The EVP_PKEY_CTX carrying padding, digests, and salt length.
static EVP_PKEY_CTX *awslc_prov_rsa_sig_pkey_ctx(
    const AWSLC_PROV_RSA_SIG *sig) {
  return sig->message_digest_ctx != NULL
             ? EVP_MD_CTX_get_pkey_ctx(sig->message_digest_ctx)
             : sig->pkey_ctx;
}

static int awslc_prov_rsa_sig_is_verify(const AWSLC_PROV_RSA_SIG *sig) {
  return sig->operation == AWSLC_PROV_RSA_SIG_VERIFY ||
         sig->operation == AWSLC_PROV_RSA_SIG_DIGEST_VERIFY;
}

static int awslc_prov_rsa_sig_is_pss(const AWSLC_PROV_RSA_SIG *sig) {
  int padding = 0;

  return EVP_PKEY_CTX_get_rsa_padding(awslc_prov_rsa_sig_pkey_ctx(sig),
                                      &padding) &&
         padding == RSA_PKCS1_PSS_PADDING;
}

// The longest salt |md| leaves room for, which is what AWS-LC's
// RSA_PSS_SALTLEN_AUTO resolves to when signing. OpenSSL's MAX and
// AUTO_DIGEST_MAX need the number, which AWS-LC does not expose.
//
// RFC 8017 section 9.1.1 encodes into emLen = ceil((modBits - 1) / 8) bytes:
//
//   EM = maskedDB || H || 0xbc,  DB = PS || 0x01 || salt
//
// so the salt gets emLen - hLen - 2, the 2 being the 0x01 and 0xbc bytes.
static int awslc_prov_rsa_sig_max_saltlen(const AWSLC_PROV_RSA_SIG *sig,
                                          const EVP_MD *md) {
  int max = EVP_PKEY_size(sig->pkey) - (int)EVP_MD_size(md) - 2;

  // EVP_PKEY_size is ceil(modBits / 8). It exceeds emLen by one byte when
  // modBits - 1 is a multiple of 8, leaving the top byte only one bit.
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
      // OpenSSL's default. On verify it accepts any salt length, which AWS-LC
      // does not approve, so a default PSS verify reports unapproved on a FIPS
      // build where OpenSSL's FIPS provider approves it.
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
  if (!EVP_PKEY_CTX_get_signature_md(awslc_prov_rsa_sig_pkey_ctx(sig), &md)) {
    return 0;
  }
  return md == NULL || EVP_PKEY_CTX_set_rsa_pss_saltlen(
                           awslc_prov_rsa_sig_pkey_ctx(sig),
                           awslc_prov_rsa_sig_awslc_saltlen(sig, md));
}

void awslc_prov_rsa_sig_free(void *sig_ptr) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;

  if (sig == NULL) {
    return;
  }
  EVP_MD_CTX_free(sig->message_digest_ctx);
  EVP_PKEY_CTX_free(sig->pkey_ctx);
  EVP_PKEY_free(sig->pkey);
  OPENSSL_free(sig);
}

int awslc_prov_rsa_sig_operation_is_digest(
    AWSLC_PROV_RSA_SIG_OPERATION operation) {
  return operation == AWSLC_PROV_RSA_SIG_DIGEST_SIGN ||
         operation == AWSLC_PROV_RSA_SIG_DIGEST_VERIFY;
}

static int awslc_prov_rsa_sig_init(AWSLC_PROV_RSA_SIG *sig, const EVP_MD *md) {
  int ok = 0;

  if (awslc_prov_rsa_sig_operation_is_digest(sig->operation)) {
    sig->message_digest_ctx = EVP_MD_CTX_new();
    if (sig->message_digest_ctx == NULL) {
      return 0;
    }
    return sig->operation == AWSLC_PROV_RSA_SIG_DIGEST_SIGN
               ? EVP_DigestSignInit(sig->message_digest_ctx, NULL, md, NULL,
                                    sig->pkey)
               : EVP_DigestVerifyInit(sig->message_digest_ctx, NULL, md, NULL,
                                      sig->pkey);
  }
  sig->pkey_ctx = EVP_PKEY_CTX_new(sig->pkey, NULL);
  if (sig->pkey_ctx == NULL) {
    return 0;
  }
  switch (sig->operation) {
    case AWSLC_PROV_RSA_SIG_SIGN:
      ok = EVP_PKEY_sign_init(sig->pkey_ctx);
      break;
    case AWSLC_PROV_RSA_SIG_VERIFY:
      ok = EVP_PKEY_verify_init(sig->pkey_ctx);
      break;
    case AWSLC_PROV_RSA_SIG_VERIFY_RECOVER:
      ok = EVP_PKEY_verify_recover_init(sig->pkey_ctx);
      break;
    default:
      return 0;
  }
  return ok && (md == NULL || EVP_PKEY_CTX_set_signature_md(sig->pkey_ctx, md));
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
      (restricted && !EVP_PKEY_CTX_get_rsa_pss_saltlen(
                         awslc_prov_rsa_sig_pkey_ctx(sig), &sig->saltlen)) ||
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
  if (sig->message_digest_ctx != NULL) {
    copy->message_digest_ctx = EVP_MD_CTX_new();
    if (copy->message_digest_ctx == NULL ||
        !EVP_MD_CTX_copy_ex(copy->message_digest_ctx,
                            sig->message_digest_ctx)) {
      awslc_prov_rsa_sig_free(copy);
      return NULL;
    }
  } else {
    copy->pkey_ctx = EVP_PKEY_CTX_dup(sig->pkey_ctx);
    if (copy->pkey_ctx == NULL) {
      awslc_prov_rsa_sig_free(copy);
      return NULL;
    }
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
  return sig != NULL &&
         EVP_PKEY_CTX_set_rsa_padding(awslc_prov_rsa_sig_pkey_ctx(sig), mode) &&
         awslc_prov_rsa_sig_apply_saltlen(sig);
}

int awslc_prov_rsa_sig_set_digest(void *sig_ptr, const char *digest) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  const EVP_MD *md = awslc_prov_digest_md(digest);

  return sig != NULL && sig->message_digest_ctx == NULL && md != NULL &&
         EVP_PKEY_CTX_set_signature_md(awslc_prov_rsa_sig_pkey_ctx(sig), md) &&
         awslc_prov_rsa_sig_apply_saltlen(sig);
}

int awslc_prov_rsa_sig_set_mgf1_digest(void *sig_ptr, const char *digest) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  const EVP_MD *md = awslc_prov_digest_md(digest);

  return sig != NULL && md != NULL &&
         EVP_PKEY_CTX_set_rsa_mgf1_md(awslc_prov_rsa_sig_pkey_ctx(sig), md);
}

int awslc_prov_rsa_sig_set_pss_saltlen(void *sig_ptr, int saltlen) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;

  if (sig == NULL || saltlen < AWSLC_PROV_RSA_PSS_SALTLEN_AUTO_DIGEST_MAX) {
    return 0;
  }
  // Without PSS padding AWS-LC refuses any salt length; it raises the error.
  if (!awslc_prov_rsa_sig_is_pss(sig)) {
    return EVP_PKEY_CTX_set_rsa_pss_saltlen(awslc_prov_rsa_sig_pkey_ctx(sig),
                                            RSA_PSS_SALTLEN_DIGEST);
  }
  sig->saltlen = saltlen;
  return awslc_prov_rsa_sig_apply_saltlen(sig);
}

int awslc_prov_rsa_sig_padding(const void *sig_ptr) {
  const AWSLC_PROV_RSA_SIG *sig = (const AWSLC_PROV_RSA_SIG *)sig_ptr;
  int mode = 0;

  if (sig == NULL ||
      !EVP_PKEY_CTX_get_rsa_padding(awslc_prov_rsa_sig_pkey_ctx(sig), &mode)) {
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

  if (sig == NULL ||
      !EVP_PKEY_CTX_get_signature_md(awslc_prov_rsa_sig_pkey_ctx(sig), &md)) {
    return NULL;
  }
  return md;
}

// The MGF1 digest under PSS padding, or NULL for any other padding.
static const EVP_MD *awslc_prov_rsa_sig_mgf1_md(const AWSLC_PROV_RSA_SIG *sig) {
  const EVP_MD *md = NULL;

  if (sig == NULL || !awslc_prov_rsa_sig_is_pss(sig)) {
    return NULL;
  }
  return EVP_PKEY_CTX_get_rsa_mgf1_md(awslc_prov_rsa_sig_pkey_ctx(sig), &md)
             ? md
             : NULL;
}

const char *awslc_prov_rsa_sig_digest(const void *sig) {
  return awslc_prov_digest_md_name(
      awslc_prov_rsa_sig_md((const AWSLC_PROV_RSA_SIG *)sig));
}

const char *awslc_prov_rsa_sig_mgf1_digest(const void *sig) {
  return awslc_prov_digest_md_name(
      awslc_prov_rsa_sig_mgf1_md((const AWSLC_PROV_RSA_SIG *)sig));
}

AWSLC_PROV_RSA_SIG_OPERATION awslc_prov_rsa_sig_operation(const void *sig) {
  return ((const AWSLC_PROV_RSA_SIG *)sig)->operation;
}

int awslc_prov_rsa_sig_pss_saltlen(const void *sig) {
  return sig == NULL ? 0 : ((const AWSLC_PROV_RSA_SIG *)sig)->saltlen;
}

// |sig->saltlen| as OpenSSL resolves it for the AlgorithmIdentifier, the same
// on sign and verify.
static int awslc_prov_rsa_sig_aid_saltlen(const AWSLC_PROV_RSA_SIG *sig,
                                          const EVP_MD *md) {
  const int digest_len = (int)EVP_MD_size(md);
  const int max = awslc_prov_rsa_sig_max_saltlen(sig, md);

  switch (sig->saltlen) {
    case AWSLC_PROV_RSA_PSS_SALTLEN_DIGEST:
      return digest_len;
    case AWSLC_PROV_RSA_PSS_SALTLEN_AUTO_DIGEST_MAX:
      return max < digest_len ? max : digest_len;
    case AWSLC_PROV_RSA_PSS_SALTLEN_AUTO:
    case AWSLC_PROV_RSA_PSS_SALTLEN_MAX:
      return max;
    default:
      return sig->saltlen;
  }
}

// RFC 5280 section 4.1.1.2, filled in for RSA by RFC 8017 appendix A.2:
//
//   AlgorithmIdentifier ::= SEQUENCE {
//     algorithm   OBJECT IDENTIFIER,
//     parameters  ANY DEFINED BY algorithm OPTIONAL }
//
// PKCS#1 v1.5 (A.2.4): |algorithm| names the digest's signature, such as
// sha256WithRSAEncryption, and |parameters| is NULL.
//
// PSS (A.2.3): |algorithm| is id-RSASSA-PSS and |parameters| is
// RSASSA-PSS-params, from awslc_prov_rsa_marshal_pss_params, with a special
// salt length resolved to an exact one.
//
// No padding, or no digest, names no signature, so it fails.
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
    int sig_nid = NID_undef;
    CBB null;

    ok = OBJ_find_sigid_by_algs(&sig_nid, EVP_MD_type(md), EVP_PKEY_RSA) &&
         CBB_add_asn1(&cbb, &algorithm, CBS_ASN1_SEQUENCE) &&
         OBJ_nid2cbb(&algorithm, sig_nid) &&
         CBB_add_asn1(&algorithm, &null, CBS_ASN1_NULL);
  } else if (padding == AWSLC_PROV_RSA_PADDING_PSS) {
    const EVP_MD *mgf1_md = awslc_prov_rsa_sig_mgf1_md(sig);
    const int saltlen = awslc_prov_rsa_sig_aid_saltlen(sig, md);

    ok = mgf1_md != NULL && saltlen >= 0 &&
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

  if (sig == NULL || sig->message_digest_ctx == NULL) {
    return 0;
  }
  return sig->operation == AWSLC_PROV_RSA_SIG_DIGEST_SIGN
             ? EVP_DigestSignUpdate(sig->message_digest_ctx, data, len)
             : EVP_DigestVerifyUpdate(sig->message_digest_ctx, data, len);
}

int awslc_prov_rsa_sig_sign_final(void *sig_ptr, unsigned char *out,
                                  size_t *out_len, size_t out_size) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  size_t len = out_size;

  if (sig == NULL || out_len == NULL ||
      sig->operation != AWSLC_PROV_RSA_SIG_DIGEST_SIGN ||
      !EVP_DigestSignFinal(sig->message_digest_ctx, out, &len)) {
    return 0;
  }
  *out_len = len;
  return 1;
}

int awslc_prov_rsa_sig_verify_final(void *sig_ptr, const unsigned char *in,
                                    size_t in_len) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;

  return sig != NULL && sig->operation == AWSLC_PROV_RSA_SIG_DIGEST_VERIFY &&
         EVP_DigestVerifyFinal(sig->message_digest_ctx, in, in_len) == 1;
}

int awslc_prov_rsa_sig_sign(void *sig_ptr, unsigned char *out, size_t *out_len,
                            size_t out_size, const unsigned char *tbs,
                            size_t tbs_len) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  size_t len = out_size;

  if (sig == NULL || out_len == NULL ||
      sig->operation != AWSLC_PROV_RSA_SIG_SIGN ||
      !EVP_PKEY_sign(awslc_prov_rsa_sig_pkey_ctx(sig), out, &len, tbs,
                     tbs_len)) {
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
         EVP_PKEY_verify(awslc_prov_rsa_sig_pkey_ctx(sig), in, in_len, tbs,
                         tbs_len) == 1;
}

int awslc_prov_rsa_sig_verify_recover(void *sig_ptr, unsigned char *out,
                                      size_t *out_len, size_t out_size,
                                      const unsigned char *in, size_t in_len) {
  AWSLC_PROV_RSA_SIG *sig = (AWSLC_PROV_RSA_SIG *)sig_ptr;
  size_t len = out_size;

  if (sig == NULL || out_len == NULL ||
      sig->operation != AWSLC_PROV_RSA_SIG_VERIFY_RECOVER ||
      !EVP_PKEY_verify_recover(awslc_prov_rsa_sig_pkey_ctx(sig), out, &len, in,
                               in_len)) {
    return 0;
  }
  *out_len = len;
  return 1;
}
