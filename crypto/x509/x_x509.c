// Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com) All rights reserved.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdio.h>

#include <openssl/asn1t.h>
#include <openssl/bytestring.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/obj.h>
#include <openssl/pool.h>
#include <openssl/sha.h>
#include <openssl/thread.h>
#include <openssl/x509.h>

#include "../asn1/internal.h"
#include "../internal.h"
#include "internal.h"

#include "x509_view.h"

static CRYPTO_EX_DATA_CLASS g_ex_data_class = CRYPTO_EX_DATA_CLASS_INIT;

static struct CRYPTO_STATIC_MUTEX g_x509_view_fallback_lock =
    CRYPTO_STATIC_MUTEX_INIT;
static uint64_t
    g_x509_view_fallback_counts[AWSLC_X509_PARSE_INPUT_TOO_LARGE + 1];

enum {
  X509_VIEW_MATERIALIZED_SERIAL = 1 << 0,
  X509_VIEW_MATERIALIZED_ISSUER = 1 << 1,
  X509_VIEW_MATERIALIZED_VALIDITY = 1 << 2,
  X509_VIEW_MATERIALIZED_SUBJECT = 1 << 3,
  X509_VIEW_MATERIALIZED_KEY = 1 << 4,
  X509_VIEW_MATERIALIZED_EXTENSIONS = 1 << 5,
  X509_VIEW_MATERIALIZED_TBS_SIG_ALG = 1 << 6,
  X509_VIEW_MATERIALIZED_SIG_ALG = 1 << 7,
  X509_VIEW_MATERIALIZED_SIGNATURE = 1 << 8,
};

static int x509_i2d_view_range(const X509 *x509, int tbs, unsigned char **out,
                               int *out_handled);
static X509 *x509_new_parsed_view(CRYPTO_BUFFER *buf,
                                  const AWSLC_X509_CERTIFICATE_VIEW *view);
static int x509_ex_new(ASN1_VALUE **val, const ASN1_ITEM *it);
static void x509_ex_free(ASN1_VALUE **val, const ASN1_ITEM *it);
static int x509_ex_d2i(ASN1_VALUE **val, const unsigned char **in, long len,
                       const ASN1_ITEM *it, int tag, int aclass, char opt,
                       ASN1_TLC *ctx);
static int x509_ex_i2d(ASN1_VALUE **val, unsigned char **out,
                       const ASN1_ITEM *it, int tag, int aclass);

static void x509_record_view_fallback(uint32_t parse_result) {
  if (parse_result == AWSLC_X509_PARSE_OK ||
      parse_result > AWSLC_X509_PARSE_INPUT_TOO_LARGE) {
    return;
  }
  CRYPTO_STATIC_MUTEX_lock_write(&g_x509_view_fallback_lock);
  g_x509_view_fallback_counts[parse_result]++;
  CRYPTO_STATIC_MUTEX_unlock_write(&g_x509_view_fallback_lock);
}

uint64_t x509_view_fallback_count_for_testing(uint32_t parse_result) {
  if (parse_result > AWSLC_X509_PARSE_INPUT_TOO_LARGE) {
    return 0;
  }
  CRYPTO_STATIC_MUTEX_lock_read(&g_x509_view_fallback_lock);
  const uint64_t count = g_x509_view_fallback_counts[parse_result];
  CRYPTO_STATIC_MUTEX_unlock_read(&g_x509_view_fallback_lock);
  return count;
}

void x509_view_reset_fallback_counts_for_testing(void) {
  CRYPTO_STATIC_MUTEX_lock_write(&g_x509_view_fallback_lock);
  OPENSSL_memset(g_x509_view_fallback_counts, 0,
                 sizeof(g_x509_view_fallback_counts));
  CRYPTO_STATIC_MUTEX_unlock_write(&g_x509_view_fallback_lock);
}

ASN1_SEQUENCE_enc(X509_CINF, enc, 0) = {
    ASN1_EXP_OPT(X509_CINF, version, ASN1_INTEGER, 0),
    ASN1_SIMPLE(X509_CINF, serialNumber, ASN1_INTEGER),
    ASN1_SIMPLE(X509_CINF, signature, X509_ALGOR),
    ASN1_SIMPLE(X509_CINF, issuer, X509_NAME),
    ASN1_SIMPLE(X509_CINF, validity, X509_VAL),
    ASN1_SIMPLE(X509_CINF, subject, X509_NAME),
    ASN1_SIMPLE(X509_CINF, key, X509_PUBKEY),
    ASN1_IMP_OPT(X509_CINF, issuerUID, ASN1_BIT_STRING, 1),
    ASN1_IMP_OPT(X509_CINF, subjectUID, ASN1_BIT_STRING, 2),
    ASN1_EXP_SEQUENCE_OF_OPT(X509_CINF, extensions, X509_EXTENSION, 3),
} ASN1_SEQUENCE_END_enc(X509_CINF, X509_CINF)

IMPLEMENT_ASN1_FUNCTIONS(X509_CINF)
// X509 top level structure needs a bit of customisation

static int x509_cb(int operation, ASN1_VALUE **pval, const ASN1_ITEM *it,
                   void *exarg) {
  X509 *ret = (X509 *)*pval;

  switch (operation) {
    case ASN1_OP_NEW_POST:
      ret->ex_flags = 0;
      ret->ex_pathlen = -1;
      ret->skid = NULL;
      ret->akid = NULL;
      ret->aux = NULL;
      ret->crldp = NULL;
      ret->buf = NULL;
      ret->view_state = X509_VIEW_STATE_EAGER;
      CRYPTO_new_ex_data(&ret->ex_data);
      CRYPTO_MUTEX_init(&ret->lock);
      break;

    case ASN1_OP_D2I_PRE:
      CRYPTO_BUFFER_free(ret->buf);
      ret->buf = NULL;
      OPENSSL_memset(&ret->view, 0, sizeof(ret->view));
      ret->view_state = X509_VIEW_STATE_EAGER;
      break;

    case ASN1_OP_D2I_POST: {
      // The version must be one of v1(0), v2(1), or v3(2).
      long version = X509_VERSION_1;
      if (ret->cert_info->version != NULL) {
        version = ASN1_INTEGER_get(ret->cert_info->version);
        // TODO(https://crbug.com/boringssl/364): |X509_VERSION_1| should
        // also be rejected here. This means an explicitly-encoded X.509v1
        // version. v1 is DEFAULT, so DER requires it be omitted.
        if (version < X509_VERSION_1 || version > X509_VERSION_3) {
          OPENSSL_PUT_ERROR(X509, X509_R_INVALID_VERSION);
          return 0;
        }
      }

      // Per RFC 5280, section 4.1.2.8, these fields require v2 or v3.
      if (version == X509_VERSION_1 && (ret->cert_info->issuerUID != NULL ||
                                        ret->cert_info->subjectUID != NULL)) {
        OPENSSL_PUT_ERROR(X509, X509_R_INVALID_FIELD_FOR_VERSION);
        return 0;
      }

      // Per RFC 5280, section 4.1.2.9, extensions require v3.
      if (version != X509_VERSION_3 && ret->cert_info->extensions != NULL) {
        OPENSSL_PUT_ERROR(X509, X509_R_INVALID_FIELD_FOR_VERSION);
        return 0;
      }

      break;
    }

    case ASN1_OP_FREE_POST:
      ASN1_INTEGER_free(ret->view_serial);
      X509_NAME_free(ret->view_issuer);
      X509_VAL_free(ret->view_validity);
      X509_NAME_free(ret->view_subject);
      X509_PUBKEY_free(ret->view_key);
      sk_X509_EXTENSION_pop_free(ret->view_extensions, X509_EXTENSION_free);
      X509_ALGOR_free(ret->view_tbs_sig_alg);
      X509_ALGOR_free(ret->view_sig_alg);
      ASN1_BIT_STRING_free(ret->view_signature);
      CRYPTO_MUTEX_cleanup(&ret->lock);
      CRYPTO_free_ex_data(&g_ex_data_class, ret, &ret->ex_data);
      X509_CERT_AUX_free(ret->aux);
      ASN1_OCTET_STRING_free(ret->skid);
      AUTHORITY_KEYID_free(ret->akid);
      CRL_DIST_POINTS_free(ret->crldp);
      GENERAL_NAMES_free(ret->altname);
      NAME_CONSTRAINTS_free(ret->nc);
      CRYPTO_BUFFER_free(ret->buf);
      break;
  }

  return 1;
}

typedef X509 X509_LEGACY;

ASN1_SEQUENCE_ref(X509_LEGACY, x509_cb) = {
    ASN1_SIMPLE(X509_LEGACY, cert_info, X509_CINF),
    ASN1_SIMPLE(X509_LEGACY, sig_alg, X509_ALGOR),
    ASN1_SIMPLE(X509_LEGACY, signature, ASN1_BIT_STRING),
} ASN1_SEQUENCE_END_ref(X509_LEGACY, X509_LEGACY)

static const ASN1_EXTERN_FUNCS x509_ff = {
    NULL, x509_ex_new, x509_ex_free, x509_ex_d2i, x509_ex_i2d, NULL,
};

IMPLEMENT_EXTERN_ASN1(X509, V_ASN1_SEQUENCE, x509_ff)

static int x509_ex_new(ASN1_VALUE **val, const ASN1_ITEM *it) {
  return ASN1_item_ex_new(val, ASN1_ITEM_rptr(X509_LEGACY));
}

static void x509_ex_free(ASN1_VALUE **val, const ASN1_ITEM *it) {
  ASN1_item_ex_free(val, ASN1_ITEM_rptr(X509_LEGACY));
}

static int x509_ex_d2i(ASN1_VALUE **val, const unsigned char **in, long len,
                       const ASN1_ITEM *it, int tag, int aclass, char opt,
                       ASN1_TLC *ctx) {
  if (*val != NULL && !x509_ensure_legacy((X509 *)*val)) {
    return 0;
  }
  return ASN1_item_ex_d2i(val, in, len, ASN1_ITEM_rptr(X509_LEGACY), tag,
                          aclass, opt, ctx);
}

static int x509_ex_i2d(ASN1_VALUE **val, unsigned char **out,
                       const ASN1_ITEM *it, int tag, int aclass) {
  X509 *x509 = (X509 *)*val;
  if (tag == -1) {
    int handled = 0;
    const int view_result = x509_i2d_view_range(x509, /*tbs=*/0, out, &handled);
    if (handled) {
      return view_result;
    }
  }
  if (!x509_ensure_legacy(x509)) {
    return -1;
  }
  return ASN1_item_ex_i2d(val, out, ASN1_ITEM_rptr(X509_LEGACY), tag, aclass);
}

X509 *X509_new(void) { return (X509 *)ASN1_item_new(ASN1_ITEM_rptr(X509)); }

void X509_free(X509 *x509) {
  ASN1_item_free((ASN1_VALUE *)x509, ASN1_ITEM_rptr(X509));
}

static X509 *d2i_X509_legacy(X509 **out, const unsigned char **in, long len) {
  if (out != NULL && *out != NULL && !x509_ensure_legacy(*out)) {
    return NULL;
  }
  return (X509 *)ASN1_item_d2i((ASN1_VALUE **)out, in, len,
                               ASN1_ITEM_rptr(X509));
}

X509 *d2i_X509(X509 **out, const unsigned char **in, long len) {
  // Preserve the legacy decoder's in-place object reuse semantics. Optimizing
  // this case requires resetting the complete object graph and extension
  // caches while preserving the outer pointer, reference count, and ex-data.
  if (out != NULL && *out != NULL) {
    return d2i_X509_legacy(out, in, len);
  }

  uint32_t view_parse_result = AWSLC_X509_PARSE_NULL_POINTER;
  int view_parse_attempted = 0;
  if (in != NULL && *in != NULL && len >= 0) {
    AWSLC_X509_CERTIFICATE_VIEW view;
    OPENSSL_memset(&view, 0, sizeof(view));
    view_parse_attempted = 1;
    view_parse_result =
        x509_parse_der_view(*in, (size_t)len, /*exact=*/0, &view);
    if (view_parse_result == AWSLC_X509_PARSE_OK) {
      if (view.certificate.offset != 0 ||
          view.certificate.length > (uint64_t)len) {
        OPENSSL_PUT_ERROR(X509, ERR_R_INTERNAL_ERROR);
        return NULL;
      }

      CRYPTO_BUFFER *buf =
          CRYPTO_BUFFER_new(*in, view.certificate.length, NULL);
      if (buf == NULL) {
        return NULL;
      }
      X509 *x509 = x509_new_parsed_view(buf, &view);
      CRYPTO_BUFFER_free(buf);
      if (x509 == NULL) {
        return NULL;
      }

      *in += view.certificate.length;
      if (out != NULL) {
        *out = x509;
      }
      return x509;
    }
  }

  // Compatibility fallback for BER and legacy encodings not yet accepted by
  // the selected view parser.
  X509 *ret = d2i_X509_legacy(out, in, len);
  if (ret != NULL && view_parse_attempted) {
    x509_record_view_fallback(view_parse_result);
  }
  return ret;
}

int i2d_X509(X509 *x509, unsigned char **out) {
  int handled = 0;
  const int view_result = x509_i2d_view_range(x509, /*tbs=*/0, out, &handled);
  if (handled) {
    return view_result;
  }
  if (!x509_ensure_legacy(x509)) {
    return -1;
  }
  return ASN1_item_i2d((ASN1_VALUE *)x509, out, ASN1_ITEM_rptr(X509));
}

X509 *X509_dup(X509 *x509) {
  if (x509 != NULL && x509->buf != NULL) {
    CRYPTO_MUTEX_lock_read(&x509->lock);
    if (x509->view_state == X509_VIEW_STATE_PARSED) {
      X509 *ret = x509_new_parsed_view(x509->buf, &x509->view);
      CRYPTO_MUTEX_unlock_read(&x509->lock);
      return ret;
    }
    CRYPTO_MUTEX_unlock_read(&x509->lock);
  }
  if (!x509_ensure_legacy(x509)) {
    return NULL;
  }
  return ASN1_item_dup(ASN1_ITEM_rptr(X509), x509);
}

static int x509_i2d_view_range(const X509 *x509, int tbs, unsigned char **out,
                               int *out_handled) {
  // Mutable-pointer getters do not invalidate the cached encoding in the
  // legacy representation. Preserve that behavior by serializing pristine
  // view bytes until an API explicitly transitions the object to eager form.
  *out_handled = 0;
  if (x509 == NULL || x509->buf == NULL) {
    return -1;
  }

  CRYPTO_MUTEX_lock_read((CRYPTO_MUTEX *)&x509->lock);
  if (x509->view_state != X509_VIEW_STATE_PARSED) {
    CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&x509->lock);
    return 0;
  }
  *out_handled = 1;

  const AWSLC_X509_DER_RANGE range =
      tbs ? x509->view.tbs_certificate : x509->view.certificate;
  const size_t buffer_len = CRYPTO_BUFFER_len(x509->buf);
  if (range.offset > buffer_len || range.length > buffer_len - range.offset ||
      range.length > INT_MAX) {
    CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&x509->lock);
    OPENSSL_PUT_ERROR(X509, ERR_R_INTERNAL_ERROR);
    return -1;
  }

  const uint8_t *data = CRYPTO_BUFFER_data(x509->buf) + range.offset;
  if (out == NULL) {
    CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&x509->lock);
    return (int)range.length;
  }
  if (*out == NULL) {
    uint8_t *copy = OPENSSL_memdup(data, range.length);
    CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&x509->lock);
    if (copy == NULL) {
      return -1;
    }
    *out = copy;
    return (int)range.length;
  }

  OPENSSL_memcpy(*out, data, range.length);
  *out += range.length;
  CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&x509->lock);
  return (int)range.length;
}

static X509 *x509_new_parsed_view(CRYPTO_BUFFER *buf,
                                  const AWSLC_X509_CERTIFICATE_VIEW *view) {
  X509 *x509 = OPENSSL_zalloc(sizeof(X509));
  if (x509 == NULL) {
    return NULL;
  }

  x509->references = 1;
  x509->ex_pathlen = -1;
  x509->view = *view;
  x509->view_state = X509_VIEW_STATE_PARSED;
  CRYPTO_new_ex_data(&x509->ex_data);
  CRYPTO_MUTEX_init(&x509->lock);
  CRYPTO_BUFFER_up_ref(buf);
  x509->buf = buf;
  return x509;
}

int x509_ensure_legacy(const X509 *const_x509) {
  if (const_x509 == NULL) {
    return 0;
  }
  X509 *x509 = (X509 *)const_x509;

  // Eager objects and stack-only lookup keys do not retain an input buffer.
  // The latter do not have an initialized mutex.
  if (x509->buf == NULL) {
    return x509->cert_info != NULL;
  }

  CRYPTO_MUTEX_lock_read(&x509->lock);
  const uint8_t state = x509->view_state;
  CRYPTO_MUTEX_unlock_read(&x509->lock);
  if (state == X509_VIEW_STATE_EAGER) {
    return 1;
  }
  X509 *legacy = X509_new();
  if (legacy == NULL) {
    return 0;
  }
  legacy->cert_info->enc.alias_only_on_next_parse = 1;

  const uint8_t *input = CRYPTO_BUFFER_data(x509->buf);
  const size_t input_len = CRYPTO_BUFFER_len(x509->buf);
  X509 *legacy_out = legacy;
  X509 *decoded = d2i_X509_legacy(&legacy_out, &input, (long)input_len);
  if (decoded == NULL || input != CRYPTO_BUFFER_data(x509->buf) + input_len) {
    X509_free(legacy_out);
    // A successful view parse guarantees structural materializability. A
    // failure here is therefore transient (normally allocation failure) or an
    // internal parser bug. Leave the view intact so a later call can retry.
    return 0;
  }

  CRYPTO_MUTEX_lock_write(&x509->lock);
  if (x509->view_state == X509_VIEW_STATE_PARSED) {
    const uint16_t materialized = x509->view_materialized;
    if (materialized & X509_VIEW_MATERIALIZED_SERIAL) {
      ASN1_INTEGER_free(legacy->cert_info->serialNumber);
      legacy->cert_info->serialNumber = x509->view_serial;
      x509->view_serial = NULL;
    }
    if (materialized & X509_VIEW_MATERIALIZED_ISSUER) {
      X509_NAME_free(legacy->cert_info->issuer);
      legacy->cert_info->issuer = x509->view_issuer;
      x509->view_issuer = NULL;
    }
    if (materialized & X509_VIEW_MATERIALIZED_VALIDITY) {
      X509_VAL_free(legacy->cert_info->validity);
      legacy->cert_info->validity = x509->view_validity;
      x509->view_validity = NULL;
    }
    if (materialized & X509_VIEW_MATERIALIZED_SUBJECT) {
      X509_NAME_free(legacy->cert_info->subject);
      legacy->cert_info->subject = x509->view_subject;
      x509->view_subject = NULL;
    }
    if (materialized & X509_VIEW_MATERIALIZED_KEY) {
      X509_PUBKEY_free(legacy->cert_info->key);
      legacy->cert_info->key = x509->view_key;
      x509->view_key = NULL;
    }
    if (materialized & X509_VIEW_MATERIALIZED_EXTENSIONS) {
      sk_X509_EXTENSION_pop_free(legacy->cert_info->extensions,
                                 X509_EXTENSION_free);
      legacy->cert_info->extensions = x509->view_extensions;
      x509->view_extensions = NULL;
    }
    if (materialized & X509_VIEW_MATERIALIZED_TBS_SIG_ALG) {
      X509_ALGOR_free(legacy->cert_info->signature);
      legacy->cert_info->signature = x509->view_tbs_sig_alg;
      x509->view_tbs_sig_alg = NULL;
    }
    if (materialized & X509_VIEW_MATERIALIZED_SIG_ALG) {
      X509_ALGOR_free(legacy->sig_alg);
      legacy->sig_alg = x509->view_sig_alg;
      x509->view_sig_alg = NULL;
    }
    if (materialized & X509_VIEW_MATERIALIZED_SIGNATURE) {
      ASN1_BIT_STRING_free(legacy->signature);
      legacy->signature = x509->view_signature;
      x509->view_signature = NULL;
    }
    x509->cert_info = legacy->cert_info;
    legacy->cert_info = NULL;
    x509->sig_alg = legacy->sig_alg;
    legacy->sig_alg = NULL;
    x509->signature = legacy->signature;
    legacy->signature = NULL;
    x509->view_materialized = 0;
    x509->view_state = X509_VIEW_STATE_EAGER;
  }
  CRYPTO_MUTEX_unlock_write(&x509->lock);
  X509_free(legacy);
  return 1;
}

int x509_get_view_version(const X509 *x509, long *out_version) {
  if (x509 == NULL || x509->buf == NULL) {
    return 0;
  }
  CRYPTO_MUTEX_lock_read((CRYPTO_MUTEX *)&x509->lock);
  const int is_view = x509->view_state == X509_VIEW_STATE_PARSED;
  if (is_view) {
    *out_version = x509->view.version;
  }
  CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&x509->lock);
  return is_view;
}

static void x509_free_materialized_field(uint16_t field, void *value) {
  switch (field) {
    case X509_VIEW_MATERIALIZED_SERIAL:
      ASN1_INTEGER_free(value);
      break;
    case X509_VIEW_MATERIALIZED_ISSUER:
    case X509_VIEW_MATERIALIZED_SUBJECT:
      X509_NAME_free(value);
      break;
    case X509_VIEW_MATERIALIZED_VALIDITY:
      X509_VAL_free(value);
      break;
    case X509_VIEW_MATERIALIZED_KEY:
      X509_PUBKEY_free(value);
      break;
    case X509_VIEW_MATERIALIZED_EXTENSIONS:
      sk_X509_EXTENSION_pop_free(value, X509_EXTENSION_free);
      break;
    case X509_VIEW_MATERIALIZED_TBS_SIG_ALG:
    case X509_VIEW_MATERIALIZED_SIG_ALG:
      X509_ALGOR_free(value);
      break;
    case X509_VIEW_MATERIALIZED_SIGNATURE:
      ASN1_BIT_STRING_free(value);
      break;
  }
}

static int x509_materialize_field(const X509 *const_x509, uint16_t field) {
  if (const_x509 == NULL) {
    return 0;
  }
  X509 *x509 = (X509 *)const_x509;
  if (x509->buf == NULL) {
    return x509->cert_info != NULL;
  }

  AWSLC_X509_DER_RANGE range;
  CRYPTO_MUTEX_lock_read(&x509->lock);
  if (x509->view_state == X509_VIEW_STATE_EAGER ||
      (x509->view_state == X509_VIEW_STATE_PARSED &&
       (x509->view_materialized & field))) {
    CRYPTO_MUTEX_unlock_read(&x509->lock);
    return 1;
  }
  switch (field) {
    case X509_VIEW_MATERIALIZED_SERIAL:
      range = x509->view.serial;
      break;
    case X509_VIEW_MATERIALIZED_ISSUER:
      range = x509->view.issuer;
      break;
    case X509_VIEW_MATERIALIZED_VALIDITY:
      range = x509->view.validity;
      break;
    case X509_VIEW_MATERIALIZED_SUBJECT:
      range = x509->view.subject;
      break;
    case X509_VIEW_MATERIALIZED_KEY:
      range = x509->view.spki;
      break;
    case X509_VIEW_MATERIALIZED_EXTENSIONS:
      range = x509->view.extensions;
      break;
    case X509_VIEW_MATERIALIZED_TBS_SIG_ALG:
      range = x509->view.tbs_signature_algorithm;
      break;
    case X509_VIEW_MATERIALIZED_SIG_ALG:
      range = x509->view.signature_algorithm;
      break;
    case X509_VIEW_MATERIALIZED_SIGNATURE:
      range = x509->view.signature;
      break;
    default:
      CRYPTO_MUTEX_unlock_read(&x509->lock);
      return 0;
  }
  CRYPTO_MUTEX_unlock_read(&x509->lock);

  const size_t buffer_len = CRYPTO_BUFFER_len(x509->buf);
  if (range.offset > buffer_len || range.length > buffer_len - range.offset) {
    OPENSSL_PUT_ERROR(X509, ERR_R_INTERNAL_ERROR);
    return 0;
  }
#if LONG_MAX < UINT32_MAX
  if (range.length > (uint32_t)LONG_MAX) {
    OPENSSL_PUT_ERROR(X509, ERR_R_OVERFLOW);
    return 0;
  }
#endif

  const uint8_t *start = CRYPTO_BUFFER_data(x509->buf) + range.offset;
  const uint8_t *input = start;
  void *candidate = NULL;
  int decoded = 0;
  switch (field) {
    case X509_VIEW_MATERIALIZED_SERIAL:
      candidate = d2i_ASN1_INTEGER(NULL, &input, (long)range.length);
      decoded = candidate != NULL;
      break;
    case X509_VIEW_MATERIALIZED_ISSUER:
    case X509_VIEW_MATERIALIZED_SUBJECT:
      candidate = d2i_X509_NAME(NULL, &input, (long)range.length);
      decoded = candidate != NULL;
      break;
    case X509_VIEW_MATERIALIZED_VALIDITY:
      candidate = d2i_X509_VAL(NULL, &input, (long)range.length);
      decoded = candidate != NULL;
      break;
    case X509_VIEW_MATERIALIZED_KEY:
      candidate = d2i_X509_PUBKEY(NULL, &input, (long)range.length);
      decoded = candidate != NULL;
      break;
    case X509_VIEW_MATERIALIZED_EXTENSIONS: {
      if (range.length == 0) {
        decoded = 1;
        break;
      }
      CBS encoded, explicit_extensions;
      CBS_init(&encoded, input, range.length);
      if (CBS_get_asn1(&encoded, &explicit_extensions,
                       CBS_ASN1_CONTEXT_SPECIFIC | CBS_ASN1_CONSTRUCTED | 3) &&
          CBS_len(&encoded) == 0) {
        input = CBS_data(&explicit_extensions);
        candidate =
            d2i_X509_EXTENSIONS(NULL, &input, CBS_len(&explicit_extensions));
        decoded =
            candidate != NULL && input == CBS_data(&explicit_extensions) +
                                              CBS_len(&explicit_extensions);
      }
      break;
    }
    case X509_VIEW_MATERIALIZED_TBS_SIG_ALG:
    case X509_VIEW_MATERIALIZED_SIG_ALG:
      candidate = d2i_X509_ALGOR(NULL, &input, (long)range.length);
      decoded = candidate != NULL;
      break;
    case X509_VIEW_MATERIALIZED_SIGNATURE:
      candidate = d2i_ASN1_BIT_STRING(NULL, &input, (long)range.length);
      decoded = candidate != NULL;
      break;
  }
  if (field != X509_VIEW_MATERIALIZED_EXTENSIONS) {
    decoded = decoded && input == start + range.length;
  }

  if (!decoded) {
    x509_free_materialized_field(field, candidate);
    CRYPTO_MUTEX_lock_read(&x509->lock);
    const int raced_with_full_decode =
        x509->view_state == X509_VIEW_STATE_EAGER;
    CRYPTO_MUTEX_unlock_read(&x509->lock);
    // Do not poison the certificate on allocation failure. Since the parser's
    // accepted language is a subset of these decoders, structural failures
    // indicate a parser bug and remain retryable as well.
    if (!raced_with_full_decode && ERR_peek_error() == 0) {
      OPENSSL_PUT_ERROR(X509, ERR_R_INTERNAL_ERROR);
    }
    return raced_with_full_decode;
  }

  CRYPTO_MUTEX_lock_write(&x509->lock);
  if (x509->view_state == X509_VIEW_STATE_PARSED &&
      !(x509->view_materialized & field)) {
    switch (field) {
      case X509_VIEW_MATERIALIZED_SERIAL:
        x509->view_serial = candidate;
        break;
      case X509_VIEW_MATERIALIZED_ISSUER:
        x509->view_issuer = candidate;
        break;
      case X509_VIEW_MATERIALIZED_VALIDITY:
        x509->view_validity = candidate;
        break;
      case X509_VIEW_MATERIALIZED_SUBJECT:
        x509->view_subject = candidate;
        break;
      case X509_VIEW_MATERIALIZED_KEY:
        x509->view_key = candidate;
        break;
      case X509_VIEW_MATERIALIZED_EXTENSIONS:
        x509->view_extensions = candidate;
        break;
      case X509_VIEW_MATERIALIZED_TBS_SIG_ALG:
        x509->view_tbs_sig_alg = candidate;
        break;
      case X509_VIEW_MATERIALIZED_SIG_ALG:
        x509->view_sig_alg = candidate;
        break;
      case X509_VIEW_MATERIALIZED_SIGNATURE:
        x509->view_signature = candidate;
        break;
    }
    x509->view_materialized |= field;
    candidate = NULL;
  }
  CRYPTO_MUTEX_unlock_write(&x509->lock);
  x509_free_materialized_field(field, candidate);
  return 1;
}

static void *x509_get_cached_field(const X509 *x509, uint16_t field) {
  if (!x509_materialize_field(x509, field)) {
    return NULL;
  }
  if (x509->buf == NULL) {
    switch (field) {
      case X509_VIEW_MATERIALIZED_SERIAL:
        return x509->cert_info->serialNumber;
      case X509_VIEW_MATERIALIZED_ISSUER:
        return x509->cert_info->issuer;
      case X509_VIEW_MATERIALIZED_VALIDITY:
        return x509->cert_info->validity;
      case X509_VIEW_MATERIALIZED_SUBJECT:
        return x509->cert_info->subject;
      case X509_VIEW_MATERIALIZED_KEY:
        return x509->cert_info->key;
      case X509_VIEW_MATERIALIZED_EXTENSIONS:
        return x509->cert_info->extensions;
      case X509_VIEW_MATERIALIZED_TBS_SIG_ALG:
        return x509->cert_info->signature;
      case X509_VIEW_MATERIALIZED_SIG_ALG:
        return x509->sig_alg;
      case X509_VIEW_MATERIALIZED_SIGNATURE:
        return x509->signature;
    }
  }

  void *result = NULL;
  CRYPTO_MUTEX_lock_read((CRYPTO_MUTEX *)&x509->lock);
  if (x509->view_state == X509_VIEW_STATE_EAGER) {
    switch (field) {
      case X509_VIEW_MATERIALIZED_SERIAL:
        result = x509->cert_info->serialNumber;
        break;
      case X509_VIEW_MATERIALIZED_ISSUER:
        result = x509->cert_info->issuer;
        break;
      case X509_VIEW_MATERIALIZED_VALIDITY:
        result = x509->cert_info->validity;
        break;
      case X509_VIEW_MATERIALIZED_SUBJECT:
        result = x509->cert_info->subject;
        break;
      case X509_VIEW_MATERIALIZED_KEY:
        result = x509->cert_info->key;
        break;
      case X509_VIEW_MATERIALIZED_EXTENSIONS:
        result = x509->cert_info->extensions;
        break;
      case X509_VIEW_MATERIALIZED_TBS_SIG_ALG:
        result = x509->cert_info->signature;
        break;
      case X509_VIEW_MATERIALIZED_SIG_ALG:
        result = x509->sig_alg;
        break;
      case X509_VIEW_MATERIALIZED_SIGNATURE:
        result = x509->signature;
        break;
    }
  } else if (x509->view_state == X509_VIEW_STATE_PARSED) {
    switch (field) {
      case X509_VIEW_MATERIALIZED_SERIAL:
        result = x509->view_serial;
        break;
      case X509_VIEW_MATERIALIZED_ISSUER:
        result = x509->view_issuer;
        break;
      case X509_VIEW_MATERIALIZED_VALIDITY:
        result = x509->view_validity;
        break;
      case X509_VIEW_MATERIALIZED_SUBJECT:
        result = x509->view_subject;
        break;
      case X509_VIEW_MATERIALIZED_KEY:
        result = x509->view_key;
        break;
      case X509_VIEW_MATERIALIZED_EXTENSIONS:
        result = x509->view_extensions;
        break;
      case X509_VIEW_MATERIALIZED_TBS_SIG_ALG:
        result = x509->view_tbs_sig_alg;
        break;
      case X509_VIEW_MATERIALIZED_SIG_ALG:
        result = x509->view_sig_alg;
        break;
      case X509_VIEW_MATERIALIZED_SIGNATURE:
        result = x509->view_signature;
        break;
    }
  }
  CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&x509->lock);
  return result;
}

ASN1_INTEGER *x509_get_cached_serial(const X509 *x509) {
  return x509_get_cached_field(x509, X509_VIEW_MATERIALIZED_SERIAL);
}

X509_NAME *x509_get_cached_issuer(const X509 *x509) {
  return x509_get_cached_field(x509, X509_VIEW_MATERIALIZED_ISSUER);
}

X509_VAL *x509_get_cached_validity(const X509 *x509) {
  return x509_get_cached_field(x509, X509_VIEW_MATERIALIZED_VALIDITY);
}

X509_NAME *x509_get_cached_subject(const X509 *x509) {
  return x509_get_cached_field(x509, X509_VIEW_MATERIALIZED_SUBJECT);
}

X509_PUBKEY *x509_get_cached_pubkey(const X509 *x509) {
  return x509_get_cached_field(x509, X509_VIEW_MATERIALIZED_KEY);
}

STACK_OF(X509_EXTENSION) *x509_get_cached_extensions(const X509 *x509) {
  return x509_get_cached_field(x509, X509_VIEW_MATERIALIZED_EXTENSIONS);
}

int x509_get_cached_extensions_ex(const X509 *x509,
                                  STACK_OF(X509_EXTENSION) **out_extensions) {
  if (!x509_materialize_field(x509, X509_VIEW_MATERIALIZED_EXTENSIONS)) {
    *out_extensions = NULL;
    return 0;
  }
  *out_extensions = x509_get_cached_extensions(x509);
  return 1;
}

void *x509_get_view_extension_d2i(const X509 *x509, int slot, int nid,
                                  int *out_status, int *out_handled) {
  *out_status = -1;
  *out_handled = 0;
  if (x509 == NULL || x509->buf == NULL || slot < 0 ||
      slot >= AWSLC_X509_EXTENSION_SLOT_COUNT) {
    return NULL;
  }

  if (x509->view_state != X509_VIEW_STATE_PARSED ||
      (x509->view_materialized & X509_VIEW_MATERIALIZED_EXTENSIONS)) {
    return NULL;
  }
  *out_handled = 1;
  const uint32_t present = 1u << slot;
  const uint32_t duplicate = 1u
                             << (AWSLC_X509_EXTENSION_DUPLICATE_SHIFT + slot);
  const uint32_t critical = 1u << (AWSLC_X509_EXTENSION_CRITICAL_SHIFT + slot);
  const uint32_t flags = x509->view.extension_flags;
  const AWSLC_X509_DER_RANGE range = x509->view.extension_values[slot];

  if ((flags & duplicate) != 0) {
    *out_status = -2;
    return NULL;
  }
  if ((flags & present) == 0) {
    return NULL;
  }
  *out_status = (flags & critical) != 0;

  const size_t buffer_len = CRYPTO_BUFFER_len(x509->buf);
  if (range.offset > buffer_len || range.length > buffer_len - range.offset) {
    OPENSSL_PUT_ERROR(X509, ERR_R_INTERNAL_ERROR);
    return NULL;
  }
  return x509v3_ext_d2i_nid(nid, CRYPTO_BUFFER_data(x509->buf) + range.offset,
                            range.length);
}

void *x509_get_view_extension_d2i_by_nid(const X509 *x509, int nid,
                                         int *out_status, int *out_handled) {
  int slot = -1;
  switch (nid) {
    case NID_basic_constraints:
      slot = AWSLC_X509_EXTENSION_BASIC_CONSTRAINTS;
      break;
    case NID_key_usage:
      slot = AWSLC_X509_EXTENSION_KEY_USAGE;
      break;
    case NID_ext_key_usage:
      slot = AWSLC_X509_EXTENSION_EXTENDED_KEY_USAGE;
      break;
    case NID_netscape_cert_type:
      slot = AWSLC_X509_EXTENSION_NETSCAPE_CERT_TYPE;
      break;
    case NID_subject_key_identifier:
      slot = AWSLC_X509_EXTENSION_SUBJECT_KEY_IDENTIFIER;
      break;
    case NID_authority_key_identifier:
      slot = AWSLC_X509_EXTENSION_AUTHORITY_KEY_IDENTIFIER;
      break;
    case NID_subject_alt_name:
      slot = AWSLC_X509_EXTENSION_SUBJECT_ALT_NAME;
      break;
    case NID_name_constraints:
      slot = AWSLC_X509_EXTENSION_NAME_CONSTRAINTS;
      break;
    case NID_crl_distribution_points:
      slot = AWSLC_X509_EXTENSION_CRL_DISTRIBUTION_POINTS;
      break;
    default:
      *out_status = -1;
      *out_handled = 0;
      return NULL;
  }

  if (x509 == NULL || x509->buf == NULL) {
    *out_status = -1;
    *out_handled = 0;
    return NULL;
  }
  CRYPTO_MUTEX_lock_read((CRYPTO_MUTEX *)&x509->lock);
  void *ret =
      x509_get_view_extension_d2i(x509, slot, nid, out_status, out_handled);
  CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&x509->lock);
  return ret;
}

int x509_view_has_unsupported_critical(const X509 *x509, int *out_value,
                                       int *out_handled) {
  *out_value = 0;
  *out_handled = 0;
  if (x509 == NULL || x509->buf == NULL) {
    return 1;
  }

  if (x509->view_state == X509_VIEW_STATE_PARSED &&
      !(x509->view_materialized & X509_VIEW_MATERIALIZED_EXTENSIONS)) {
    *out_handled = 1;
    *out_value = (x509->view.extension_flags &
                  AWSLC_X509_EXTENSION_UNSUPPORTED_CRITICAL) != 0;
  }
  return 1;
}

X509_ALGOR *x509_get_cached_signature_algorithm(const X509 *x509) {
  return x509_get_cached_field(x509, X509_VIEW_MATERIALIZED_SIG_ALG);
}

X509_ALGOR *x509_get_cached_tbs_signature_algorithm(const X509 *x509) {
  return x509_get_cached_field(x509, X509_VIEW_MATERIALIZED_TBS_SIG_ALG);
}

ASN1_BIT_STRING *x509_get_cached_signature(const X509 *x509) {
  return x509_get_cached_field(x509, X509_VIEW_MATERIALIZED_SIGNATURE);
}

int x509_digest_pristine_view(const X509 *x509,
                              uint8_t out[SHA256_DIGEST_LENGTH],
                              int *out_handled) {
  *out_handled = 0;
  if (x509 == NULL || x509->buf == NULL) {
    return 1;
  }

  int ok = 1;
  CRYPTO_MUTEX_lock_read((CRYPTO_MUTEX *)&x509->lock);
  if (x509->view_state == X509_VIEW_STATE_PARSED) {
    const AWSLC_X509_DER_RANGE range = x509->view.certificate;
    const size_t buffer_len = CRYPTO_BUFFER_len(x509->buf);
    if (range.offset > buffer_len || range.length > buffer_len - range.offset) {
      OPENSSL_PUT_ERROR(X509, ERR_R_INTERNAL_ERROR);
      ok = 0;
    } else {
      SHA256(CRYPTO_BUFFER_data(x509->buf) + range.offset, range.length, out);
      *out_handled = 1;
    }
  }
  CRYPTO_MUTEX_unlock_read((CRYPTO_MUTEX *)&x509->lock);
  return ok;
}

X509 *X509_parse_from_buffer(CRYPTO_BUFFER *buf) {
  if (CRYPTO_BUFFER_len(buf) > LONG_MAX) {
    OPENSSL_PUT_ERROR(SSL, ERR_R_OVERFLOW);
    return 0;
  }

  AWSLC_X509_CERTIFICATE_VIEW view;
  OPENSSL_memset(&view, 0, sizeof(view));
  const uint32_t parse_result =
      x509_parse_der_view(CRYPTO_BUFFER_data(buf), CRYPTO_BUFFER_len(buf),
                          /*exact=*/1, &view);
  if (parse_result == AWSLC_X509_PARSE_OK) {
    return x509_new_parsed_view(buf, &view);
  }

  X509 *x509 = X509_new();
  if (x509 == NULL) {
    return NULL;
  }

  x509->cert_info->enc.alias_only_on_next_parse = 1;

  const uint8_t *inp = CRYPTO_BUFFER_data(buf);
  X509 *x509p = x509;
  X509 *ret = d2i_X509_legacy(&x509p, &inp, CRYPTO_BUFFER_len(buf));
  if (ret == NULL ||
      inp - CRYPTO_BUFFER_data(buf) != (ptrdiff_t)CRYPTO_BUFFER_len(buf)) {
    X509_free(x509p);
    return NULL;
  }
  assert(x509p == x509);
  assert(ret == x509);

  x509_record_view_fallback(parse_result);
  CRYPTO_BUFFER_up_ref(buf);
  ret->buf = buf;

  return ret;
}

int X509_up_ref(X509 *x) {
  if (x == NULL) {
    return 0;
  }
  CRYPTO_refcount_inc(&x->references);
  return 1;
}

int X509_get_ex_new_index(long argl, void *argp, CRYPTO_EX_unused *unused,
                          CRYPTO_EX_dup *dup_unused,
                          CRYPTO_EX_free *free_func) {
  int index;
  if (!CRYPTO_get_ex_new_index(&g_ex_data_class, &index, argl, argp,
                               free_func)) {
    return -1;
  }
  return index;
}

int X509_set_ex_data(X509 *r, int idx, void *arg) {
  return (CRYPTO_set_ex_data(&r->ex_data, idx, arg));
}

void *X509_get_ex_data(X509 *r, int idx) {
  return (CRYPTO_get_ex_data(&r->ex_data, idx));
}

// X509_AUX ASN1 routines. X509_AUX is the name given to a certificate with
// extra info tagged on the end. Since these functions set how a certificate
// is trusted they should only be used when the certificate comes from a
// reliable source such as local storage.

X509 *d2i_X509_AUX(X509 **a, const unsigned char **pp, long length) {
  const unsigned char *q = *pp;
  X509 *ret;
  int freeret = 0;

  if (!a || *a == NULL) {
    freeret = 1;
  }
  ret = d2i_X509(a, &q, length);
  // If certificate unreadable then forget it
  if (!ret) {
    return NULL;
  }
  // update length
  length -= q - *pp;
  // Parse auxiliary information if there is any.
  if (length > 0 && !d2i_X509_CERT_AUX(&ret->aux, &q, length)) {
    goto err;
  }
  *pp = q;
  return ret;
err:
  if (freeret) {
    X509_free(ret);
    if (a) {
      *a = NULL;
    }
  }
  return NULL;
}

// Serialize trusted certificate to *pp or just return the required buffer
// length if pp == NULL.  We ultimately want to avoid modifying *pp in the
// error path, but that depends on similar hygiene in lower-level functions.
// Here we avoid compounding the problem.
static int i2d_x509_aux_internal(X509 *a, unsigned char **pp) {
  int length, tmplen;
  unsigned char *start = pp != NULL ? *pp : NULL;

  assert(pp == NULL || *pp != NULL);

  // This might perturb *pp on error, but fixing that belongs in i2d_X509()
  // not here.  It should be that if a == NULL length is zero, but we check
  // both just in case.
  length = i2d_X509(a, pp);
  if (length <= 0 || a == NULL) {
    return length;
  }

  if (a->aux != NULL) {
    tmplen = i2d_X509_CERT_AUX(a->aux, pp);
    if (tmplen < 0) {
      if (start != NULL) {
        *pp = start;
      }
      return tmplen;
    }
    length += tmplen;
  }

  return length;
}

// Serialize trusted certificate to *pp, or just return the required buffer
// length if pp == NULL.
//
// When pp is not NULL, but *pp == NULL, we allocate the buffer, but since
// we're writing two ASN.1 objects back to back, we can't have i2d_X509() do
// the allocation, nor can we allow i2d_X509_CERT_AUX() to increment the
// allocated buffer.
int i2d_X509_AUX(X509 *a, unsigned char **pp) {
  int length;
  unsigned char *tmp;

  // Buffer provided by caller
  if (pp == NULL || *pp != NULL) {
    return i2d_x509_aux_internal(a, pp);
  }

  // Obtain the combined length
  if ((length = i2d_x509_aux_internal(a, NULL)) <= 0) {
    return length;
  }

  // Allocate requisite combined storage
  *pp = tmp = OPENSSL_malloc(length);
  if (tmp == NULL) {
    return -1;  // Push error onto error stack?
  }

  // Encode, but keep *pp at the originally malloced pointer
  length = i2d_x509_aux_internal(a, &tmp);
  if (length <= 0) {
    OPENSSL_free(*pp);
    *pp = NULL;
  }
  return length;
}

int i2d_re_X509_tbs(X509 *x509, unsigned char **outp) {
  if (!x509_ensure_legacy(x509)) {
    return -1;
  }
  asn1_encoding_clear(&x509->cert_info->enc);
  return i2d_X509_CINF(x509->cert_info, outp);
}

int i2d_X509_tbs(X509 *x509, unsigned char **outp) {
  int handled = 0;
  const int view_result = x509_i2d_view_range(x509, /*tbs=*/1, outp, &handled);
  if (handled) {
    return view_result;
  }
  if (!x509_ensure_legacy(x509)) {
    return -1;
  }
  return i2d_X509_CINF(x509->cert_info, outp);
}

int X509_set1_signature_algo(X509 *x509, const X509_ALGOR *algo) {
  if (!x509_ensure_legacy(x509)) {
    return 0;
  }
  X509_ALGOR *copy1 = X509_ALGOR_dup(algo);
  X509_ALGOR *copy2 = X509_ALGOR_dup(algo);
  if (copy1 == NULL || copy2 == NULL) {
    X509_ALGOR_free(copy1);
    X509_ALGOR_free(copy2);
    return 0;
  }

  X509_ALGOR_free(x509->sig_alg);
  x509->sig_alg = copy1;
  X509_ALGOR_free(x509->cert_info->signature);
  x509->cert_info->signature = copy2;
  return 1;
}

int X509_set1_signature_value(X509 *x509, const uint8_t *sig, size_t sig_len) {
  if (!x509_ensure_legacy(x509)) {
    return 0;
  }
  if (!ASN1_STRING_set(x509->signature, sig, sig_len)) {
    return 0;
  }
  x509->signature->flags &= ~(ASN1_STRING_FLAG_BITS_LEFT | 0x07);
  x509->signature->flags |= ASN1_STRING_FLAG_BITS_LEFT;
  return 1;
}

void X509_get0_signature(const ASN1_BIT_STRING **psig, const X509_ALGOR **palg,
                         const X509 *x) {
  if (psig) {
    *psig = x509_get_cached_signature(x);
  }
  if (palg) {
    *palg = x509_get_cached_signature_algorithm(x);
  }
}

int X509_get_signature_nid(const X509 *x) {
  X509_ALGOR *algorithm = x509_get_cached_signature_algorithm(x);
  return algorithm == NULL ? NID_undef : OBJ_obj2nid(algorithm->algorithm);
}
