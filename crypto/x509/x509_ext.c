// Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com) All rights reserved.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/asn1.h>
#include <openssl/evp.h>
#include <openssl/obj.h>
#include <openssl/stack.h>
#include <openssl/x509.h>

#include "internal.h"

int X509_CRL_get_ext_count(const X509_CRL *x) {
  return (X509v3_get_ext_count(x->crl->extensions));
}

int X509_CRL_get_ext_by_NID(const X509_CRL *x, int nid, int lastpos) {
  return (X509v3_get_ext_by_NID(x->crl->extensions, nid, lastpos));
}

int X509_CRL_get_ext_by_OBJ(const X509_CRL *x, const ASN1_OBJECT *obj,
                            int lastpos) {
  return (X509v3_get_ext_by_OBJ(x->crl->extensions, obj, lastpos));
}

int X509_CRL_get_ext_by_critical(const X509_CRL *x, int crit, int lastpos) {
  return (X509v3_get_ext_by_critical(x->crl->extensions, crit, lastpos));
}

X509_EXTENSION *X509_CRL_get_ext(const X509_CRL *x, int loc) {
  return (X509v3_get_ext(x->crl->extensions, loc));
}

X509_EXTENSION *X509_CRL_delete_ext(X509_CRL *x, int loc) {
  return (X509v3_delete_ext(x->crl->extensions, loc));
}

void *X509_CRL_get_ext_d2i(const X509_CRL *crl, int nid, int *out_critical,
                           int *out_idx) {
  return X509V3_get_d2i(crl->crl->extensions, nid, out_critical, out_idx);
}

int X509_CRL_add1_ext_i2d(X509_CRL *x, int nid, void *value, int crit,
                          unsigned long flags) {
  return X509V3_add1_i2d(&x->crl->extensions, nid, value, crit, flags);
}

int X509_CRL_add_ext(X509_CRL *x, const X509_EXTENSION *ex, int loc) {
  return (X509v3_add_ext(&(x->crl->extensions), ex, loc) != NULL);
}

int X509_get_ext_count(const X509 *x) {
  if (x == NULL) {
    return 0;
  }
  STACK_OF(X509_EXTENSION) *extensions = NULL;
  if (!x509_get_cached_extensions_ex(x, &extensions)) {
    return -1;
  }
  return X509v3_get_ext_count(extensions);
}

int X509_get_ext_by_NID(const X509 *x, int nid, int lastpos) {
  STACK_OF(X509_EXTENSION) *extensions = x509_get_cached_extensions(x);
  return X509v3_get_ext_by_NID(extensions, nid, lastpos);
}

int X509_get_ext_by_OBJ(const X509 *x, const ASN1_OBJECT *obj, int lastpos) {
  STACK_OF(X509_EXTENSION) *extensions = x509_get_cached_extensions(x);
  return X509v3_get_ext_by_OBJ(extensions, obj, lastpos);
}

int X509_get_ext_by_critical(const X509 *x, int crit, int lastpos) {
  STACK_OF(X509_EXTENSION) *extensions = x509_get_cached_extensions(x);
  return X509v3_get_ext_by_critical(extensions, crit, lastpos);
}

X509_EXTENSION *X509_get_ext(const X509 *x, int loc) {
  STACK_OF(X509_EXTENSION) *extensions = x509_get_cached_extensions(x);
  return X509v3_get_ext(extensions, loc);
}

X509_EXTENSION *X509_delete_ext(X509 *x, int loc) {
  // Report a materialization failure the way the other extension accessors do,
  // then materialize the legacy state before mutating, as |X509_add_ext| does,
  // so a mutation never lands on a view-backed object.
  STACK_OF(X509_EXTENSION) *extensions = NULL;
  if (!x509_get_cached_extensions_ex(x, &extensions) || !x509_ensure_legacy(x)) {
    return NULL;
  }
  return X509v3_delete_ext(x->cert_info->extensions, loc);
}

int X509_add_ext(X509 *x, const X509_EXTENSION *ex, int loc) {
  if (!x509_ensure_legacy(x)) {
    return 0;
  }
  return (X509v3_add_ext(&(x->cert_info->extensions), ex, loc) != NULL);
}

void *X509_get_ext_d2i(const X509 *x509, int nid, int *out_critical,
                       int *out_idx) {
  if (out_idx == NULL) {
    int status = -1;
    int handled = 0;
    void *ret =
        x509_get_view_extension_d2i_by_nid(x509, nid, &status, &handled);
    if (handled) {
      if (out_critical != NULL) {
        *out_critical = status;
      }
      return ret;
    }
  }
  STACK_OF(X509_EXTENSION) *extensions = x509_get_cached_extensions(x509);
  return X509V3_get_d2i(extensions, nid, out_critical, out_idx);
}

int X509_add1_ext_i2d(X509 *x, int nid, void *value, int crit,
                      unsigned long flags) {
  if (!x509_ensure_legacy(x)) {
    return 0;
  }
  return X509V3_add1_i2d(&x->cert_info->extensions, nid, value, crit, flags);
}

int X509_REVOKED_get_ext_count(const X509_REVOKED *x) {
  return (X509v3_get_ext_count(x->extensions));
}

int X509_REVOKED_get_ext_by_NID(const X509_REVOKED *x, int nid, int lastpos) {
  return (X509v3_get_ext_by_NID(x->extensions, nid, lastpos));
}

int X509_REVOKED_get_ext_by_OBJ(const X509_REVOKED *x, const ASN1_OBJECT *obj,
                                int lastpos) {
  return (X509v3_get_ext_by_OBJ(x->extensions, obj, lastpos));
}

int X509_REVOKED_get_ext_by_critical(const X509_REVOKED *x, int crit,
                                     int lastpos) {
  return (X509v3_get_ext_by_critical(x->extensions, crit, lastpos));
}

X509_EXTENSION *X509_REVOKED_get_ext(const X509_REVOKED *x, int loc) {
  return (X509v3_get_ext(x->extensions, loc));
}

X509_EXTENSION *X509_REVOKED_delete_ext(X509_REVOKED *x, int loc) {
  return (X509v3_delete_ext(x->extensions, loc));
}

int X509_REVOKED_add_ext(X509_REVOKED *x, const X509_EXTENSION *ex, int loc) {
  return (X509v3_add_ext(&(x->extensions), ex, loc) != NULL);
}

void *X509_REVOKED_get_ext_d2i(const X509_REVOKED *revoked, int nid,
                               int *out_critical, int *out_idx) {
  return X509V3_get_d2i(revoked->extensions, nid, out_critical, out_idx);
}

int X509_REVOKED_add1_ext_i2d(X509_REVOKED *x, int nid, void *value, int crit,
                              unsigned long flags) {
  return X509V3_add1_i2d(&x->extensions, nid, value, crit, flags);
}
