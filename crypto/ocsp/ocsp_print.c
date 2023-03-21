/*
 * Copyright 2000-2016 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#include <openssl/ocsp.h>

typedef struct {
  long t;
  const char *m;
} OCSP_TBLSTR;

static const char *do_table2string(long s, const OCSP_TBLSTR *ts, size_t len) {
  size_t i;
  for (i = 0; i < len; i++) {
    if (ts[i].t == s) {
      return ts[i].m;
    }
  }
  return "(UNKNOWN)";
}

const char *OCSP_response_status_str(long status_code) {
  static const OCSP_TBLSTR rstat_tbl[] = {
      {OCSP_RESPONSE_STATUS_SUCCESSFUL, "successful"},
      {OCSP_RESPONSE_STATUS_MALFORMEDREQUEST, "malformedrequest"},
      {OCSP_RESPONSE_STATUS_INTERNALERROR, "internalerror"},
      {OCSP_RESPONSE_STATUS_TRYLATER, "trylater"},
      {OCSP_RESPONSE_STATUS_SIGREQUIRED, "sigrequired"},
      {OCSP_RESPONSE_STATUS_UNAUTHORIZED, "unauthorized"}};
  size_t tbl_size = (sizeof(rstat_tbl) / sizeof((rstat_tbl)[0]));
  return do_table2string(status_code, rstat_tbl, tbl_size);
}

const char *OCSP_cert_status_str(long status_code) {
  static const OCSP_TBLSTR cstat_tbl[] = {
      {V_OCSP_CERTSTATUS_GOOD, "good"},
      {V_OCSP_CERTSTATUS_REVOKED, "revoked"},
      {V_OCSP_CERTSTATUS_UNKNOWN, "unknown"}};
  size_t tbl_size = (sizeof(cstat_tbl) / sizeof((cstat_tbl)[0]));
  return do_table2string(status_code, cstat_tbl, tbl_size);
}
