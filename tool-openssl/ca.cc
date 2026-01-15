// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "ca.h"

#include <cctype>
#include <cstdlib>
#include <cstring>
#include <memory>

// TODO: figure out windows
#include <sys/stat.h>

#include <openssl/asn1.h>
#include <openssl/bio.h>
#include <openssl/digest.h>
#include <openssl/ocsp.h>
#include <openssl/pem.h>
#include "txt_db/txt_db.h"

#include "ca_req_common.h"
#include "internal.h"

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-verbose", kBooleanArgument,
     "This prints extra details about the operations being performed"},
    {"-in", kOptionalArgument,
     "An input filename containing a single certificate request (CSR) to be "
     "signed by the CA."},
    {"-out", kOptionalArgument,
     "The output file to output certificates to. The default is standard "
     "output. The certificate details will also be printed out to this file in "
     "PEM format."},
    {"-batch", kBooleanArgument,
     "This sets the batch mode. In this mode no questions will be asked and "
     "all certificates will be certified automatically. This argument is "
     "always enabled even if not explicitly passed, but this behavior may be "
     "changed later. If you rely on this behavior you must continue to set "
     "it."},
    {"-config", kOptionalArgument, "Specifies the configuration file to use."},
    {"-notext", kBooleanArgument,
     "Don't output the text form of a certificate to the output file."},
    {"-selfsign", kBooleanArgument,
     "Indicates the issued certificates are to be signed with the key "
     "the certificate requests were signed with. Certificate requests signed "
     "with a different key are ignored. This argument is currently always "
     "enabled even if not explicitly passed, but this behavior may be changed "
     "later. If you rely on this behavior you must continue to set it."},
    {"-passin", kOptionalArgument,
     "The key password source for key files and certificate PKCS#12 files."},
    {"-startdate", kOptionalArgument,
     "This allows the start date to be explicitly set. The format of the date "
     "is YYMMDDHHMMSSZ (the same as an ASN1 UTCTime structure), or "
     "YYYYMMDDHHMMSSZ (the same as an ASN1 GeneralizedTime structure). In both "
     "formats, seconds SS and timezone Z must be present. Alternatively, you "
     "can also use \"today\"."},
    {"-enddate", kOptionalArgument,
     "This allows the expiry date to be explicitly set. The format of the date "
     "is YYMMDDHHMMSSZ (the same as an ASN1 UTCTime structure), or "
     "YYYYMMDDHHMMSSZ (the same as an ASN1 GeneralizedTime structure). In both "
     "formats, seconds SS and timezone Z must be present. Alternatively, you "
     "can also use \"today\""},
    {"", kOptionalArgument, ""}};

struct db_attr_st {
  int unique_subject;
};

struct ca_db_st {
  DB_ATTR attributes;
  TXT_DB *db;
  char *dbfname;
  struct stat dbst;
};

using ossl_free = decltype(&OPENSSL_free);

using ossl_string_ptr = std::unique_ptr<OPENSSL_STRING, ossl_free>;
using ossl_uint8_ptr = std::unique_ptr<uint8_t, ossl_free>;
using ossl_char_ptr = std::unique_ptr<char, ossl_free>;

#ifdef _WIN32

#define rename(from,to) WIN32_rename((from),(to))

#undef fileno
#define fileno(a) (int)_fileno(a)

#include <windows.h>
#include <tchar.h>

static int WIN32_rename(const char *from, const char *to) {
  TCHAR *tfrom = nullptr, *tto = nullptr;
  DWORD err = 0;
  int ret = 0;

  if (sizeof(TCHAR) == 1) {
    tfrom = (TCHAR *)from;
    tto = (TCHAR *)to;
  } else { /* UNICODE path */
    size_t i, flen = strlen(from) + 1, tlen = strlen(to) + 1;
    tfrom = (TCHAR*)malloc(sizeof(TCHAR) * (flen + tlen));
    if (tfrom == NULL) {
      goto err;
    }
    tto = tfrom + flen;
    for (i = 0; i < flen; i++) {
      tfrom[i] = (TCHAR)from[i];
    }
    for (i = 0; i < tlen; i++) {
      tto[i] = (TCHAR)to[i];
    }
  }

  if (MoveFile(tfrom, tto)) {
    goto ok;
  }
  err = GetLastError();
  if (err == ERROR_ALREADY_EXISTS || err == ERROR_FILE_EXISTS) {
    if (DeleteFile(tto) && MoveFile(tfrom, tto)) {
      goto ok;
    }
    err = GetLastError();
  }
  if (err == ERROR_FILE_NOT_FOUND || err == ERROR_PATH_NOT_FOUND) {
    errno = ENOENT;
  } else if (err == ERROR_ACCESS_DENIED) {
    errno = EACCES;
  } else {
    errno = EINVAL; /* we could map more codes... */
  }
err:
  ret = -1;
ok:
  if (tfrom != NULL && tfrom != (TCHAR *)from) {
    free(tfrom);
  }
  return ret;
}
#endif

static std::unique_ptr<std::string> GetSectionValue(bssl::UniquePtr<CONF> &conf,
                                                    std::string section,
                                                    std::string key) {
  auto *value = NCONF_get_string(conf.get(), section.c_str(), key.c_str());
  if (value == NULL) {
    return std::unique_ptr<std::string>(nullptr);
  }
  return std::unique_ptr<std::string>(new std::string(value));
}

static bool ParseBoolSectionValue(bssl::UniquePtr<CONF> &conf,
                                  std::string section, std::string key,
                                  bool default_value) {
  auto value = GetSectionValue(conf, section, key);
  if (!value) {
    return default_value;
  }
  return parse_bool(value.get()->c_str(), default_value);
}

static long ParseNumberSectionValue(bssl::UniquePtr<CONF> &conf,
                                    std::string section, std::string key,
                                    long default_value) {
  auto value = GetSectionValue(conf, section, key);
  if (!value) {
    return default_value;
  }
  return std::atol(value->c_str());
}

static EXT_COPY_TYPE ParseCopyExtensionValue(std::string value) {
  if (strcasecmp(value.c_str(), "none") == 0) {
    return EXT_COPY_NONE;
  } else if (strcasecmp(value.c_str(), "copy") == 0) {
    return EXT_COPY_ADD;
  } else if (strcasecmp(value.c_str(), "copyall") == 0) {
    return EXT_COPY_ALL;
  }
  return EXT_COPY_UNKNOWN;
}

#undef BSIZE
#define BSIZE 256

#define DB_type 0
#define DB_exp_date 1
#define DB_rev_date 2
#define DB_serial 3 /* index - unique */
#define DB_file 4
#define DB_name                           \
  5 /* index - unique when active and not \
     * disabled */
#define DB_NUMBER 6

#define DB_TYPE_REV 'R'  /* Revoked  */
#define DB_TYPE_EXP 'E'  /* Expired  */
#define DB_TYPE_VAL 'V'  /* Valid ; inserted with: ca ... -valid */
#define DB_TYPE_SUSP 'S' /* Suspended  */

static bssl::UniquePtr<CA_DB> LoadIndex(const std::string dbfile,
                                        DB_ATTR *db_attr) {
  bssl::UniquePtr<CONF> dbattr_conf(NCONF_new(nullptr));
  bssl::UniquePtr<CA_DB> retdb;
  bssl::UniquePtr<TXT_DB> tmpdb;
  char buf[BSIZE] = {0};
  FILE *dbfp = NULL;
  struct stat dbst;

  bssl::UniquePtr<BIO> in(BIO_new_file(dbfile.c_str(), "r"));
  if (!in) {
    goto err;
  }

  if (!BIO_get_fp(in.get(), &dbfp) || fstat(fileno(dbfp), &dbst) == -1) {
    OPENSSL_PUT_SYSTEM_ERROR();
    goto err;
  }

  tmpdb.reset(TXT_DB_read(in.get(), DB_NUMBER));

  if (!tmpdb) {
    goto err;
  }

  BIO_snprintf(buf, sizeof(buf), "%s.attr", dbfile.c_str());

  if (!NCONF_load(dbattr_conf.get(), buf, nullptr)) {
    goto err;
  }

  retdb.reset((CA_DB *)OPENSSL_malloc(sizeof(CA_DB)));
  retdb->db = tmpdb.release();
  if (db_attr) {
    retdb->attributes = *db_attr;
  } else {
    retdb->attributes.unique_subject = 1;
  }

  if (dbattr_conf) {
    const char *p = NCONF_get_string(dbattr_conf.get(), NULL, "unique_subject");
    if (p) {
      retdb->attributes.unique_subject = parse_bool(p, true);
    }
  }

  retdb->dbfname = OPENSSL_strdup(dbfile.c_str());
  retdb->dbst = dbst;

err:
  return retdb;
}

static const char *crl_reasons[] = {
    /* CRL reason strings */
    "unspecified", "keyCompromise", "CACompromise", "affiliationChanged",
    "superseded", "cessationOfOperation", "certificateHold", "removeFromCRL",
    /* Additional pseudo reasons */
    "holdInstruction", "keyTime", "CAkeyTime"};

#define ARR_SIZE(x) (sizeof(x) / sizeof((x)[0]))

#define NUM_REASONS ARR_SIZE(crl_reasons)

static int UnpackRevinfo(bssl::UniquePtr<ASN1_TIME> &prevtm, int *preason,
                         bssl::UniquePtr<ASN1_OBJECT> &phold,
                         bssl::UniquePtr<ASN1_GENERALIZEDTIME> &pinvtm,
                         std::string str) {
  ossl_char_ptr tmp = ossl_char_ptr(nullptr, OPENSSL_free);
  char *rtime_str = NULL, *reason_str = NULL, *arg_str = NULL, *p = NULL;
  int reason_code = -1;
  int ret = 0;
  unsigned int i = 0;
  bssl::UniquePtr<ASN1_OBJECT> hold;
  bssl::UniquePtr<ASN1_GENERALIZEDTIME> comp_time;

  tmp.reset(OPENSSL_strdup(str.c_str()));
  if (!tmp) {
    fprintf(stderr, "memory allocation failure\n");
    goto end;
  }

  p = strchr(tmp.get(), ',');

  rtime_str = tmp.get();

  if (p) {
    *p = '\0';
    p++;
    reason_str = p;
    p = strchr(p, ',');
    if (p) {
      *p = '\0';
      arg_str = p + 1;
    }
  }

  if (prevtm) {
    prevtm.reset(ASN1_UTCTIME_new());
    if (!prevtm) {
      fprintf(stderr, "memory allocation failure\n");
      goto end;
    }
    if (!ASN1_UTCTIME_set_string(prevtm.get(), rtime_str)) {
      fprintf(stderr, "invalid revocation date %s\n", rtime_str);
      goto end;
    }
  }
  if (reason_str) {
    for (i = 0; i < NUM_REASONS; i++) {
      if (strcasecmp(reason_str, crl_reasons[i]) == 0) {
        reason_code = i;
        break;
      }
    }
    if (reason_code == OCSP_REVOKED_STATUS_NOSTATUS) {
      fprintf(stderr, "invalid reason code %s\n", reason_str);
      goto end;
    }

    if (reason_code == 7) {
      reason_code = OCSP_REVOKED_STATUS_REMOVEFROMCRL;
    } else if (reason_code == 8) { /* Hold instruction */
      if (!arg_str) {
        fprintf(stderr, "missing hold instruction\n");
        goto end;
      }
      reason_code = OCSP_REVOKED_STATUS_CERTIFICATEHOLD;
      hold.reset(OBJ_txt2obj(arg_str, 0));

      if (!hold) {
        fprintf(stderr, "invalid object identifier %s\n", arg_str);
        goto end;
      }
      if (phold) {
        phold = std::move(hold);
      } else {
        hold.reset();
      }
    } else if ((reason_code == 9) || (reason_code == 10)) {
      if (!arg_str) {
        fprintf(stderr, "missing compromised time\n");
        goto end;
      }
      comp_time.reset(ASN1_GENERALIZEDTIME_new());
      if (!comp_time) {
        fprintf(stderr, "memory allocation failure\n");
        goto end;
      }
      if (!ASN1_GENERALIZEDTIME_set_string(comp_time.get(), arg_str)) {
        fprintf(stderr, "invalid compromised time %s\n", arg_str);
        goto end;
      }
      if (reason_code == 9) {
        reason_code = OCSP_REVOKED_STATUS_KEYCOMPROMISE;
      } else {
        reason_code = OCSP_REVOKED_STATUS_CACOMPROMISE;
      }
    }
  }

  if (preason) {
    *preason = reason_code;
  }
  if (pinvtm) {
    pinvtm = std::move(comp_time);
  }

  ret = 1;

end:

  return ret;
}

/*-
 * Convert revocation field to X509_REVOKED entry
 * return code:
 * 0 error
 * 1 OK
 * 2 OK and some extensions added (i.e. V2 CRL)
 */
static int MakeRevoked(X509_REVOKED *rev, std::string str) {
  int reason_code = -1;
  int i = 0, ret = 0;
  bssl::UniquePtr<ASN1_OBJECT> hold;
  bssl::UniquePtr<ASN1_GENERALIZEDTIME> comp_time;
  bssl::UniquePtr<ASN1_ENUMERATED> rtmp;

  bssl::UniquePtr<ASN1_TIME> revDate;

  i = UnpackRevinfo(revDate, &reason_code, hold, comp_time, str);

  if (i == 0) {
    goto end;
  }

  if (rev && !X509_REVOKED_set_revocationDate(rev, revDate.get())) {
    goto end;
  }

  if (rev && (reason_code != OCSP_REVOKED_STATUS_NOSTATUS)) {
    rtmp.reset(ASN1_ENUMERATED_new());
    if (rtmp == NULL || !ASN1_ENUMERATED_set(rtmp.get(), reason_code)) {
      goto end;
    }
    if (!X509_REVOKED_add1_ext_i2d(rev, NID_crl_reason, rtmp.get(), 0, 0)) {
      goto end;
    }
  }

  if (rev && comp_time) {
    if (!X509_REVOKED_add1_ext_i2d(rev, NID_invalidity_date, comp_time.get(), 0,
                                   0)) {
      goto end;
    }
  }
  if (rev && hold) {
    if (!X509_REVOKED_add1_ext_i2d(rev, NID_hold_instruction_code, hold.get(),
                                   0, 0)) {
      goto end;
    }
  }

  if (reason_code != OCSP_REVOKED_STATUS_NOSTATUS) {
    ret = 2;
  } else {
    ret = 1;
  }

end:

  return ret;
}

static int CheckTimeFormat(std::string str) {
  return ASN1_TIME_set_string(NULL, str.c_str());
}

static uint32_t index_serial_hash(const OPENSSL_STRING *a) {
  const char *n = nullptr;

  n = a[DB_serial];
  while (*n == '0') {
    n++;
  }
  return OPENSSL_strhash(n);
}

static int index_serial_cmp(const OPENSSL_STRING *a, const OPENSSL_STRING *b) {
  const char *aa = nullptr, *bb = nullptr;

  for (aa = a[DB_serial]; *aa == '0'; aa++) {
  }
  for (bb = b[DB_serial]; *bb == '0'; bb++) {
  }
  return strcmp(aa, bb);
}

static int index_name_qual(char **a) { return (a[0][0] == 'V'); }

static uint32_t index_name_hash(const OPENSSL_STRING *a) {
  return OPENSSL_strhash(a[DB_name]);
}

static int index_name_cmp(const OPENSSL_STRING *a, const OPENSSL_STRING *b) {
  return strcmp(a[DB_name], b[DB_name]);
}

static int IndexIndex(bssl::UniquePtr<CA_DB> &db) {
  if (!TXT_DB_create_index(db->db, DB_serial, NULL, index_serial_hash,
                           index_serial_cmp)) {
    fprintf(stderr, "error creating serial number index:(%ld,%ld,%ld)\n",
            db->db->error, db->db->arg1, db->db->arg2);
    return 0;
  }

  if (db->attributes.unique_subject &&
      !TXT_DB_create_index(db->db, DB_name, index_name_qual, index_name_hash,
                           index_name_cmp)) {
    fprintf(stderr, "error creating name index:(%ld,%ld,%ld)\n", db->db->error,
            db->db->arg1, db->db->arg2);
    return 0;
  }
  return 1;
}

static int SaveIndex(std::string dbfile, std::string suffix,
                     bssl::UniquePtr<CA_DB> &db) {
  char buf[3][BSIZE];
  bssl::UniquePtr<BIO> out;
  int j = 0;

  j = strlen(dbfile.c_str()) + strlen(suffix.c_str());
  if (j + 6 >= BSIZE) {
    fprintf(stderr, "file name too long\n");
    goto err;
  }
  (void)BIO_snprintf(buf[2], sizeof(buf[2]), "%s.attr", dbfile.c_str());
  (void)BIO_snprintf(buf[1], sizeof(buf[1]), "%s.attr.%s", dbfile.c_str(),
                     suffix.c_str());
  (void)BIO_snprintf(buf[0], sizeof(buf[0]), "%s.%s", dbfile.c_str(),
                     suffix.c_str());
  out.reset(BIO_new_file(buf[0], "w"));
  if (out == NULL) {
    perror(dbfile.c_str());
    fprintf(stderr, "unable to open '%s'\n", dbfile.c_str());
    goto err;
  }
  j = TXT_DB_write(out.get(), db->db);
  if (j <= 0) {
    goto err;
  }

  out.reset(BIO_new_file(buf[1], "w"));
  if (out == NULL) {
    perror(buf[2]);
    fprintf(stderr, "unable to open '%s'\n", buf[2]);
    goto err;
  }
  BIO_printf(out.get(), "unique_subject = %s\n",
             db->attributes.unique_subject ? "yes" : "no");

  return 1;
err:
  return 0;
}

static int RotateIndex(std::string dbfile, std::string new_suffix,
                       std::string old_suffix) {
  char buf[5][BSIZE];
  int i = 0, j = 0;

  i = strlen(dbfile.c_str()) + strlen(old_suffix.c_str());
  j = strlen(dbfile.c_str()) + strlen(new_suffix.c_str());
  if (i > j) {
    j = i;
  }
  if (j + 6 >= BSIZE) {
    fprintf(stderr, "file name too long\n");
    goto err;
  }
  (void)BIO_snprintf(buf[4], sizeof(buf[4]), "%s.attr", dbfile.c_str());
  (void)BIO_snprintf(buf[3], sizeof(buf[3]), "%s.attr.%s", dbfile.c_str(),
                     old_suffix.c_str());
  (void)BIO_snprintf(buf[2], sizeof(buf[2]), "%s.attr.%s", dbfile.c_str(),
                     new_suffix.c_str());
  (void)BIO_snprintf(buf[1], sizeof(buf[1]), "%s.%s", dbfile.c_str(),
                     old_suffix.c_str());
  (void)BIO_snprintf(buf[0], sizeof(buf[0]), "%s.%s", dbfile.c_str(),
                     new_suffix.c_str());
  if (rename(dbfile.c_str(), buf[1]) < 0 && errno != ENOENT &&
      errno != ENOTDIR) {
    fprintf(stderr, "unable to rename %s to %s\n", dbfile.c_str(), buf[1]);
    perror("reason");
    goto err;
  }
  if (rename(buf[0], dbfile.c_str()) < 0) {
    fprintf(stderr, "unable to rename %s to %s\n", buf[0], dbfile.c_str());
    perror("reason");
    rename(buf[1], dbfile.c_str());
    goto err;
  }
  if (rename(buf[4], buf[3]) < 0 && errno != ENOENT && errno != ENOTDIR) {
    fprintf(stderr, "unable to rename %s to %s\n", buf[4], buf[3]);
    perror("reason");
    rename(dbfile.c_str(), buf[0]);
    rename(buf[1], dbfile.c_str());
    goto err;
  }
  if (rename(buf[2], buf[4]) < 0) {
    fprintf(stderr, "unable to rename %s to %s\n", buf[2], buf[4]);
    perror("reason");
    rename(buf[3], buf[4]);
    rename(dbfile.c_str(), buf[0]);
    rename(buf[1], dbfile.c_str());
    goto err;
  }
  return 1;
err:
  return 0;
}

void FreeIndex(CA_DB *db) {
  if (!db) {
    return;
  }
  TXT_DB_free(db->db);
  OPENSSL_free(db->dbfname);
  OPENSSL_free(db);
}

static DEF_DGST_USAGE EVP_PKEY_get_default_digest_nid(
    bssl::UniquePtr<EVP_PKEY> &pkey, const EVP_MD **usage) {
  if (usage == nullptr) {
    abort();
  }
  *usage = nullptr;
  if (!pkey) {
    return DEF_DGST_UNKNOWN;
  }
  auto pkey_id = EVP_PKEY_id(pkey.get());
  if (pkey_id == EVP_PKEY_EC || pkey_id == EVP_PKEY_RSA ||
      pkey_id == EVP_PKEY_DSA) {
    *usage = EVP_sha256();
    return DEF_DGST_ADVISORY;
  } else if (pkey_id == EVP_PKEY_ED25519) {
    *usage = nullptr;
    return DEF_DGST_REQUIRED;
  } else if (pkey_id == EVP_PKEY_RSA_PSS) {
    const auto *rsa = EVP_PKEY_get0_RSA(pkey.get());
    if (rsa == nullptr) {
      return DEF_DGST_UNKNOWN;
    }
    auto params = RSA_get0_ssa_pss_params(rsa);
    if (!params) {
      return DEF_DGST_ADVISORY;
    }
    const EVP_MD *md = nullptr;
    const EVP_MD *mgf1md = nullptr;
    int saltlen = 0;
    if (!RSASSA_PSS_PARAMS_get(params, &md, &mgf1md, &saltlen)) {
      return DEF_DGST_UNKNOWN;
    }
    *usage = md;
    return DEF_DGST_REQUIRED;
  }
  return DEF_DGST_UNKNOWN;
}

static int RandSerial(bssl::UniquePtr<BIGNUM> &b, ASN1_INTEGER *ai) {
  int ret = 0;

  if (!b) {
    b.reset(BN_new());
    if (!b) {
      goto end;
    }
  }

  /*
   * IETF RFC 5280 says serial number must be <= 20 bytes. Use 159 bits
   * so that the first bit will never be one, so that the DER encoding
   * rules won't force a leading octet.
   */
  if (!BN_rand(b.get(), 159, BN_RAND_TOP_ANY, BN_RAND_BOTTOM_ANY)) {
    goto end;
  }
  if (ai && !BN_to_ASN1_INTEGER(b.get(), ai)) {
    goto end;
  }

  ret = 1;

end:
  return ret;
}

static bssl::UniquePtr<BIGNUM> LoadSerial(std::string serialfile, int *exists,
                                          int create) {
  bssl::UniquePtr<BIO> in;
  bssl::UniquePtr<BIGNUM> ret;
  bssl::UniquePtr<ASN1_INTEGER> ai;
  char buf[1024] = {0};

  ai.reset(ASN1_INTEGER_new());
  if (ai == NULL) {
    goto err;
  }

  in = bssl::UniquePtr<BIO>(BIO_new_file(serialfile.c_str(), "r"));
  if (exists != NULL) {
    *exists = in != NULL;
  }
  if (!in) {
    if (!create) {
      perror(serialfile.c_str());
      goto err;
    }
    ERR_clear_error();
    ret = bssl::UniquePtr<BIGNUM>(BN_new());
    if (ret == NULL) {
      fprintf(stderr, "Out of memory\n");
    } else if (!RandSerial(ret, nullptr)) {
      fprintf(stderr, "Error creating random number to store in %s\n",
              serialfile.c_str());
      ret = NULL;
    }
  } else {
    if (!a2i_ASN1_INTEGER(in.get(), ai.get(), buf, 1024)) {
      fprintf(stderr, "unable to load number from %s\n", serialfile.c_str());
      goto err;
    }
    ret.reset(ASN1_INTEGER_to_BN(ai.get(), NULL));
    if (!ret) {
      fprintf(stderr, "error converting number from bin to BIGNUM\n");
      goto err;
    }
  }

err:
  return ret;
}

static int SetCertTimes(X509 *x, std::string startdate, std::string enddate,
                        int days) {
  if (startdate.empty() || strcmp(startdate.c_str(), "today") == 0) {
    if (X509_gmtime_adj(X509_getm_notBefore(x), 0) == NULL) {
      return 0;
    }
  } else {
    if (!ASN1_TIME_set_string_X509(X509_getm_notBefore(x), startdate.c_str())) {
      return 0;
    }
  }
  if (enddate.empty()) {
    if (X509_time_adj_ex(X509_getm_notAfter(x), days, 0, NULL) == NULL) {
      return 0;
    }
  } else if (!ASN1_TIME_set_string_X509(X509_getm_notAfter(x),
                                        enddate.c_str())) {
    return 0;
  }
  return 1;
}

static int CopyExtensions(X509 *x, X509_REQ *req, EXT_COPY_TYPE copy_type) {
  STACK_OF(X509_EXTENSION) *exts = NULL;
  X509_EXTENSION *ext = nullptr, *tmpext = nullptr;
  ASN1_OBJECT *obj = nullptr;
  int idx = 0, ret = 0;
  if (!x || !req || (copy_type == EXT_COPY_NONE)) {
    return 1;
  }
  exts = X509_REQ_get_extensions(req);

  for (size_t i = 0; i < sk_X509_EXTENSION_num(exts); i++) {
    ext = sk_X509_EXTENSION_value(exts, i);
    obj = X509_EXTENSION_get_object(ext);
    idx = X509_get_ext_by_OBJ(x, obj, -1);
    /* Does extension exist? */
    if (idx != -1) {
      /* If normal copy don't override existing extension */
      if (copy_type == EXT_COPY_ADD) {
        continue;
      }
      /* Delete all extensions of same type */
      do {
        tmpext = X509_get_ext(x, idx);
        X509_delete_ext(x, idx);
        X509_EXTENSION_free(tmpext);
        idx = X509_get_ext_by_OBJ(x, obj, -1);
      } while (idx != -1);
    }
    if (!X509_add_ext(x, ext, -1)) {
      goto end;
    }
  }

  ret = 1;

end:

  sk_X509_EXTENSION_pop_free(exts, X509_EXTENSION_free);

  return ret;
}

static int DoX509Sign(bssl::UniquePtr<X509> &x, bssl::UniquePtr<EVP_PKEY> &pkey,
                      const EVP_MD *md) {
  int rv = 0;
  EVP_PKEY_CTX *pkctx = NULL;
  bssl::UniquePtr<EVP_MD_CTX> mctx(EVP_MD_CTX_new());

  if (!EVP_DigestSignInit(mctx.get(), &pkctx, md, nullptr, pkey.get())) {
    goto err;
  }
  rv = X509_sign_ctx(x.get(), mctx.get());
err:
  return rv;
}

static void WriteNewCertificate(bssl::UniquePtr<BIO> &bp, X509 *x,
                                int output_der, int notext) {
  if (output_der) {
    (void)i2d_X509_bio(bp.get(), x);
    return;
  }
  if (!notext) {
    X509_print(bp.get(), x);
  }
  PEM_write_bio_X509(bp.get(), x);
}

static int old_entry_print(bssl::UniquePtr<BIO> &bio_err,
                           const ASN1_OBJECT *obj, const ASN1_STRING *str) {
  char buf[25], *pbuf = nullptr;
  const char *p = nullptr;
  int j = 0;

  j = i2a_ASN1_OBJECT(bio_err.get(), obj);
  pbuf = buf;
  for (j = 22 - j; j > 0; j--) {
    *(pbuf++) = ' ';
  }
  *(pbuf++) = ':';
  *(pbuf++) = '\0';
  BIO_puts(bio_err.get(), buf);

  if (str->type == V_ASN1_PRINTABLESTRING) {
    BIO_printf(bio_err.get(), "PRINTABLE:'");
  } else if (str->type == V_ASN1_T61STRING) {
    BIO_printf(bio_err.get(), "T61STRING:'");
  } else if (str->type == V_ASN1_IA5STRING) {
    BIO_printf(bio_err.get(), "IA5STRING:'");
  } else if (str->type == V_ASN1_UNIVERSALSTRING) {
    BIO_printf(bio_err.get(), "UNIVERSALSTRING:'");
  } else {
    BIO_printf(bio_err.get(), "ASN.1 %2d:'", str->type);
  }

  p = (const char *)str->data;
  for (j = str->length; j > 0; j--) {
    if ((*p >= ' ') && (*p <= '~')) {
      BIO_printf(bio_err.get(), "%c", *p);
    } else if (*p & 0x80) {
      BIO_printf(bio_err.get(), "\\0x%02X", (unsigned char)*p);
    } else if ((unsigned char)*p == 0xf7) {
      BIO_printf(bio_err.get(), "^?");
    } else {
      BIO_printf(bio_err.get(), "^%c", *p + '@');
    }
    p++;
  }
  BIO_printf(bio_err.get(), "'\n");
  return 1;
}

static int DoBody(bssl::UniquePtr<BIO> &bio_err, X509 **xret,
                  bssl::UniquePtr<EVP_PKEY> &pkey, X509 *x509,
                  const EVP_MD *dgst, const STACK_OF(CONF_VALUE) *policy,
                  bssl::UniquePtr<CA_DB> &db, bssl::UniquePtr<BIGNUM> &serial,
                  std::string subj, unsigned long chtype, std::string startdate,
                  std::string enddate, long days, int verbose,
                  bssl::UniquePtr<X509_REQ> &req, std::string ext_sect,
                  bssl::UniquePtr<CONF> &lconf, EXT_COPY_TYPE ext_copy,
                  int selfsign, int preserve) {
  X509_NAME *name = nullptr;
  bssl::UniquePtr<X509_NAME> CAname, subject;
  const ASN1_TIME *tm = nullptr;
  ASN1_STRING *str = nullptr, *str2 = nullptr;
  ASN1_OBJECT *obj = nullptr;
  bssl::UniquePtr<X509> ret;
  X509_NAME_ENTRY *ne = nullptr, *tne = nullptr;
  EVP_PKEY *pktmp = nullptr;
  int ok = -1, i = 0, j = 0, last = 0, nid = 0;
  const char *p = nullptr;
  CONF_VALUE *cv = nullptr;
  OPENSSL_STRING row[DB_NUMBER];
  ossl_string_ptr irow(nullptr, OPENSSL_free);
  OPENSSL_STRING *rrow = NULL;
  bssl::UniquePtr<X509_NAME> dn_subject;
  X509_NAME_ENTRY *tmpne = nullptr;

  for (i = 0; i < DB_NUMBER; i++) {
    row[i] = nullptr;
  }

  if (!subj.empty()) {
    bssl::UniquePtr<X509_NAME> n(ParseSubjectName(subj));
    if (!n) {
      goto end;
    }
    X509_REQ_set_subject_name(req.get(), n.get());
  }

  BIO_printf(bio_err.get(), "The Subject's Distinguished Name is as follows\n");

  name = X509_REQ_get_subject_name(req.get());
  for (i = 0; i < X509_NAME_entry_count(name); i++) {
    ne = X509_NAME_get_entry(name, i);
    str = X509_NAME_ENTRY_get_data(ne);
    obj = X509_NAME_ENTRY_get_object(ne);
    nid = OBJ_obj2nid(obj);

    if (nid == NID_pkcs9_emailAddress) {
      continue;
    }

    if (str->type != V_ASN1_PRINTABLESTRING && str->type != V_ASN1_UTF8STRING) {
      // TODO: OpenSSL had some otherweird handling here for checking printable
      //       types an T61 / IA5 string formats. These shouldn't be used in
      //       modern X.509 standards and X509_NAME_add_entry_by_NID used by
      //       ParseSubject should do the right thing here based on NID. As
      //       minimally per RFC 5280 UTF-8 is prefered, followed by Printable,
      //       and everything else is legacy. So let's just enforce that here.
      //       Exception will be SANs, in which IA5String is mandated.
      BIO_printf(
          bio_err.get(),
          "subject DN must only contain printable or UTF8 string types\n");
      goto end;
    }

    old_entry_print(bio_err, obj, str);
  }

  /* Ok, now we check the 'policy' stuff. */
  subject = bssl::UniquePtr<X509_NAME>(X509_NAME_new());
  if (!subject) {
    BIO_printf(bio_err.get(), "Memory allocation failure\n");
    goto end;
  }

  /* take a copy of the issuer name before we mess with it. */
  if (selfsign) {
    CAname = bssl::UniquePtr<X509_NAME>(X509_NAME_dup(name));
  } else {
    CAname =
        bssl::UniquePtr<X509_NAME>(X509_NAME_dup(X509_get_subject_name(x509)));
  }
  if (!CAname) {
    goto end;
  }
  str = str2 = NULL;

  for (size_t policy_i = 0; policy_i < sk_CONF_VALUE_num(policy); policy_i++) {
    cv = sk_CONF_VALUE_value(policy, policy_i); /* get the object id */
    if ((j = OBJ_txt2nid(cv->name)) == NID_undef) {
      BIO_printf(bio_err.get(),
                 "%s:unknown object type in 'policy' configuration\n",
                 cv->name);
      goto end;
    }
    obj = OBJ_nid2obj(j);

    last = -1;
    for (;;) {
      X509_NAME_ENTRY *push = NULL;

      /* lookup the object in the supplied name list */
      j = X509_NAME_get_index_by_OBJ(name, obj, last);
      if (j < 0) {
        if (last != -1) {
          break;
        }
        tne = NULL;
      } else {
        tne = X509_NAME_get_entry(name, j);
      }
      last = j;

      /* depending on the 'policy', decide what to do. */
      if (strcmp(cv->value, "optional") == 0) {
        if (tne != nullptr) {
          push = tne;
        }
        // If tne is nullptr for optional fields, just don't add anything -
        // that's fine
      } else if (strcmp(cv->value, "supplied") == 0) {
        if (tne == NULL) {
          BIO_printf(bio_err.get(),
                     "The %s field needed to be supplied and was missing\n",
                     cv->name);
          goto end;
        } else {
          push = tne;
        }
      } else if (strcmp(cv->value, "match") == 0) {
        int last2 = -1;

        if (tne == NULL) {
          BIO_printf(bio_err.get(), "The mandatory %s field was missing\n",
                     cv->name);
          goto end;
        }

      again2:
        j = X509_NAME_get_index_by_OBJ(CAname.get(), obj, last2);
        if ((j < 0) && (last2 == -1)) {
          BIO_printf(bio_err.get(),
                     "The %s field does not exist in the CA certificate,\n"
                     "the 'policy' is misconfigured\n",
                     cv->name);
          goto end;
        }
        if (j >= 0) {
          push = X509_NAME_get_entry(CAname.get(), j);
          str = X509_NAME_ENTRY_get_data(tne);
          str2 = X509_NAME_ENTRY_get_data(push);
          last2 = j;
          if (ASN1_STRING_cmp(str, str2) != 0) {
            goto again2;
          }
        }
        if (j < 0) {
          BIO_printf(bio_err.get(),
                     "The %s field is different between\n"
                     "CA certificate (%s) and the request (%s)\n",
                     cv->name, ((str2 == NULL) ? "NULL" : (char *)str2->data),
                     ((str == NULL) ? "NULL" : (char *)str->data));
          goto end;
        }
      } else {
        BIO_printf(bio_err.get(), "%s:invalid type in 'policy' configuration\n",
                   cv->value);
        goto end;
      }

      if (push != NULL) {
        if (!X509_NAME_add_entry(subject.get(), push, -1, 0)) {
          BIO_printf(bio_err.get(), "Memory allocation failure\n");
          goto end;
        }
      }
      if (j < 0) {
        break;
      }
    }
  }

  if (preserve) {
    subject.reset(X509_NAME_dup(name));
    if (!subject) {
      goto end;
    }
  }

  /* We are now totally happy, lets make and sign the certificate */
  if (verbose) {
    BIO_printf(
        bio_err.get(),
        "Everything appears to be ok, creating and signing the certificate\n");
  }

  ret.reset(X509_new());
  if (!ret) {
    goto end;
  }

  // Assumption: We should only support V3 certificates

  /* Make it an X509 v3 certificate. */
  if (!X509_set_version(ret.get(), 2)) {
    goto end;
  }

  if (BN_to_ASN1_INTEGER(serial.get(), X509_get_serialNumber(ret.get())) ==
      NULL) {
    goto end;
  }

  if (selfsign) {
    if (!X509_set_issuer_name(ret.get(), subject.get())) {
      goto end;
    }
  } else if (!X509_set_issuer_name(ret.get(), X509_get_subject_name(x509))) {
    goto end;
  }

  if (!SetCertTimes(ret.get(), startdate, enddate, days)) {
    goto end;
  }

  if (!enddate.empty()) {
    int tdays = 0, out_seconds = 0;

    if (!ASN1_TIME_diff(&tdays, &out_seconds, NULL,
                        X509_get0_notAfter(ret.get()))) {
      goto end;
    }
    days = tdays;
  }

  if (!X509_set_subject_name(ret.get(), subject.get())) {
    goto end;
  }

  pktmp = X509_REQ_get0_pubkey(req.get());
  if (!X509_set_pubkey(ret.get(), pktmp)) {
    goto end;
  }

  /* Lets add the extensions, if there are any */
  if (!ext_sect.empty()) {
    X509V3_CTX ctx;

    /* Initialize the context structure */
    if (selfsign) {
      X509V3_set_ctx(&ctx, ret.get(), ret.get(), req.get(), nullptr, 0);
    } else {
      X509V3_set_ctx(&ctx, x509, ret.get(), req.get(), nullptr, 0);
    }

    /* We found extensions to be set from config file */
    X509V3_set_nconf(&ctx, lconf.get());

    if (!X509V3_EXT_add_nconf(lconf.get(), &ctx, ext_sect.c_str(), ret.get())) {
      BIO_printf(bio_err.get(), "ERROR: adding extensions in section %s\n",
                 ext_sect.c_str());
      goto end;
    }

    if (verbose) {
      BIO_printf(bio_err.get(), "Successfully added extensions from config\n");
    }
  }

  /* Copy extensions from request (if any) */

  if (!CopyExtensions(ret.get(), req.get(), ext_copy)) {
    BIO_printf(bio_err.get(), "ERROR: adding extensions from request\n");
    goto end;
  }

  if (verbose) {
    BIO_printf(
        bio_err.get(),
        "The subject name appears to be ok, checking data base for clashes\n");
  }

  /* Build the correct Subject if no e-mail is wanted in the subject. */

  /*
   * Its best to dup the subject DN and then delete any email addresses
   * because this retains its structure.
   */
  dn_subject.reset(X509_NAME_dup(subject.get()));
  if (!dn_subject) {
    BIO_printf(bio_err.get(), "Memory allocation failure\n");
    goto end;
  }
  i = -1;
  while ((i = X509_NAME_get_index_by_NID(dn_subject.get(),
                                         NID_pkcs9_emailAddress, i)) >= 0) {
    tmpne = X509_NAME_delete_entry(dn_subject.get(), i--);
    X509_NAME_ENTRY_free(tmpne);
  }

  if (!X509_set_subject_name(ret.get(), dn_subject.get())) {
    goto end;
  }

  row[DB_name] = X509_NAME_oneline(X509_get_subject_name(ret.get()), NULL, 0);
  if (row[DB_name] == NULL) {
    BIO_printf(bio_err.get(), "Memory allocation failure\n");
    goto end;
  }

  if (BN_is_zero(serial.get())) {
    row[DB_serial] = OPENSSL_strdup("00");
  } else {
    row[DB_serial] = BN_bn2hex(serial.get());
  }
  if (row[DB_serial] == NULL) {
    BIO_printf(bio_err.get(), "Memory allocation failure\n");
    goto end;
  }

  if (row[DB_name][0] == '\0') {
    /*
     * An empty subject! We'll use the serial number instead. If
     * unique_subject is in use then we don't want different entries with
     * empty subjects matching each other.
     */
    OPENSSL_free(row[DB_name]);
    row[DB_name] = OPENSSL_strdup(row[DB_serial]);
    if (row[DB_name] == NULL) {
      BIO_printf(bio_err.get(), "Memory allocation failure\n");
      goto end;
    }
  }

  if (db->attributes.unique_subject) {
    OPENSSL_STRING *crow = row;

    rrow = TXT_DB_get_by_index(db->db, DB_name, crow);
    if (rrow != NULL) {
      BIO_printf(bio_err.get(), "ERROR:There is already a certificate for %s\n",
                 row[DB_name]);
    }
  }
  if (rrow == NULL) {
    rrow = TXT_DB_get_by_index(db->db, DB_serial, row);
    if (rrow != NULL) {
      BIO_printf(bio_err.get(),
                 "ERROR:Serial number %s has already been issued,\n",
                 row[DB_serial]);
      BIO_printf(bio_err.get(),
                 "      check the database/serial_file for corruption\n");
    }
  }

  if (rrow != NULL) {
    BIO_printf(bio_err.get(), "The matching entry has the following details\n");
    if (rrow[DB_type][0] == DB_TYPE_EXP) {
      p = "Expired";
    } else if (rrow[DB_type][0] == DB_TYPE_REV) {
      p = "Revoked";
    } else if (rrow[DB_type][0] == DB_TYPE_VAL) {
      p = "Valid";
    } else {
      p = "\ninvalid type, Data base error\n";
    }
    BIO_printf(bio_err.get(), "Type          :%s\n", p);
    if (rrow[DB_type][0] == DB_TYPE_REV) {
      p = rrow[DB_exp_date];
      if (p == NULL) {
        p = "undef";
      }
      BIO_printf(bio_err.get(), "Was revoked on:%s\n", p);
    }
    p = rrow[DB_exp_date];
    if (p == NULL) {
      p = "undef";
    }
    BIO_printf(bio_err.get(), "Expires on    :%s\n", p);
    p = rrow[DB_serial];
    if (p == NULL) {
      p = "undef";
    }
    BIO_printf(bio_err.get(), "Serial Number :%s\n", p);
    p = rrow[DB_file];
    if (p == NULL) {
      p = "undef";
    }
    BIO_printf(bio_err.get(), "File name     :%s\n", p);
    p = rrow[DB_name];
    if (p == NULL) {
      p = "undef";
    }
    BIO_printf(bio_err.get(), "Subject Name  :%s\n", p);
    ok = -1; /* This is now a 'bad' error. */
    goto end;
  }

  BIO_printf(bio_err.get(), "Certificate is to be certified until ");
  ASN1_TIME_print(bio_err.get(), X509_get0_notAfter(ret.get()));
  if (days) {
    BIO_printf(bio_err.get(), " (%ld days)", days);
  }
  BIO_printf(bio_err.get(), "\n");

  // Assumption: I believe we are always operating in batch mode so we don't
  // prompt to sign

  pktmp = X509_get0_pubkey(ret.get());
  if (EVP_PKEY_missing_parameters(pktmp) &&
      !EVP_PKEY_missing_parameters(pkey.get())) {
    EVP_PKEY_copy_parameters(pktmp, pkey.get());
  }

  if (!DoX509Sign(ret, pkey, dgst)) {
    goto end;
  }

  /* We now just add it to the database as DB_TYPE_VAL('V') */
  row[DB_type] = OPENSSL_strdup("V");
  tm = X509_get0_notAfter(ret.get());
  if ((row[DB_exp_date] = (OPENSSL_STRING)OPENSSL_malloc(tm->length + 1)) ==
      NULL) {
    BIO_printf(bio_err.get(), "Memory allocation failure\n");
    goto end;
  }
  memcpy(row[DB_exp_date], tm->data, tm->length);
  row[DB_exp_date][tm->length] = '\0';
  row[DB_rev_date] = NULL;
  row[DB_file] = OPENSSL_strdup("unknown");
  if ((row[DB_type] == nullptr) || (row[DB_file] == nullptr) ||
      (row[DB_name] == nullptr)) {
    BIO_printf(bio_err.get(), "Memory allocation failure\n");
    goto end;
  }

  irow.reset((OPENSSL_STRING *)OPENSSL_malloc(sizeof(OPENSSL_STRING *) *
                                              (DB_NUMBER + 1)));
  if (!irow) {
    BIO_printf(bio_err.get(), "Memory allocation failure\n");
    goto end;
  }
  for (i = 0; i < DB_NUMBER; i++) {
    irow.get()[i] = row[i];
  }
  irow.get()[DB_NUMBER] = nullptr;

  if (!TXT_DB_insert(db->db, irow.get())) {
    BIO_printf(bio_err.get(), "failed to update database\n");
    BIO_printf(bio_err.get(), "TXT_DB error number %ld\n", db->db->error);
    goto end;
  }
  irow.release();
  ok = 1;
end:
  if (ok != 1) {
    for (i = 0; i < DB_NUMBER; i++) {
      OPENSSL_free(row[i]);
    }
  }

  if (ok <= 0) {
    ret.reset();
  } else {
    *xret = ret.release();
  }
  return ok;
}

static int Certify(X509 **ret, std::string infile,
                   bssl::UniquePtr<EVP_PKEY> &pkey, X509 *x509,
                   const EVP_MD *dgst, const STACK_OF(CONF_VALUE) *policy,
                   bssl::UniquePtr<CA_DB> &db, bssl::UniquePtr<BIGNUM> &serial,
                   std::string subj, unsigned long chtype,
                   std::string startdate, std::string enddate, long days,
                   std::string ext_sect, bssl::UniquePtr<CONF> &lconf,
                   int verbose, EXT_COPY_TYPE ext_copy, int selfsign,
                   int preserve) {
  bssl::UniquePtr<X509_REQ> req;
  bssl::UniquePtr<BIO> in;
  EVP_PKEY *pktmp = NULL;
  int ok = -1, i = 0;
  bssl::UniquePtr<BIO> bio_err(BIO_new_fp(stderr, BIO_NOCLOSE));
  if (!bio_err) {
    goto end;
  }

  in = bssl::UniquePtr<BIO>(BIO_new_file(infile.c_str(), "r"));
  if (!in) {
    goto end;
  }
  req = bssl::UniquePtr<X509_REQ>(
      PEM_read_bio_X509_REQ(in.get(), nullptr, nullptr, nullptr));
  if (!req) {
    BIO_printf(bio_err.get(), "Error reading certificate request in %s\n",
               infile.c_str());
    goto end;
  }
  if (verbose) {
    X509_REQ_print_ex(bio_err.get(), req.get(), 0, X509_FLAG_COMPAT);
  }

  BIO_printf(bio_err.get(), "Check that the request matches the signature\n");

  if (selfsign && !X509_REQ_check_private_key(req.get(), pkey.get())) {
    BIO_printf(bio_err.get(),
               "Certificate request and CA private key do not match\n");
    ok = 0;
    goto end;
  }
  if ((pktmp = X509_REQ_get0_pubkey(req.get())) == NULL) {
    BIO_printf(bio_err.get(), "error unpacking public key\n");
    goto end;
  }
  i = X509_REQ_verify(req.get(), pktmp);
  if (i < 0) {
    ok = 0;
    BIO_printf(bio_err.get(), "Signature verification problems....\n");
    goto end;
  }
  if (i == 0) {
    ok = 0;
    BIO_printf(bio_err.get(),
               "Signature did not match the certificate request\n");
    goto end;
  } else {
    BIO_printf(bio_err.get(), "Signature ok\n");
  }

  ok = DoBody(bio_err, ret, pkey, x509, dgst, policy, db, serial, subj, chtype,
              startdate, enddate, days, verbose, req, ext_sect, lconf, ext_copy,
              selfsign, preserve);

end:
  return ok;
}

static int SaveSerial(std::string serialfile, std::string suffix,
                      bssl::UniquePtr<BIGNUM> &serial) {
  char buf[1][BSIZE];
  bssl::UniquePtr<BIO> out;
  ossl_char_ptr hex(nullptr, OPENSSL_free);
  int ret = 0;
  bssl::UniquePtr<ASN1_INTEGER> ai;
  int j = 0;

  if (suffix.empty()) {
    j = strlen(serialfile.c_str());
  } else {
    j = strlen(serialfile.c_str()) + strlen(suffix.c_str()) + 1;
  }
  if (j >= BSIZE) {
    fprintf(stderr, "file name too long\n");
    goto err;
  }

  if (suffix.empty()) {
    OPENSSL_strlcpy(buf[0], serialfile.c_str(), BSIZE);
  } else {
    (void)BIO_snprintf(buf[0], sizeof(buf[0]), "%s.%s", serialfile.c_str(),
                       suffix.c_str());
  }
  out.reset(BIO_new_file(buf[0], "w"));
  if (!out) {
    goto err;
  }
  ai.reset(BN_to_ASN1_INTEGER(serial.get(), NULL));
  if (!ai) {
    fprintf(stderr, "error converting serial to ASN.1 format\n");
    goto err;
  }
  i2a_ASN1_INTEGER(out.get(), ai.get());
  BIO_puts(out.get(), "\n");
  ret = 1;
err:
  return ret;
}

static int RotateSerial(std::string serialfile, std::string new_suffix,
                        std::string old_suffix) {
  char buf[2][BSIZE];
  int i = 0, j = 0;

  i = strlen(serialfile.c_str()) + strlen(old_suffix.c_str());
  j = strlen(serialfile.c_str()) + strlen(new_suffix.c_str());
  if (i > j) {
    j = i;
  }
  if (j + 1 >= BSIZE) {
    fprintf(stderr, "file name too long\n");
    goto err;
  }
  (void)BIO_snprintf(buf[0], sizeof(buf[0]), "%s.%s", serialfile.c_str(),
                     new_suffix.c_str());
  (void)BIO_snprintf(buf[1], sizeof(buf[1]), "%s.%s", serialfile.c_str(),
                     old_suffix.c_str());
  if (rename(serialfile.c_str(), buf[1]) < 0 && errno != ENOENT &&
      errno != ENOTDIR) {
    fprintf(stderr, "unable to rename %s to %s\n", serialfile.c_str(), buf[1]);
    perror("reason");
    goto err;
  }
  if (rename(buf[0], serialfile.c_str()) < 0) {
    fprintf(stderr, "unable to rename %s to %s\n", buf[0], serialfile.c_str());
    perror("reason");
    rename(buf[1], serialfile.c_str());
    goto err;
  }
  return 1;
err:
  return 0;
}

bool caTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args,
                                     kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, outfile, config_path, start_date, end_date, outdir,
      dbfile;
  bool help = false, self_sign = false, notext = false, batch = true,
       preserveDN = false, rand_serial = false;
  std::string ca_section, policy, keyfile, serialfile, extensions;
  EXT_COPY_TYPE copy_extensions = EXT_COPY_NONE;
  DB_ATTR dbattr = {0};
  bssl::UniquePtr<CA_DB> db(nullptr);
  const EVP_MD *md = nullptr;
  DEF_DGST_USAGE md_usage = DEF_DGST_UNKNOWN;
  bssl::UniquePtr<BIGNUM> serial;
  const STACK_OF(CONF_VALUE) *attribs = nullptr;
  auto cert_sk = sk_X509_new_null();
  int total = 0, total_done = 0;
  long days = 0;
  char new_cert[PATH_MAX];
  size_t outdirlen = 0;
  bssl::UniquePtr<CONF> ca_conf(nullptr);
  Password passin;
  bssl::UniquePtr<EVP_PKEY> pkey;
  bool ret = false, verbose = false;

  GetBoolArgument(&help, "-help", parsed_args);
  GetBoolArgument(&verbose, "-verbose", parsed_args);
  GetString(&in_path, "-in", "", parsed_args);
  GetString(&outfile, "-out", "", parsed_args);
  GetString(&config_path, "-config", "", parsed_args);
  GetString(&passin.get(), "-passin", "", parsed_args);
  GetString(&start_date, "-startdate", "", parsed_args);
  GetString(&end_date, "-enddate", "", parsed_args);
  GetBoolArgument(&notext, "-notext", parsed_args);
  GetBoolArgument(&self_sign, "-selfsign", parsed_args);
  // GetBoolArgument(&batch, "-batch", parsed_args);
  (void)self_sign;
  (void)batch;

  // Assumption: we default as if `-noemailDN` was provided and don't support
  // `email_in_dn` attribute in the configuration file Per RFC 5280 for v3
  // certificates: "Conforming implementations generating new certificates with
  //  electronic mail addresses MUST use the rfc822Name in the subject
  //  alternative name extension (Section 4.2.1.6) to describe such
  //  identities."

  // Display asn1parse tool option summary
  if (help) {
    PrintUsage(kArguments);
    goto err;
  }

  if (!self_sign || in_path.empty()) {
    // TODO: Error we are only supporting a specfic use-case for 'openssl ca'
    // at this time.
    goto err;
  }

  if (config_path.empty() || !LoadConfig(config_path, ca_conf)) {
    goto err;
  }

  {
    std::unique_ptr<std::string> value =
        GetSectionValue(ca_conf, CA_SECTION, CA_DEFAULT_CA_OPT);
    if (!value) {
      goto err;
    }
    ca_section = std::move(*value);
  }

  /*
   * These features we are choosing not to support regarding CA options:
   * RANDFILE
   * oid_file
   * oid_section
   * name_opt
   * cert_opt
   * crlnumber
   * msie_hack
   * string_mask (not documented as a feature in OpenSSL 3.x CLIs but 1.1.1
   * seemed to read)
   */

  dbattr.unique_subject =
      ParseBoolSectionValue(ca_conf, ca_section, CA_UNIQ_SUBJ_OPT, 1);

  // Do private key related stuff...
  {
    auto value = GetSectionValue(ca_conf, ca_section, CA_PRIVATE_KEY_OPT);
    if (!value) {
      goto err;
    }
    keyfile = std::move(*value);
  }

  if (!LoadPrivateKey(keyfile, passin, pkey)) {
    // LoadPrivateKey will print a message for us
    goto err;
  }

  preserveDN =
      ParseBoolSectionValue(ca_conf, ca_section, CA_PRESERVE_OPT, false);

  {
    auto value = GetSectionValue(ca_conf, ca_section, CA_COPY_EXT_OPT);
    if (value) {
      copy_extensions = ParseCopyExtensionValue(*value.get());
      if (copy_extensions == EXT_COPY_UNKNOWN) {
        goto err;
      }
    }
  }

  // Assumption: We are always working with the expectation that `-in` is
  // provided, that this is a CSR, additionally we are continuing with the
  // assumption that `-selfsign` was also provided.

  {
    auto value = GetSectionValue(ca_conf, ca_section, CA_NEW_CERTS_DIR_OPT);
    if (!value) {
      goto err;
    }
    outdir = std::move(*value);
  }

  // Assumption: not supporting -status for serial querying
  {
    auto value = GetSectionValue(ca_conf, ca_section, CA_DATABASE_OPT);
    if (!value) {
      goto err;
    }
    dbfile = std::move(*value);
  }

  db = LoadIndex(dbfile, &dbattr);
  if (!db) {
    goto err;
  }

  /* Lets check some fields */
  for (size_t i = 0; i < sk_OPENSSL_PSTRING_num(db.get()->db->data); i++) {
    auto pp = sk_OPENSSL_PSTRING_value(db->db->data, i);
    if ((pp[DB_type][0] != DB_TYPE_REV) && (pp[DB_rev_date][0] != '\0')) {
      fprintf(stderr, "entry %zu: not revoked yet, but has a revocation date\n",
              i + 1);
      goto err;
    }
    if ((pp[DB_type][0] == DB_TYPE_REV) &&
        !MakeRevoked(NULL, pp[DB_rev_date])) {
      fprintf(stderr, " in entry %zu\n", i + 1);
      goto err;
    }
    if (!CheckTimeFormat((char *)pp[DB_exp_date])) {
      fprintf(stderr, "entry %zu: invalid expiry date\n", i + 1);
      goto err;
    }
    auto p = pp[DB_serial];
    auto j = strlen(p);
    if (*p == '-') {
      p++;
      j--;
    }
    if ((j & 1) || (j < 2)) {
      fprintf(stderr, "entry %zu: bad serial number length (%zu)\n", i + 1, j);
      goto err;
    }
    for (; *p; p++) {
      if (!isxdigit((unsigned char)(*p))) {
        fprintf(stderr, "entry %zu: bad char 0%o '%c' in serial number\n",
                i + 1, (unsigned int)*p, *p);
        goto err;
      }
    }
  }

  if (!IndexIndex(db)) {
    goto err;
  }

  // Assumption: Not supporting -extfile or -extensions flags only supporting
  // conf file configuration.

  // Figure out the signing digest to use
  md_usage = EVP_PKEY_get_default_digest_nid(pkey, &md);
  {
    auto value = GetSectionValue(ca_conf, ca_section, CA_DFLT_MD_OPT);
    if (value) {
      if (strcasecmp(value->c_str(), "default") != 0) {
        if (md_usage == DEF_DGST_REQUIRED) {
          goto err;
        }
        md = EVP_get_digestbyname(value->c_str());
        if (!md) {
          goto err;
        }
      }
    } else if (md_usage == DEF_DGST_UNKNOWN) {
      goto err;
    }
  }

  // Assumption: not going to support email_in_dn

  // Find the policy info
  {
    auto value = GetSectionValue(ca_conf, ca_section, CA_POLICY_OPT);
    if (!value) {
      goto err;
    }
    policy = std::move(*value);
  }

  // figure out whether we are generating a random serial or not, OpenSSL 1.1.1
  // CLI appears to have taken any value as being truthy. But we adjust that
  // behavior here.
  rand_serial =
      ParseBoolSectionValue(ca_conf, ca_section, CA_RAND_SERIAL_OPT, 0);
  if (!rand_serial) {
    auto value = GetSectionValue(ca_conf, ca_section, CA_SERIAL_OPT);
    if (!value) {
      goto err;
    }
    serialfile = std::move(*value);
  }

  {
    auto value = GetSectionValue(ca_conf, ca_section, CA_X509_EXT_OPT);
    if (value) {
      /* Check syntax of file */
      X509V3_CTX ctx;
      X509V3_set_ctx_test(&ctx);
      X509V3_set_nconf(&ctx, ca_conf.get());
      if (!X509V3_EXT_add_nconf(ca_conf.get(), &ctx, value->c_str(), NULL)) {
        fprintf(stderr, "Error Loading extension section %s\n",
                extensions.c_str());
        goto err;
      }
      extensions = std::move(*value);
    }
  }

  if (start_date.empty()) {
    auto value = GetSectionValue(ca_conf, ca_section, CA_DFLT_STRTDT_OPT);
    if (value && !ASN1_TIME_set_string_X509(NULL, value->c_str())) {
      fprintf(stderr,
              "start date is invalid, it should be YYMMDDHHMMSSZ or "
              "YYYYMMDDHHMMSSZ\n");
      goto err;
    }
    if (value) {
      start_date = std::move(*value);
    } else {
      start_date = "today";
    }
  }

  if (end_date.empty()) {
    auto value = GetSectionValue(ca_conf, ca_section, CA_DFLT_ENDDT_OPT);
    if (value && !ASN1_TIME_set_string_X509(NULL, value->c_str())) {
      fprintf(stderr,
              "end date is invalid, it should be YYMMDDHHMMSSZ or "
              "YYYYMMDDHHMMSSZ\n");
      goto err;
    }
    if (value) {
      end_date = std::move(*value);
    }
  }

  days = ParseNumberSectionValue(ca_conf, ca_section, CA_DAYS_OPT, 0);
  if (days <= 0 && end_date.empty()) {
    fprintf(stderr, "cannot lookup how many days to certify for\n");
    goto err;
  }

  if (rand_serial) {
    if (!RandSerial(serial, nullptr)) {
      fprintf(stderr, "error generating serial number\n");
      goto err;
    }
  } else {
    serial = LoadSerial(serialfile, NULL, 0);
    if (!serial) {
      fprintf(stderr, "error while loading serial number\n");
      goto err;
    }
  }

  attribs = NCONF_get_section(ca_conf.get(), policy.c_str());
  if (!attribs) {
    fprintf(stderr, "unable to find 'section' for %s\n", policy.c_str());
    goto err;
  }

  {
    int j = 0;
    X509 *signer = nullptr;  // Only supporting self-sign use-case
    X509 *out = nullptr;
    bssl::UniquePtr<X509> out_owner;
    total++;
    j = Certify(&out, in_path, pkey, signer, md, attribs, db, serial, "",
                MBSTRING_ASC, start_date, end_date, days, extensions, ca_conf,
                verbose, copy_extensions, 1, preserveDN);
    if (j <= 0) {
      goto err;
    }
    out_owner.reset(out);
    total_done++;
    fprintf(stderr, "\n");
    if (!BN_add_word(serial.get(), 1)) {
      goto err;
    }
    if (!sk_X509_push(cert_sk, out_owner.get())) {
      fprintf(stderr, "Memory allocation failure\n");
      goto err;
    }
    out_owner.release();
    for (size_t i = 0; i < extra_args.size(); i++) {
      if (i > INT_MAX) {
        goto err;
      }
      total++;
      j = Certify(&out, extra_args[i], pkey, signer, md, attribs, db, serial,
                  "", MBSTRING_ASC, start_date, end_date, days, extensions,
                  ca_conf, verbose, copy_extensions, 1, preserveDN);
      if (j <= 0) {
        goto err;
      }
      total_done++;
      out_owner.reset(out);
      fprintf(stderr, "\n");
      if (!BN_add_word(serial.get(), 1)) {
        goto err;
      }
      if (!sk_X509_push(cert_sk, out_owner.get())) {
        fprintf(stderr, "Memory allocation failure\n");
        goto err;
      }
      out_owner.release();
    }
  }

  /*
   * we have a stack of newly certified certificates and a data base
   * and serial number that need updating
   */
  if (sk_X509_num(cert_sk) > 0) {
    fprintf(stderr, "Write out database with %zu new entries\n",
            sk_X509_num(cert_sk));

    if (!serialfile.empty() && !SaveSerial(serialfile, "new", serial)) {
      goto err;
    }

    if (!SaveIndex(dbfile, "new", db)) {
      goto err;
    }
  }

  (void)OPENSSL_strlcpy(new_cert, outdir.c_str(), sizeof(new_cert));
  (void)OPENSSL_strlcat(new_cert, "/", sizeof(new_cert));

  if (verbose) {
    fprintf(stderr, "writing new certificates\n");
  }

  {
    for (size_t i = 0; i < sk_X509_num(cert_sk); i++) {
      bssl::UniquePtr<BIO> new_cert_bio, outfile_bio;
      X509 *xi = sk_X509_value(cert_sk, i);
      ASN1_INTEGER *serialNumber = X509_get_serialNumber(xi);
      const unsigned char *psn = ASN1_STRING_get0_data(serialNumber);
      const int snl = ASN1_STRING_length(serialNumber);
      const int filen_len = 2 * (snl > 0 ? snl : 1) + sizeof(".pem");
      char *n = new_cert + outdirlen;

      if (outdirlen + filen_len > PATH_MAX) {
        fprintf(stderr, "certificate file name too long\n");
        goto err;
      }

      if (snl > 0) {
        static const char HEX_DIGITS[] = "0123456789ABCDEF";

        for (int j = 0; j < snl; j++, psn++) {
          *n++ = HEX_DIGITS[*psn >> 4];
          *n++ = HEX_DIGITS[*psn & 0x0F];
        }
      } else {
        *(n++) = '0';
        *(n++) = '0';
      }
      *(n++) = '.';
      *(n++) = 'p';
      *(n++) = 'e';
      *(n++) = 'm';
      *n = '\0'; /* closing new_cert */
      if (verbose) {
        fprintf(stderr, "writing %s\n", new_cert);
      }

      if (outfile.empty()) {
        outfile_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
      } else {
        outfile_bio.reset(BIO_new_file(outfile.c_str(), "w"));
      }
      if (!outfile_bio) {
        goto err;
      }

      new_cert_bio = bssl::UniquePtr<BIO>(BIO_new_file(new_cert, "w"));
      if (!new_cert_bio) {
        perror(new_cert);
        goto err;
      }
      WriteNewCertificate(new_cert_bio, xi, 0, notext);
      WriteNewCertificate(outfile_bio, xi, 0, notext);
    }
  }

  if (sk_X509_num(cert_sk)) {
    /* Rename the database and the serial file */
    if (!serialfile.empty() && !RotateSerial(serialfile, "new", "old")) {
      goto err;
    }

    if (!RotateIndex(dbfile, "new", "old")) {
      goto err;
    }

    fprintf(stderr, "Data Base Updated\n");
  }

  (void)total;
  (void)total_done;

  ret = true;

err:
  if (!ret) {
    ERR_print_errors_fp(stderr);
  }
  sk_X509_pop_free(cert_sk, X509_free);
  return ret;
}
