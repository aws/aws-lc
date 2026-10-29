// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/digest.h>
#include <openssl/obj.h>
#include <openssl/ocsp.h>
#include <openssl/pem.h>
#include <openssl/x509.h>

#include <cctype>
#include <cerrno>
#include <climits>
#include <cstdlib>
#include <cstring>
#include <string>

#include "ca_req_common.h"
#include "internal.h"
#include "txt_db/txt_db.h"

#define DB_NUMBER 6
#define DB_type 0
#define DB_rev_date 2
#define DB_serial 3
#define DB_TYPE_REV 'R'
#define DB_TYPE_VAL 'V'
#define DB_TYPE_EXP 'E'

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-issuer", kOptionalArgument,
     "Issuer certificate of the certificate being checked (request mode)."},
    {"-cert", kOptionalArgument,
     "Certificate to add to the OCSP request (request mode)."},
    {"-reqout", kOptionalArgument,
     "Write the DER-encoded OCSP request to this file."},
    {"-reqin", kOptionalArgument,
     "Read a DER-encoded OCSP request from this file (responder mode)."},
    {"-respout", kOptionalArgument,
     "Write the DER-encoded OCSP response to this file (responder mode)."},
    {"-index", kOptionalArgument,
     "CA index database file used to determine certificate status."},
    {"-CA", kOptionalArgument,
     "CA certificate the request is issued under (responder mode)."},
    {"-rsigner", kOptionalArgument,
     "Certificate used to sign the OCSP response."},
    {"-rkey", kOptionalArgument,
     "Private key used to sign the OCSP response."},
    {"-ndays", kOptionalArgument,
     "Number of days before the next OCSP response update is due."},
    {"", kOptionalArgument, ""}};

static bssl::UniquePtr<X509> LoadCert(const std::string &path) {
  bssl::UniquePtr<BIO> in(BIO_new_file(path.c_str(), "r"));
  if (!in) {
    return nullptr;
  }
  return bssl::UniquePtr<X509>(
      PEM_read_bio_X509(in.get(), nullptr, nullptr, nullptr));
}

static uint32_t index_serial_hash(const OPENSSL_STRING *a) {
  const char *n = a[DB_serial];
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

static OPENSSL_STRING *LookupSerial(bssl::UniquePtr<TXT_DB> &db,
                                    const ASN1_INTEGER *serial) {
  OPENSSL_STRING row[DB_NUMBER];
  for (int i = 0; i < DB_NUMBER; i++) {
    row[i] = nullptr;
  }
  bssl::UniquePtr<BIGNUM> bn(ASN1_INTEGER_to_BN(serial, nullptr));
  if (!bn) {
    return nullptr;
  }
  bssl::UniquePtr<char> hex(BN_is_zero(bn.get()) ? OPENSSL_strdup("00")
                                                 : BN_bn2hex(bn.get()));
  if (!hex) {
    return nullptr;
  }
  row[DB_serial] = hex.get();
  return TXT_DB_get_by_index(db, DB_serial, row);
}

// Request mode: build an OCSP request for -cert under -issuer and write it.
static bool BuildRequest(const std::string &issuer_path,
                         const std::string &cert_path,
                         const std::string &reqout_path) {
  if (issuer_path.empty() || cert_path.empty()) {
    fprintf(stderr, "-reqout requires -issuer and -cert\n");
    return false;
  }
  bssl::UniquePtr<X509> issuer(LoadCert(issuer_path));
  bssl::UniquePtr<X509> cert(LoadCert(cert_path));
  if (!issuer || !cert) {
    fprintf(stderr, "unable to load -issuer or -cert\n");
    return false;
  }
  bssl::UniquePtr<OCSP_REQUEST> req(OCSP_REQUEST_new());
  if (!req) {
    return false;
  }
  OCSP_CERTID *id = OCSP_cert_to_id(nullptr, cert.get(), issuer.get());
  if (id == nullptr || !OCSP_request_add0_id(req.get(), id)) {
    OCSP_CERTID_free(id);
    return false;
  }
  bssl::UniquePtr<BIO> out(BIO_new_file(reqout_path.c_str(), "wb"));
  if (!out || !i2d_OCSP_REQUEST_bio(out.get(), req.get())) {
    fprintf(stderr, "unable to write OCSP request to %s\n", reqout_path.c_str());
    return false;
  }
  return true;
}

// Maps an index CRL reason string to an OCSP_REVOKED_STATUS_* code (same reason
// set as ca.cc's UnpackRevinfo), or OCSP_REVOKED_STATUS_NOSTATUS (-1) if
// unknown. The reason's argument is dropped, unlike OpenSSL; see README.
static int OcspReasonFromString(const std::string &reason) {
  static const char *const kReasons[] = {
      "unspecified",          "keyCompromise",   "CACompromise",
      "affiliationChanged",   "superseded",      "cessationOfOperation",
      "certificateHold",      "removeFromCRL",   "holdInstruction",
      "keyTime",              "CAkeyTime"};
  int idx = -1;
  for (int i = 0; i < static_cast<int>(sizeof(kReasons) / sizeof(kReasons[0]));
       i++) {
    if (OPENSSL_strcasecmp(reason.c_str(), kReasons[i]) == 0) {
      idx = i;
      break;
    }
  }
  switch (idx) {
    case 0: return OCSP_REVOKED_STATUS_UNSPECIFIED;
    case 1: return OCSP_REVOKED_STATUS_KEYCOMPROMISE;
    case 2: return OCSP_REVOKED_STATUS_CACOMPROMISE;
    case 3: return OCSP_REVOKED_STATUS_AFFILIATIONCHANGED;
    case 4: return OCSP_REVOKED_STATUS_SUPERSEDED;
    case 5: return OCSP_REVOKED_STATUS_CESSATIONOFOPERATION;
    case 6: return OCSP_REVOKED_STATUS_CERTIFICATEHOLD;
    case 7: return OCSP_REVOKED_STATUS_REMOVEFROMCRL;
    case 8: return OCSP_REVOKED_STATUS_CERTIFICATEHOLD;  // holdInstruction
    case 9: return OCSP_REVOKED_STATUS_KEYCOMPROMISE;    // keyTime
    case 10: return OCSP_REVOKED_STATUS_CACOMPROMISE;    // CAkeyTime
    default: return OCSP_REVOKED_STATUS_NOSTATUS;
  }
}

// Responder mode: read -reqin, determine each certificate's status from the
// -index database under -CA, sign the response with -rsigner/-rkey, and write
// it to -respout.
static bool MakeResponse(const std::string &reqin_path,
                         const std::string &respout_path,
                         const std::string &index_path,
                         const std::string &ca_path,
                         const std::string &rsigner_path,
                         const std::string &rkey_path, long ndays) {
  if (reqin_path.empty() || index_path.empty() || ca_path.empty() ||
      rsigner_path.empty() || rkey_path.empty()) {
    fprintf(stderr,
            "-respout requires -reqin, -index, -CA, -rsigner, and -rkey\n");
    return false;
  }

  bssl::UniquePtr<BIO> reqin(BIO_new_file(reqin_path.c_str(), "rb"));
  bssl::UniquePtr<OCSP_REQUEST> req(
      reqin ? d2i_OCSP_REQUEST_bio(reqin.get(), nullptr) : nullptr);
  if (!req) {
    fprintf(stderr, "unable to read OCSP request from %s\n", reqin_path.c_str());
    return false;
  }

  bssl::UniquePtr<X509> ca_cert(LoadCert(ca_path));
  bssl::UniquePtr<X509> rsigner(LoadCert(rsigner_path));
  if (!ca_cert || !rsigner) {
    fprintf(stderr, "unable to load -CA or -rsigner\n");
    return false;
  }
  Password passin;
  bssl::UniquePtr<EVP_PKEY> rkey;
  if (!LoadPrivateKey(rkey_path, passin, rkey)) {
    return false;
  }

  bssl::UniquePtr<BIO> index_bio(BIO_new_file(index_path.c_str(), "r"));
  bssl::UniquePtr<TXT_DB> db(index_bio ? TXT_DB_read(index_bio, DB_NUMBER)
                                       : nullptr);
  if (!db) {
    fprintf(stderr, "unable to load index from %s\n", index_path.c_str());
    return false;
  }
  if (!TXT_DB_create_index(db, DB_serial, nullptr, index_serial_hash,
                           index_serial_cmp)) {
    fprintf(stderr, "unable to index the database\n");
    return false;
  }

  bssl::UniquePtr<OCSP_BASICRESP> bs(OCSP_BASICRESP_new());
  if (!bs) {
    return false;
  }
  bssl::UniquePtr<ASN1_TIME> thisupd(X509_gmtime_adj(nullptr, 0));
  bssl::UniquePtr<ASN1_TIME> nextupd(
      ndays > 0 ? X509_time_adj_ex(nullptr, ndays, 0, nullptr) : nullptr);
  if (!thisupd || (ndays > 0 && !nextupd)) {
    return false;
  }

  const int count = OCSP_request_onereq_count(req.get());
  if (count <= 0) {
    fprintf(stderr, "OCSP request contains no certificate IDs\n");
    return false;
  }
  for (int i = 0; i < count; i++) {
    OCSP_ONEREQ *one = OCSP_request_onereq_get0(req.get(), i);
    OCSP_CERTID *cid = OCSP_onereq_get0_id(one);

    ASN1_OBJECT *md_oid = nullptr;
    OCSP_id_get0_info(nullptr, &md_oid, nullptr, nullptr, cid);
    const EVP_MD *req_md = EVP_get_digestbyobj(md_oid);
    if (req_md == nullptr) {
      // Without the request's hash we cannot build a comparable CertID, so the
      // issuer check would spuriously miss and we'd sign an "unknown" the
      // client might cache. Reject instead, as OpenSSL's responder does.
      fprintf(stderr, "unsupported certificate ID hash\n");
      return false;
    }

    bssl::UniquePtr<OCSP_CERTID> ca_id(
        OCSP_cert_to_id(req_md, nullptr, ca_cert.get()));
    const bool found = ca_id && OCSP_id_issuer_cmp(ca_id.get(), cid) == 0;

    ASN1_INTEGER *serial = nullptr;
    OCSP_id_get0_info(nullptr, nullptr, nullptr, &serial, cid);
    OPENSSL_STRING *row = found ? LookupSerial(db, serial) : nullptr;

    int status = V_OCSP_CERTSTATUS_UNKNOWN;
    int reason = 0;
    bssl::UniquePtr<ASN1_TIME> revtm;
    if (!found || row == nullptr) {
      status = V_OCSP_CERTSTATUS_UNKNOWN;
    } else if (row[DB_type][0] == DB_TYPE_VAL ||
               row[DB_type][0] == DB_TYPE_EXP) {
      // Deliberate deviation: OpenSSL emits no response for an expired ('E')
      // entry; we report GOOD instead (see README differences list).
      status = V_OCSP_CERTSTATUS_GOOD;
    } else if (row[DB_type][0] == DB_TYPE_REV) {
      status = V_OCSP_CERTSTATUS_REVOKED;
      // The index field is "date[,reason[,arg]]". Honor the stored reason and
      // fall back to "unspecified" only when none is present, since AWS-LC's
      // OCSP_basic_add1_status rejects OCSP_REVOKED_STATUS_NOSTATUS (-1).
      reason = OCSP_REVOKED_STATUS_UNSPECIFIED;
      std::string field(row[DB_rev_date] ? row[DB_rev_date] : "");
      std::string date = field;
      const size_t comma = field.find(',');
      if (comma != std::string::npos) {
        date = field.substr(0, comma);
        std::string rest = field.substr(comma + 1);
        const size_t comma2 = rest.find(',');
        const std::string reason_str =
            comma2 == std::string::npos ? rest : rest.substr(0, comma2);
        reason = OcspReasonFromString(reason_str);
        if (reason == OCSP_REVOKED_STATUS_NOSTATUS) {
          fprintf(stderr, "invalid revocation reason '%s' in index\n",
                  reason_str.c_str());
          return false;
        }
      }
      revtm.reset(ASN1_TIME_new());
      if (!revtm || !ASN1_TIME_set_string(revtm.get(), date.c_str())) {
        fprintf(stderr, "invalid revocation date in index\n");
        return false;
      }
    } else {
      // Unrecognized index entry type: report UNKNOWN so the client gets a
      // definitive answer instead of a certificate with no status.
      status = V_OCSP_CERTSTATUS_UNKNOWN;
    }

    if (OCSP_basic_add1_status(bs.get(), cid, status, reason, revtm.get(),
                               thisupd.get(), nextupd.get()) == nullptr) {
      fprintf(stderr, "unable to add certificate status to OCSP response\n");
      return false;
    }
  }

  OCSP_copy_nonce(bs.get(), req.get());

  if (!OCSP_basic_sign(bs.get(), rsigner.get(), rkey.get(), EVP_sha256(),
                       nullptr, 0)) {
    fprintf(stderr, "unable to sign OCSP response\n");
    return false;
  }
  bssl::UniquePtr<OCSP_RESPONSE> resp(
      OCSP_response_create(OCSP_RESPONSE_STATUS_SUCCESSFUL, bs.get()));
  if (!resp) {
    return false;
  }
  bssl::UniquePtr<BIO> out(BIO_new_file(respout_path.c_str(), "wb"));
  if (!out || !i2d_OCSP_RESPONSE_bio(out.get(), resp.get())) {
    fprintf(stderr, "unable to write OCSP response to %s\n",
            respout_path.c_str());
    return false;
  }
  return true;
}

// Parse a -ndays value: the whole token must be a positive decimal integer
// within the range X509_time_adj_ex accepts (an int day count). OpenSSL
// rejects non-numeric, negative, zero, trailing-garbage, and out-of-range
// values rather than silently reinterpreting them.
static bool ParseNdays(const std::string &s, long *out) {
  if (s.empty() || !isdigit(static_cast<unsigned char>(s[0]))) {
    return false;
  }
  errno = 0;
  char *end = nullptr;
  const long v = strtol(s.c_str(), &end, 10);
  if (errno != 0 || end != s.c_str() + s.size() || v <= 0 || v > INT_MAX) {
    return false;
  }
  *out = v;
  return true;
}

int ocspTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args,
                                     kArguments) ||
      !extra_args.empty()) {
    PrintUsage(kArguments);
    return kToolExitFailure;
  }

  bool help = false;
  std::string issuer, cert, reqout, reqin, respout, index, ca, rsigner, rkey,
      ndays_str;
  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&issuer, "-issuer", "", parsed_args);
  GetString(&cert, "-cert", "", parsed_args);
  GetString(&reqout, "-reqout", "", parsed_args);
  GetString(&reqin, "-reqin", "", parsed_args);
  GetString(&respout, "-respout", "", parsed_args);
  GetString(&index, "-index", "", parsed_args);
  GetString(&ca, "-CA", "", parsed_args);
  GetString(&rsigner, "-rsigner", "", parsed_args);
  GetString(&rkey, "-rkey", "", parsed_args);
  GetString(&ndays_str, "-ndays", "", parsed_args);

  if (help) {
    PrintUsage(kArguments);
    return kToolExitSuccess;
  }

  if (reqout.empty() && respout.empty()) {
    fprintf(stderr, "No operation specified (use -reqout or -respout)\n");
    return kToolExitFailure;
  }

  if (!reqout.empty() && !BuildRequest(issuer, cert, reqout)) {
    return kToolExitFailure;
  }
  if (!respout.empty()) {
    long ndays = -1;
    if (!ndays_str.empty() && !ParseNdays(ndays_str, &ndays)) {
      fprintf(stderr, "invalid -ndays value '%s'\n", ndays_str.c_str());
      return kToolExitFailure;
    }
    if (!MakeResponse(reqin, respout, index, ca, rsigner, rkey, ndays)) {
      return kToolExitFailure;
    }
  }
  return kToolExitSuccess;
}
