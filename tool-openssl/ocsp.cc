// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/digest.h>
#include <openssl/obj.h>
#include <openssl/ocsp.h>
#include <openssl/pem.h>
#include <openssl/x509.h>

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
  const char *aa, *bb;
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
  bssl::UniquePtr<BIO> out(BIO_new_file(reqout_path.c_str(), "w"));
  if (!out || !i2d_OCSP_REQUEST_bio(out.get(), req.get())) {
    fprintf(stderr, "unable to write OCSP request to %s\n", reqout_path.c_str());
    return false;
  }
  return true;
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

  bssl::UniquePtr<BIO> reqin(BIO_new_file(reqin_path.c_str(), "r"));
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
  if (!thisupd) {
    return false;
  }

  const int count = OCSP_request_onereq_count(req.get());
  for (int i = 0; i < count; i++) {
    OCSP_ONEREQ *one = OCSP_request_onereq_get0(req.get(), i);
    OCSP_CERTID *cid = OCSP_onereq_get0_id(one);

    ASN1_OBJECT *md_oid = nullptr;
    OCSP_id_get0_info(nullptr, &md_oid, nullptr, nullptr, cid);
    const EVP_MD *req_md = EVP_get_digestbyobj(md_oid);

    bssl::UniquePtr<OCSP_CERTID> ca_id(
        OCSP_cert_to_id(req_md, nullptr, ca_cert.get()));
    const bool found = ca_id && OCSP_id_issuer_cmp(ca_id.get(), cid) == 0;

    ASN1_INTEGER *serial = nullptr;
    OCSP_id_get0_info(nullptr, nullptr, nullptr, &serial, cid);
    OPENSSL_STRING *row = found ? LookupSerial(db, serial) : nullptr;

    if (!found || row == nullptr) {
      OCSP_basic_add1_status(bs.get(), cid, V_OCSP_CERTSTATUS_UNKNOWN, 0,
                             nullptr, thisupd.get(), nextupd.get());
    } else if (row[DB_type][0] == DB_TYPE_VAL) {
      OCSP_basic_add1_status(bs.get(), cid, V_OCSP_CERTSTATUS_GOOD, 0, nullptr,
                             thisupd.get(), nextupd.get());
    } else if (row[DB_type][0] == DB_TYPE_REV) {
      std::string rev(row[DB_rev_date] ? row[DB_rev_date] : "");
      const size_t comma = rev.find(',');
      if (comma != std::string::npos) {
        rev = rev.substr(0, comma);
      }
      bssl::UniquePtr<ASN1_TIME> revtm(ASN1_TIME_new());
      if (!revtm || !ASN1_TIME_set_string(revtm.get(), rev.c_str())) {
        fprintf(stderr, "invalid revocation date in index\n");
        return false;
      }
      // AWS-LC requires a concrete reason code for revoked entries; the index
      // produced by `ca -revoke` carries no reason, so report "unspecified".
      if (OCSP_basic_add1_status(bs.get(), cid, V_OCSP_CERTSTATUS_REVOKED,
                                 OCSP_REVOKED_STATUS_UNSPECIFIED, revtm.get(),
                                 thisupd.get(), nextupd.get()) == nullptr) {
        return false;
      }
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
  bssl::UniquePtr<BIO> out(BIO_new_file(respout_path.c_str(), "w"));
  if (!out || !i2d_OCSP_RESPONSE_bio(out.get(), resp.get())) {
    fprintf(stderr, "unable to write OCSP response to %s\n",
            respout_path.c_str());
    return false;
  }
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
    const long ndays = ndays_str.empty() ? -1 : std::atol(ndays_str.c_str());
    if (!MakeResponse(reqin, respout, index, ca, rsigner, rkey, ndays)) {
      return kToolExitFailure;
    }
  }
  return kToolExitSuccess;
}
