// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>
#include <algorithm>
#include <ctime>
#include <iostream>
#include <string>
#include "internal.h"

static const argument_t kArguments[] = {
    // General options
    {"-help", kBooleanArgument, "Display option summary"},
    {"-in", kOptionalArgument,
     "Certificate input, or CSR input file with -req"},
    {"-req", kBooleanArgument,
     "Input is a CSR file (rather than a certificate)"},
    {"-signkey", kOptionalArgument,
     "Causes input file to be self signed using supplied private key"},
    {"-inform", kOptionalArgument,
     "This specifies the input format normally the command will expect an X509 "
     "certificate but this can change if other options such as -req are "
     "present. "
     "The DER format is the DER encoding of the certificate and PEM is the "
     "base64 "
     "encoding of the DER encoding with header and footer lines added. The "
     "default "
     "format is PEM."},
    {"-out", kOptionalArgument,
     "Filepath to write all output to, if not set write to stdout"},
    {"-outform", kOptionalArgument, "Output format (DER or PEM) - default PEM"},
    // Micro-CA
    {"-CA", kOptionalArgument,
     "Use the given CA certificate to sign certificates. Cannot be used with "
     "-signkey"},
    {"-CAkey", kOptionalArgument,
     "The corresponding CA key. If not specified, the private key is assumed "
     "to be in the CA file"},
    // Certificate printing
    {"-noout", kBooleanArgument,
     "Prevents output of the encoded version of the certificate"},
    {"-dates", kBooleanArgument,
     "Print the start and expiry dates of a certificate"},
    {"-modulus", kBooleanArgument,
     "Prints out value of the modulus of the public key contained in the "
     "certificate"},
    {"-subject", kBooleanArgument, "Prints the subject name"},
    {"-subject_hash", kBooleanArgument, "Prints subject hash value"},
    {"-subject_hash_old", kBooleanArgument,
     "Prints old OpenSSL style (MD5) subject hash value"},
    {"-fingerprint", kBooleanArgument, "Prints the certificate fingerprint"},
    {"-pubkey", kBooleanArgument, "Print the public key in PEM format"},
    {"-text", kBooleanArgument, "Pretty print the contents of the certificate"},
    {"-enddate", kBooleanArgument,
     "Prints out the expiry date of the certificate, that is the notAfter "
     "date."},
    // Certificate checking
    {"-checkend", kOptionalArgument,
     "Check whether cert expires in the next arg seconds"},
    // Certificate output
    {"-days", kOptionalArgument,
     "Number of days until newly generated certificate expires - default 30"},
    {"-extfile", kOptionalArgument,
     "Config file with X509V3 extensions to add"},
    {"-extensions", kOptionalArgument,
     "Section of extfile to use - default: unnamed section"},
    {"", kOptionalArgument, ""}};

static bool WriteSignedCertificate(X509 *x509, bssl::UniquePtr<BIO> &output_bio,
                                   const std::string &out_path,
                                   const std::string &outform) {
  if (!outform.empty() && isStringUpperCaseEqual(outform, "DER")) {
    if (!i2d_X509_bio(output_bio.get(), x509)) {
      fprintf(stderr, "Error: error writing certificate to '%s'\n",
              out_path.c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }
  } else {
    if (!PEM_write_bio_X509(output_bio.get(), x509)) {
      fprintf(stderr, "Error: error writing certificate to '%s'\n",
              out_path.c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }
  }

  return true;
}

static bool isCharUpperCaseEqual(char a, char b) {
  return ::toupper(a) == ::toupper(b);
}

bool isStringUpperCaseEqual(const std::string &a, const std::string &b) {
  return a.size() == b.size() &&
         std::equal(a.begin(), a.end(), b.begin(), isCharUpperCaseEqual);
}

static int AdaptExtension(X509 *cert, X509V3_CTX *ext_ctx, const char *name,
                          const char *value, int add_default) {
  bssl::UniquePtr<X509_EXTENSION> new_ext(
      X509V3_EXT_nconf(NULL, ext_ctx, name, value));

  if (new_ext == NULL) {
    return 0;
  }

  const ASN1_OBJECT *ext_obj = X509_EXTENSION_get_object(new_ext.get());
  if (ext_obj == NULL) {
    return 0;
  }

  int idx = X509_get_ext_by_OBJ(cert, ext_obj, -1);
  if (idx >= 0) {
    X509_EXTENSION *found_ext = X509_get_ext(cert, idx);
    if (ASN1_STRING_length(X509_EXTENSION_get_data(found_ext)) <= 2) {
      X509_delete_ext(cert, idx);
    }
    return 1;
  }

  return !add_default || X509_add_ext(cert, new_ext.get(), -1);
}

static bool LoadExtensionsAndSignCertificate(const X509 *issuer, X509 *subject,
                                             EVP_PKEY *pkey,
                                             const std::string pkey_path,
                                             const std::string &ext_file_path,
                                             std::string &ext_section) {
  X509V3_CTX ext_ctx;
  bssl::UniquePtr<CONF> ext_conf(nullptr);

  X509V3_set_ctx(&ext_ctx, issuer, subject, NULL, NULL, X509V3_CTX_REPLACE);

  if (ext_file_path.empty()) {
    if (!ext_section.empty()) {
      fprintf(stderr,
              "Warning: ignoring -extensions option without -extfile\n");
    }
  } else {
    X509V3_CTX temp_ctx;
    bssl::UniquePtr<BIO> ext_bio(BIO_new_file(ext_file_path.c_str(), "r"));
    if (!ext_bio) {
      fprintf(stderr, "Error: unable to load extension file from '%s'\n",
              ext_file_path.c_str());
      return false;
    }

    ext_conf.reset(NCONF_new(NULL));
    if (!ext_conf) {
      fprintf(stderr, "Failed to create extension config\n");
      return false;
    }

    if (NCONF_load_bio(ext_conf.get(), ext_bio.get(), NULL) <= 0) {
      fprintf(stderr, "Error: Failed to load config from BIO\n");
      return false;
    }

    if (ext_section.empty()) {
      const char *res =
          NCONF_get_string(ext_conf.get(), "default", "extensions");
      ext_section = res ? res : "default";
    }

    // validate extension config
    X509V3_set_ctx_test(&temp_ctx);
    X509V3_set_nconf(&temp_ctx, ext_conf.get());
    if (!X509V3_EXT_add_nconf(ext_conf.get(), &temp_ctx, ext_section.c_str(),
                              NULL)) {
      fprintf(stderr, "Error: Failed to check extension section\n");
      return false;
    }

    // initialize actual extension context
    X509V3_set_nconf(&ext_ctx, ext_conf.get());

    if (!X509V3_EXT_add_nconf(ext_conf.get(), &ext_ctx, ext_section.c_str(),
                              subject)) {
      fprintf(stderr, "Error: Failed to add extensions from section %s\n",
              ext_section.c_str());
      return false;
    }
  }

  if (!X509_set_version(subject, X509_VERSION_3)) {
    fprintf(stderr, "Error: unable to set certificate version\n");
    return false;
  }

  /* Prevent X509_V_ERR_MISSING_SUBJECT_KEY_IDENTIFIER */
  if (!AdaptExtension(subject, &ext_ctx, "subjectKeyIdentifier", "hash", 1)) {
    fprintf(stderr, "Error: Failed to handle subject key identifier\n");
    return false;
  }
  /* Prevent X509_V_ERR_MISSING_AUTHORITY_KEY_IDENTIFIER */
  int self_sign = X509_check_private_key(subject, pkey);
  if (!AdaptExtension(subject, &ext_ctx, "authorityKeyIdentifier",
                      "keyid, issuer", !self_sign)) {
    fprintf(stderr, "Error: Failed to handle authority key identifier\n");
    return false;
  }

  // TODO: make customizable with -digest option
  if (!X509_sign(subject, pkey, EVP_sha256())) {
    fprintf(stderr, "Error: error signing certificate with key from '%s'\n",
            pkey_path.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }

  return true;
}

static bool LoadPrivateKey(bssl::UniquePtr<EVP_PKEY> &pkey,
                           const std::string &signkey_path) {
  ScopedFILE signkey_file(fopen(signkey_path.c_str(), "rb"));
  if (!signkey_file) {
    fprintf(stderr, "Error: unable to load private key from '%s'\n",
            signkey_path.c_str());
    return false;
  }
  pkey.reset(
      PEM_read_PrivateKey(signkey_file.get(), nullptr, nullptr, nullptr));
  if (!pkey) {
    fprintf(stderr, "Error: error reading private key from '%s'\n",
            signkey_path.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }

  return true;
}

static bool LoadCA(bssl::UniquePtr<X509> &ca, bssl::UniquePtr<EVP_PKEY> &ca_key,
                   const std::string &ca_file_path,
                   const std::string &ca_key_path) {
  ScopedFILE ca_file(fopen(ca_file_path.c_str(), "rb"));

  if (!ca_file) {
    fprintf(stderr, "Error: ");
    return false;
  }

  ca.reset(PEM_read_X509(ca_file.get(), nullptr, nullptr,
                         nullptr));  // TODO: add password obtained from -passin

  if (!ca) {
    fprintf(stderr, "Error: ");
    return false;
  }

  if (!ca_key_path.empty()) {
    ScopedFILE ca_key_file(fopen(ca_key_path.c_str(), "rb"));

    if (!ca_key_file) {
      fprintf(stderr, "Error: ");
      return false;
    }

    ca_key.reset(
        PEM_read_PrivateKey(ca_key_file.get(), nullptr, nullptr, nullptr));
  } else {
    ca_key.reset(PEM_read_PrivateKey(ca_file.get(), nullptr, nullptr, nullptr));
  }

  if (!ca_key) {
    fprintf(stderr, "Error: ");
    return false;
  }

  // Do validation
  if (!X509_check_private_key(ca.get(), ca_key.get())) {
    fprintf(stderr,
            "Error: CA certificate and CA private key does not match\n");
    return false;
  }

  return true;
}

bool IsNumeric(const std::string &str) {
  return !str.empty() && std::all_of(str.begin(), str.end(), ::isdigit);
}

static bool handleModulus(X509 *x509, BIO *output_bio) {
  bssl::UniquePtr<EVP_PKEY> pkey(X509_get_pubkey(x509));
  if (!pkey) {
    fprintf(stderr, "Error: unable to load public key from certificate\n");
    return false;
  }

  if (EVP_PKEY_base_id(pkey.get()) != EVP_PKEY_RSA) {
    fprintf(stderr, "Error: public key is not an RSA key\n");
    return false;
  }

  const RSA *rsa = EVP_PKEY_get0_RSA(pkey.get());
  if (!rsa) {
    fprintf(stderr, "Error: unable to load RSA key\n");
    return false;
  }

  const BIGNUM *n = RSA_get0_n(rsa);
  if (!n) {
    fprintf(stderr, "Error: unable to load modulus\n");
    return false;
  }

  char *hex_modulus = BN_bn2hex(n);
  if (!hex_modulus) {
    fprintf(stderr, "Error: unable to convert modulus to hex\n");
    return false;
  }

  for (char *p = hex_modulus; *p; ++p) {
    *p = toupper(*p);
  }
  BIO_printf(output_bio, "Modulus=%s\n", hex_modulus);
  OPENSSL_free(hex_modulus);
  return true;
}

static bool handlePubkey(X509 *x509, BIO *output_bio) {
  bssl::UniquePtr<EVP_PKEY> pkey(X509_get_pubkey(x509));

  if (!pkey) {
    fprintf(stderr, "Error: unable to load public key from certificate\n");
    return false;
  }

  if (!PEM_write_bio_PUBKEY(output_bio, pkey.get())) {
    fprintf(stderr, "Error: failed to write public key in PEM format\n");
    return false;
  }
  return true;
}

static bool handleSubject(X509 *x509, BIO *output_bio) {
  X509_NAME *subject_name = X509_get_subject_name(x509);
  if (!subject_name) {
    fprintf(stderr, "Error: unable to obtain subject from certificate\n");
    return false;
  }
  BIO_printf(output_bio, "subject=");
  X509_NAME_print_ex(output_bio, subject_name, 0, XN_FLAG_ONELINE);
  BIO_printf(output_bio, "\n");
  return true;
}

static bool handleFingerprint(X509 *x509, BIO *output_bio) {
  unsigned int out_len = 0;
  unsigned char md[EVP_MAX_MD_SIZE];
  const EVP_MD *digest = EVP_sha1();

  if (!X509_digest(x509, digest, md, &out_len)) {
    fprintf(stderr, "Error: unable to obtain digest\n");
    return false;
  }

  BIO_printf(output_bio, "%s Fingerprint=", OBJ_nid2sn(EVP_MD_type(digest)));
  for (int j = 0; j < (int)out_len; j++) {
    BIO_printf(output_bio, "%02X%c", md[j],
               (j + 1 == (int)out_len) ? '\n' : ':');
  }
  return true;
}

static bool handleDates(X509 *x509, BIO *output_bio) {
  BIO_printf(output_bio, "notBefore=");
  ASN1_TIME_print(output_bio, X509_get_notBefore(x509));
  BIO_printf(output_bio, "\n");
  BIO_printf(output_bio, "notAfter=");
  ASN1_TIME_print(output_bio, X509_get_notAfter(x509));
  BIO_printf(output_bio, "\n");
  return true;
}

static bool handleCheckend(X509 *x509, BIO *output_bio,
                           const std::string &arg_value) {
  if (!IsNumeric(arg_value)) {
    fprintf(stderr,
            "Error: '-checkend' option must include a non-negative integer\n");
    return false;
  }

  unsigned checkend_val = std::stoul(arg_value);
  bssl::UniquePtr<ASN1_TIME> current_time(
      ASN1_TIME_set(nullptr, std::time(nullptr)));
  ASN1_TIME *end_time = X509_getm_notAfter(x509);
  int days_left = 0, seconds_left = 0;

  if (!ASN1_TIME_diff(&days_left, &seconds_left, current_time.get(),
                      end_time)) {
    fprintf(stderr, "Error: failed to calculate time difference\n");
    return false;
  }

  BIO_printf(output_bio, "%s\n",
             (days_left * 86400 + seconds_left) < static_cast<int>(checkend_val)
                 ? "Certificate will expire"
                 : "Certificate will not expire");
  return true;
}

static bool ProcessArgument(const std::string &arg_name,
                            const std::string &arg_value, X509 *x509,
                            bssl::UniquePtr<BIO> &output_bio,
                            bool *dates_processed) {
  if (arg_name == "-modulus") {
    return handleModulus(x509, output_bio.get());
  }
  if (arg_name == "-pubkey") {
    return handlePubkey(x509, output_bio.get());
  }
  if (arg_name == "-text") {
    X509_print(output_bio.get(), x509);
    return true;
  }
  if (arg_name == "-subject") {
    return handleSubject(x509, output_bio.get());
  }
  if (arg_name == "-subject_hash") {
    const uint32_t hash_value = X509_subject_name_hash(x509);
    BIO_printf(output_bio.get(), "%08x\n", hash_value);
    return true;
  }
  if (arg_name == "-subject_hash_old") {
    const uint32_t hash_value = X509_subject_name_hash_old(x509);
    BIO_printf(output_bio.get(), "%08x\n", hash_value);
    return true;
  }
  if (arg_name == "-fingerprint") {
    return handleFingerprint(x509, output_bio.get());
  }
  if (arg_name == "-dates") {
    *dates_processed = true;
    return handleDates(x509, output_bio.get());
  }
  if (arg_name == "-enddate" && !*dates_processed) {
    BIO_printf(output_bio.get(), "notAfter=");
    ASN1_TIME_print(output_bio.get(), X509_get_notAfter(x509));
    BIO_printf(output_bio.get(), "\n");
    return true;
  }
  if (arg_name == "-checkend") {
    return handleCheckend(x509, output_bio.get(), arg_value);
  }
  return true;
}

// Map arguments using tool/args.cc
bool X509Tool(const args_list_t &args) {
  // Use the ordered argument list instead of the standard map
  ordered_args::ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ordered_args::ParseOrderedKeyValueArguments(parsed_args, extra_args,
                                                   args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, out_path, signkey_path, days_str, inform, outform,
      ca_file_path, ca_key_path, ext_file_path, ext_section;
  bool noout = false, dates = false, req = false, help = false;
  std::unique_ptr<unsigned> days;

  ordered_args::GetBoolArgument(&help, "-help", parsed_args);
  ordered_args::GetString(&in_path, "-in", "", parsed_args);
  ordered_args::GetBoolArgument(&req, "-req", parsed_args);
  ordered_args::GetString(&signkey_path, "-signkey", "", parsed_args);
  ordered_args::GetString(&out_path, "-out", "", parsed_args);
  ordered_args::GetBoolArgument(&noout, "-noout", parsed_args);
  ordered_args::GetBoolArgument(&dates, "-dates", parsed_args);
  ordered_args::GetString(&inform, "-inform", "", parsed_args);
  ordered_args::GetString(&outform, "-outform", "", parsed_args);
  ordered_args::GetString(&ca_file_path, "-CA", "", parsed_args);
  ordered_args::GetString(&ca_key_path, "-CAkey", "", parsed_args);
  ordered_args::GetString(&ext_file_path, "-extfile", "", parsed_args);
  ordered_args::GetString(&ext_section, "-extensions", "", parsed_args);

  // Display x509 tool option summary
  if (help) {
    PrintUsage(kArguments);
    return true;
  }
  bssl::UniquePtr<BIO> output_bio;
  if (out_path.empty()) {
    output_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    output_bio.reset(BIO_new(BIO_s_file()));
    if (1 != BIO_write_filename(output_bio.get(), out_path.c_str())) {
      fprintf(stderr, "Error: unable to write to '%s'\n", out_path.c_str());
      return false;
    }
  }

  // -req must include a private key
  if (req && signkey_path.empty() && ca_file_path.empty()) {
    fprintf(
        stderr,
        "Error: '-req' option must be used with '-signkey' or '-CA' option\n");
    return false;
  }

  // -CAkey must include -CA
  if (!ca_key_path.empty() && ca_file_path.empty()) {
    fprintf(stderr, "Error: '-CAkey' option must be used with '-CA' option\n");
    return false;
  }

  // Check for mutually exclusive options
  if (req && (dates || ordered_args::HasArgument(parsed_args, "-checkend"))) {
    fprintf(stderr,
            "Error: '-req' option cannot be used with '-dates' and '-checkend' "
            "options\n");
    return false;
  }
  if (!signkey_path.empty() &&
      (dates || ordered_args::HasArgument(parsed_args, "-checkend"))) {
    fprintf(stderr,
            "Error: '-signkey' option cannot be used with '-dates' and "
            "'-checkend' options\n");
    return false;
  }
  if (!signkey_path.empty() &&
      (!ca_file_path.empty() || !ca_key_path.empty())) {
    fprintf(stderr,
            "Error: '-signkey' option cannot be used with '-CA' and "
            "'-CAkey'options\n");
    return false;
  }
  if (ordered_args::HasArgument(parsed_args, "-days") &&
      (dates || ordered_args::HasArgument(parsed_args, "-checkend"))) {
    fprintf(stderr,
            "Error: '-days' option cannot be used with '-dates' and "
            "'-checkend' options\n");
    return false;
  }

  // Check that -days argument is valid, int > 0
  if (ordered_args::HasArgument(parsed_args, "-days")) {
    ordered_args::GetString(&days_str, "-days", "", parsed_args);
    if (!IsNumeric(days_str) || std::stoul(days_str) == 0) {
      fprintf(stderr,
              "Error: '-days' option must include a positive integer\n");
      return false;
    }
    days.reset(new unsigned(std::stoul(days_str)));
  }

  // Check -inform has a valid value
  if (!inform.empty()) {
    if (!isStringUpperCaseEqual(inform, "DER") &&
        !isStringUpperCaseEqual(inform, "PEM")) {
      fprintf(
          stderr,
          "Error: '-inform' option must specify a valid encoding DER|PEM\n");
      return false;
    }
  }

  // Check -outform has a valid value
  if (!outform.empty()) {
    if (!isStringUpperCaseEqual(outform, "DER") &&
        !isStringUpperCaseEqual(outform, "PEM")) {
      fprintf(
          stderr,
          "Error: '-outform' option must specify a valid encoding DER|PEM\n");
      return false;
    }
  }

  // Read from stdin if no -in path provided
  ScopedFILE in_file;
  if (in_path.empty()) {
    in_file.reset(stdin);
  } else {
    in_file.reset(fopen(in_path.c_str(), "rb"));
    if (!in_file) {
      fprintf(stderr, "Error: unable to load certificate from '%s'\n",
              in_path.c_str());
      return false;
    }
  }

  // Load CA and CA key
  bssl::UniquePtr<X509> ca;
  bssl::UniquePtr<EVP_PKEY> pkey;
  if (!ca_file_path.empty()) {
    if (!LoadCA(ca, pkey, ca_file_path, ca_key_path)) {
      return false;
    }
  } else if (!signkey_path.empty()) {
    if (!LoadPrivateKey(pkey, signkey_path)) {
      return false;
    }
  }

  if (req) {
    bssl::UniquePtr<X509_REQ> csr;
    if (!inform.empty() && isStringUpperCaseEqual(inform, "DER")) {
      csr.reset(d2i_X509_REQ_fp(in_file.get(), nullptr));
    } else {
      csr.reset(PEM_read_X509_REQ(in_file.get(), nullptr, nullptr, nullptr));
    }

    if (!csr) {
      fprintf(stderr, "Error: error parsing CSR from '%s'\n", in_path.c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }

    // Create and sign certificate based on CSR
    bssl::UniquePtr<X509> x509(X509_new());
    if (!x509) {
      fprintf(stderr, "Error: unable to create new X509 certificate\n");
      return false;
    }

    // Set the subject from CSR
    if (!X509_set_subject_name(x509.get(),
                               X509_REQ_get_subject_name(csr.get()))) {
      fprintf(stderr, "Error: unable to set subject name from CSR\n");
      return false;
    }

    // Set the public key from CSR
    bssl::UniquePtr<EVP_PKEY> csr_pkey(X509_REQ_get_pubkey(csr.get()));
    if ((!signkey_path.empty() && !csr_pkey) ||
        !X509_set_pubkey(x509.get(),
                         !signkey_path.empty() ? pkey.get() : csr_pkey.get())) {
      fprintf(stderr,
              "Error: unable to set public key from either CSR or a provided "
              "key\n");
      return false;
    }

    // Set issuer name
    X509_NAME *issuer = ca_file_path.empty()
                            ? X509_REQ_get_subject_name(csr.get())
                            : X509_get_subject_name(ca.get());

    if (!X509_set_issuer_name(x509.get(), issuer)) {
      fprintf(stderr, "Error: unable to set issuer name\n");
      return false;
    }

    // Set validity period, default 30 days if not specified
    unsigned valid_days = days ? *days : 30;
    if (!X509_gmtime_adj(X509_getm_notBefore(x509.get()), 0) ||
        !X509_gmtime_adj(X509_getm_notAfter(x509.get()),
                         60 * 60 * 24 * valid_days)) {
      fprintf(stderr, "Error: unable to set validity period\n");
      return false;
    }

    // Sign the certificate with the provided key
    if (!ca_file_path.empty()) {
      if (!LoadExtensionsAndSignCertificate(ca.get(), x509.get(), pkey.get(),
                                            ca_file_path, ext_file_path,
                                            ext_section)) {
        return false;
      }
    } else if (!signkey_path.empty()) {
      if (!LoadExtensionsAndSignCertificate(x509.get(), x509.get(), pkey.get(),
                                            signkey_path, ext_file_path,
                                            ext_section)) {
        return false;
      }
    }

    if (!WriteSignedCertificate(x509.get(), output_bio, out_path, outform)) {
      return false;
    }
  } else {
    // Parse x509 certificate from input file
    bssl::UniquePtr<X509> x509;
    if (!inform.empty() && isStringUpperCaseEqual(inform, "DER")) {
      x509.reset(d2i_X509_fp(in_file.get(), nullptr));
    } else {
      x509.reset(PEM_read_X509(in_file.get(), nullptr, nullptr, nullptr));
    }

    if (!x509) {
      fprintf(stderr, "Error: error parsing certificate from '%s'\n",
              in_path.c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }

    if (!signkey_path.empty() && !X509_set_pubkey(x509.get(), pkey.get())) {
      fprintf(stderr, "Error: unable to set public key using a provided key\n");
      return false;
    }

    if (!ca_file_path.empty()) {
      if (!X509_set_issuer_name(x509.get(), X509_get_subject_name(ca.get()))) {
        fprintf(stderr, "Error: unable to set issuer name\n");
        return false;
      }
    }

    // Sign the certificate with the provided key
    if (!ca_file_path.empty()) {
      if (!LoadExtensionsAndSignCertificate(ca.get(), x509.get(), pkey.get(),
                                            ca_file_path, ext_file_path,
                                            ext_section)) {
        return false;
      }
    } else if (!signkey_path.empty()) {
      if (!LoadExtensionsAndSignCertificate(x509.get(), x509.get(), pkey.get(),
                                            signkey_path, ext_file_path,
                                            ext_section)) {
        return false;
      }
    }

    // Process arguments in the order they were provided
    bool dates_processed = false;
    for (const auto &arg_pair : parsed_args) {
      const std::string &arg_name = arg_pair.first;
      const std::string &arg_value = arg_pair.second;

      // Skip non-output arguments
      if (arg_name == "-in" || arg_name == "-out" || arg_name == "-inform" ||
          arg_name == "-signkey" || arg_name == "-days" || arg_name == "-req" ||
          arg_name == "-noout" || arg_name == "-help" || arg_name == "-CA" ||
          arg_name == "-CAkey") {
        continue;
      }

      if (!ProcessArgument(arg_name, arg_value, x509.get(), output_bio,
                           &dates_processed)) {
        return false;
      }
    }

    if (!noout && !ordered_args::HasArgument(parsed_args, "-checkend")) {
      if (!WriteSignedCertificate(x509.get(), output_bio, out_path, outform)) {
        return false;
      }
    }
  }
  return true;
}
