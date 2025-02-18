// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/x509.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include "internal.h"
#include <ctime>
#include <string>

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kOptionalArgument, "Certificate input, or CSR input file with -req" },
  { "-req", kBooleanArgument, "Input is a CSR file (rather than a certificate)" },
  { "-signkey", kOptionalArgument, "Causes input file to be self signed using supplied private key" },
  { "-out", kOptionalArgument, "Filepath to write all output to, if not set write to stdout" },
  { "-noout", kBooleanArgument, "Prevents output of the encoded version of the certificate" },
  { "-dates", kBooleanArgument, "Print the start and expiry dates of a certificate" },
  { "-modulus", kBooleanArgument, "Prints out value of the modulus of the public key contained in the certificate" },
  { "-subject", kBooleanArgument, "Prints the subject name"},
  { "-subject_hash", kBooleanArgument, "Prints subject hash value"},
  { "-subject_hash_old", kBooleanArgument, "Prints old OpenSSL style (MD5) subject hash value"},
  { "-fingerprint", kBooleanArgument, "Prints the certificate fingerprint"},
  { "-checkend", kOptionalArgument, "Check whether cert expires in the next arg seconds" },
  { "-days", kOptionalArgument, "Number of days until newly generated certificate expires - default 30" },
  { "-text", kBooleanArgument, "Pretty print the contents of the certificate"},
  { "-inform", kOptionalArgument, "This specifies the input format normally the command will expect an X509 "
                                  "certificate but this can change if other options such as -req are present. "
                                  "The DER format is the DER encoding of the certificate and PEM is the base64 "
                                  "encoding of the DER encoding with header and footer lines added. The default "
                                  "format is PEM."},
  { "-enddate", kBooleanArgument, "Prints out the expiry date of the certificate, that is the notAfter date."},
  { "", kOptionalArgument, "" }
};

static bool WriteSignedCertificate(X509 *x509, bssl::UniquePtr<BIO> &output_bio, const std::string &out_path) {
  if (!PEM_write_bio_X509(output_bio.get(), x509)) {
    fprintf(stderr, "Error: error writing certificate to '%s'\n", out_path.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }
  return true;
}

static bool isCharUpperCaseEqual(char a, char b) {
  return ::toupper(a) ==  ::toupper(b);
}

static bool isStringUpperCaseEqual(const std::string &a, const std::string &b) {
  return a.size() == b.size() && std::equal(a.begin(), a.end(), b.begin(), isCharUpperCaseEqual);
}

bool LoadPrivateKeyAndSignCertificate(X509 *x509, const std::string &signkey_path) {
  ScopedFILE signkey_file(fopen(signkey_path.c_str(), "rb"));
  if (!signkey_file) {
    fprintf(stderr, "Error: unable to load private key from '%s'\n", signkey_path.c_str());
    return false;
  }
  bssl::UniquePtr<EVP_PKEY> pkey(PEM_read_PrivateKey(signkey_file.get(), nullptr, nullptr, nullptr));
  if (!pkey) {
    fprintf(stderr, "Error: error reading private key from '%s'\n", signkey_path.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }
  // TODO: make customizable with -digest option
  if (!X509_sign(x509, pkey.get(), EVP_sha256())) {
    fprintf(stderr, "Error: error signing certificate with key from '%s'\n", signkey_path.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }
  return true;
}

bool IsNumeric(const std::string& str) {
  return !str.empty() && std::all_of(str.begin(), str.end(), ::isdigit);
}

// Map arguments using tool/args.cc
bool X509Tool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, out_path, signkey_path, checkend_str, days_str, inform;
  bool noout = false, modulus = false, dates = false, req = false, help = false,
  text = false, subject = false, fingerprint = false, enddate = false,
  subject_hash = false, subject_hash_old = false;
  std::unique_ptr<unsigned> checkend, days;

  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&in_path, "-in", "", parsed_args);
  GetBoolArgument(&req, "-req", parsed_args);
  GetString(&signkey_path, "-signkey", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetBoolArgument(&noout, "-noout", parsed_args);
  GetBoolArgument(&dates, "-dates", parsed_args);
  GetBoolArgument(&modulus, "-modulus", parsed_args);
  GetBoolArgument(&subject, "-subject", parsed_args);
  GetBoolArgument(&subject_hash, "-subject_hash", parsed_args);
  GetBoolArgument(&subject_hash_old, "-subject_hash_old", parsed_args);
  GetBoolArgument(&fingerprint, "-fingerprint", parsed_args);
  GetBoolArgument(&text, "-text", parsed_args);
  GetString(&inform, "-inform", "", parsed_args);
  GetBoolArgument(&enddate, "-enddate", parsed_args);

  // Display x509 tool option summary
  if (help) {
    PrintUsage(kArguments);
    return false;
  }
  bssl::UniquePtr<BIO> output_bio;
  if (out_path.empty()) {
    output_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    output_bio.reset(BIO_new(BIO_s_file()));
    BIO_write_filename(output_bio.get(), out_path.c_str());
  }

  // -req must include -signkey
  if (req && signkey_path.empty()) {
    fprintf(stderr, "Error: '-req' option must be used with '-signkey' option\n");
    return false;
  }

  // Check for mutually exclusive options
  if (req && (dates || parsed_args.count("-checkend"))){
    fprintf(stderr, "Error: '-req' option cannot be used with '-dates' and '-checkend' options\n");
    return false;
  }
  if (!signkey_path.empty() && (dates || parsed_args.count("-checkend"))){
    fprintf(stderr, "Error: '-signkey' option cannot be used with '-dates' and '-checkend' options\n");
    return false;
  }
  if (parsed_args.count("-days") && (dates || parsed_args.count("-checkend"))){
    fprintf(stderr, "Error: '-days' option cannot be used with '-dates' and '-checkend' options\n");
    return false;
  }

  // Check that -checkend argument is valid, int >=0
  if (parsed_args.count("-checkend")) {
    checkend_str = parsed_args["-checkend"];
    if (!IsNumeric(checkend_str)) {
      fprintf(stderr, "Error: '-checkend' option must include a non-negative integer\n");
      return false;
    }
    checkend.reset(new unsigned(std::stoul(checkend_str)));
  }

  // Check that -days argument is valid, int > 0
  if (parsed_args.count("-days")) {
    days_str = parsed_args["-days"];
    if (!IsNumeric(days_str) || std::stoul(days_str) == 0) {
      fprintf(stderr, "Error: '-days' option must include a positive integer\n");
      return false;
    }
    days.reset(new unsigned(std::stoul(days_str)));
  }

  // Check -inform has a valid value
  if(!inform.empty()) {
    if (!isStringUpperCaseEqual(inform, "DER") && !isStringUpperCaseEqual(inform, "PEM")) {
      fprintf(stderr, "Error: '-inform' option must specify a valid encoding DER|PEM\n");
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
      fprintf(stderr, "Error: unable to load certificate from '%s'\n", in_path.c_str());
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
    if (!X509_set_subject_name(x509.get(), X509_REQ_get_subject_name(csr.get()))) {
      fprintf(stderr, "Error: unable to set subject name from CSR\n");
      return false;
    }

    // Set the public key from CSR
    bssl::UniquePtr<EVP_PKEY> csr_pkey(X509_REQ_get_pubkey(csr.get()));
    if (!csr_pkey || !X509_set_pubkey(x509.get(), csr_pkey.get())) {
      fprintf(stderr, "Error: unable to set public key from CSR\n");
      return false;
    }

    // Set issuer name
    if (!X509_set_issuer_name(x509.get(), X509_REQ_get_subject_name(csr.get()))) {
      fprintf(stderr, "Error: unable to set issuer name\n");
      return false;
    }

    // Set validity period, default 30 days if not specified
    unsigned valid_days = days ? *days : 30;
    if (!X509_gmtime_adj(X509_getm_notBefore(x509.get()), 0) ||
        !X509_gmtime_adj(X509_getm_notAfter(x509.get()), 60 * 60 * 24 * valid_days)) {
      fprintf(stderr, "Error: unable to set validity period\n");
      return false;
    }

    // Sign the certificate with the provided key
    if (!signkey_path.empty()) {
      if (!LoadPrivateKeyAndSignCertificate(x509.get(), signkey_path)) {
        return false;
      }
    }

    if (!WriteSignedCertificate(x509.get(), output_bio, out_path)) {
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
      fprintf(stderr, "Error: error parsing certificate from '%s'\n", in_path.c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }

    if (modulus) {
      bssl::UniquePtr<EVP_PKEY> pkey(X509_get_pubkey(x509.get()));
      if (!pkey) {
        fprintf(stderr, "Error: unable to load public key from certificate\n");
        return false;
      }

      if (EVP_PKEY_base_id(pkey.get()) == EVP_PKEY_RSA) {
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
        BIO_printf(output_bio.get(), "Modulus=%s\n", hex_modulus);

        OPENSSL_free(hex_modulus);
      } else {
        fprintf(stderr, "Error: public key is not an RSA key\n");
        return false;
      }
    }

    if(text) {
      X509_print(output_bio.get(), x509.get());
    }

    if (subject) {
      X509_NAME *subject_name = X509_get_subject_name(x509.get());
      if (!subject_name) {
        fprintf(stderr, "Error: unable to obtain subject from certificate\n");
        return false;
      }

      BIO_printf(output_bio.get(), "subject=");
      X509_NAME_print_ex(output_bio.get(), subject_name, 0, XN_FLAG_ONELINE);
      BIO_printf(output_bio.get(), "\n");
    }

    if (fingerprint) {
      unsigned int out_len;
      unsigned char md[EVP_MAX_MD_SIZE];
      const EVP_MD *digest = EVP_sha1();

      if (!X509_digest(x509.get(), digest, md, &out_len)) {
        fprintf(stderr, "Error: unable to obtain digest\n");
        return false;
      }
      BIO_printf(output_bio.get(), "%s Fingerprint=",
                 OBJ_nid2sn(EVP_MD_type(digest)));
      for (int j = 0; j < (int)out_len; j++) {
        BIO_printf(output_bio.get(), "%02X%c", md[j], (j + 1 == (int)out_len)
                                                      ? '\n' : ':');
      }
    }

    if (subject_hash) {
      BIO_printf(output_bio.get(), "%08x\n", X509_subject_name_hash(x509.get()));
    }

    if(subject_hash_old) {
      BIO_printf(output_bio.get(), "%08x\n", X509_subject_name_hash_old(x509.get()));
    }

    if (dates) {
      BIO_printf(output_bio.get(), "notBefore=");
      ASN1_TIME_print(output_bio.get(), X509_get_notBefore(x509.get()));
      BIO_printf(output_bio.get(), "\n");

      BIO_printf(output_bio.get(), "notAfter=");
      ASN1_TIME_print(output_bio.get(), X509_get_notAfter(x509.get()));
      BIO_printf(output_bio.get(), "\n");
    }

    if (!dates && enddate) {
      BIO_printf(output_bio.get(), "notAfter=");
      ASN1_TIME_print(output_bio.get(), X509_get_notAfter(x509.get()));
      BIO_printf(output_bio.get(), "\n");
    }

    if (checkend) {
      bssl::UniquePtr<ASN1_TIME> current_time(ASN1_TIME_set(nullptr, std::time(nullptr)));
      ASN1_TIME *end_time = X509_getm_notAfter(x509.get());
      int days_left, seconds_left;
      if (!ASN1_TIME_diff(&days_left, &seconds_left, current_time.get(), end_time)) {
        fprintf(stderr, "Error: failed to calculate time difference\n");
        return false;
      }

      if ((days_left * 86400 + seconds_left) < static_cast<int>(*checkend)) {
        BIO_printf(output_bio.get(), "Certificate will expire\n");
      } else {
        BIO_printf(output_bio.get(), "Certificate will not expire\n");
      }
    }

    if (!signkey_path.empty()) {
      if (!LoadPrivateKeyAndSignCertificate(x509.get(), signkey_path)) {
        return false;
      }
    }

    if (!noout && !checkend) {
      if (!WriteSignedCertificate(x509.get(), output_bio, out_path)) {
        return false;
      }
    }
  }
  return true;
}
