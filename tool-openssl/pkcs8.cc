// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/bytestring.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/pkcs8.h>
#include <cstring>
#include <string>
#include <unordered_set>
#include "internal.h"

// Maximum size for crypto files to prevent loading excessively large files
// (1MB)
static constexpr long DEFAULT_MAX_CRYPTO_FILE_SIZE = 1024 * 1024;

// Checks if BIO size is within allowed limits
static bool validate_bio_size(BIO &bio,
                              long max_size = DEFAULT_MAX_CRYPTO_FILE_SIZE) {
  const long current_pos = BIO_tell(&bio);
  if (current_pos < 0) {
    return false;
  }
  if (BIO_seek(&bio, 0) < 0) {
    return false;
  }
  long size = 0;
  char buffer[4096] = {};
  int bytes_read = 0;
  while ((bytes_read = BIO_read(&bio, buffer, sizeof(buffer))) > 0) {
    size += bytes_read;
    if (size > max_size) {
      BIO_seek(&bio, current_pos);
      fprintf(stderr, "File exceeds maximum allowed size\n");
      return false;
    }
  }
  if (BIO_seek(&bio, current_pos) < 0) {
    return false;
  }
  return true;
}

// Validates input/output format is PEM or DER
static bool validate_format(const std::string &format) {
  if (format != "PEM" && format != "DER") {
    fprintf(stderr, "Format must be PEM or DER\n");
    return false;
  }
  return true;
}

// Supported cipher algorithms for key encryption
static const std::unordered_set<std::string> kSupportedCiphers = {
    "aes-128-cbc", "aes-192-cbc", "aes-256-cbc", "des-ede3-cbc", "des-cbc"};

// Checks if the cipher name is supported and can be initialized
static bool validate_cipher(const std::string &cipher_name) {
  if (kSupportedCiphers.find(cipher_name) == kSupportedCiphers.end()) {
    fprintf(stderr, "Unsupported cipher algorithm\n");
    return false;
  }
  const EVP_CIPHER *cipher = EVP_get_cipherbyname(cipher_name.c_str());
  if (!cipher) {
    fprintf(stderr, "Cannot initialize cipher\n");
    return false;
  }

  return true;
}

// Supported PRF algorithms for PKCS#5 v2.0
static const std::unordered_set<std::string> kSupportedPRFs = {
    "hmacWithSHA1"  // Currently the only supported PRF in AWS-LC
};

// Checks if the PRF algorithm name is supported
static bool validate_prf(const std::string &prf_name) {
  if (kSupportedPRFs.find(prf_name) == kSupportedPRFs.end()) {
    fprintf(stderr, "Only hmacWithSHA1 PRF is supported\n");
    return false;
  }
  return true;
}

// Reads a private key from BIO in DER format with optional password
static bssl::UniquePtr<EVP_PKEY> read_private_der(BIO *in_bio, const char *passin) {
  if (!in_bio) {
    return nullptr;
  }

  BIO_reset(in_bio);
  
  if (passin) {
    // Try encrypted PKCS8 DER
    return bssl::UniquePtr<EVP_PKEY>(
        d2i_PKCS8PrivateKey_bio(in_bio, nullptr, nullptr, const_cast<char *>(passin)));
  }
  
  // Try unencrypted DER formats in order of preference
  // 1. Try unencrypted PKCS8 DER
  bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(d2i_PKCS8_PRIV_KEY_INFO_bio(in_bio, nullptr));
  if (p8inf) {
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKCS82PKEY(p8inf.get()));
    if (pkey) {
      return pkey;
    }
  }
  
  // 2. Fall back to traditional DER (auto-detect RSA/DSA/EC)
  BIO_reset(in_bio);
  return bssl::UniquePtr<EVP_PKEY>(d2i_PrivateKey_bio(in_bio, nullptr));
}

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-in", kOptionalArgument, "Input file"},
    {"-out", kOptionalArgument, "Output file"},
    {"-inform", kOptionalArgument, "Input format (DER or PEM)"},
    {"-outform", kOptionalArgument, "Output format (DER or PEM)"},
    {"-topk8", kBooleanArgument, "Convert traditional format to PKCS#8"},
    {"-nocrypt", kBooleanArgument, "Use unencrypted private key"},
    {"-v2", kOptionalArgument, "Use PKCS#5 v2.0 and specified cipher"},
    {"-v2prf", kOptionalArgument,
     "Use specified PRF algorithm with PKCS#5 v2.0"},
    {"-passin", kOptionalArgument, "Input file passphrase source"},
    {"-passout", kOptionalArgument, "Output file passphrase source"},
    {"", kOptionalArgument, ""}};

bool pkcs8Tool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  bool help = false;
  std::string in_path, out_path;
  std::string inform = "PEM", outform = "PEM";
  bool topk8 = false, nocrypt = false;

  // Sensitive strings will be automatically cleared on function exit
  bssl::UniquePtr<std::string> passin_arg(new std::string());
  bssl::UniquePtr<std::string> passout_arg(new std::string());

  bssl::UniquePtr<BIO> in;
  bssl::UniquePtr<BIO> out;
  bssl::UniquePtr<EVP_PKEY> pkey;
  bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf;

  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  GetBoolArgument(&help, "-help", parsed_args);
  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  GetString(&in_path, "-in", "", parsed_args);
  if (in_path.empty()) {
    fprintf(stderr, "Input file required\n");
    return false;
  }
  GetString(&out_path, "-out", "", parsed_args);

  GetString(&inform, "-inform", "PEM", parsed_args);
  GetString(&outform, "-outform", "PEM", parsed_args);
  if (!validate_format(inform) || !validate_format(outform)) {
    return false;
  }

  GetBoolArgument(&topk8, "-topk8", parsed_args);
  GetBoolArgument(&nocrypt, "-nocrypt", parsed_args);

  if (parsed_args.count("-v2") > 0 && !parsed_args["-v2"].empty() &&
      !validate_cipher(parsed_args["-v2"])) {
    return false;
  }
  if (parsed_args.count("-v2prf") > 0 && !parsed_args["-v2prf"].empty() &&
      !validate_prf(parsed_args["-v2prf"])) {
    return false;
  }

  GetString(passin_arg.get(), "-passin", "", parsed_args);
  GetString(passout_arg.get(), "-passout", "", parsed_args);

  // Extract passwords (handles same-file case where both passwords are in one file)
  if (!pass_util::ExtractPasswords(passin_arg, passout_arg)) {
    fprintf(stderr, "Error extracting passwords\n");
    return false;
  }

  // Check for contradictory arguments
  if (nocrypt && !passin_arg->empty() && !passout_arg->empty()) {
    fprintf(stderr,
            "Error: -nocrypt cannot be used with both -passin and -passout\n");
    return false;
  }

  in.reset(BIO_new_file(in_path.c_str(), "rb"));
  if (!in) {
    fprintf(stderr, "Cannot open input file\n");
    return false;
  }
  if (!validate_bio_size(*in)) {
    return false;
  }

  if (!out_path.empty()) {
    out.reset(BIO_new_file(out_path.c_str(), "wb"));
  } else {
    out.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  }
  if (!out) {
    fprintf(stderr, "Cannot open output file\n");
    return false;
  }

  pkey.reset((inform == "PEM")
                 ? PEM_read_bio_PrivateKey(in.get(), nullptr, nullptr,
                                           passin_arg->empty() ? nullptr : const_cast<char*>(passin_arg->c_str()))
                 : read_private_der(in.get(), passin_arg->empty() ? nullptr : passin_arg->c_str()).release());
  if (!pkey) {
    fprintf(stderr, "Unable to load private key\n");
    return false;
  }

  bool result = false;
  if (!topk8) {
    // Default behavior: output unencrypted PKCS#8 format
    // (AWS-LC doesn't support -traditional option)
    result = (outform == "PEM")
        ? PEM_write_bio_PKCS8PrivateKey(out.get(), pkey.get(), nullptr,
                                        nullptr, 0, nullptr, nullptr)
        : i2d_PKCS8PrivateKey_bio(out.get(), pkey.get(), nullptr,
                                  nullptr, 0, nullptr, nullptr);
  } else {
    // -topk8: output PKCS#8 format (encrypted by default unless -nocrypt)
    const EVP_CIPHER *cipher = (nocrypt) ? nullptr : 
        ((parsed_args.count("-v2") == 0 || parsed_args["-v2"].empty()) 
            ? EVP_aes_256_cbc() 
            : EVP_get_cipherbyname(parsed_args["-v2"].c_str()));

    result = (outform == "PEM")
        ? PEM_write_bio_PKCS8PrivateKey(out.get(), pkey.get(), cipher,
                                        passout_arg->empty() ? nullptr : passout_arg->c_str(),
                                        passout_arg->empty() ? 0 : passout_arg->length(),
                                        nullptr, nullptr)
        : i2d_PKCS8PrivateKey_bio(out.get(), pkey.get(), cipher,
                                  passout_arg->empty() ? nullptr : passout_arg->c_str(),
                                  passout_arg->empty() ? 0 : passout_arg->length(),
                                  nullptr, nullptr);
  }

  if (!result) {
    fprintf(stderr, "Error writing private key\n");
    return false;
  }

  BIO_flush(out.get());
  return true;
}
