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


// Validates input/output format is PEM or DER
static bool validate_format(const std::string &format) {
  if (format != "PEM" && format != "DER") {
    fprintf(stderr, "Format must be PEM or DER\n");
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
static bssl::UniquePtr<EVP_PKEY> read_private_der(BIO *in_bio,
                                                  const char *passin) {
  if (!in_bio) {
    return nullptr;
  }

  BIO_reset(in_bio);

  if (passin) {
    // Try encrypted PKCS8 DER
    return bssl::UniquePtr<EVP_PKEY>(d2i_PKCS8PrivateKey_bio(
        in_bio, nullptr, nullptr, const_cast<char *>(passin)));
  }

  // Try unencrypted DER formats in order of preference
  // 1. Try unencrypted PKCS8 DER
  bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf(
      d2i_PKCS8_PRIV_KEY_INFO_bio(in_bio, nullptr));
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

// Returns 1 if PEM is encrypted, 0 if not, -1 on error
static int is_pem_encrypted(BIO *bio) {
    char *name_ptr = nullptr;
    char *header_ptr = nullptr;
    unsigned char *data_ptr = nullptr;
    long len = 0;

    // Read the PEM block
    if (!PEM_read_bio(bio, &name_ptr, &header_ptr, &data_ptr, &len)) {
        return -1;  // Error reading PEM
    }

    // We are responsible for freeing these
    bssl::UniquePtr<char> name(name_ptr);
    bssl::UniquePtr<char> header(header_ptr);
    bssl::UniquePtr<uint8_t> data(data_ptr);

    int is_encrypted = 0;

    // Check if there's a header with encryption info
    if (name && strcmp(name.get(), "ENCRYPTED PRIVATE KEY") == 0) {
        is_encrypted = 1;
    }
    // Check for traditional PEM encryption (by header)
    else if (header && header.get()[0] != '\0') {
        EVP_CIPHER_INFO cipher;
        if (PEM_get_EVP_CIPHER_INFO(header.get(), &cipher)) {
            is_encrypted = (cipher.cipher != nullptr) ? 1 : 0;
        }
    }

    // Rewind buffer so it can be parsed to obtain a private key
    if (BIO_seek(bio, 0) >= 0) {
      return is_encrypted;
    }

    return -1;
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
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  bool help = false;
  std::string in_path, out_path;
  std::string inform = "PEM", outform = "PEM";
  bool topk8 = false, nocrypt = false;

  // Sensitive strings will be automatically cleared on function exit
  Password passin_arg;
  Password passout_arg;

  bssl::UniquePtr<BIO> out;
  bssl::UniquePtr<EVP_PKEY> pkey;
  const EVP_CIPHER *cipher = nullptr;
  bssl::UniquePtr<PKCS8_PRIV_KEY_INFO> p8inf;
  bool input_is_encrypted = false;

  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args,
                                     kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  GetBoolArgument(&help, "-help", parsed_args);
  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  GetString(&in_path, "-in", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetString(&inform, "-inform", "PEM", parsed_args);
  GetString(&outform, "-outform", "PEM", parsed_args);
  if (!validate_format(inform) || !validate_format(outform)) {
    return false;
  }

  GetBoolArgument(&topk8, "-topk8", parsed_args);
  GetBoolArgument(&nocrypt, "-nocrypt", parsed_args);

  std::string v2_cipher;
  GetString(&v2_cipher, "-v2", "", parsed_args);

  std::string v2_prf;
  GetString(&v2_prf, "-v2prf", "", parsed_args);
  if (!v2_prf.empty() && !validate_prf(v2_prf)) {
    return false;
  }

  GetString(&passin_arg.get(), "-passin", "", parsed_args);
  GetString(&passout_arg.get(), "-passout", "", parsed_args);

  // Extract passwords (handles same-file case where both passwords are in one
  // file)
  if (!pass_util::ExtractPasswords(passin_arg, passout_arg)) {
    fprintf(stderr, "Error extracting passwords\n");
    return false;
  }

  // Check for contradictory arguments
  if (nocrypt && !passin_arg.empty() && !passout_arg.empty()) {
    fprintf(stderr,
            "Error: -nocrypt cannot be used with both -passin and -passout\n");
    return false;
  }

  // Read from stdin if no -in path provided
  bssl::UniquePtr<BIO> in;
  if (in_path.empty()) {
    in.reset(BIO_new_fp(stdin, BIO_NOCLOSE));
  } else {
    in.reset(BIO_new_file(in_path.c_str(), "rb"));
    if (!in) {
      fprintf(stderr, "Cannot open input file\n");
      return false;
    }
  }

  // stdin is not rewindable.
  if (!in_path.empty() && inform == "PEM") {
    switch(is_pem_encrypted(in.get())) {
      case 0:
        input_is_encrypted = false;
        break;
      case 1:
        input_is_encrypted = true;
        break;
      default:
        fprintf(stderr, "Unable to load PEM file\n");
        return false;
    }
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

  pkey.reset(
      (inform == "PEM")
          ? PEM_read_bio_PrivateKey(
                in.get(), nullptr, nullptr,
                passin_arg.empty() ? nullptr
                                    : const_cast<char *>(passin_arg.get().c_str()))
          : read_private_der(
                in.get(), passin_arg.empty() ? nullptr : passin_arg.get().c_str())
                .release());
  if (!pkey) {
    if (input_is_encrypted) {
      fprintf(stderr, "Error decrypting key\n");
    } else {
      fprintf(stderr, "Unable to load private key\n");
    }
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
    cipher = nocrypt ? nullptr
                       : (v2_cipher.empty()
                              ? EVP_aes_256_cbc()
                              : EVP_get_cipherbyname(v2_cipher.c_str()));

    result = (outform == "PEM")
                 ? PEM_write_bio_PKCS8PrivateKey(
                       out.get(), pkey.get(), cipher,
                       passout_arg.empty() ? nullptr : passout_arg.get().c_str(),
                       passout_arg.empty() ? 0 : passout_arg.get().length(),
                       nullptr, nullptr)
                 : i2d_PKCS8PrivateKey_bio(
                       out.get(), pkey.get(), cipher,
                       passout_arg.empty() ? nullptr : passout_arg.get().c_str(),
                       passout_arg.empty() ? 0 : passout_arg.get().length(),
                       nullptr, nullptr);
  }

  if (!result) {
    fprintf(stderr, "Error writing private key\n");
    return false;
  }

  BIO_flush(out.get());
  return true;
}
