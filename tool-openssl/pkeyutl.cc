// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/x509.h>
#include <sys/stat.h>
#include "internal.h"
#include <string>

#define KEY_NONE        0
#define KEY_PRIVKEY     1
#define KEY_PUBKEY      2

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kOptionalArgument, "Input file - default stdin" },
  { "-out", kOptionalArgument, "Output file - default stdout" },
  { "-sign", kBooleanArgument, "Sign input data with private key" },
  { "-verify", kBooleanArgument, "Verify with public key" },
  { "-sigfile", kOptionalArgument, "Signature file, required for verify operations only" },
  { "-inkey", kOptionalArgument, "Input private key file" },
  { "-pubin", kBooleanArgument, "Input is a public key" },
  { "-passin", kOptionalArgument, "Input file pass phrase source" },
  { "", kOptionalArgument, "" }
};

static bool LoadPrivateKey(const std::string &keyfile, const std::string &passin_arg, 
                          bssl::UniquePtr<EVP_PKEY> &pkey) {
  ScopedFILE key_file;
  if (keyfile.empty()) {
    fprintf(stderr, "Error: no private key given (-inkey parameter)\n");
    return false;
  }
  
  key_file.reset(fopen(keyfile.c_str(), "rb"));
  if (!key_file) {
    fprintf(stderr, "Error: unable to load private key from '%s'\n", keyfile.c_str());
    return false;
  }

  // For simplicity, we'll handle basic password-protected keys
  // In a full implementation, we'd parse passin_arg for different password sources
  const char *password = nullptr;
  if (!passin_arg.empty()) {
    // Simple case: assume it's a direct password (not a file or other source)
    password = passin_arg.c_str();
  }

  pkey.reset(PEM_read_PrivateKey(key_file.get(), nullptr, nullptr, 
                                const_cast<char*>(password)));
  if (!pkey) {
    fprintf(stderr, "Error: error reading private key from '%s'\n", keyfile.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }

  return true;
}

static bool LoadPublicKey(const std::string &keyfile, bssl::UniquePtr<EVP_PKEY> &pkey) {
  ScopedFILE key_file;
  if (keyfile.empty()) {
    fprintf(stderr, "Error: no public key given (-inkey parameter)\n");
    return false;
  }
  
  key_file.reset(fopen(keyfile.c_str(), "rb"));
  if (!key_file) {
    fprintf(stderr, "Error: unable to load public key from '%s'\n", keyfile.c_str());
    return false;
  }

  pkey.reset(PEM_read_PUBKEY(key_file.get(), nullptr, nullptr, nullptr));
  if (!pkey) {
    fprintf(stderr, "Error: error reading public key from '%s'\n", keyfile.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }

  return true;
}

static bool ReadInputData(const std::string &in_path, std::vector<uint8_t> &data) {
  ScopedFILE in_file;
  if (in_path.empty()) {
    in_file.reset(stdin);
  } else {
    in_file.reset(fopen(in_path.c_str(), "rb"));
    if (!in_file) {
      fprintf(stderr, "Error: unable to open input file '%s'\n", in_path.c_str());
      return false;
    }
  }

  if (!ReadAll(&data, in_file.get())) {
    fprintf(stderr, "Error: error reading input data\n");
    return false;
  }

  return true;
}

static bool DoSign(EVP_PKEY *pkey, const std::vector<uint8_t> &input_data, 
                   std::vector<uint8_t> &signature) {
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new(pkey, nullptr));
  if (!ctx) {
    fprintf(stderr, "Error: failed to create signing context\n");
    return false;
  }

  if (EVP_PKEY_sign_init(ctx.get()) <= 0) {
    fprintf(stderr, "Error: failed to initialize signing context\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  size_t sig_len = 0;
  if (EVP_PKEY_sign(ctx.get(), nullptr, &sig_len, input_data.data(), input_data.size()) <= 0) {
    fprintf(stderr, "Error: failed to determine signature length\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  signature.resize(sig_len);
  if (EVP_PKEY_sign(ctx.get(), signature.data(), &sig_len, 
                    input_data.data(), input_data.size()) <= 0) {
    fprintf(stderr, "Error: failed to sign data\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  signature.resize(sig_len);
  return true;
}

static bool DoVerify(EVP_PKEY *pkey, const std::vector<uint8_t> &input_data,
                     const std::vector<uint8_t> &signature) {
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new(pkey, nullptr));
  if (!ctx) {
    fprintf(stderr, "Error: failed to create verification context\n");
    return false;
  }

  if (EVP_PKEY_verify_init(ctx.get()) <= 0) {
    fprintf(stderr, "Error: failed to initialize verification context\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  int result = EVP_PKEY_verify(ctx.get(), signature.data(), signature.size(),
                              input_data.data(), input_data.size());
  if (result == 1) {
    return true;
  } else if (result == 0) {
    return false; // Verification failed
  } else {
    fprintf(stderr, "Error: verification operation failed\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
}

static bool WriteOutput(const std::vector<uint8_t> &data, const std::string &out_path) {
  bssl::UniquePtr<BIO> output_bio;
  if (out_path.empty()) {
    output_bio.reset(BIO_new_fp(stdout, BIO_CLOSE));
  } else {
    output_bio.reset(BIO_new(BIO_s_file()));
    if (BIO_write_filename(output_bio.get(), out_path.c_str()) <= 0) {
      fprintf(stderr, "Error: failed to open output file '%s'\n", out_path.c_str());
      return false;
    }
  }

  if (!output_bio) {
    fprintf(stderr, "Error: unable to create output BIO\n");
    return false;
  }

  BIO_write(output_bio.get(), data.data(), data.size());
  return true;
}

bool pkeyutlTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;

  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, out_path, inkey_path, passin_arg, sigfile_path;
  bool sign = false, verify = false, pubin = false;

  GetString(&in_path, "-in", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetString(&inkey_path, "-inkey", "", parsed_args);
  GetString(&passin_arg, "-passin", "", parsed_args);
  GetString(&sigfile_path, "-sigfile", "", parsed_args);
  GetBoolArgument(&sign, "-sign", parsed_args);
  GetBoolArgument(&verify, "-verify", parsed_args);
  GetBoolArgument(&pubin, "-pubin", parsed_args);

  // Display help
  if (HasArgument(parsed_args, "-help")) {
    PrintUsage(kArguments);
    return true;
  }

  // Validate arguments
  if (!sign && !verify) {
    fprintf(stderr, "Error: must specify either -sign or -verify\n");
    return false;
  }

  if (sign && verify) {
    fprintf(stderr, "Error: cannot specify both -sign and -verify\n");
    return false;
  }

  if (verify && sigfile_path.empty()) {
    fprintf(stderr, "Error: No signature file specified for verify (-sigfile parameter)\n");
    return false;
  }

  if (!verify && !sigfile_path.empty()) {
    fprintf(stderr, "Error: Signature file specified for non-verify operation\n");
    return false;
  }

  if (inkey_path.empty()) {
    fprintf(stderr, "Error: no key given (-inkey parameter)\n");
    return false;
  }

  // Load the key
  bssl::UniquePtr<EVP_PKEY> pkey;
  if (pubin || verify) {
    if (!LoadPublicKey(inkey_path, pkey)) {
      return false;
    }
  } else {
    if (!LoadPrivateKey(inkey_path, passin_arg, pkey)) {
      return false;
    }
  }

  if (sign) {
    std::vector<uint8_t> signature;
    std::vector<uint8_t> input_data;
    if (!ReadInputData(in_path, input_data)) {
      return false;
    }

    // Sanity check for non-raw input
    if (input_data.size() > EVP_MAX_MD_SIZE) {
      fprintf(stderr, "Error: input data looks too long to be a hash\n");
      return false;
    }

    if (!DoSign(pkey.get(), input_data, signature)) {
      return false;
    }

    if (!WriteOutput(signature, out_path)) {
      return false;
    }
  } else if (verify) {
    // Read signature from sigfile
    std::vector<uint8_t> signature;
    ScopedFILE sig_file;
    sig_file.reset(fopen(sigfile_path.c_str(), "rb"));
    if (!sig_file) {
      fprintf(stderr, "Error: unable to open signature file '%s'\n", sigfile_path.c_str());
      return false;
    }
    
    if (!ReadAll(&signature, sig_file.get())) {
      fprintf(stderr, "Error: error reading signature data\n");
      return false;
    }

    std::vector<uint8_t> input_data;
    if (!ReadInputData(in_path, input_data)) {
      return false;
    }

    bool success = DoVerify(pkey.get(), input_data, signature);

    bssl::UniquePtr<BIO> output_bio;
    if (out_path.empty()) {
      output_bio.reset(BIO_new_fp(stdout, BIO_CLOSE));
    } else {
      output_bio.reset(BIO_new(BIO_s_file()));
      if (BIO_write_filename(output_bio.get(), out_path.c_str()) <= 0) {
        fprintf(stderr, "Error: failed to open output file '%s'\n", out_path.c_str());
        return false;
      }
    }

    if (success) {
      BIO_puts(output_bio.get(), "Signature Verified Successfully\n");
    } else {
      BIO_puts(output_bio.get(), "Signature Verification Failure\n");
    }
  }

  return true;
}
