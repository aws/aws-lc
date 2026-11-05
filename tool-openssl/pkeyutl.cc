// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC


#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <string.h>
#include <sys/stat.h>
#include "internal.h"

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-in", kOptionalArgument, "Input file - default stdin"},
    {"-out", kOptionalArgument, "Output file - default stdout"},
    {"-encrypt", kBooleanArgument, "Encrypt with public key"},
    {"-decrypt", kBooleanArgument, "Decrypt with private key"},
    {"-sign", kBooleanArgument, "Sign input data with private key (default)"},
    {"-verify", kBooleanArgument, "Verify with public key"},
    {"-sigfile", kOptionalArgument,
     "Signature file, required for verify operations only"},
    {"-inkey", kOptionalArgument, "Input private key file"},
    {"-pubin", kBooleanArgument, "Input is a public key"},
    {"-pkeyopt", kOptionalArgument, "Public key option in opt:value form"},
    {"-passin", kOptionalArgument, "Input file pass phrase source"},
    {"", kOptionalArgument, ""}};

static bool LoadPrivateKey(const std::string &keyfile,
                           Password &passin_arg,
                           bssl::UniquePtr<EVP_PKEY> &pkey) {
  ScopedFILE key_file;
  if (keyfile.empty()) {
    fprintf(stderr, "Error: no private key given (-inkey parameter)\n");
    return false;
  }

  key_file.reset(fopen(keyfile.c_str(), "rb"));
  if (!key_file) {
    fprintf(stderr, "Error: unable to load private key from '%s'\n",
            keyfile.c_str());
    return false;
  }

  // Extract password using pass_util if provided
  const char *password = nullptr;
  if (!passin_arg.empty()) {
    if (!pass_util::ExtractPassword(passin_arg)) {
      fprintf(stderr, "Error: failed to extract password\n");
      return false;
    }
    password = passin_arg.get().c_str();
  }

  pkey.reset(PEM_read_PrivateKey(key_file.get(), nullptr, nullptr,
                                 const_cast<char *>(password)));
  if (!pkey) {
    fprintf(stderr, "Error: error reading private key from '%s'\n",
            keyfile.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }

  return true;
}

static bool LoadPublicKey(const std::string &keyfile,
                          bssl::UniquePtr<EVP_PKEY> &pkey) {
  ScopedFILE key_file;
  if (keyfile.empty()) {
    fprintf(stderr, "Error: no public key given (-inkey parameter)\n");
    return false;
  }

  key_file.reset(fopen(keyfile.c_str(), "rb"));
  if (!key_file) {
    fprintf(stderr, "Error: unable to load public key from '%s'\n",
            keyfile.c_str());
    return false;
  }

  pkey.reset(PEM_read_PUBKEY(key_file.get(), nullptr, nullptr, nullptr));
  if (!pkey) {
    fprintf(stderr, "Error: error reading public key from '%s'\n",
            keyfile.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }

  return true;
}

static bool ReadInputData(const std::string &in_path,
                          std::vector<uint8_t> &data) {
  ScopedFILE in_file;
  FILE *input = stdin;
  // As in OpenSSL, "-" means stdin for -in and stdout for -out.
  if (!in_path.empty() && in_path != "-") {
    in_file.reset(fopen(in_path.c_str(), "rb"));
    if (!in_file) {
      fprintf(stderr, "Error: unable to open input file '%s'\n",
              in_path.c_str());
      return false;
    }
    input = in_file.get();
  }

  if (!ReadAll(&data, input)) {
    fprintf(stderr, "Error: error reading input data\n");
    return false;
  }

  return true;
}

static bool ApplyPkeyOptions(EVP_PKEY_CTX *ctx,
                             const std::vector<std::string> &pkeyopts,
                             const char *operation) {
  for (const auto &pkeyopt : pkeyopts) {
    if (!ApplyPkeyCtrlString(ctx, pkeyopt.c_str())) {
      fprintf(stderr, "%s parameter error \"%s\"\n", operation,
              pkeyopt.c_str());
      return false;
    }
  }
  return true;
}

static bool DoSign(EVP_PKEY *pkey, const std::vector<uint8_t> &input_data,
                   const std::vector<std::string> &pkeyopts,
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

  if (!ApplyPkeyOptions(ctx.get(), pkeyopts, "Signature")) {
    return false;
  }

  size_t sig_len = 0;
  if (EVP_PKEY_sign(ctx.get(), nullptr, &sig_len, input_data.data(),
                    input_data.size()) <= 0) {
    fprintf(stderr, "Error: failed to determine signature length\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  signature.resize(sig_len);
  if (EVP_PKEY_sign(ctx.get(), signature.data(), &sig_len, input_data.data(),
                    input_data.size()) <= 0) {
    fprintf(stderr, "Error: failed to sign data\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  signature.resize(sig_len);
  return true;
}

static bool DoVerify(EVP_PKEY *pkey, const std::vector<uint8_t> &input_data,
                     const std::vector<std::string> &pkeyopts,
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

  if (!ApplyPkeyOptions(ctx.get(), pkeyopts, "Signature")) {
    return false;
  }

  int result = EVP_PKEY_verify(ctx.get(), signature.data(), signature.size(),
                               input_data.data(), input_data.size());
  if (result == 1) {
    return true;
  } else if (result == 0) {
    return false;  // Verification failed
  } else {
    fprintf(stderr, "Error: verification operation failed\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
}

static bool DoCrypt(EVP_PKEY *pkey, const std::vector<uint8_t> &input_data,
                    const std::vector<std::string> &pkeyopts, bool encrypt,
                    std::vector<uint8_t> &output) {
  const auto init = encrypt ? EVP_PKEY_encrypt_init : EVP_PKEY_decrypt_init;
  const auto crypt = encrypt ? EVP_PKEY_encrypt : EVP_PKEY_decrypt;
  const char *op = encrypt ? "encrypt" : "decrypt";
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new(pkey, nullptr));
  if (!ctx) {
    fprintf(stderr, "Error: failed to create %s context\n", op);
    return false;
  }

  if (init(ctx.get()) <= 0) {
    fprintf(stderr, "Error: failed to initialize %s context\n", op);
    ERR_print_errors_fp(stderr);
    return false;
  }

  if (!ApplyPkeyOptions(ctx.get(), pkeyopts,
                        encrypt ? "Encryption" : "Decryption")) {
    return false;
  }

  size_t output_len = 0;
  if (crypt(ctx.get(), nullptr, &output_len, input_data.data(),
            input_data.size()) <= 0) {
    fprintf(stderr, "Error: failed to determine %s output length\n", op);
    ERR_print_errors_fp(stderr);
    return false;
  }

  output.resize(output_len);
  if (crypt(ctx.get(), output.data(), &output_len, input_data.data(),
            input_data.size()) <= 0) {
    fprintf(stderr, "Error: failed to %s data\n", op);
    ERR_print_errors_fp(stderr);
    return false;
  }

  output.resize(output_len);
  return true;
}

static bssl::UniquePtr<BIO> OpenOutput(const std::string &out_path) {
  bssl::UniquePtr<BIO> output_bio;
  if (out_path.empty() || out_path == "-") {
    output_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    output_bio.reset(BIO_new_file(out_path.c_str(), "wb"));
  }
  if (!output_bio) {
    fprintf(stderr, "Error: failed to open output file '%s'\n",
            out_path.c_str());
  }
  return output_bio;
}

static bool WriteOutput(const std::vector<uint8_t> &data,
                        const std::string &out_path) {
  bssl::UniquePtr<BIO> output_bio = OpenOutput(out_path);
  if (!output_bio) {
    return false;
  }

  if (!BIO_write_all(output_bio.get(), data.data(), data.size())) {
    fprintf(stderr, "Error: failed to write output data\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  // Buffered file writes may fail only when flushed.
  if (!BIO_flush(output_bio.get())) {
    fprintf(stderr, "Error: failed to flush output data\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  return true;
}

int pkeyutlTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;

  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args,
                                     kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return kToolExitFailure;
  }

  if (HasArgument(parsed_args, "-help")) {
    PrintUsage(kArguments);
    return kToolExitSuccess;
  }

  std::string in_path, out_path, inkey_path, sigfile_path;
  std::vector<std::string> pkeyopts;
  Password passin_arg;
  GetLastString(&in_path, "-in", "", parsed_args);
  GetLastString(&out_path, "-out", "", parsed_args);
  GetLastString(&inkey_path, "-inkey", "", parsed_args);
  GetLastString(&passin_arg.get(), "-passin", "", parsed_args);
  GetLastString(&sigfile_path, "-sigfile", "", parsed_args);
  const bool pubin = HasArgument(parsed_args, "-pubin");
  const std::string operation = GetLastOption(
      {"-encrypt", "-decrypt", "-sign", "-verify"}, "-sign", parsed_args);
  FindAll(pkeyopts, "-pkeyopt", parsed_args);

  // Validate arguments
  if (operation == "-verify" && sigfile_path.empty()) {
    fprintf(
        stderr,
        "Error: No signature file specified for verify (-sigfile parameter)\n");
    return kToolExitFailure;
  }

  if (operation != "-verify" && !sigfile_path.empty()) {
    fprintf(stderr,
            "Error: Signature file specified for non-verify operation\n");
    return kToolExitFailure;
  }

  if (pubin && (operation == "-sign" || operation == "-decrypt")) {
    fprintf(stderr, "Error: A private key is needed for this operation\n");
    return kToolExitFailure;
  }

  if (inkey_path.empty()) {
    fprintf(stderr, "Error: no key given (-inkey parameter)\n");
    return kToolExitFailure;
  }

  // Without -pubin, -inkey is a private key; -verify uses its public half.
  bssl::UniquePtr<EVP_PKEY> pkey;
  if (pubin) {
    if (!LoadPublicKey(inkey_path, pkey)) {
      return kToolExitFailure;
    }
  } else {
    if (!LoadPrivateKey(inkey_path, passin_arg, pkey)) {
      return kToolExitFailure;
    }
  }

  if (operation == "-sign") {
    std::vector<uint8_t> signature;
    std::vector<uint8_t> input_data;
    if (!ReadInputData(in_path, input_data)) {
      return kToolExitFailure;
    }

    // Sanity check for non-raw input
    if (input_data.size() > EVP_MAX_MD_SIZE) {
      fprintf(stderr, "Error: input data looks too long to be a hash\n");
      return kToolExitFailure;
    }

    if (!DoSign(pkey.get(), input_data, pkeyopts, signature)) {
      return kToolExitFailure;
    }

    if (!WriteOutput(signature, out_path)) {
      return kToolExitFailure;
    }
  } else if (operation == "-verify") {
    // Read signature from sigfile
    std::vector<uint8_t> signature;
    ScopedFILE sig_file;
    sig_file.reset(fopen(sigfile_path.c_str(), "rb"));
    if (!sig_file) {
      fprintf(stderr, "Error: unable to open signature file '%s'\n",
              sigfile_path.c_str());
      return kToolExitFailure;
    }

    if (!ReadAll(&signature, sig_file.get())) {
      fprintf(stderr, "Error: error reading signature data\n");
      return kToolExitFailure;
    }

    std::vector<uint8_t> input_data;
    if (!ReadInputData(in_path, input_data)) {
      return kToolExitFailure;
    }

    bool success = DoVerify(pkey.get(), input_data, pkeyopts, signature);

    bssl::UniquePtr<BIO> output_bio = OpenOutput(out_path);
    if (!output_bio) {
      return kToolExitFailure;
    }

    const char *message = success ? "Signature Verified Successfully\n"
                                  : "Signature Verification Failure\n";
    if (BIO_puts(output_bio.get(), message) <= 0 ||
        !BIO_flush(output_bio.get())) {
      fprintf(stderr, "Error: failed to write verification result\n");
      ERR_print_errors_fp(stderr);
      return kToolExitFailure;
    }

    if (!success) {
      return kToolExitFailure;
    }
  } else {
    std::vector<uint8_t> input_data;
    if (!ReadInputData(in_path, input_data)) {
      return kToolExitFailure;
    }

    std::vector<uint8_t> output;
    if (!DoCrypt(pkey.get(), input_data, pkeyopts, operation == "-encrypt",
                 output) ||
        !WriteOutput(output, out_path)) {
      return kToolExitFailure;
    }
  }

  return kToolExitSuccess;
}
