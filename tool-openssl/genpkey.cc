// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include "internal.h"

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display this summary"},
    {"-out", kOptionalArgument, "Output file to write the key to"},
    {"-algorithm", kRequiredArgument, "Public key algorithm to use."},
    {"-pkeyopt", kOptionalArgument,
     "Value to set the public key algorithm option to"},
    {"", kOptionalArgument, ""}};

static EVP_PKEY_CTX *init_gen_str(std::string algorithm) {
  const EVP_PKEY_ASN1_METHOD *ameth =
      EVP_PKEY_asn1_find_str(nullptr, algorithm.c_str(), algorithm.size());
  if (!ameth) {
    fprintf(stderr, "Algorithm %s not found\n", algorithm.c_str());
    return nullptr;
  }

  int pkey_id = 0;
  if (!EVP_PKEY_asn1_get0_info(&pkey_id, nullptr, nullptr, nullptr, nullptr, ameth)) {
    return nullptr;
  };
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(pkey_id, nullptr));
  if (!ctx) {
    return nullptr;
  }

  if (EVP_PKEY_keygen_init(ctx.get()) <= 0) {
    return nullptr;
  }

  return ctx.release();
}

bool genpkeyTool(const args_list_t &args) {
  ordered_args::ordered_args_map_t parsed_args;
  args_list_t extra_args{};
  std::string out_path, algorithm, pkey_options;
  bool help = false;
  bssl::UniquePtr<EVP_PKEY> pkey;
  int out_format = FORMAT_PEM;

  // Parse command line arguments
  if (!ordered_args::ParseOrderedKeyValueArguments(parsed_args, extra_args,
                                                   args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  ordered_args::GetBoolArgument(&help, "-help", parsed_args);
  ordered_args::GetString(&out_path, "-out", "", parsed_args);
  ordered_args::GetString(&algorithm, "-algorithm", "", parsed_args);
  ordered_args::GetString(&pkey_options, "-pkeyopt", "", parsed_args);

  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  bssl::UniquePtr<BIO> out;
  if (out_path.empty()) {
    out.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    out.reset(BIO_new(BIO_s_file()));
    if (!BIO_write_filename(out.get(), out_path.c_str())) {
      fprintf(stderr, "Error: failed to open output file '%s'\n",
              out_path.c_str());
      return false;
    }
  }

  bssl::UniquePtr<EVP_PKEY_CTX> ctx(init_gen_str(algorithm.c_str()));
  if (!ctx) {
    return false;
  }
  if (!pkey_options.empty() &&
      !ApplyPkeyCtrlString(ctx.get(), pkey_options.c_str())) {
    fprintf(stderr, "Error setting %s parameter:\n", pkey_options.c_str());
    return false;
  }

  EVP_PKEY *tmp_key = nullptr;
  if (!EVP_PKEY_keygen(ctx.get(), &tmp_key)) {
    fprintf(stderr, "Error generating key\n");
    return false;
  }
  pkey.reset(tmp_key);

  if (!WritePrivateKey(pkey.get(), out, out_format)) {
    return false;
  }

  return true;
}
