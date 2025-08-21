// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bio.h>
#include <openssl/ec.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <string>
#include "internal.h"

#define FORMAT_PEM 1
#define FORMAT_DER 2

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display this summary"},
    {"-inform", kOptionalArgument, "Input format (PEM or DER), default PEM"},
    {"-in", kOptionalArgument, "Input file, default stdin"},
    {"-pubout", kBooleanArgument, "Output public key, not private"},
    {"-out", kOptionalArgument, "Output file, default stdout"},
    {"-outform", kOptionalArgument, "Output format (PEM or DER), default PEM"},
    {"", kOptionalArgument, ""}};

bool ecTool(const args_list_t &args) {
  ordered_args::ordered_args_map_t parsed_args;
  args_list_t extra_args;
  std::string in_path, out_path, inform_str, outform_str;
  bool help = false, pubout = false;
  int input_format = FORMAT_PEM, output_format = FORMAT_PEM;
  bssl::UniquePtr<BIO> input_bio, output_bio;
  bssl::UniquePtr<EC_KEY> ec_key;

  if (!ordered_args::ParseOrderedKeyValueArguments(parsed_args, extra_args,
                                                   args, kArguments)) {
    PrintUsage(kArguments);
    goto err;
  }

  ordered_args::GetBoolArgument(&help, "-help", parsed_args);
  ordered_args::GetString(&in_path, "-in", "", parsed_args);
  ordered_args::GetString(&out_path, "-out", "", parsed_args);
  ordered_args::GetString(&inform_str, "-inform", "PEM", parsed_args);
  ordered_args::GetString(&outform_str, "-outform", "PEM", parsed_args);
  ordered_args::GetBoolArgument(&pubout, "-pubout", parsed_args);

  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  input_format = (inform_str == "DER") ? FORMAT_DER : FORMAT_PEM;
  output_format = (outform_str == "DER") ? FORMAT_DER : FORMAT_PEM;

  input_bio.reset(in_path.empty() ? BIO_new_fp(stdin, BIO_NOCLOSE)
                                  : BIO_new_file(in_path.c_str(), "rb"));
  if (!input_bio) {
    fprintf(stderr, "Error: Could not open input\n");
    goto err;
  }

  ec_key.reset(input_format == FORMAT_DER
                   ? d2i_ECPrivateKey_bio(input_bio.get(), nullptr)
                   : PEM_read_bio_ECPrivateKey(input_bio.get(), nullptr,
                                               nullptr, nullptr));
  if (!ec_key) {
    fprintf(stderr, "Error: Could not read EC key\n");
    goto err;
  }

  output_bio.reset(out_path.empty() ? BIO_new_fp(stdout, BIO_NOCLOSE)
                                    : BIO_new_file(out_path.c_str(), "wb"));
  if (!output_bio) {
    fprintf(stderr, "Error: Could not open output\n");
    goto err;
  }

  if (pubout) {
    if (!(output_format == FORMAT_DER
              ? i2d_EC_PUBKEY_bio(output_bio.get(), ec_key.get())
              : PEM_write_bio_EC_PUBKEY(output_bio.get(), ec_key.get()))) {
      goto err;
    }
  } else {
    if (!(output_format == FORMAT_DER
              ? i2d_ECPrivateKey_bio(output_bio.get(), ec_key.get())
              : PEM_write_bio_ECPrivateKey(output_bio.get(), ec_key.get(),
                                           nullptr, nullptr, 0, nullptr,
                                           nullptr))) {
      goto err;
    }
  }

  return true;

err:
  ERR_print_errors_fp(stderr);
  return false;
}
