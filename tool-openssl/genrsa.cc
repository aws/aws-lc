// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <cstdlib>
#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include "internal.h"

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-out", kOptionalArgument, "Output file to write the key to" },
  { "", kOptionalArgument, "Key size in bits (default: 2048)" }
};

bool genrsaTool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  std::string out_path;
  bool help = false;
  
  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);

  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  unsigned bits = 2048;
  if (!extra_args.empty()) {
    char *endptr;
    unsigned long parsed_bits = strtoul(extra_args[0].c_str(), &endptr, 10);
    if (*endptr != '\0' || parsed_bits == 0 || parsed_bits > UINT_MAX) {
      fprintf(stderr, "Error: Invalid key size '%s'\n", extra_args[0].c_str());
      return false;
    }
    bits = static_cast<unsigned>(parsed_bits);
  }

  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> e(BN_new());
  
  if (!BN_set_word(e.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), bits, e.get(), NULL)) {
    ERR_print_errors_fp(stderr);
    return false;
  }

  bssl::UniquePtr<BIO> bio;
  if (out_path.empty()) {
    bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    bio.reset(BIO_new_file(out_path.c_str(), "w"));
    if (!bio) {
      fprintf(stderr, "Error: Could not open output file '%s'\n", out_path.c_str());
      return false;
    }
  }

  if (!PEM_write_bio_RSAPrivateKey(bio.get(), rsa.get(), NULL /* cipher */,
                                   NULL /* key */, 0 /* key len */,
                                   NULL /* password callback */,
                                   NULL /* callback arg */)) {
    ERR_print_errors_fp(stderr);
    return false;
  }

  return true;
}
