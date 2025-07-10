// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <algorithm>
#include <iostream>
#include <string>
#include "internal.h"

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kRequiredArgument, "RSA key input file" },
  { "-out", kOptionalArgument, "Output file to write to" },
  { "-noout", kBooleanArgument, "Prevents output of the encoded version of the RSA key" },
  { "-modulus", kBooleanArgument, "Prints out the value of the modulus of the RSA key" },
  { "", kOptionalArgument, "" }
};

static bool handleModulus(RSA *rsa, ScopedFILE &out_file) {
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
  if (out_file) {
    fprintf(out_file.get(), "Modulus=%s\n", hex_modulus);
  } else {
    printf("Modulus=%s\n", hex_modulus);
  }
  OPENSSL_free(hex_modulus);
  return true;
}

// Map arguments using tool/args.cc
bool rsaTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, out_path;
  bool noout = false, help = false;

  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&in_path, "-in", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetBoolArgument(&noout, "-noout", parsed_args);

  // Display rsa tool option summary
  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  // Check for required option -in
  if (in_path.empty()) {
    fprintf(stderr, "Error: missing required argument '-in'\n");
    return false;
  }

  ScopedFILE in_file(fopen(in_path.c_str(), "rb"));
  if (!in_file) {
    fprintf(stderr, "Error: unable to load RSA key from '%s'\n", in_path.c_str());
    return false;
  }

  bssl::UniquePtr<RSA> rsa(PEM_read_RSAPrivateKey(in_file.get(), nullptr, nullptr, nullptr));
  if (!rsa) {
    fprintf(stderr, "Error: unable to read RSA private key from '%s'\n", in_path.c_str());
    return false;
  }

  ScopedFILE out_file;
  if (!out_path.empty()) {
    out_file.reset(fopen(out_path.c_str(), "wb"));
    if (!out_file) {
      fprintf(stderr, "Error: unable to open output file '%s'\n", out_path.c_str());
      return false;
    }
  }

  // The "rsa" command does not order output based on parameters:
  if (HasArgument(parsed_args, "-modulus")) {
    if (!handleModulus(rsa.get(), out_file)) {
      return false;
    }
  }

  if (!noout) {
    if (out_file) {
      if (!PEM_write_RSAPrivateKey(out_file.get(), rsa.get(), nullptr, nullptr, 0, nullptr, nullptr)) {
        fprintf(stderr, "Error: unable to write RSA private key to '%s'\n", out_path.c_str());
        return false;
      }
    } else {
      PEM_write_RSAPrivateKey(stdout, rsa.get(), nullptr, nullptr, 0, nullptr, nullptr);
    }
  }

  return true;
}
