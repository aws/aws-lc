// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <cstdio>
#include <string>
#include "internal.h"
#include "openssl/x509.h"

#define FORMAT_PEM 1
#define FORMAT_DER 2
#define FORMAT_UNKNOWN 3

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kRequiredArgument, "RSA key input file" },
  { "-inform", kOptionalArgument, "Input format (PEM or DER), default PEM" },
  { "-out", kOptionalArgument, "Output file to write to" },
  { "-outform", kOptionalArgument, "Output format (PEM or DER), default PEM" },
  { "-pubin", kBooleanArgument, "Read only public components from input" },
  { "-pubout", kBooleanArgument, "Output only public components" },
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

  std::string in_path, out_path, inform, outform;
  bool noout = false, help = false, pubin = false, pubout = false;
  int input_format = FORMAT_UNKNOWN;
  int output_format = FORMAT_PEM;

  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&in_path, "-in", "", parsed_args);
  GetString(&inform, "-inform", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetString(&outform, "-outform", "", parsed_args);
  GetBoolArgument(&pubin, "-pubin", parsed_args);
  GetBoolArgument(&pubout, "-pubout", parsed_args);
  GetBoolArgument(&noout, "-noout", parsed_args);

  // Display rsa tool option summary
  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  if (pubin) {
    // If reading a public key, then we can only output a public key.
    pubout = true;
  }

  // Check for required option -in
  if (in_path.empty()) {
    fprintf(stderr, "Error: missing required argument '-in'\n");
    return false;
  }

  // Check input format
  if (!inform.empty()) {
    if (isStringUpperCaseEqual(inform, "DER")) {
      input_format = FORMAT_DER;
    } else if (isStringUpperCaseEqual(inform, "PEM")) {
      input_format = FORMAT_PEM;
    } else {
      fprintf(stderr, "Error: '-inform' option must specify a valid encoding DER|PEM\n");
      return false;
    }
  }

  // Check output format
  if (!outform.empty()) {
    if (isStringUpperCaseEqual(outform, "DER")) {
      output_format = FORMAT_DER;
    } else if (isStringUpperCaseEqual(outform, "PEM")) {
      output_format = FORMAT_PEM;
    } else {
      fprintf(stderr, "Error: '-outform' option must specify a valid encoding DER|PEM\n");
      return false;
    }
  }

  ScopedFILE in_file(fopen(in_path.c_str(), "rb"));
  if (!in_file) {
    fprintf(stderr, "Error: unable to load RSA key from '%s'\n", in_path.c_str());
    return false;
  }

  bssl::UniquePtr<RSA> rsa;
  // Load the key
  if (pubin) {
    if (input_format == FORMAT_DER || input_format == FORMAT_UNKNOWN) {
      // Try raw RSAPublicKey format first
      rsa.reset(d2i_RSAPublicKey_fp(in_file.get(), nullptr));
      if (!rsa) {
        rewind(in_file.get());
        // Try PKCS#8 SubjectPublicKeyInfo format
        bssl::UniquePtr<EVP_PKEY> pkey(d2i_PUBKEY_fp(in_file.get(), nullptr));
        if (pkey) {
          rsa.reset(EVP_PKEY_get1_RSA(pkey.get()));
        }
      }
    }
    if (input_format == FORMAT_PEM || (!rsa && input_format == FORMAT_UNKNOWN)) {
      rsa.reset(PEM_read_RSA_PUBKEY(in_file.get(), nullptr, nullptr, nullptr));
      if (!rsa) {
        rewind(in_file.get());
        bssl::UniquePtr<EVP_PKEY> pkey(PEM_read_PUBKEY(in_file.get(), nullptr, nullptr, nullptr));
        if (pkey) {
          rsa.reset(EVP_PKEY_get1_RSA(pkey.get()));
        }
      }
    }
  } else {
    if (input_format == FORMAT_DER || input_format == FORMAT_UNKNOWN) {
      // Try RSAPrivateKey format first
      rsa.reset(d2i_RSAPrivateKey_fp(in_file.get(), nullptr));
      if (!rsa) {
        rewind(in_file.get());
        // Try PKCS#8 PrivateKeyInfo format
        bssl::UniquePtr<EVP_PKEY> pkey(d2i_PrivateKey_fp(in_file.get(), nullptr));
        if (pkey) {
          rsa.reset(EVP_PKEY_get1_RSA(pkey.get()));
        }
      }
    }
    if (input_format == FORMAT_PEM || (!rsa && input_format == FORMAT_UNKNOWN)) {
      rsa.reset(PEM_read_RSAPrivateKey(in_file.get(), nullptr, nullptr, nullptr));
      if (!rsa) {
        rewind(in_file.get());
        bssl::UniquePtr<EVP_PKEY> pkey(PEM_read_PrivateKey(in_file.get(), nullptr, nullptr, nullptr));
        if (pkey) {
          rsa.reset(EVP_PKEY_get1_RSA(pkey.get()));
        }
      }
    }
  }

  if (!rsa) {
    fprintf(stderr, "Error: unable to read RSA %s key from '%s'\n",
            pubin ? "public" : "private", in_path.c_str());
    ERR_print_errors_fp(stderr);
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
    FILE *out = out_file ? out_file.get() : stdout;
    bool write_success = false;
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    if (pkey && EVP_PKEY_set1_RSA(pkey.get(), rsa.release())) {
      fprintf(stderr, "writing RSA key\n");
      if (pubout) {
        // Output public key
        if (output_format == FORMAT_DER) {
          write_success = i2d_PUBKEY_fp(out, pkey.get());
        } else {
          write_success = PEM_write_PUBKEY(out, pkey.get());
        }
        if (!write_success) {
          fprintf(stderr, "Error: unable to write RSA public key%s\n",
                  out_file ? " to output file" : "");
          ERR_print_errors_fp(stderr);
          return false;
        }
      } else {
        // Output private key
        if (output_format == FORMAT_DER) {
          // For DER output, use PKCS#8 PrivateKeyInfo format to match OpenSSL
          write_success = i2d_PKCS8PrivateKeyInfo_fp(out, pkey.get());
        } else {
          write_success = PEM_write_PrivateKey(out, pkey.get(), nullptr, nullptr, 0, nullptr, nullptr);
        }
        if (!write_success) {
          fprintf(stderr, "Error: unable to write RSA private key%s\n",
                  out_file ? " to output file" : "");
          ERR_print_errors_fp(stderr);
          return false;
        }
      }
    }
  }

  return true;
}
