// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <cstdio>
#include <string>
#include "internal.h"
#include "openssl/base.h"
#include "openssl/bio.h"
#include "openssl/x509.h"

#define FORMAT_PEM 1
#define FORMAT_DER 2
#define FORMAT_UNKNOWN 3

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kOptionalArgument, "RSA key input file" },
  { "-inform", kOptionalArgument, "Input format (PEM or DER), default PEM" },
  { "-out", kOptionalArgument, "Output file to write to" },
  { "-outform", kOptionalArgument, "Output format (PEM or DER), default PEM" },
  { "-pubin", kBooleanArgument, "Read only public components from input" },
  { "-pubout", kBooleanArgument, "Output only public components" },
  { "-noout", kBooleanArgument, "Prevents output of the encoded version of the RSA key" },
  { "-modulus", kBooleanArgument, "Prints out the value of the modulus of the RSA key" },
  { "-RSAPublicKey_in", kOptionalArgument,
    "Pass in the RSAPublicKey format. (no-op, we fallback to this"
    " format if the initial parse is unsuccessful)" },
  { "", kOptionalArgument, "" }
};

static bool handleModulus(RSA *rsa, BIO* out_file) {
  bool ret_val = false;
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
  if(BIO_puts(out_file, "Modulus=") > 0 &&
    BIO_puts(out_file, hex_modulus) > 0 &&
    BIO_puts(out_file, "\n") > 0) {
    ret_val = true;
  }
  OPENSSL_free(hex_modulus);
  return ret_val;
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

  // Read from stdin if no -in path provided
  bssl::UniquePtr<BIO> in_file;
  if (in_path.empty()) {
      in_file.reset(BIO_new_fp(stdin, BIO_NOCLOSE));
    } else {
      in_file.reset(BIO_new_file(in_path.c_str(), "rb"));
      if (!in_file) {
        fprintf(stderr, "Error: unable to load RSA key from '%s'\n",
            in_path.c_str());
        return false;
      }
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

  bssl::UniquePtr<RSA> rsa;
  // Load the key
  if (pubin) {
    if (input_format == FORMAT_DER || input_format == FORMAT_UNKNOWN) {
      // OpenSSL prioritizes PKCS#8 SubjectPublicKeyInfo format first.
      bssl::UniquePtr<EVP_PKEY> pkey(d2i_PUBKEY_bio(in_file.get(), nullptr));
      if (pkey) {
        rsa.reset(EVP_PKEY_get1_RSA(pkey.get()));
      }
      if (!rsa && BIO_seek(in_file.get(), 0) == 0) {
        // Try raw RSAPublicKey format.
        // This is the "RSAPublicKey_in" flag in OpenSSL, but we support
        // this behind a no-op flag and an automatic fallback.
        rsa.reset(d2i_RSAPublicKey_bio(in_file.get(), nullptr));
      }
    }
    if (input_format == FORMAT_PEM || (!rsa && input_format == FORMAT_UNKNOWN)) {
      bssl::UniquePtr<EVP_PKEY> pkey(PEM_read_bio_PUBKEY(in_file.get(), nullptr, nullptr, nullptr));
      if (pkey) {
        rsa.reset(EVP_PKEY_get1_RSA(pkey.get()));
      }
      if (!rsa && BIO_seek(in_file.get(), 0) == 0) {
        rsa.reset(PEM_read_bio_RSA_PUBKEY(in_file.get(), nullptr, nullptr, nullptr));
      }
    }
  } else {
    if (input_format == FORMAT_DER || input_format == FORMAT_UNKNOWN) {
      // OpenSSL prioritizes PKCS#8 PrivateKeyInfo format first.
      bssl::UniquePtr<EVP_PKEY> pkey(d2i_PrivateKey_bio(in_file.get(), nullptr));
      if (pkey) {
        rsa.reset(EVP_PKEY_get1_RSA(pkey.get()));
      }
      if (!rsa && BIO_seek(in_file.get(), 0) == 0) {
        // Try RSAPrivateKey format. OpenSSL's |d2i_PrivateKey_bio| automatically
        // falls back to PKCS1, if PKCS8 is unsuccessful. We have to do things
        // manually here.
        rsa.reset(d2i_RSAPrivateKey_bio(in_file.get(), nullptr));
      }
    }
    if (input_format == FORMAT_PEM || (!rsa && input_format == FORMAT_UNKNOWN)) {
      bssl::UniquePtr<EVP_PKEY> pkey(PEM_read_bio_PrivateKey(in_file.get(), nullptr, nullptr, nullptr));
      if (pkey) {
        rsa.reset(EVP_PKEY_get1_RSA(pkey.get()));
      }
      if (!rsa && BIO_seek(in_file.get(), 0) == 0) {
        rsa.reset(PEM_read_bio_RSAPrivateKey(in_file.get(), nullptr, nullptr, nullptr));
      }
    }
  }

  if (!rsa) {
    fprintf(stderr, "Error: unable to read RSA %s key from '%s'\n",
            pubin ? "public" : "private", in_path.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }

  bssl::UniquePtr<BIO> out_file;
  if (!out_path.empty()) {
    if (!pubout) {
      SetUmaskForPrivateKey();
    }
    out_file.reset(BIO_new_file(out_path.c_str(), "wb"));
  } else {
    out_file.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  }
  if (!out_file) {
    fprintf(stderr, "Error: unable to open output file '%s'\n", out_path.c_str());
    return false;
  }

  // The "rsa" command does not order output based on parameters:
  if (HasArgument(parsed_args, "-modulus")) {
    if (!handleModulus(rsa.get(), out_file.get())) {
      return false;
    }
  }

  if (!noout) {
    bool write_success = false;
    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    if (pkey && EVP_PKEY_set1_RSA(pkey.get(), rsa.get())) {
      fprintf(stderr, "writing RSA key\n");
      if (pubout) {
        // Output public key
        if (output_format == FORMAT_DER) {
          write_success = i2d_PUBKEY_bio(out_file.get(), pkey.get());
        } else {
          write_success = PEM_write_bio_PUBKEY(out_file.get(), pkey.get());
        }
        if (!write_success) {
          fprintf(stderr, "Error: unable to write RSA public key\n");
          ERR_print_errors_fp(stderr);
          return false;
        }
      } else {
        // Output private key
        if (output_format == FORMAT_DER) {
          // For DER output, use PKCS#8 PrivateKeyInfo format to match OpenSSL
          write_success = i2d_PKCS8PrivateKeyInfo_bio(out_file.get(), pkey.get());
        } else {
          write_success = PEM_write_bio_PrivateKey(out_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr);
        }
        if (!write_success) {
          fprintf(stderr, "Error: unable to write RSA private key\n");
          ERR_print_errors_fp(stderr);
          return false;
        }
      }
    }
  }

  return true;
}
