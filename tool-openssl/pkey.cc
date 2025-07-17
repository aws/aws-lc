// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include "internal.h"
#include <string>

#define FORMAT_PEM 1
#define FORMAT_DER 2

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-in", kOptionalArgument, "Input key file" },
  { "-inform", kOptionalArgument, "Input format (PEM or DER), default PEM" },
  { "-outform", kOptionalArgument, "Output format (PEM or DER), default PEM" },
  { "-out", kOptionalArgument, "Output file, default stdout" },
  { "-pubin", kBooleanArgument, "Read only public components from input" },
  { "-pubout", kBooleanArgument, "Output only public components" },
  { "-noout", kBooleanArgument, "Don't output the key in encoded form" },
  { "-text", kBooleanArgument, "Output key components in plaintext" },
  { "-text_pub", kBooleanArgument, "Output only public key components in plaintext" },
  { "", kOptionalArgument, "" }
};

static bool WritePrivateKey(EVP_PKEY *pkey, bssl::UniquePtr<BIO> &output_bio, int output_format) {
  if (output_format == FORMAT_DER) {
    if (!i2d_PrivateKey_bio(output_bio.get(), pkey)) {
      fprintf(stderr, "Error: error writing private key in DER format\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
  } else {
    if (!PEM_write_bio_PrivateKey(output_bio.get(), pkey, nullptr, nullptr, 0, nullptr, nullptr)) {
      fprintf(stderr, "Error: error writing private key in PEM format\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
  }
  return true;
}

static bool WritePublicKey(EVP_PKEY *pkey, bssl::UniquePtr<BIO> &output_bio, int output_format) {
  if (output_format == FORMAT_DER) {
    if (!i2d_PUBKEY_bio(output_bio.get(), pkey)) {
      fprintf(stderr, "Error: failed to write public key in DER format\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    return true;
  } else if (output_format == FORMAT_PEM) {
    if (!PEM_write_bio_PUBKEY(output_bio.get(), pkey)) {
      fprintf(stderr, "Error: failed to write public key in PEM format\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    return true;
  }

  fprintf(stderr, "Error: unsupported output format\n");
  return false;
}


bool pkeyTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;

  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, out_path, inform, outform;
  bool pubin = false, pubout = false;
  bool noout = false, text = false, textpub = false;
  int input_format = FORMAT_PEM;
  int output_format = FORMAT_PEM;

  GetString(&in_path, "-in", "", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);
  GetString(&inform, "-inform", "", parsed_args);
  GetString(&outform, "-outform", "", parsed_args);
  GetBoolArgument(&pubin, "-pubin", parsed_args);
  GetBoolArgument(&pubout, "-pubout", parsed_args);
  GetBoolArgument(&noout, "-noout", parsed_args);
  GetBoolArgument(&text, "-text", parsed_args);
  GetBoolArgument(&textpub, "-text_pub", parsed_args);

  // Display pkey tool option summary
  if (HasArgument(parsed_args, "-help")) {
    PrintUsage(kArguments);
    return true;
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

  // Check for mutually exclusive options
  if (text && textpub) {
    fprintf(stderr, "Warning: The -text option is ignored with -text_pub\n");
    text = false;
  }

  // -pubout and -text is the same as -text_pub
  if (!textpub && pubout && text) {
    text = false;
    textpub = true;
  }

  // Set up input file
  ScopedFILE in_file;
  if (in_path.empty()) {
    in_file.reset(stdin);
  } else {
    in_file.reset(fopen(in_path.c_str(), "rb"));
    if (!in_file) {
      fprintf(stderr, "Error: unable to load key from '%s'\n", in_path.c_str());
      return false;
    }
  }

  // Set up output BIO
  bssl::UniquePtr<BIO> output_bio;
  if (out_path.empty()) {
    output_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
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

  // Load the key
  bssl::UniquePtr<EVP_PKEY> pkey;
  if (pubin) {
    if (input_format == FORMAT_DER) {
      pkey.reset(d2i_PUBKEY_fp(in_file.get(), nullptr));
    } else {
      pkey.reset(PEM_read_PUBKEY(in_file.get(), nullptr, nullptr, nullptr));
    }
  } else {
    if (input_format == FORMAT_DER) {
      pkey.reset(d2i_PrivateKey_fp(in_file.get(), nullptr));
    } else {
      pkey.reset(PEM_read_PrivateKey(in_file.get(), nullptr, nullptr, nullptr));
    }
  }

  if (!pkey) {
    fprintf(stderr, "Error: error reading %s key from '%s'\n", 
            pubin ? "public" : "private", in_path.empty() ? "stdin" : in_path.c_str());
    ERR_print_errors_fp(stderr);
    return false;
  }

  if (!noout) {
    if (pubout || pubin) {
      if (!WritePublicKey(pkey.get(), output_bio, output_format)) {
        return false;
      }
    } else {
      if (!WritePrivateKey(pkey.get(), output_bio, output_format)) {
        return false;
      }
    }
  }

  if (textpub) {
    if (EVP_PKEY_print_public(output_bio.get(), pkey.get(), 0, nullptr) <= 0) {
      fprintf(stderr, "Error: unable to print public key components\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
  } else if (text) {
    if (EVP_PKEY_print_private(output_bio.get(), pkey.get(), 0, nullptr) <= 0) {
      fprintf(stderr, "Error: unable to print private key components\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
  }

  return true;
}
