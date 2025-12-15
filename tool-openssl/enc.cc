// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>
#include <stdio.h>
#include <string.h>
#include <algorithm>
#include <iostream>
#include "../tool/internal.h"
#include "internal.h"

#define BUF_SIZE 1024

static const argument_t kArguments[] = {
    // General options
    {"-help", kBooleanArgument, "Display option summary"},
    {"-in", kOptionalArgument, "Input file, default stdin"},
    {"-out", kOptionalArgument, "Output file, default stdout"},
    {"-e", kBooleanArgument, "Encrypt"},
    {"-d", kBooleanArgument, "Decrypt"},
    {"-K", kOptionalArgument, "Raw key to use, in hex form"},
    {"-iv", kOptionalArgument, "IV to use, in hex form"},
    {"-aes-128-cbc", kExclusiveBooleanArgument, "Supported cipher"},
    {"", kOptionalArgument, ""}};

static bool HexToBinary(uint8_t *buffer, const std::string &hex_string,
                        unsigned int size) {
  // First validate that the string contains only valid hex characters
  for (char c : hex_string) {
    if (!OPENSSL_isxdigit(c)) {
      return false;
    }
  }

  if (hex_string.size() != size * 2) {
    return false;
  }

  BIGNUM *raw = NULL;
  if (BN_hex2bn(&raw, hex_string.c_str()) == 0) {
    return false;
  }

  int ret = BN_bn2binpad(raw, buffer, size);
  BN_free(raw);
  return ret != -1;
}

bool encTool(const args_list_t &args) {
  ordered_args::ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ordered_args::ParseOrderedKeyValueArguments(parsed_args, extra_args,
                                                   args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  std::string in_path, out_path, hiv, cipher_name;
  bssl::UniquePtr<std::string> hkey(new std::string);
  bool help = false, e = false, d = false;

  ordered_args::GetBoolArgument(&help, "-help", parsed_args);
  ordered_args::GetString(&in_path, "-in", "", parsed_args);
  ordered_args::GetString(&out_path, "-out", "", parsed_args);
  ordered_args::GetBoolArgument(&e, "-e", parsed_args);
  ordered_args::GetBoolArgument(&d, "-d", parsed_args);
  ordered_args::GetString(hkey.get(), "-K", "", parsed_args);
  ordered_args::GetString(&hiv, "-iv", "", parsed_args);
  ordered_args::GetExclusiveBoolArgument(&cipher_name, kArguments, "",
                                         parsed_args);

  // Display enc tool option summary
  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  // Since we do not implement key generation, a raw key is required
  // TODO: remove/modify if we ever implement -k, -kfile, or -S
  if (hkey->empty()) {
    fprintf(stderr, "Error: A raw key is required\n");
    return false;
  }

  if (e && d) {
    fprintf(stderr, "Error: -e and -d are mutually exclusive\n");
    return false;
  }

  bool enc = true;
  if (d) {
    enc = false;
  }

  // Read from stdin if no -in path provided
  ScopedFILE in_file;
  if (in_path.empty()) {
    in_file.reset(stdin);
  } else {
    in_file.reset(fopen(in_path.c_str(), "rb"));
    if (!in_file) {
      fprintf(stderr, "Error: unable to load data from '%s'\n",
              in_path.c_str());
      return false;
    }
  }

  if (cipher_name.empty()) {
    cipher_name = "aes-128-cbc";
  } else {
    cipher_name = cipher_name.substr(1);
  }
  const EVP_CIPHER *cipher = EVP_get_cipherbyname(cipher_name.c_str());

  if (cipher == nullptr) {
    fprintf(stderr, "Error: Unknown cipher %s\n", cipher_name.c_str());
    return false;
  }

  unsigned int iv_length = EVP_CIPHER_iv_length(cipher);
  uint8_t iv[EVP_MAX_IV_LENGTH];

  if (!hiv.empty()) {
    if (iv_length == 0) {
      fprintf(stderr, "Warning: IV is not used by cipher %s\n",
              cipher_name.c_str());
    } else {
      if (!HexToBinary(iv, hiv, iv_length)) {
        fprintf(stderr, "Error: Invalid hex IV value\n");
        return false;
      }
    }
  } else {
    if (iv_length != 0) {
      fprintf(stderr, "Error: IV is required for cipher %s\n",
              cipher_name.c_str());
      return false;
    }
  }

  uint8_t key[EVP_MAX_KEY_LENGTH];

  if (!hkey->empty()) {
    if (!HexToBinary(key, *hkey, EVP_CIPHER_key_length(cipher))) {
      fprintf(stderr, "Error: Invalid hex key value\n");
      return false;
    }
  }

  bssl::UniquePtr<BIO> output_bio;
  if (out_path.empty()) {
    output_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    output_bio.reset(BIO_new(BIO_s_file()));
    if (1 != BIO_write_filename(output_bio.get(), out_path.c_str())) {
      fprintf(stderr, "Error: unable to write to '%s'\n", out_path.c_str());
      return false;
    }
  }

  // Create and initialize cipher context
  bssl::UniquePtr<EVP_CIPHER_CTX> ctx(EVP_CIPHER_CTX_new());
  if (!EVP_CipherInit_ex(ctx.get(), cipher, nullptr, key, iv, enc)) {
    fprintf(stderr, "Error: Failed to initialize cipher\n");
    return false;
  }

  // Process the input file
  uint8_t inbuf[BUF_SIZE];
  uint8_t outbuf[BUF_SIZE + EVP_MAX_BLOCK_LENGTH];
  int inlen = 0, outlen = 0;

  for (;;) {
    if (feof(in_file.get())) {
      break;
    }

    inlen = fread(inbuf, 1, sizeof(inbuf), in_file.get());

    if (ferror(in_file.get())) {
      fprintf(stderr, "Error reading from '%s'.\n", in_path.c_str());
      return false;
    }

    if (!EVP_CipherUpdate(ctx.get(), outbuf, &outlen, inbuf, inlen)) {
      fprintf(stderr, "Error: Cipher update failed\n");
      return false;
    }
    BIO_write(output_bio.get(), outbuf, outlen);
  }

  // Finalize
  if (!EVP_CipherFinal_ex(ctx.get(), outbuf, &outlen)) {
    fprintf(stderr, "Error: Cipher final failed\n");
    return false;
  }

  BIO_write(output_bio.get(), outbuf, outlen);

  return true;
}
