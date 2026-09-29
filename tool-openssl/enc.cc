// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>
#include <openssl/mem.h>
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
    {"-nopad", kBooleanArgument, "Disable standard block padding"},
    {"-none", kBooleanArgument, "Copy input without encryption (default)"},
    {"-K", kOptionalArgument, "Raw key to use, in hex form"},
    {"-iv", kOptionalArgument, "IV to use, in hex form"},
    {"-aes-128-cbc", kBooleanArgument, "Supported cipher"},
    {"-aes-128-cfb", kBooleanArgument, "Supported cipher"},
    {"-aes-128-ctr", kBooleanArgument, "Supported cipher"},
    {"-aes-128-ecb", kBooleanArgument, "Supported cipher"},
    {"-aes-128-ofb", kBooleanArgument, "Supported cipher"},
    {"-aes-192-cbc", kBooleanArgument, "Supported cipher"},
    {"-aes-192-cfb", kBooleanArgument, "Supported cipher"},
    {"-aes-192-ctr", kBooleanArgument, "Supported cipher"},
    {"-aes-192-ecb", kBooleanArgument, "Supported cipher"},
    {"-aes-192-ofb", kBooleanArgument, "Supported cipher"},
    {"-aes-256-cbc", kBooleanArgument, "Supported cipher"},
    {"-aes-256-cfb", kBooleanArgument, "Supported cipher"},
    {"-aes-256-ctr", kBooleanArgument, "Supported cipher"},
    {"-aes-256-ecb", kBooleanArgument, "Supported cipher"},
    {"-aes-256-ofb", kBooleanArgument, "Supported cipher"},
    {"-aes128", kBooleanArgument, "Supported cipher alias"},
    {"-aes256", kBooleanArgument, "Supported cipher alias"},
    {"-des-cbc", kBooleanArgument, "Supported cipher"},
    {"-des-ede3-cbc", kBooleanArgument, "Supported cipher"},
    {"", kOptionalArgument, ""}};

static bool HexToBinary(uint8_t *buffer, const std::string &hex_string,
                        size_t size) {
  const size_t hex_len = 2 * size;
  if (hex_string.size() < hex_len) {
    fprintf(stderr,
            "hex string is too short, padding with zero bytes to length\n");
  } else if (hex_string.size() > hex_len) {
    fprintf(stderr, "hex string is too long, ignoring excess\n");
  }

  // Like OpenSSL, zero-pad on the right (including an odd trailing nibble) and
  // validate only the retained prefix.
  memset(buffer, 0, size);
  for (size_t i = 0; i < std::min(hex_string.size(), hex_len); i++) {
    uint8_t digit;
    if (!OPENSSL_fromxdigit(&digit, hex_string[i])) {
      return false;
    }
    buffer[i / 2] |= static_cast<uint8_t>(digit << (i % 2 == 0 ? 4 : 0));
  }
  return true;
}

int encTool(const args_list_t &args) {
  ordered_args::ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ordered_args::ParseOrderedKeyValueArguments(parsed_args, extra_args,
                                                   args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return kToolExitFailure;
  }

  std::string in_path, out_path, cipher_name;
  Password hex_key, hex_iv;
  bool encode = true, nopad = false, has_key = false, has_iv = false;

  // OpenSSL processes repeated options in order: the last value wins.
  for (const auto &arg : parsed_args) {
    if (arg.first == "-help") {
      PrintUsage(kArguments);
      return kToolExitSuccess;
    } else if (arg.first == "-in") {
      in_path = arg.second;
    } else if (arg.first == "-out") {
      out_path = arg.second;
    } else if (arg.first == "-e" || arg.first == "-d") {
      encode = arg.first == "-e";
    } else if (arg.first == "-nopad") {
      nopad = true;
    } else if (arg.first == "-K") {
      hex_key.get() = arg.second;
      has_key = true;
    } else if (arg.first == "-iv") {
      hex_iv.get() = arg.second;
      has_iv = true;
    } else if (arg.first == "-none") {
      cipher_name.clear();
    } else {
      // All remaining accepted options are cipher names.
      cipher_name = arg.first.substr(1);
    }
  }

  // As in OpenSSL, an absent path or "-" means stdin/stdout.
  ScopedFILE in_file;
  FILE *input = stdin;
  if (!in_path.empty() && in_path != "-") {
    in_file.reset(fopen(in_path.c_str(), "rb"));
    if (!in_file) {
      fprintf(stderr, "Error: unable to load data from '%s'\n",
              in_path.c_str());
      return kToolExitFailure;
    }
    input = in_file.get();
  }

  bssl::UniquePtr<EVP_CIPHER_CTX> ctx;
  if (!cipher_name.empty()) {
    const EVP_CIPHER *cipher = EVP_get_cipherbyname(cipher_name.c_str());
    if (cipher == nullptr) {
      fprintf(stderr, "Error: Unknown cipher %s\n", cipher_name.c_str());
      return kToolExitFailure;
    }
    // Password-based key derivation is unsupported. An empty -K is still a
    // valid (all-zero) key.
    if (!has_key) {
      fprintf(stderr, "Error: A raw key is required\n");
      return kToolExitFailure;
    }

    const size_t iv_length = EVP_CIPHER_iv_length(cipher);
    uint8_t iv[EVP_MAX_IV_LENGTH] = {0};
    if (has_iv) {
      if (iv_length == 0) {
        fprintf(stderr, "Warning: IV is not used by cipher %s\n",
                cipher_name.c_str());
      } else if (!HexToBinary(iv, hex_iv.get(), iv_length)) {
        fprintf(stderr, "Error: Invalid hex IV value\n");
        return kToolExitFailure;
      }
    } else if (iv_length != 0) {
      fprintf(stderr, "Error: IV is required for cipher %s\n",
              cipher_name.c_str());
      return kToolExitFailure;
    }

    uint8_t key[EVP_MAX_KEY_LENGTH];
    if (!HexToBinary(key, hex_key.get(), EVP_CIPHER_key_length(cipher))) {
      OPENSSL_cleanse(key, sizeof(key));
      fprintf(stderr, "Error: Invalid hex key value\n");
      return kToolExitFailure;
    }
    ctx.reset(EVP_CIPHER_CTX_new());
    const bool init_ok =
        ctx && EVP_CipherInit_ex(ctx.get(), cipher, nullptr, key, iv, encode);
    OPENSSL_cleanse(key, sizeof(key));
    if (!init_ok) {
      fprintf(stderr, "Error: Failed to initialize cipher\n");
      return kToolExitFailure;
    }
    if (nopad) {
      EVP_CIPHER_CTX_set_padding(ctx.get(), 0);
    }
  }

  bssl::UniquePtr<BIO> output_bio;
  if (out_path.empty() || out_path == "-") {
    output_bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    output_bio.reset(BIO_new_file(out_path.c_str(), "wb"));
  }
  if (!output_bio) {
    fprintf(stderr, "Error: unable to write to '%s'\n", out_path.c_str());
    return kToolExitFailure;
  }

  // Process the input file
  uint8_t inbuf[BUF_SIZE];
  uint8_t outbuf[BUF_SIZE + EVP_MAX_BLOCK_LENGTH];
  int inlen = 0, outlen = 0;

  for (;;) {
    if (feof(input)) {
      break;
    }

    inlen = fread(inbuf, 1, sizeof(inbuf), input);

    if (ferror(input)) {
      fprintf(stderr, "Error reading from '%s'.\n", in_path.c_str());
      return kToolExitFailure;
    }

    const uint8_t *output = inbuf;
    outlen = inlen;
    if (ctx) {
      if (!EVP_CipherUpdate(ctx.get(), outbuf, &outlen, inbuf, inlen)) {
        fprintf(stderr, "Error: Cipher update failed\n");
        return kToolExitFailure;
      }
      output = outbuf;
    }
    if (!BIO_write_all(output_bio.get(), output, outlen)) {
      fprintf(stderr, "Error: Error writing to '%s'\n", out_path.c_str());
      return kToolExitFailure;
    }
  }

  if (ctx) {
    if (!EVP_CipherFinal_ex(ctx.get(), outbuf, &outlen)) {
      fprintf(stderr, "Error: Cipher final failed\n");
      return kToolExitFailure;
    }
    if (!BIO_write_all(output_bio.get(), outbuf, outlen)) {
      fprintf(stderr, "Error: Error writing to '%s'\n", out_path.c_str());
      return kToolExitFailure;
    }
  }

  if (!BIO_flush(output_bio.get())) {
    fprintf(stderr, "Error: Error writing to '%s'\n", out_path.c_str());
    return kToolExitFailure;
  }

  return kToolExitSuccess;
}
