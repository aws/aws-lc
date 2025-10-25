// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <cstdlib>
#include <cstring>
#include "internal.h"

static const unsigned kDefaultKeySize = 2048;
static const unsigned kMinKeySize = 1024;
static const unsigned kRecommendedMaxKeySize = 16384;
static const char kKeyArgName[] = "key_size";

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display this summary"},
    {"-out", kOptionalArgument, "Output file to write the key to"},
    {"-aes128", kBooleanArgument, "Encrypt the private key with AES-128-CBC"},
    {"-aes192", kBooleanArgument, "Encrypt the private key with AES-192-CBC"},
    {"-aes256", kBooleanArgument, "Encrypt the private key with AES-256-CBC"},
    {"-des3", kBooleanArgument, "Encrypt the private key with DES3"},
    {"-passout", kOptionalArgument, "Output file pass phrase source"},
    {"", kOptionalArgument, ""}};

static void DisplayHelp(BIO *bio) {
  BIO_printf(bio, "Usage: genrsa [options] numbits\n\n");
  BIO_printf(bio, "Options:\n");

  for (size_t i = 0; kArguments[i].name[0] != '\0'; i++) {
    BIO_printf(bio, " %-20s %s\n", kArguments[i].name,
               kArguments[i].description);
  }
  BIO_printf(bio, "\n numbits  Size of key in bits (default: %u)\n",
             kDefaultKeySize);
}

static bool ParseKeySize(const args_list_t &extra_args, unsigned &KeySizeBits) {
  KeySizeBits = kDefaultKeySize;

  if (extra_args.empty()) {
    return true;
  }

  if (extra_args.size() > 1) {
    fprintf(stderr, "Error: Only one key size argument allowed\n");
    return false;
  }

  ordered_args::ordered_args_map_t temp_args;
  temp_args.push_back(std::make_pair(kKeyArgName, extra_args[0]));

  if (!ordered_args::GetUnsigned(&KeySizeBits, kKeyArgName, 0, temp_args)) {
    fprintf(stderr, "Error: Invalid key size '%s'\n", extra_args[0].c_str());
    return false;
  }

  if (KeySizeBits < kMinKeySize) {
    fprintf(stderr, "Error: Key size must be at least %u bits\n", kMinKeySize);
    return false;
  }

  if (KeySizeBits > kRecommendedMaxKeySize) {
    fprintf(stderr, "Warning: It is not recommended to use more than %u bits for RSA keys.\n", kRecommendedMaxKeySize);
    fprintf(stderr, "         Your key size is %u! Larger key sizes may not behave as expected.\n", KeySizeBits);
  }

  return true;
}

static bssl::UniquePtr<EVP_PKEY> GenerateRSAKey(unsigned bits) {
  bssl::UniquePtr<EVP_PKEY> pkey;
  EVP_PKEY *raw_pkey = nullptr;
  bssl::UniquePtr<EVP_PKEY_CTX> ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_RSA, nullptr));
  if (!ctx || !EVP_PKEY_keygen_init(ctx.get()) ||
      !EVP_PKEY_CTX_set_rsa_keygen_bits(ctx.get(), bits)) {
    return pkey;
  }

  if (!EVP_PKEY_keygen(ctx.get(), &raw_pkey)) {
    return pkey;
  }

  pkey.reset(raw_pkey);
  return pkey;
}

static bssl::UniquePtr<BIO> CreateOutputBIO(const std::string &out_path) {
  bssl::UniquePtr<BIO> bio;
  if (out_path.empty()) {
    bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
    if (!bio) {
      fprintf(stderr, "Error: Could not create BIO for stdout\n");
      return nullptr;
    }
  } else {
    bio.reset(BIO_new_file(out_path.c_str(), "wb"));
    if (!bio) {
      fprintf(stderr, "Error: Could not open output file '%s'\n",
              out_path.c_str());
      return nullptr;
    }
  }
  return bio;
}

bool genrsaTool(const args_list_t &args) {
  ordered_args::ordered_args_map_t parsed_args;
  args_list_t extra_args{};
  std::string out_path;
  bool help = false, aes128 = false, aes192 = false, aes256 = false, des3 = false;
  bssl::UniquePtr<std::string> passout_arg(new std::string());
  bssl::UniquePtr<BIO> bio;
  bssl::UniquePtr<EVP_PKEY> pkey;
  unsigned KeySizeBits = 0;
  const EVP_CIPHER *cipher = NULL;
  const char *password = NULL;
  int password_len = 0;
  int cipher_count = 0;

  // Parse command line arguments
  if (!ordered_args::ParseOrderedKeyValueArguments(parsed_args, extra_args,
                                                   args, kArguments)) {
    bio.reset(BIO_new_fp(stderr, BIO_NOCLOSE));
    if (bio) {
      DisplayHelp(bio.get());
    }
    goto err;
  }

  ordered_args::GetBoolArgument(&help, "-help", parsed_args);
  ordered_args::GetString(&out_path, "-out", "", parsed_args);
  ordered_args::GetBoolArgument(&aes128, "-aes128", parsed_args);
  ordered_args::GetBoolArgument(&aes192, "-aes192", parsed_args);
  ordered_args::GetBoolArgument(&aes256, "-aes256", parsed_args);
  ordered_args::GetBoolArgument(&des3, "-des3", parsed_args);
  ordered_args::GetString(passout_arg.get(), "-passout", "", parsed_args);

  // Parse and validate key size first (catches multiple key sizes)
  if (!ParseKeySize(extra_args, KeySizeBits)) {
    goto err;
  }

  // Simple validation that numbits is the last argument
  if (!extra_args.empty() && args[args.size()-1] != extra_args[0]) {
    fprintf(stderr,
            "Error: Key size must be specified after all options\n");
    fprintf(stderr, "Usage: genrsa [options] numbits\n");
    goto err;
  }

  // Handle help request
  if (help) {
    bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
    if (!bio) {
      goto err;
    }
    DisplayHelp(bio.get());
    return true;  // Help display is a successful exit
  }

  if (!passout_arg->empty()) {
    if (!pass_util::ExtractPassword(passout_arg)) {
      fprintf(stderr, "Error: Failed to extract password\n");
      goto err;
    }
  }

  // Set up output BIO
  bio = CreateOutputBIO(out_path);
  if (!bio) {
    goto err;
  }

  // Generate RSA key
  pkey = GenerateRSAKey(KeySizeBits);
  if (!pkey) {
    fprintf(stderr, "Error: Failed to generate RSA key\n");
    goto err;
  }

  // Cipher selection and mutual exclusion validation
  cipher_count = aes128 + aes192 + aes256 + des3;
  if (cipher_count > 1) {
    fprintf(stderr, "Error: Only one encryption cipher may be specified\n");
    goto err;
  }

  if (aes128) {
    cipher = EVP_get_cipherbyname("aes-128-cbc");
  } else if (aes192) {
    cipher = EVP_get_cipherbyname("aes-192-cbc");
  } else if (aes256) {
    cipher = EVP_get_cipherbyname("aes-256-cbc");
  } else if (des3) {
    cipher = EVP_get_cipherbyname("des-ede3-cbc");
  } else {
    cipher = NULL;
  }

  // Write the key with optional encryption
  password = (!passout_arg->empty()) ? passout_arg->c_str() : NULL;
  password_len = (!passout_arg->empty()) ? static_cast<int>(passout_arg->length()) : 0;
  
  if (!PEM_write_bio_PrivateKey(bio.get(), pkey.get(), cipher,
                                (unsigned char*)password, password_len,
                                NULL, NULL)) {
    goto err;
  }

  // Flush output
  if (!BIO_flush(bio.get())) {
    goto err;
  }

  return true;

err:
  ERR_print_errors_fp(stderr);
  if (bio) {
    BIO_flush(bio.get());
  }
  return false;
}
