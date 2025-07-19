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
static const unsigned kMinKeySize = 1;
static const char kKeyArgName[] = "key_size";

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display this summary"},
    {"-out", kOptionalArgument, "Output file to write the key to"},
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

static bool ParseKeySize(const args_list_t &extra_args, unsigned &bits) {
  bits = kDefaultKeySize;

  if (extra_args.empty()) {
    return true;
  }

  ordered_args::ordered_args_map_t temp_args;
  temp_args.push_back(std::make_pair(kKeyArgName, extra_args[0]));

  if (!ordered_args::GetUnsigned(&bits, kKeyArgName, 0, temp_args) ||
      bits < kMinKeySize) {
    fprintf(stderr, "Error: Invalid key size '%s'\n", extra_args[0].c_str());
    return false;
  }

  return true;
}

static bssl::UniquePtr<RSA> GenerateRSAKey(unsigned bits) {
  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> e(BN_new());

  if (!BN_set_word(e.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), bits, e.get(), NULL)) {
    ERR_print_errors_fp(stderr);
    return nullptr;
  }

  return rsa;
}

static bssl::UniquePtr<BIO> CreateOutputBIO(const std::string &out_path) {
  bssl::UniquePtr<BIO> bio;
  if (out_path.empty()) {
    bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
  } else {
    bio.reset(BIO_new_file(out_path.c_str(), "w"));
    if (!bio) {
      fprintf(stderr, "Error: Could not open output file '%s'\n",
              out_path.c_str());
      return nullptr;
    }
  }
  return bio;
}

static bool WriteRSAKeyToBIO(BIO *bio, RSA *rsa) {
  if (!PEM_write_bio_RSAPrivateKey(bio, rsa, NULL, NULL, 0, NULL, NULL)) {
    ERR_print_errors_fp(stderr);
    return false;
  }
  return true;
}

bool genrsaTool(const args_list_t &args) {
  ordered_args::ordered_args_map_t parsed_args;
  args_list_t extra_args{};
  std::string out_path;
  bool help = false;
  bssl::UniquePtr<BIO> bio;

  // Define a cleanup guard that will ensure proper BIO cleanup on all exit paths
  struct BIOCleanupGuard {
    bssl::UniquePtr<BIO>& bio_ref;
    ~BIOCleanupGuard() {
      if (bio_ref && bio_ref.get()) {
        BIO_flush(bio_ref.get());
        // Explicitly reset to ensure file handle is closed
        // This is especially important on Windows
        bio_ref.reset();
      }
    }
  } bio_guard{bio};

  if (!ordered_args::ParseOrderedKeyValueArguments(parsed_args, extra_args,
                                                   args, kArguments)) {
    bio.reset(BIO_new_fp(stderr, BIO_NOCLOSE));
    if (bio) {
      DisplayHelp(bio.get());
    }
    return false;
  }

  ordered_args::GetBoolArgument(&help, "-help", parsed_args);
  ordered_args::GetString(&out_path, "-out", "", parsed_args);

  // Simple validation that numbits is after all options
  // This works because ParseOrderedKeyValueArguments processes args in order
  for (size_t i = 0; i < args.size(); i++) {
    if (i < args.size() - 1 && !extra_args.empty() &&
        args[i] == extra_args[0]) {
      // Found the numbits argument, check if any options come after it
      for (size_t j = i + 1; j < args.size(); j++) {
        if (::IsFlag(args[j])) {
          fprintf(stderr,
                  "Error: Key size must be specified after all options\n");
          fprintf(stderr, "Usage: genrsa [options] numbits\n");
          return false;
        }
      }
      break;
    }
  }

  if (help) {
    bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
    if (!bio) {
      return false;
    }
    DisplayHelp(bio.get());
    return true;
  }

  unsigned bits = 0;
  if (!ParseKeySize(extra_args, bits)) {
    return false;
  }

  bssl::UniquePtr<RSA> rsa = GenerateRSAKey(bits);
  if (!rsa) {
    return false;
  }

  bio = CreateOutputBIO(out_path);
  if (!bio) {
    return false;
  }

  bool result = WriteRSAKeyToBIO(bio.get(), rsa.get());
  return result;
  
  // No need for explicit cleanup - the BIOCleanupGuard's destructor
  // will handle it automatically when the function exits
}
