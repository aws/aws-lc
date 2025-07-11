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

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display this summary"},
    {"-out", kOptionalArgument, "Output file to write the key to"},
    {"", kOptionalArgument, ""}};

// Helper function to find an option in the kArguments array by name
static const argument_t* FindOptionByName(const char* option_name) {
  for (size_t i = 0; kArguments[i].name[0] != '\0' || i == 0; i++) {
    if (strcmp(kArguments[i].name, option_name) == 0) {
      return &kArguments[i];
    }
  }
  return nullptr; // Return nullptr if option not found
}

static void DisplayHelp(BIO *bio) {
  BIO_printf(bio, "Usage: genrsa [options] numbits\n\n");

  BIO_printf(bio, "General options:\n");
  const argument_t* help_option = FindOptionByName("-help");
  if (help_option) {
    BIO_printf(bio, " -help               %s\n\n", help_option->description);
  }

  BIO_printf(bio, "Output options:\n");
  const argument_t* out_option = FindOptionByName("-out");
  if (out_option) {
    BIO_printf(bio, " -out outfile        %s\n\n", out_option->description);
  }

  BIO_printf(bio, "Parameters:\n");
  BIO_printf(bio, " numbits             Size of key in bits (default: %u)\n",
             kDefaultKeySize);
}

static bool ValidateArgumentOrder(
    const args_list_t &args,
    const ordered_args::ordered_args_map_t &parsed_args,
    const args_list_t &extra_args) {
  if (extra_args.empty() || parsed_args.empty()) {
    return true;
  }

  size_t numbits_pos = SIZE_MAX;
  for (size_t i = 0; i < args.size(); i++) {
    if (args[i] == extra_args[0]) {
      numbits_pos = i;
      break;
    }
  }

  size_t last_option_pos = 0;
  for (const auto &parsed_arg : parsed_args) {
    for (size_t i = 0; i < args.size(); i++) {
      if (args[i] == parsed_arg.first) {
        size_t option_end_pos = i;
        if (!parsed_arg.second.empty()) {
          option_end_pos = i + 1;
        }
        last_option_pos = std::max(last_option_pos, option_end_pos);
        break;
      }
    }
  }

  if (numbits_pos != SIZE_MAX && numbits_pos < last_option_pos) {
    fprintf(stderr, "Error: Key size must be specified after all options\n");
    fprintf(stderr, "Usage: genrsa [options] numbits\n");
    return false;
  }

  return true;
}

static bool ParseKeySize(const args_list_t &extra_args, unsigned &bits) {
  bits = kDefaultKeySize;

  if (extra_args.empty()) {
    return true;
  }

  const std::string &bits_str = extra_args[0];
  char *endptr = nullptr;
  unsigned long parsed_bits = strtoul(bits_str.c_str(), &endptr, 10);

  if (*endptr != '\0' || parsed_bits == 0 || parsed_bits > UINT_MAX) {
    fprintf(stderr, "Error: Invalid key size '%s'\n", bits_str.c_str());
    return false;
  }

  bits = static_cast<unsigned>(parsed_bits);
  return true;
}

static bool ParseArguments(const args_list_t &args,
                           ordered_args::ordered_args_map_t &parsed_args,
                           args_list_t &extra_args, std::string &out_path,
                           bool &help) {
  if (!ordered_args::ParseOrderedKeyValueArguments(parsed_args, extra_args,
                                                   args, kArguments)) {
    return false;
  }

  ordered_args::GetBoolArgument(&help, "-help", parsed_args);
  ordered_args::GetString(&out_path, "-out", "", parsed_args);

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

  auto cleanup = [&bio]() {
    if (bio && bio.get()) {
      BIO_flush(bio.get());
    }
  };

  if (!ParseArguments(args, parsed_args, extra_args, out_path, help)) {
    bio.reset(BIO_new_fp(stderr, BIO_NOCLOSE));
    if (bio) {
      DisplayHelp(bio.get());
    }
    return false;
  }

  if (help) {
    bio.reset(BIO_new_fp(stdout, BIO_NOCLOSE));
    if (!bio) {
      return false;
    }
    DisplayHelp(bio.get());
    return true;
  }

  if (!ValidateArgumentOrder(args, parsed_args, extra_args)) {
    return false;
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

  cleanup();

  return result;
}
