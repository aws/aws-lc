// Copyright (c) 2015, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>

#include "internal.h"


static const argument_t kArguments[] = {
    {
     "-bits", kOptionalArgument,
     "The number of bits in the modulus (default: 2048)",
    },
    {
     "", kOptionalArgument, "",
    },
};

bool GenerateRSAKey(const std::vector<std::string> &args) {
  std::map<std::string, std::string> args_map;
  args_list_t extra_args;

  if (!ParseKeyValueArguments(args_map, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  unsigned bits;
  if (!GetUnsigned(&bits, "-bits", 2048, args_map)) {
    PrintUsage(kArguments);
    return false;
  }

  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> e(BN_new());
  bssl::UniquePtr<BIO> bio(BIO_new_fp(stdout, BIO_NOCLOSE));

  if (!BN_set_word(e.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), bits, e.get(), NULL) ||
      !PEM_write_bio_RSAPrivateKey(bio.get(), rsa.get(), NULL /* cipher */,
                                   NULL /* key */, 0 /* key len */,
                                   NULL /* password callback */,
                                   NULL /* callback arg */)) {
    ERR_print_errors_fp(stderr);
    return false;
  }

  return true;
}
