// Copyright (c) 2017, Google Inc.
// SPDX-License-Identifier: ISC

#include <map>
#include <vector>

#include <openssl/bio.h>
#include <openssl/evp.h>
#include <openssl/pem.h>

#include "internal.h"


static const argument_t kArguments[] = {
    {"-key", kRequiredArgument, "The private key, in PEM format, to sign with"},
    {"-digest", kOptionalArgument, "The digest algorithm to use"},
    {"", kOptionalArgument, ""},
};

bool Sign(const args_list_t &args) {
  args_map_t args_map;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(args_map, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  // Load the private key.
  bssl::UniquePtr<BIO> bio(BIO_new(BIO_s_file()));
  if (!bio || !BIO_read_filename(bio.get(), args_map["-key"].c_str())) {
    return false;
  }
  bssl::UniquePtr<EVP_PKEY> key(
      PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, nullptr));
  if (!key) {
    return false;
  }

  const EVP_MD *md = nullptr;
  if (args_map.count("-digest")) {
    md = EVP_get_digestbyname(args_map["-digest"].c_str());
    if (md == nullptr) {
      fprintf(stderr, "Unknown digest algorithm: %s\n",
              args_map["-digest"].c_str());
      return false;
    }
  }

  bssl::ScopedEVP_MD_CTX ctx;
  if (!EVP_DigestSignInit(ctx.get(), nullptr, md, nullptr, key.get())) {
    return false;
  }

  std::vector<uint8_t> data;
  if (!ReadAll(&data, stdin)) {
    fprintf(stderr, "Error reading input.\n");
    return false;
  }

  size_t sig_len = EVP_PKEY_size(key.get());
  std::unique_ptr<uint8_t[]> sig(new uint8_t[sig_len]);
  if (!EVP_DigestSign(ctx.get(), sig.get(), &sig_len, data.data(),
                      data.size())) {
    return false;
  }

  if (fwrite(sig.get(), 1, sig_len, stdout) != sig_len) {
    fprintf(stderr, "Error writing signature.\n");
    return false;
  }

  return true;
}
