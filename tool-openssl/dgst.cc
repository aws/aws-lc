// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <fcntl.h>
#include <iostream>
#include <string.h>

#include <openssl/evp.h>
#include <openssl/hmac.h>
#include "internal.h"

#if !defined(O_BINARY)
#define O_BINARY 0
#endif

// MD5 command currently only supports stdin
static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-hmac", kOptionalArgument, "Create a hashed MAC with the corresponding key" },
  { "", kOptionalArgument, "" }
};

static bool dgst_file_op(BIO *out, std::string filename, const EVP_MD *digest, std::string hmac_key) {
  ScopedFD scoped_fd = OpenFD(filename.c_str(), O_RDONLY | O_BINARY);
  int fd = scoped_fd.get();

  static const size_t kBufSize = 8192;
  std::unique_ptr<uint8_t[]> buf(new uint8_t[kBufSize]);

  if (!hmac_key.empty()) {
    bssl::ScopedHMAC_CTX ctx;
    if (!HMAC_Init_ex(ctx.get(), hmac_key.data(), hmac_key.size(), digest,
                      nullptr)) {
      fprintf(stderr, "Failed to initialize HMAC_Init_ex.\n");
      return false;
    }

    // Update |buf| from file continuously.
    for (;;) {
      size_t n;
      if (!ReadFromFD(fd, &n, buf.get(), kBufSize)) {
        fprintf(stderr, "Failed to read from %s: %s\n", filename.c_str(),
                strerror(errno));
        return false;
      }

      if (n == 0) {
        break;
      }

      if (!HMAC_Update(ctx.get(), buf.get(), n)) {
        fprintf(stderr, "Failed to update HMAC.\n");
        return false;
      }
    }

    const unsigned expected_mac_len = EVP_MD_size(digest);
    std::unique_ptr<uint8_t[]> mac(new uint8_t[expected_mac_len]);
    unsigned mac_len;
    if (!HMAC_Final(ctx.get(), mac.get(), &mac_len)) {
      fprintf(stderr, "Failed to finalize HMAC.\n");
      return false;
    }

    for (size_t i = 0; i < expected_mac_len; i++) {
      printf("%02x", mac[i]);
    }
    printf("\n");
    return true;
  }


  return false;
}

// Map arguments using tool/args.cc
bool dgstTool(const args_list_t &args) {
  args_map_t parsed_args;
  if (!ParseKeyValueArguments(&parsed_args, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  bool help = false;
  std::string hmac_key_string;
  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&hmac_key_string, "-hmac", "", parsed_args);

  // Default is SHA-256.
  // TODO: Make this customizable when "-digest" is introduced.
  const EVP_MD *digest = EVP_sha256();

  if (help) {
    PrintUsage(kArguments);
    return false;
  }

  if(hmac_key_string.empty()) {
    fprintf(stderr, "Only HMAC is supported as of now\n");
    return false;
  }

  // TODO: This needs to be massaged to take file names directly
  // See ../tool/digest.cc's |DigestSum|.
  if(!dgst_file_op(nullptr, "API-CONVENTIONS.md", digest, hmac_key_string)){
    return false;
  }

  return true;
}
