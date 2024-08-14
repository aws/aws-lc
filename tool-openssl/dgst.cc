// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <fcntl.h>
#include <string.h>
#include <iostream>

#include <openssl/evp.h>
#include <openssl/hmac.h>
#include "internal.h"

// MD5 command currently only supports stdin
static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-hmac", kOptionalArgument,
     "Create a hashed MAC with the corresponding key"},
    {"", kOptionalArgument, ""}};

static bool dgst_file_op(const std::string &filename, const EVP_MD *digest,
                         const char *hmac_key, const size_t hmac_key_len) {
  ScopedFD scoped_fd = OpenFD(filename.c_str(), O_RDONLY | O_BINARY);
  int fd = scoped_fd.get();

  static const size_t kBufSize = 8192;
  std::unique_ptr<uint8_t[]> buf(new uint8_t[kBufSize]);

  if (hmac_key) {
    bssl::ScopedHMAC_CTX ctx;
    if (!HMAC_Init_ex(ctx.get(), hmac_key, hmac_key_len, digest, nullptr)) {
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

    // Print HMAC output.
    fprintf(stdout, "HMAC-%s(%s)= ", EVP_MD_get0_name(digest),
            filename.c_str());
    for (size_t i = 0; i < expected_mac_len; i++) {
      fprintf(stdout, "%02x", mac[i]);
    }
    fprintf(stdout, "\n");
    return true;
  }


  return false;
}

// Map arguments using tool/args.cc
bool dgstTool(const args_list_t &args) {
  std::vector<std::string> file_inputs;

  // Default is SHA-256.
  // TODO: Make this customizable when "-digest" is introduced.
  const EVP_MD *digest = EVP_sha256();

  // HMAC keys can be empty, but C++ strings have no way to differentiate
  // between null and empty.
  const char *hmac_key = nullptr;
  size_t hmac_key_len = 0;

  auto it = args.begin();
  while (it != args.end()) {
    const std::string &arg = *it;
    if (!arg.empty() && arg[0] != '-') {
      // Any input without a '-' prefix is parsed as a file. This
      // also marks the end of any option input.
      while (it != args.end()) {
        if (!(*it).empty()) {
          file_inputs.push_back(*it);
        }
        it++;
      }
      break;
    }

    if (!arg.empty() && arg[0] == '-') {
      const std::string option = arg.substr(1);
      if (option == "help") {
        PrintUsage(kArguments);
        return false;
      } else if (option == "hmac") {
        // Read next argument as key string.
        it++;
        // HMAC allows for empty keys.
        if (it != args.end()) {
          hmac_key = (*it).c_str();
          hmac_key_len = (*it).length();
        } else {
          fprintf(stderr,
                  "dgst: Option -hmac needs a value\ndgst: Use -help for "
                  "summary.\n");
          return false;
        }
      } else {
        fprintf(stderr, "Unknown option '%s'.\n", option.c_str());
        return false;
      }
    } else {
      // Empty input. OpenSSL continues processing the next file even when
      // provided an invalid file.
      fprintf(stderr, "Failed to read from empty input.");
    }

    // Increment while loop.
    it++;
  }

  if (hmac_key == nullptr) {
    fprintf(stderr, "Only HMAC is supported as of now\n");
    return false;
  }

  if (file_inputs.empty()) {
    fprintf(stderr, "stdin is not supported as of now\n");
    return false;
  };

  // Do the dgst/hmac operation on all file inputs.
  for (const auto &file_input : file_inputs) {
    if (!dgst_file_op(file_input, digest, hmac_key, hmac_key_len)) {
      return false;
    }
  }

  return true;
}
