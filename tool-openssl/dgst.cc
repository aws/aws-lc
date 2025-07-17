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

static bool dgst_file_op(const std::string &filename, const int fd,
                         const EVP_MD *digest) {
  static const size_t kBufSize = 8192;
  std::unique_ptr<uint8_t[]> buf(new uint8_t[kBufSize]);

  bssl::ScopedEVP_MD_CTX ctx;
  if (!EVP_DigestInit_ex(ctx.get(), digest, nullptr)) {
    fprintf(stderr, "Failed to initialize EVP_MD_CTX.\n");
    return false;
  }

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

    if (!EVP_DigestUpdate(ctx.get(), buf.get(), n)) {
      fprintf(stderr, "Failed to update hash.\n");
      return false;
    }
  }

  uint8_t hash[EVP_MAX_MD_SIZE];
  unsigned hash_len;
  if (!EVP_DigestFinal_ex(ctx.get(), hash, &hash_len)) {
    fprintf(stderr, "Failed to finish hash.\n");
    return false;
  }

  // Print digest output. OpenSSL outputs the digest name with files, but not
  // with stdin.
  if (fd != 0) {
    fprintf(stdout, "%s(%s)= ", EVP_MD_get0_name(digest), filename.c_str());
  } else {
    fprintf(stdout, "(%s)= ", filename.c_str());
  };
  for (size_t i = 0; i < hash_len; i++) {
    fprintf(stdout, "%02x", hash[i]);
  }
  fprintf(stdout, "\n");
  return true;
}

static bool hmac_file_op(const std::string &filename, const int fd,
                         const EVP_MD *digest, const char *hmac_key,
                         const size_t hmac_key_len) {
  static const size_t kBufSize = 8192;
  std::unique_ptr<uint8_t[]> buf(new uint8_t[kBufSize]);

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

  // Print HMAC output. OpenSSL outputs the digest name with files, but not
  // with stdin.
  if (fd != 0) {
    fprintf(stdout, "HMAC-%s(%s)= ", EVP_MD_get0_name(digest),
            filename.c_str());
  } else {
    fprintf(stdout, "(%s)= ", filename.c_str());
  };
  for (size_t i = 0; i < expected_mac_len; i++) {
    fprintf(stdout, "%02x", mac[i]);
  }
  fprintf(stdout, "\n");
  return true;
}

static bool dgst_tool_op(const args_list_t &args, const EVP_MD *digest) {
  std::vector<std::string> file_inputs;

  // Default is SHA-256.
  // TODO: Make this customizable when "-digest" is introduced.
  if (digest == nullptr) {
    digest = EVP_sha256();
  }

  // HMAC keys can be empty, but C++ std::string has no way to differentiate
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
        return true;
      } else if (option == "hmac") {
        // Read next argument as key string.
        it++;
        // HMAC allows for empty keys.
        if (it != args.end()) {
          hmac_key = (*it).c_str();
          hmac_key_len = (*it).length();
        } else {
          fprintf(stderr,
                  "dgst: Option -hmac needs a value\n"
                  "dgst: Use -help for summary.\n");
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

  // Use stdin if no files are provided.
  if (file_inputs.empty()) {
    // 0 denotes stdin.
    std::string file_name = "stdin";
    int fd = 0;
    if (hmac_key) {
      if (!hmac_file_op(file_name, fd, digest, hmac_key, hmac_key_len)) {
        return false;
      }
    } else {
      if (!dgst_file_op(file_name, fd, digest)) {
        return false;
      }
    }
    return true;
  }

  // Do the dgst operation on all file inputs.
  for (const auto &file_name : file_inputs) {
    ScopedFD scoped_fd = OpenFD(file_name.c_str(), O_RDONLY | O_BINARY);
    int fd = scoped_fd.get();
    if (hmac_key) {
      if (!hmac_file_op(file_name, fd, digest, hmac_key, hmac_key_len)) {
        return false;
      }
    } else {
      if (!dgst_file_op(file_name, fd, digest)) {
        return false;
      }
    }
  }

  return true;
}

bool dgstTool(const args_list_t &args) { return dgst_tool_op(args, nullptr); }
bool md5Tool(const args_list_t &args) { return dgst_tool_op(args, EVP_md5()); }
