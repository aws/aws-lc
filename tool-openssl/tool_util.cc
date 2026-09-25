// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/bio.h>
#include <openssl/evp.h>


#include <string.h>
#include "internal.h"

static bool isCharUpperCaseEqual(char a, char b) {
  return ::toupper(a) == ::toupper(b);
}

bool isStringUpperCaseEqual(const std::string &a, const std::string &b) {
  return a.size() == b.size() &&
         std::equal(a.begin(), a.end(), b.begin(), isCharUpperCaseEqual);
}

bssl::UniquePtr<BIO> NewPrivateFileBIO(const std::string &path) {
  ScopedFILE file = OpenPrivateFile(path);
  if (!file) {
    return nullptr;
  }
  bssl::UniquePtr<BIO> bio(BIO_new_fp(file.get(), BIO_CLOSE));
  if (bio == nullptr) {
    fprintf(stderr, "Error: failed to open output file '%s'\n", path.c_str());
    return nullptr;
  }
  file.release();
  return bio;
}

bool ApplyPkeyCtrlString(EVP_PKEY_CTX *ctx, const char *pkeyopt) {
  bssl::UniquePtr<char> stmp(OPENSSL_strdup(pkeyopt));
  if (!stmp) {
    return false;
  }

  // The OpenSSL algorithm options are defined using the pattern "opt:value".
  char *vtmp = strchr(stmp.get(), ':');
  if (!vtmp) {
    return false;
  }

  *vtmp = '\0';
  vtmp++;

  OPENSSL_BEGIN_ALLOW_DEPRECATED
  int result = EVP_PKEY_CTX_ctrl_str(ctx, stmp.get(), vtmp);
  OPENSSL_END_ALLOW_DEPRECATED

  return result == 1;
}
