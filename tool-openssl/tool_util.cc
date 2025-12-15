// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>


#include <string.h>
#include "internal.h"
#if !defined(OPENSSL_WINDOWS)
  #include <sys/stat.h>
#endif

static bool isCharUpperCaseEqual(char a, char b) {
  return ::toupper(a) == ::toupper(b);
}

bool isStringUpperCaseEqual(const std::string &a, const std::string &b) {
  return a.size() == b.size() &&
         std::equal(a.begin(), a.end(), b.begin(), isCharUpperCaseEqual);
}

void SetUmaskForPrivateKey() {
// On Windows, the default behavior for new files is to inherit ACLs from the parent directory,
// and there's no process-wide "mask" to subtract permissions like in POSIX systems.
#if !defined(OPENSSL_WINDOWS)
  umask(0077);
#endif
}

bool ApplyPkeyCtrlString(EVP_PKEY_CTX *ctx, const char *pkeyopt) {
  bssl::UniquePtr<char> stmp(OPENSSL_strdup(pkeyopt));
  if (!stmp) {
    return false;
  }

  char *vtmp = strchr(stmp.get(), ':');
  if (!vtmp) {
    return false;
  }

  *vtmp = 0;
  vtmp++;

  OPENSSL_BEGIN_ALLOW_DEPRECATED
  int result = EVP_PKEY_CTX_ctrl_str(ctx, stmp.get(), vtmp);
  OPENSSL_END_ALLOW_DEPRECATED

  return result == 1;
}
