// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include <string>
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
