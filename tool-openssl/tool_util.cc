// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include <string>

static bool isCharUpperCaseEqual(char a, char b) {
  return ::toupper(a) == ::toupper(b);
}

bool isStringUpperCaseEqual(const std::string &a, const std::string &b) {
  return a.size() == b.size() &&
         std::equal(a.begin(), a.end(), b.begin(), isCharUpperCaseEqual);
}
