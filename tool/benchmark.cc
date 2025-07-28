// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"
#include <openssl/opensslv.h>

int main(int argc, char **argv) {
  unsigned long build_version = OPENSSL_VERSION_NUMBER;
  unsigned long runtime_version = SSLeay();
  if (build_version != runtime_version) {
    fprintf(stderr, "Incorrect version number detected, built with %lx, loaded %lx at runtime.", build_version, runtime_version);
    return 1;
  }
  args_list_t args;
  for (int i = 1; i < argc; i++) {
    args.push_back(argv[i]);
  }
  return Speed(args) ? 0 : 1;
}
