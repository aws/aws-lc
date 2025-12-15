// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This file determines whether `explicit_bzero` is available.
#if !defined(_DEFAULT_SOURCE)
#define _DEFAULT_SOURCE
#endif
#include <strings.h>
#include <string.h>

#define BUF_SIZE 1024
int main(int argc, char **argv) {
  char buffer[BUF_SIZE];
  explicit_bzero(buffer, BUF_SIZE);
  return 0;
}
