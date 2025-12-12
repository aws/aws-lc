// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// This file determines whether `explicit_bzero` is available.
#include <string.h>

#define BUF_SIZE 1024;
int main() {
  char buffer[BUF_SIZE];
  explicit_bzero(buffer, BUF_SIZE);
  return 0;
}
