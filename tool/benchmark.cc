// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "internal.h"

int main(int argc, char **argv) {
  args_list_t args;
  for (int i = 1; i < argc; i++) {
    args.push_back(argv[i]);
  }
  return Speed(args) ? 0 : 1;
}
