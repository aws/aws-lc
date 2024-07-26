// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/md5.h>
#include <iostream>
#include "internal.h"

// MD5 command currently only supports stdin
static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "", kOptionalArgument, "" }
};

// Map arguments using tool/args.cc
bool md5Tool(const args_list_t &args) {
  args_map_t parsed_args;
  if (!ParseKeyValueArguments(&parsed_args, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  bool help = false;
  GetBoolArgument(&help, "-help", parsed_args);

  if (help) {
    PrintUsage(kArguments);
    return false;
  }

  // Read input from stdin
  std::string input;
  std::getline(std::cin, input);

  if (input.empty()) {
    fprintf(stderr, "Error: no input provided\n");
    return false;
  }

  unsigned char md5_digest[MD5_DIGEST_LENGTH];
  MD5(reinterpret_cast<const unsigned char*>(input.c_str()), input.length(), md5_digest);

  printf("MD5(stdin)= ");
  for (int i = 0; i < MD5_DIGEST_LENGTH; ++i) {
    printf("%02x", md5_digest[i]);
  }
  printf("\n");

  return true;
}

