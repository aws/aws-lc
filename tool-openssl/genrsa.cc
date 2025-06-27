// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <iostream>
#include "internal.h"

static const argument_t kArguments[] = {
  { "-help", kBooleanArgument, "Display option summary" },
  { "-out", kOptionalArgument, "Output file to write the key to" },
  { "", kOptionalArgument, "Key size in bits (default: 2048)" }
};

bool genrsaTool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments)) {
    PrintUsage(kArguments);
    return false;
  }

  std::string out_path;
  bool help = false;
  
  GetBoolArgument(&help, "-help", parsed_args);
  GetString(&out_path, "-out", "", parsed_args);

  if (help) {
    PrintUsage(kArguments);
    return true;
  }

  std::cout << "genrsa: Barebones implementation - Options detected:" << std::endl;
  
  if (!out_path.empty()) {
    std::cout << "  -out: " << out_path << std::endl;
  }
  
  if (!extra_args.empty()) {
    std::cout << "  key_size: " << extra_args[0] << std::endl;
  } else {
    std::cout << "  key_size: 2048 (default)" << std::endl;
  }
  
  return true;
}
