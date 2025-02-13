// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include "internal.h"

static const argument_t kArguments[] = {
    { "", kOptionalArgument, "" }
};

bool VersionTool(const args_list_t &args) {
  args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(parsed_args, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }
  printf("%s\n", OPENSSL_VERSION_TEXT);
  return true;
}
