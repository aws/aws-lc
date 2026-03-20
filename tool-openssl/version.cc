// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include <openssl/crypto.h>
#include "internal.h"

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-a", kBooleanArgument, "Print all version information"},
    {"-p", kBooleanArgument, "Print platform"},
    {"", kOptionalArgument, ""}
};

bool VersionTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args,
                                     kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  if (HasArgument(parsed_args, "-help")) {
    PrintUsage(kArguments);
    return true;
  }

  bool all = false;
  bool platform = false;
  GetBoolArgument(&all, "-a", parsed_args);
  GetBoolArgument(&platform, "-p", parsed_args);

  if (all) {
    printf("%s\n", OPENSSL_VERSION_TEXT);
    printf("%s\n", OpenSSL_version(OPENSSL_BUILT_ON));
    printf("%s\n", OpenSSL_version(OPENSSL_PLATFORM));
    printf("%s\n", OpenSSL_version(OPENSSL_CFLAGS));
    printf("%s\n", OpenSSL_version(OPENSSL_DIR));
    return true;
  }

  if (platform) {
    printf("%s\n", OpenSSL_version(OPENSSL_PLATFORM));
    return true;
  }

  printf("%s\n", OPENSSL_VERSION_TEXT);
  return true;
}
