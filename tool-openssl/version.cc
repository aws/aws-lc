// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif
#include <inttypes.h>

#include <openssl/base.h>
#include <openssl/crypto.h>
#include "internal.h"

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-a", kBooleanArgument, "Print all version information"},
    {"-p", kBooleanArgument, "Print platform"},
    {"-fips", kBooleanArgument, "Print FIPS status and module version"},
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
  bool fips = false;
  GetBoolArgument(&all, "-a", parsed_args);
  GetBoolArgument(&platform, "-p", parsed_args);
  GetBoolArgument(&fips, "-fips", parsed_args);

  if (platform) {
    printf("%s\n", OpenSSL_version(OPENSSL_PLATFORM));
    return true;
  }

  printf("%s\n", OPENSSL_VERSION_TEXT);

  if (all) {
    // The fields below are hard-coded "n/a" compatibility placeholders: AWS-LC
    // does not track build-time metadata the way OpenSSL does, so OpenSSL_version
    // returns fixed strings for them.
    printf("%s\n", OpenSSL_version(OPENSSL_BUILT_ON));
    printf("%s\n", OpenSSL_version(OPENSSL_PLATFORM));
    printf("%s\n", OpenSSL_version(OPENSSL_CFLAGS));
    printf("%s\n", OpenSSL_version(OPENSSL_DIR));
    return true;
  }

  if (fips) {
    if (FIPS_mode()) {
      printf("FIPS: enabled\n");
      printf("FIPS module version: %" PRIu32 "\n", FIPS_version());
    } else {
      printf("FIPS: disabled\n");
    }
    return true;
  }

  return true;
}
