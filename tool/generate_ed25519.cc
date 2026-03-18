// Copyright (c) 2015, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/curve25519.h>

#include <errno.h>
#include <stdio.h>
#include <string.h>

#include "internal.h"


static const argument_t kArguments[] = {
    {
        "-out-public", kRequiredArgument, "The file to write the public key to",
    },
    {
        "-out-private", kRequiredArgument,
        "The file to write the private key to",
    },
    {
        "", kOptionalArgument, "",
    },
};

bool GenerateEd25519Key(const std::vector<std::string> &args) {
  std::map<std::string, std::string> args_map;
  args_list_t extra_args;

  if (!ParseKeyValueArguments(args_map, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  uint8_t public_key[32], private_key[64];
  ED25519_keypair(public_key, private_key);

  return WriteToFile(args_map["-out-public"], public_key, sizeof(public_key)) &&
         WriteToFile(args_map["-out-private"], private_key,
                     sizeof(private_key));
}
