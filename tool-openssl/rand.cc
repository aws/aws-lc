// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <cstdio>
#include <string>
#include <vector>

#include <openssl/bio.h>
#include <openssl/rand.h>

#include "internal.h"

static const argument_t kArguments[] = {
    {"-help", kBooleanArgument, "Display option summary"},
    {"-base64", kBooleanArgument, "Base64 encode output"},
    {"-hex", kBooleanArgument, "Hex encode output"},
    {"-out", kOptionalArgument, "Output file"},
    {"", kOptionalArgument, ""},
};

int randTool(const args_list_t &args) {
  using namespace ordered_args;
  ordered_args_map_t parsed_args;
  args_list_t extra_args;
  if (!ParseOrderedKeyValueArguments(parsed_args, extra_args, args,
                                     kArguments)) {
    PrintUsage(kArguments);
    return kToolExitFailure;
  }

  if (HasArgument(parsed_args, "-help")) {
    PrintUsage(kArguments);
    return kToolExitSuccess;
  }

  bool base64 = false, hex = false;
  GetBoolArgument(&base64, "-base64", parsed_args);
  GetBoolArgument(&hex, "-hex", parsed_args);

  if (base64 && hex) {
    fprintf(stderr, "error: -base64 and -hex are mutually exclusive\n");
    return kToolExitFailure;
  }

  if (extra_args.empty()) {
    fprintf(stderr, "error: missing num argument\n");
    PrintUsage(kArguments);
    return kToolExitFailure;
  }

  if (extra_args.size() > 1) {
    fprintf(stderr, "error: too many arguments\n");
    PrintUsage(kArguments);
    return kToolExitFailure;
  }

  char *endptr = nullptr;
  unsigned long long num = strtoull(extra_args[0].c_str(), &endptr, 10);
  if (*endptr != '\0' || extra_args[0].empty()) {
    fprintf(stderr, "error: invalid num value '%s'\n", extra_args[0].c_str());
    return kToolExitFailure;
  }

  std::string out_path;
  GetString(&out_path, "-out", "", parsed_args);

  FILE *out_file = stdout;
  if (!out_path.empty()) {
    out_file = fopen(out_path.c_str(), "wb");
    if (out_file == nullptr) {
      fprintf(stderr, "error: cannot open '%s' for writing\n",
              out_path.c_str());
      return kToolExitFailure;
    }
  }

  std::vector<uint8_t> buf(num);
  if (num > 0 && !RAND_bytes(buf.data(), num)) {
    fprintf(stderr, "error: RAND_bytes failed\n");
    if (out_file != stdout) {
      fclose(out_file);
    }
    return kToolExitFailure;
  }

  int ret = kToolExitSuccess;

  if (base64) {
    BIO *bio_out = BIO_new_fp(out_file, BIO_NOCLOSE);
    BIO *b64 = BIO_new(BIO_f_base64());
    if (!bio_out || !b64) {
      BIO_free(bio_out);
      BIO_free(b64);
      fprintf(stderr, "error: failed to create BIO\n");
      ret = kToolExitFailure;
    } else {
      BIO_push(b64, bio_out);
      if (num > 0) {
        BIO_write(b64, buf.data(), static_cast<int>(num));
      }
      BIO_flush(b64);
      BIO_free_all(b64);
    }
  } else if (hex) {
    for (size_t i = 0; i < num; i++) {
      if (fprintf(out_file, "%02x", buf[i]) < 0) {
        ret = kToolExitFailure;
        break;
      }
    }
    if (ret == kToolExitSuccess) {
      fprintf(out_file, "\n");
    }
  } else {
    if (num > 0 && fwrite(buf.data(), 1, num, out_file) != num) {
      ret = kToolExitFailure;
    }
  }

  if (out_file != stdout) {
    fclose(out_file);
  }

  return ret;
}
