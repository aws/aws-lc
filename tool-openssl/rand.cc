// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <cerrno>
#include <climits>
#include <cstdio>
#include <string>
#include <vector>

#include <openssl/bio.h>
#include <openssl/rand.h>

#include "internal.h"

static const size_t kMaxRandBytes = 256 * 1024 * 1024;

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

  if (extra_args[0].empty() || extra_args[0][0] == '-') {
    fprintf(stderr, "error: invalid num value '%s'\n", extra_args[0].c_str());
    return kToolExitFailure;
  }

  errno = 0;
  char *endptr = nullptr;
  unsigned long long num = strtoull(extra_args[0].c_str(), &endptr, 10);
  if (*endptr != '\0' || errno == ERANGE) {
    fprintf(stderr, "error: invalid num value '%s'\n", extra_args[0].c_str());
    return kToolExitFailure;
  }

  if (num > kMaxRandBytes) {
    fprintf(stderr, "error: num too large (max %zu)\n", kMaxRandBytes);
    return kToolExitFailure;
  }

  std::string out_path;
  GetString(&out_path, "-out", "", parsed_args);

  ScopedFILE out_scoped;
  FILE *out_file = stdout;
  if (!out_path.empty()) {
    out_scoped.reset(fopen(out_path.c_str(), "wb"));
    if (!out_scoped) {
      fprintf(stderr, "error: cannot open '%s' for writing\n",
              out_path.c_str());
      return kToolExitFailure;
    }
    out_file = out_scoped.get();
  }

  const size_t nbytes = static_cast<size_t>(num);
  std::vector<uint8_t> buf(nbytes);
  if (nbytes > 0 && !RAND_bytes(buf.data(), nbytes)) {
    fprintf(stderr, "error: RAND_bytes failed\n");
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
      if (nbytes > 0) {
        BIO_write(b64, buf.data(), static_cast<int>(nbytes));
      }
      BIO_flush(b64);
      BIO_free_all(b64);
    }
  } else if (hex) {
    for (size_t i = 0; i < nbytes; i++) {
      if (fprintf(out_file, "%02x", buf[i]) < 0) {
        ret = kToolExitFailure;
        break;
      }
    }
    if (ret == kToolExitSuccess) {
      fprintf(out_file, "\n");
    }
  } else {
    if (nbytes > 0 && fwrite(buf.data(), 1, nbytes, out_file) != nbytes) {
      ret = kToolExitFailure;
    }
  }

  return ret;
}
