// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <cerrno>
#include <climits>
#include <cstdio>
#include <cstring>
#include <string>

#include <openssl/bio.h>
#include <openssl/rand.h>

#include "internal.h"

static const size_t kChunkSize = 65536;

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

  const std::string format =
      GetLastOption({"-base64", "-hex"}, "", parsed_args);
  const bool base64 = format == "-base64";
  const bool hex = format == "-hex";

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

  const char *num_str = extra_args[0].c_str();
  while (*num_str == ' ' || *num_str == '\t' || *num_str == '\n' ||
         *num_str == '\r' || *num_str == '\f' || *num_str == '\v') {
    num_str++;
  }
  if (*num_str == '\0' || *num_str == '-') {
    fprintf(stderr, "error: invalid num value '%s'\n", extra_args[0].c_str());
    return kToolExitFailure;
  }

  errno = 0;
  char *endptr = nullptr;
  unsigned long long num = strtoull(num_str, &endptr, 0);
  if (*endptr != '\0' || errno == ERANGE || num == 0) {
    fprintf(stderr, "error: invalid num value '%s'\n", extra_args[0].c_str());
    return kToolExitFailure;
  }

  std::string out_path;
  GetLastString(&out_path, "-out", "", parsed_args);

  ScopedFILE out_scoped;
  FILE *out_file = stdout;
  if (!out_path.empty() && out_path != "-") {
    out_scoped.reset(fopen(out_path.c_str(), "wb"));
    if (!out_scoped) {
      fprintf(stderr, "error: cannot open '%s' for writing\n",
              out_path.c_str());
      return kToolExitFailure;
    }
    out_file = out_scoped.get();
  }

  int ret = kToolExitSuccess;
  uint8_t chunk[kChunkSize];
  unsigned long long remaining = num;

  if (base64) {
    int bio_close = out_scoped ? BIO_CLOSE : BIO_NOCLOSE;
    BIO *bio_out = BIO_new_fp(out_file, bio_close);
    if (bio_out && out_scoped) {
      out_scoped.release();
    }
    BIO *b64 = BIO_new(BIO_f_base64());
    if (!bio_out || !b64) {
      BIO_free(bio_out);
      BIO_free(b64);
      if (bio_close == BIO_CLOSE) {
        out_file = nullptr;
      }
      fprintf(stderr, "error: failed to create BIO\n");
      ret = kToolExitFailure;
    } else {
      BIO_push(b64, bio_out);
      while (remaining > 0 && ret == kToolExitSuccess) {
        size_t n = remaining < kChunkSize ? static_cast<size_t>(remaining)
                                          : kChunkSize;
        if (!RAND_bytes(chunk, n)) {
          fprintf(stderr, "error: RAND_bytes failed\n");
          ret = kToolExitFailure;
          break;
        }
        if (!BIO_write_all(b64, chunk, n)) {
          fprintf(stderr, "error: failed to write output: %s\n",
                  strerror(errno));
          ret = kToolExitFailure;
          break;
        }
        remaining -= n;
      }
      if (ret == kToolExitSuccess && BIO_flush(b64) != 1) {
        fprintf(stderr, "error: failed to flush output: %s\n", strerror(errno));
        ret = kToolExitFailure;
      }
      BIO_free_all(b64);
      if (bio_close == BIO_CLOSE) {
        out_file = nullptr;
      }
    }
  } else if (hex) {
    while (remaining > 0 && ret == kToolExitSuccess) {
      size_t n = remaining < kChunkSize ? static_cast<size_t>(remaining)
                                        : kChunkSize;
      if (!RAND_bytes(chunk, n)) {
        fprintf(stderr, "error: RAND_bytes failed\n");
        ret = kToolExitFailure;
        break;
      }
      for (size_t i = 0; i < n; i++) {
        if (fprintf(out_file, "%02x", chunk[i]) < 0) {
          fprintf(stderr, "error: failed to write output: %s\n",
                  strerror(errno));
          ret = kToolExitFailure;
          break;
        }
      }
      remaining -= n;
    }
    if (ret == kToolExitSuccess && fprintf(out_file, "\n") < 0) {
      fprintf(stderr, "error: failed to write output: %s\n", strerror(errno));
      ret = kToolExitFailure;
    }
  } else {
    while (remaining > 0 && ret == kToolExitSuccess) {
      size_t n = remaining < kChunkSize ? static_cast<size_t>(remaining)
                                        : kChunkSize;
      if (!RAND_bytes(chunk, n)) {
        fprintf(stderr, "error: RAND_bytes failed\n");
        ret = kToolExitFailure;
        break;
      }
      if (fwrite(chunk, 1, n, out_file) != n) {
        fprintf(stderr, "error: failed to write output: %s\n", strerror(errno));
        ret = kToolExitFailure;
        break;
      }
      remaining -= n;
    }
  }

  if (out_file && ret == kToolExitSuccess && fflush(out_file) != 0) {
    fprintf(stderr, "error: failed to flush output: %s\n", strerror(errno));
    ret = kToolExitFailure;
  }

  return ret;
}
