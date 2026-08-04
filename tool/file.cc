// Copyright (c) 2017, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/bytestring.h>

#include <errno.h>
#include <stdio.h>
#include <string.h>

#include <algorithm>
#include <vector>

#include "internal.h"


bool ReadAll(std::vector<uint8_t> *out, FILE *file) {
  out->clear();

  constexpr size_t kMaxSize = 1024 * 1024;
  size_t len = 0;
  out->resize(128);

  for (;;) {
    len += fread(out->data() + len, 1, out->size() - len, file);

    if (feof(file)) {
      out->resize(len);
      return true;
    }
    if (ferror(file)) {
      return false;
    }

    if (len == out->size()) {
      if (out->size() == kMaxSize) {
        fprintf(stderr, "Input too large.\n");
        return false;
      }
      size_t cap = std::min(out->size() * 2, kMaxSize);
      out->resize(cap);
    }
  }
}

bool WriteToFile(const std::string &path, const uint8_t *in,
                        size_t in_len) {
  ScopedFILE file(fopen(path.c_str(), "wb"));
  if (!file) {
    fprintf(stderr, "Failed to open '%s': %s\n", path.c_str(), strerror(errno));
    return false;
  }
  if (fwrite(in, in_len, 1, file.get()) != 1) {
    fprintf(stderr, "Failed to write to '%s': %s\n", path.c_str(),
            strerror(errno));
    return false;
  }
  return true;
}
