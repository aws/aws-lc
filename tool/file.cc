// Copyright (c) 2017, Google Inc.
// SPDX-License-Identifier: ISC

#include <openssl/bytestring.h>

#include <errno.h>
#include <stdio.h>
#include <string.h>

#include <algorithm>
#include <vector>

#if !defined(OPENSSL_WINDOWS)
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#endif

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

#if !defined(OPENSSL_WINDOWS)
// OpenPrivateFD opens |path| for writing and restricts it to its owner. It
// returns -1 on failure, after printing the reason to stderr.
static int OpenPrivateFD(const std::string &path, bool append) {
  int flags = O_WRONLY | O_CREAT | (append ? O_APPEND : O_TRUNC);
  int fd = open(path.c_str(), flags, 0600);
  if (fd < 0) {
    fprintf(stderr, "Failed to open '%s': %s\n", path.c_str(), strerror(errno));
    return -1;
  }
  // The mode passed to |open| applies to files it creates, so a file that
  // already existed keeps whatever permissions it was given. Devices and pipes
  // have no permissions worth narrowing.
  struct stat st;
  if (fstat(fd, &st) != 0 ||
      (S_ISREG(st.st_mode) && (st.st_mode & 0777) != 0600 &&
       fchmod(fd, 0600) != 0)) {
    fprintf(stderr, "Failed to restrict permissions on '%s': %s\n", path.c_str(),
            strerror(errno));
    close(fd);
    return -1;
  }
  return fd;
}
#endif

ScopedFILE OpenPrivateFile(const std::string &path, bool append) {
#if defined(OPENSSL_WINDOWS)
  // On Windows, file ACLs are inherited from the parent directory.
  ScopedFILE file(fopen(path.c_str(), append ? "ab" : "wb"));
#else
  int fd = OpenPrivateFD(path, append);
  if (fd < 0) {
    return nullptr;
  }
  ScopedFILE file(fdopen(fd, append ? "ab" : "wb"));
  if (!file) {
    close(fd);
  }
#endif
  if (!file) {
    fprintf(stderr, "Failed to open '%s': %s\n", path.c_str(), strerror(errno));
  }
  return file;
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

bool WritePrivateKeyToFile(const std::string &path, const uint8_t *in,
                           size_t in_len) {
#if defined(OPENSSL_WINDOWS)
  // On Windows, fall back to standard write. File ACLs are inherited from the
  // parent directory.
  return WriteToFile(path, in, in_len);
#else
  int fd = OpenPrivateFD(path, /*append=*/false);
  if (fd < 0) {
    return false;
  }
  const uint8_t *ptr = in;
  size_t remaining = in_len;
  while (remaining > 0) {
    ssize_t written = write(fd, ptr, remaining);
    if (written < 0) {
      fprintf(stderr, "Failed to write to '%s': %s\n", path.c_str(),
              strerror(errno));
      close(fd);
      return false;
    }
    ptr += written;
    remaining -= written;
  }
  close(fd);
  return true;
#endif
}
