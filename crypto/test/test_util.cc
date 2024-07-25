/* Copyright (c) 2015, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include "test_util.h"

#include <ostream>

#include "../internal.h"
#include "openssl/pem.h"


void hexdump(FILE *fp, const char *msg, const void *in, size_t len) {
  const uint8_t *data = reinterpret_cast<const uint8_t *>(in);

  fputs(msg, fp);
  for (size_t i = 0; i < len; i++) {
    fprintf(fp, "%02x", data[i]);
  }
  fputs("\n", fp);
}

std::ostream &operator<<(std::ostream &os, const Bytes &in) {
  if (in.span_.empty()) {
    return os << "<empty Bytes>";
  }

  // Print a byte slice as hex.
  os << EncodeHex(in.span_);
  return os;
}

bool DecodeHex(std::vector<uint8_t> *out, const std::string &in) {
  out->clear();
  if (in.size() % 2 != 0) {
    return false;
  }
  out->reserve(in.size() / 2);
  for (size_t i = 0; i < in.size(); i += 2) {
    uint8_t hi, lo;
    if (!OPENSSL_fromxdigit(&hi, in[i]) ||
        !OPENSSL_fromxdigit(&lo, in[i + 1])) {
      return false;
    }
    out->push_back((hi << 4) | lo);
  }
  return true;
}

std::vector<uint8_t> HexToBytes(const char *str) {
  std::vector<uint8_t> ret;
  if (!DecodeHex(&ret, str)) {
    abort();
  }
  return ret;
}

std::string EncodeHex(bssl::Span<const uint8_t> in) {
  static const char kHexDigits[] = "0123456789abcdef";
  std::string ret;
  ret.reserve(in.size() * 2);
  for (uint8_t b : in) {
    ret += kHexDigits[b >> 4];
    ret += kHexDigits[b & 0xf];
  }
  return ret;
}

// CertFromPEM parses the given, NUL-terminated pem block and returns an
// |X509*|.
bssl::UniquePtr<X509> CertFromPEM(const char *pem) {
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem, strlen(pem)));
  if (!bio) {
    return nullptr;
  }
  return bssl::UniquePtr<X509>(
      PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
}

#if defined(OPENSSL_WINDOWS)
size_t createTempFILEpath(char buffer[PATH_MAX]) {
  // On Windows, tmpfile() may attempt to create temp files in the root directory
  // of the drive, which requires Admin privileges, resulting in test failure.
  char pathname[PATH_MAX];
  if(0 == GetTempPathA(PATH_MAX, pathname)) {
    return 0;
  }
  return GetTempFileNameA(pathname, "awslctest", 0, buffer);
}
FILE* createRawTempFILE() {
  char filename[PATH_MAX];
  if(createTempFILEpath(filename) == 0) {
    return nullptr;
  }
  return fopen(filename, "w+b");
}
#else
#include <cstdlib>
size_t createTempFILEpath(char buffer[PATH_MAX]) {
OPENSSL_BEGIN_ALLOW_DEPRECATED
  OPENSSL_STATIC_ASSERT(PATH_MAX >= L_tmpnam, PATH_MAX_too_short);
  // Functions for constructing a tempfile path (i.e., tmpname and mktemp)
  // are deprecated in C99.
  if(nullptr == tmpnam(buffer)) {
    return 0;
  }
OPENSSL_END_ALLOW_DEPRECATED
  return strnlen(buffer, PATH_MAX);
}
FILE* createRawTempFILE() {
  return tmpfile();
}
#endif


TempFILE createTempFILE() {
  return TempFILE(createRawTempFILE());
}

void CustomDataFree(void *parent, void *ptr, CRYPTO_EX_DATA *ad,
                           int index, long argl, void *argp) {
  free(ptr);
}

