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

bssl::UniquePtr<RSA> RSAFromPEM(const char *pem) {
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(pem, strlen(pem)));
  if (!bio) {
    return nullptr;
  }
  return bssl::UniquePtr<RSA>(
      PEM_read_bio_RSAPrivateKey(bio.get(), nullptr, nullptr, nullptr));
}

bssl::UniquePtr<STACK_OF(X509)> CertsToStack(
    const std::vector<X509 *> &certs) {
  bssl::UniquePtr<STACK_OF(X509)> stack(sk_X509_new_null());
  if (!stack) {
    return nullptr;
  }
  for (auto cert : certs) {
    if (!bssl::PushToStack(stack.get(), bssl::UpRef(cert))) {
      return nullptr;
    }
  }
  return stack;
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
#include <unistd.h>
size_t createTempFILEpath(char buffer[PATH_MAX]) {
  snprintf(buffer, PATH_MAX, "awslcTestTmpFileXXXXXX");

  int fd = mkstemp(buffer);
  if (fd == -1) {
    return 0;
  }

  close(fd);
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

