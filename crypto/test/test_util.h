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

#ifndef OPENSSL_HEADER_CRYPTO_TEST_TEST_UTIL_H
#define OPENSSL_HEADER_CRYPTO_TEST_TEST_UTIL_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <iosfwd>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/span.h>

#include "../internal.h"


// hexdump writes |msg| to |fp| followed by the hex encoding of |len| bytes
// from |in|.
void hexdump(FILE *fp, const char *msg, const void *in, size_t len);

// Bytes is a wrapper over a byte slice which may be compared for equality. This
// allows it to be used in EXPECT_EQ macros.
struct Bytes {
  Bytes(const uint8_t *data_arg, size_t len_arg) : span_(data_arg, len_arg) {}
  Bytes(const char *data_arg, size_t len_arg)
      : span_(reinterpret_cast<const uint8_t *>(data_arg), len_arg) {}

  explicit Bytes(const char *str)
      : span_(reinterpret_cast<const uint8_t *>(str), strlen(str)) {}
  explicit Bytes(const std::string &str)
      : span_(reinterpret_cast<const uint8_t *>(str.data()), str.size()) {}
  explicit Bytes(bssl::Span<const uint8_t> span) : span_(span) {}

  bssl::Span<const uint8_t> span_;
};

inline bool operator==(const Bytes &a, const Bytes &b) {
  return a.span_ == b.span_;
}

inline bool operator!=(const Bytes &a, const Bytes &b) { return !(a == b); }

std::ostream &operator<<(std::ostream &os, const Bytes &in);

// DecodeHex decodes |in| from hexadecimal and writes the output to |out|. It
// returns true on success and false if |in| is not a valid hexadecimal byte
// string.
bool DecodeHex(std::vector<uint8_t> *out, const std::string &in);

// HexToBytes decodes |str| from hexadecimal and returns a new vector of bytes.
// If |str| is invalid it aborts.
std::vector<uint8_t> HexToBytes(const char *str);

// EncodeHex returns |in| encoded in hexadecimal.
std::string EncodeHex(bssl::Span<const uint8_t> in);

// CertFromPEM parses the given, NUL-terminated pem block and returns an
// |X509*|.
bssl::UniquePtr<X509> CertFromPEM(const char *pem);

// CertsToStack converts a vector of |X509*| to an OpenSSL STACK_OF(X509),
// bumping the reference counts for each certificate in question.
bssl::UniquePtr<STACK_OF(X509)> CertsToStack(const std::vector<X509 *> &certs);

// RSAFromPEM parses the given, NUL-terminated pem block and returns an
// |RSA*|.
bssl::UniquePtr<RSA> RSAFromPEM(const char *pem);

// kReferenceTime is the reference time used by certs created by |MakeTestCert|.
// It is the unix timestamp for Sep 27th, 2016.
static const int64_t kReferenceTime = 1474934400;

// MakeTestCert creates an X509 certificate for use in testing. It is configured
// to be valid from 1 day prior |kReferenceTime| until 1 day after
// |kReferenceTime|.
bssl::UniquePtr<X509> MakeTestCert(const char *issuer,
                                          const char *subject, EVP_PKEY *key,
                                          bool is_ca);

// unique_ptr will automatically call fclose on the file descriptior when the
// variable goes out of scope, so we need to specify BIO_NOCLOSE close flags
// to avoid a double-free condition.
struct TempFileCloser {
  void operator()(FILE *f) const { fclose(f); }
};

using TempFILE = std::unique_ptr<FILE, TempFileCloser>;

#if defined(OPENSSL_WINDOWS)
#include <windows.h>
#ifndef PATH_MAX
#define PATH_MAX MAX_PATH
#endif
#else
#include <limits.h>
#endif

size_t createTempFILEpath(char buffer[PATH_MAX]);
FILE* createRawTempFILE();
TempFILE createTempFILE();
size_t createTempDirPath(char buffer[PATH_MAX]);

// CustomData is for testing new structs that we add support for |ex_data|.
typedef struct {
  int custom_data;
} CustomData;

void CustomDataFree(void *parent, void *ptr, CRYPTO_EX_DATA *ad,
                           int index, long argl, void *argp);
// ErrorEquals asserts that |err| is an error with library |lib| and reason
// |reason|.
testing::AssertionResult ErrorEquals(uint32_t err, int lib, int reason);


#endif  // OPENSSL_HEADER_CRYPTO_TEST_TEST_UTIL_H
