// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Tests that libssl survives each of its allocations failing in turn: a call
// fails, or does its work, but never crashes or returns an object that is not
// whole. The allocator is replaced with strong |OPENSSL_memory_*| symbols, as
// mem_test.cc does, so these tests run in an executable of their own, and only
// where weak symbols are supported well.
#if defined(__ELF__) && defined(__GNUC__)

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <gtest/gtest.h>

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/mem.h>
#include <openssl/pem.h>
#include <openssl/pool.h>
#include <openssl/rand.h>
#include <openssl/ssl.h>
#include <openssl/x509.h>

extern "C" {
OPENSSL_EXPORT void *OPENSSL_memory_alloc(size_t size);
OPENSSL_EXPORT void OPENSSL_memory_free(void *ptr);
OPENSSL_EXPORT size_t OPENSSL_memory_get_size(void *ptr);
OPENSSL_EXPORT void *OPENSSL_memory_realloc(void *ptr, size_t size);
}

// The allocation to fail, counting from one since |ScopedAllocFailure| armed
// the allocator, or zero to fail none; the allocations counted since; and
// whether the one to fail was reached.
static uint64_t g_fail_at = 0;
static uint64_t g_allocs = 0;
static bool g_failed = false;

static bool ShouldFail() {
  if (g_fail_at == 0 || ++g_allocs != g_fail_at) {
    return false;
  }
  g_failed = true;
  return true;
}

// Each block carries its size in a header of its own, for
// |OPENSSL_memory_get_size|, which keeps the payload aligned as |malloc| does.
static const size_t kHeaderSize = 16;

static void *WithSize(uint8_t *block, size_t size) {
  if (block == nullptr) {
    return nullptr;
  }
  memcpy(block, &size, sizeof(size));
  return block + kHeaderSize;
}

static uint8_t *BlockOf(void *ptr) {
  return static_cast<uint8_t *>(ptr) - kHeaderSize;
}

void *OPENSSL_memory_alloc(size_t size) {
  if (ShouldFail() || size > SIZE_MAX - kHeaderSize) {
    return nullptr;
  }
  return WithSize(static_cast<uint8_t *>(malloc(size + kHeaderSize)), size);
}

void OPENSSL_memory_free(void *ptr) {
  if (ptr != nullptr) {
    free(BlockOf(ptr));
  }
}

size_t OPENSSL_memory_get_size(void *ptr) {
  size_t size;
  memcpy(&size, BlockOf(ptr), sizeof(size));
  return size;
}

void *OPENSSL_memory_realloc(void *ptr, size_t size) {
  if (ptr == nullptr) {
    return OPENSSL_memory_alloc(size);
  }
  if (ShouldFail() || size > SIZE_MAX - kHeaderSize) {
    return nullptr;
  }
  return WithSize(
      static_cast<uint8_t *>(realloc(BlockOf(ptr), size + kHeaderSize)), size);
}

// Fails the |n|th allocation from now, counting from one, and no other, for
// the lifetime of the object.
class ScopedAllocFailure {
 public:
  explicit ScopedAllocFailure(uint64_t n) {
    g_allocs = 0;
    g_failed = false;
    g_fail_at = n;
  }
  ~ScopedAllocFailure() { g_fail_at = 0; }
  ScopedAllocFailure(const ScopedAllocFailure &) = delete;
  ScopedAllocFailure &operator=(const ScopedAllocFailure &) = delete;

  // Whether the allocation to fail was reached.
  bool Failed() const { return g_failed; }
};

// Builds the calling thread's random number generator state, which is not
// built lazily inside a failure window: AWS-LC aborts when it cannot allocate
// that state.
static void WarmUpRandom() {
  uint8_t byte;
  ASSERT_TRUE(RAND_bytes(&byte, 1));
}

static bssl::UniquePtr<EVP_PKEY> TestKey() {
  static const char kKeyPEM[] =
      "-----BEGIN PRIVATE KEY-----\n"
      "MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQgB44OSLEvehvdsm8D\n"
      "nBwNbdIMrOjai2bFBgV5wCbEfP+hRANCAAQ+1r4NwRhAT1jBxK/Cq/JMVYo52CiW\n"
      "FVCCR5nzuetFMdfYa+rXtVXHHngwxdfRjJEXBo3ZDTkeM1Dgsefmirsz\n"
      "-----END PRIVATE KEY-----\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(kKeyPEM, sizeof(kKeyPEM) - 1));
  return bssl::UniquePtr<EVP_PKEY>(
      PEM_read_bio_PrivateKey(bio.get(), nullptr, nullptr, nullptr));
}

static bssl::UniquePtr<CRYPTO_BUFFER> TestCertificate() {
  static const char kCertPEM[] =
      "-----BEGIN CERTIFICATE-----\n"
      "MIIBnDCCAUGgAwIBAgIUd7br4xl4e83efLBPVnDoHlJABBowCgYIKoZIzj0EAwIw\n"
      "IjEgMB4GA1UEAwwXYWxsb2NhdGlvbiBmYWlsdXJlIHRlc3QwIBcNMjYxMTA0MDkz\n"
      "ODMwWhgPMjEyNjEwMTEwOTM4MzBaMCIxIDAeBgNVBAMMF2FsbG9jYXRpb24gZmFp\n"
      "bHVyZSB0ZXN0MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAEPta+DcEYQE9YwcSv\n"
      "wqvyTFWKOdgolhVQgkeZ87nrRTHX2Gvq17VVxx54MMXX0YyRFwaN2Q05HjNQ4LHn\n"
      "5oq7M6NTMFEwHQYDVR0OBBYEFJ09z2i6CjtDsvtIIoIE+G1OpafuMB8GA1UdIwQY\n"
      "MBaAFJ09z2i6CjtDsvtIIoIE+G1OpafuMA8GA1UdEwEB/wQFMAMBAf8wCgYIKoZI\n"
      "zj0EAwIDSQAwRgIhAMmEBcQfjznujzDTWgXjSP/h27vAtIsuI+mr1TUWM4t4AiEA\n"
      "zCVgjnMQ3YmwcUIOpvngdXcOxSnWfS/ZytQAAEkUVeo=\n"
      "-----END CERTIFICATE-----\n";
  bssl::UniquePtr<BIO> bio(BIO_new_mem_buf(kCertPEM, sizeof(kCertPEM) - 1));
  bssl::UniquePtr<X509> x509(
      PEM_read_bio_X509(bio.get(), nullptr, nullptr, nullptr));
  if (!x509) {
    return nullptr;
  }
  uint8_t *der = nullptr;
  int der_len = i2d_X509(x509.get(), &der);
  if (der_len <= 0) {
    return nullptr;
  }
  bssl::UniquePtr<uint8_t> free_der(der);
  return bssl::UniquePtr<CRYPTO_BUFFER>(
      CRYPTO_BUFFER_new(der, der_len, nullptr));
}

// Each allocation of |SSL_CTX_new| fails in turn. The context is not built, or
// it is whole: a connection can be made from it.
TEST(SSLMemTest, CTXNewFailsEachAllocation) {
  WarmUpRandom();
  for (uint64_t n = 1;; n++) {
    SCOPED_TRACE(n);
    bssl::UniquePtr<SSL_CTX> ctx;
    bool failed;
    {
      ScopedAllocFailure failure(n);
      ctx.reset(SSL_CTX_new(TLS_method()));
      failed = failure.Failed();
    }
    ERR_clear_error();
    if (!failed) {
      ASSERT_TRUE(ctx);
      break;
    }
    if (ctx) {
      bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
      EXPECT_TRUE(ssl) << "a context built past a failed allocation is broken";
    }
  }
}

// Each allocation of |SSL_set_chain_and_key| fails in turn: the call fails or
// sets the chain and key, and the connection takes them once allocations
// succeed again.
TEST(SSLMemTest, SetChainAndKeyFailsEachAllocation) {
  WarmUpRandom();
  bssl::UniquePtr<EVP_PKEY> key = TestKey();
  ASSERT_TRUE(key);
  bssl::UniquePtr<CRYPTO_BUFFER> leaf = TestCertificate();
  ASSERT_TRUE(leaf);
  CRYPTO_BUFFER *chain[] = {leaf.get()};

  for (uint64_t n = 1;; n++) {
    SCOPED_TRACE(n);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);
    bssl::UniquePtr<SSL> ssl(SSL_new(ctx.get()));
    ASSERT_TRUE(ssl);
    int ok;
    bool failed;
    {
      ScopedAllocFailure failure(n);
      ok = SSL_set_chain_and_key(ssl.get(), chain, 1, key.get(), nullptr);
      failed = failure.Failed();
    }
    ERR_clear_error();
    if (!failed) {
      EXPECT_TRUE(ok);
      break;
    }
    EXPECT_TRUE(SSL_set_chain_and_key(ssl.get(), chain, 1, key.get(), nullptr));
  }
}

// The same for |SSL_CTX_set_chain_and_key|.
TEST(SSLMemTest, CTXSetChainAndKeyFailsEachAllocation) {
  WarmUpRandom();
  bssl::UniquePtr<EVP_PKEY> key = TestKey();
  ASSERT_TRUE(key);
  bssl::UniquePtr<CRYPTO_BUFFER> leaf = TestCertificate();
  ASSERT_TRUE(leaf);
  CRYPTO_BUFFER *chain[] = {leaf.get()};

  for (uint64_t n = 1;; n++) {
    SCOPED_TRACE(n);
    bssl::UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);
    int ok;
    bool failed;
    {
      ScopedAllocFailure failure(n);
      ok = SSL_CTX_set_chain_and_key(ctx.get(), chain, 1, key.get(), nullptr);
      failed = failure.Failed();
    }
    ERR_clear_error();
    if (!failed) {
      EXPECT_TRUE(ok);
      break;
    }
    EXPECT_TRUE(
        SSL_CTX_set_chain_and_key(ctx.get(), chain, 1, key.get(), nullptr));
  }
}

#endif  // defined(__ELF__) && defined(__GNUC__)
