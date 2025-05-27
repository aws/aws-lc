/* Copyright (c) 2014, Google Inc.
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

#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include <assert.h>
#include <errno.h>

#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif
#include <inttypes.h>

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "internal.h"

#include <openssl/crypto.h>

#include "openssl/cmac.h"
#if defined(OPENSSL_IS_AWSLC)
#include "bssl_bm.h"
#include "../crypto/internal.h"
#include <thread>
#include <sstream>
#elif defined(OPENSSL_IS_BORINGSSL)
#define BORINGSSL_BENCHMARK
#include "bssl_bm.h"
#else
#define OPENSSL_BENCHMARK
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
#define OPENSSL_3_0_BENCHMARK
#elif OPENSSL_VERSION_NUMBER >= 0x10100000L
#define OPENSSL_1_1_BENCHMARK
#elif OPENSSL_VERSION_NUMBER >= 0x10000000L
#define OPENSSL_1_0_BENCHMARK
#else
#error unknown OpenSSL version
#endif
#include "ossl_bm.h"
#endif

#if defined(OPENSSL_WINDOWS)
OPENSSL_MSVC_PRAGMA(warning(push, 3))
#include <windows.h>
OPENSSL_MSVC_PRAGMA(warning(pop))
#elif defined(OPENSSL_APPLE)
#include <sys/time.h>
#else
#include <time.h>
#endif

#if !defined(OPENSSL_IS_AWSLC)
// align_pointer returns |ptr|, advanced to |alignment|. |alignment| must be a
// power of two, and |ptr| must have at least |alignment - 1| bytes of scratch
// space.
static inline void *align_pointer(void *ptr, size_t alignment) {
  // |alignment| must be a power of two.
  assert(alignment != 0 && (alignment & (alignment - 1)) == 0);
  // Instead of aligning |ptr| as a |uintptr_t| and casting back, compute the
  // offset and advance in pointer space. C guarantees that casting from pointer
  // to |uintptr_t| and back gives the same pointer, but general
  // integer-to-pointer conversions are implementation-defined. GCC does define
  // it in the useful way, but this makes fewer assumptions.
  uintptr_t offset = (0u - (uintptr_t)ptr) & (alignment - 1);
  ptr = (char *)ptr + offset;
  assert(((uintptr_t)ptr & (alignment - 1)) == 0);
  return ptr;
}
#endif

#if defined(INTERNAL_TOOL)
#include "../crypto/rand_extra/internal.h"
#endif


#if defined(OPENSSL_IS_AWSLC) && defined(AARCH64_DIT_SUPPORTED) && (AWSLC_API_VERSION > 30)
#include "../crypto/fipsmodule/cpucap/internal.h"
#define DIT_OPTION
#endif

static inline void *BM_memset(void *dst, int c, size_t n) {
  if (n == 0) {
    return dst;
  }

  return memset(dst, c, n);
}

// g_print_json is true if printed output is JSON formatted.
static bool g_print_json = false;

#if defined(DIT_OPTION)
// g_dit is true if the DIT macro is to be enabled before benchmarking
static bool g_dit = false;
#endif

static std::string ChunkLenSuffix(size_t chunk_len) {
  char buf[32];
  snprintf(buf, sizeof(buf), " (%zu byte%s)", chunk_len,
           chunk_len != 1 ? "s" : "");
  return buf;
}

static std::string PrimeLenSuffix(size_t prime_length) {
  char buf[32];
  snprintf(buf, sizeof(buf), " (%zu bit%s)", prime_length,
           prime_length != 1 ? "s" : "");
  return buf;
}

// TimeResults represents the results of benchmarking a function.
struct TimeResults {
  // num_calls is the number of function calls done in the time period.
  uint64_t num_calls;
  // us is the number of microseconds that elapsed in the time period.
  uint64_t us;

  void Print(const std::string &description) const {
    if (g_print_json) {
      PrintJSON(description);
    } else {
      printf(
          "Did %" PRIu64 " %s operations in %" PRIu64 "us (%.1f ops/sec)\n",
          num_calls, description.c_str(), us,
          (static_cast<double>(num_calls) / static_cast<double>(us)) * 1000000);
    }
  }

  void PrintWithBytes(const std::string &description,
                      size_t bytes_per_call) const {
    if (g_print_json) {
      PrintJSON(description, bytes_per_call);
    } else {
      printf(
          "Did %" PRIu64 " %s operations in %" PRIu64
          "us (%.1f ops/sec): %.1f MB/s\n",
          num_calls, (description + ChunkLenSuffix(bytes_per_call)).c_str(), us,
          (static_cast<double>(num_calls) / static_cast<double>(us)) * 1000000,
          static_cast<double>(bytes_per_call * num_calls) /
              static_cast<double>(us));
    }
  }

  void PrintWithPrimes(const std::string &description,
                      size_t prime_size) const {
    if (g_print_json) {
      PrintJSON(description, "primeSizePerCall", prime_size);
    } else {
      printf(
          "Did %" PRIu64 " %s operations in %" PRIu64
          "us (%.3f ops/sec)\n",
          num_calls, (description + PrimeLenSuffix(prime_size)).c_str(), us,
          (static_cast<double>(num_calls) / static_cast<double>(us)) * 1000000);
    }
  }

 private:
  void PrintJSON(const std::string &description,
                 size_t bytes_per_call = 0) const {
    if (first_json_printed) {
      puts(",");
    }

    printf("{\"description\": \"%s\", \"numCalls\": %" PRIu64
           ", \"microseconds\": %" PRIu64,
           description.c_str(), num_calls, us);

    if (bytes_per_call > 0) {
      printf(", \"bytesPerCall\": %zu", bytes_per_call);
    }

    printf("}");
    first_json_printed = true;
  }

  void PrintJSON(const std::string &description,
                 const std::string &size_label,
                 size_t size = 0) const {
    if (first_json_printed) {
      puts(",");
    }

    printf("{\"description\": \"%s\", \"numCalls\": %" PRIu64
           ", \"microseconds\": %" PRIu64,
           description.c_str(), num_calls, us);

    if (size > 0) {
      printf(", \"%s\": %zu", size_label.c_str(), size);
    }

    printf("}");
    first_json_printed = true;
  }

  // first_json_printed is true if |g_print_json| is true and the first item in
  // the JSON results has been printed already. This is used to handle the
  // commas between each item in the result list.
  static bool first_json_printed;
};

bool TimeResults::first_json_printed = false;

#if defined(OPENSSL_WINDOWS)
static uint64_t time_now() { return GetTickCount64() * 1000; }
#elif defined(OPENSSL_APPLE)
static uint64_t time_now() {
  struct timeval tv;
  uint64_t ret;

  gettimeofday(&tv, NULL);
  ret = tv.tv_sec;
  ret *= 1000000;
  ret += tv.tv_usec;
  return ret;
}
#else
static uint64_t time_now() {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);

  uint64_t ret = ts.tv_sec;
  ret *= 1000000;
  ret += ts.tv_nsec / 1000;
  return ret;
}
#endif

#define TIMEOUT_MS_DEFAULT 1000
static uint64_t g_timeout_ms = TIMEOUT_MS_DEFAULT;
static std::vector<size_t> g_chunk_lengths = {16, 256, 1350, 8192, 16384};
static std::vector<size_t> g_threads = {1, 2, 4, 8, 16, 32, 64};
static std::vector<size_t> g_prime_bit_lengths = {2048, 3072};
static std::vector<std::string> g_filters = {""};

static bool TimeFunction(TimeResults *results, std::function<bool()> func) {
  // The first time |func| is called an expensive self check might run that
  // will skew the iterations between checks calculation
  if (!func()) {
    return false;
  }
  // total_us is the total amount of time that we'll aim to measure a function
  // for.
  const uint64_t total_us = g_timeout_ms * 1000;
  uint64_t start = time_now(), now, delta;

  if (!func()) {
    return false;
  }
  now = time_now();
  delta = now - start;
  unsigned iterations_between_time_checks;
  if (delta == 0) {
    iterations_between_time_checks = 250;
  } else {
    // Aim for about 100ms between time checks.
    iterations_between_time_checks =
        static_cast<double>(100000) / static_cast<double>(delta);
    if (iterations_between_time_checks > 1000) {
      iterations_between_time_checks = 1000;
    } else if (iterations_between_time_checks < 1) {
      iterations_between_time_checks = 1;
    }
  }

  // Don't include the time taken to run |func| to calculate
  // |iterations_between_time_checks|
  start = time_now();
  uint64_t done = 0;
  for (;;) {
    for (unsigned i = 0; i < iterations_between_time_checks; i++) {
      if (!func()) {
        return false;
      }
      done++;
    }

    now = time_now();
    if (now - start > total_us) {
      break;
    }
  }

  results->us = now - start;
  results->num_calls = done;
  return true;
}

static bool SpeedRSA(const std::string &selected) {
  if (!selected.empty() && selected.find("RSA") == std::string::npos) {
    return true;
  }

  static const struct {
    const char *name;
    const uint8_t *key;
    const size_t key_len;
  } kRSAKeys[] = {
    {"RSA 2048", kDERRSAPrivate2048, kDERRSAPrivate2048Len},
    {"RSA 3072", kDERRSAPrivate3072, kDERRSAPrivate3072Len},
    {"RSA 4096", kDERRSAPrivate4096, kDERRSAPrivate4096Len},
    {"RSA 8192", kDERRSAPrivate8192, kDERRSAPrivate8192Len},
  };

  for (size_t i = 0; i < BM_ARRAY_SIZE(kRSAKeys); i++) {
    const std::string name = kRSAKeys[i].name;

    // d2i_RSAPrivateKey expects to be able to modify the input pointer as it parses the input data and we don't want it
    // to modify the original |*key| data. Therefore create a new temp variable that points to the same data and pass
    // in the reference to it. As a sanity check make sure |input_key| points to the end of the |*key|.
    const uint8_t *input_key = kRSAKeys[i].key;
    BM_NAMESPACE::UniquePtr<RSA> key(d2i_RSAPrivateKey(NULL, &input_key, (long) kRSAKeys[i].key_len));
    if (key == nullptr) {
      fprintf(stderr, "Failed to parse %s key.\n", name.c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }

    std::unique_ptr<uint8_t[]> sig(new uint8_t[RSA_size(key.get())]);
    const uint8_t fake_sha256_hash[32] = {0};
    unsigned sig_len;

    TimeResults results;
    if (!TimeFunction(&results,
                      [&key, &sig, &fake_sha256_hash, &sig_len]() -> bool {
          // Usually during RSA signing we're using a long-lived |RSA| that has
          // already had all of its |BN_MONT_CTX|s constructed, so it makes
          // sense to use |key| directly here.
          return RSA_sign(NID_sha256, fake_sha256_hash, sizeof(fake_sha256_hash),
                          sig.get(), &sig_len, key.get());
        })) {
      fprintf(stderr, "RSA_sign failed.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    results.Print(name + " signing");

    if (!TimeFunction(&results,
                      [&key, &fake_sha256_hash, &sig, sig_len]() -> bool {
          return RSA_verify(
              NID_sha256, fake_sha256_hash, sizeof(fake_sha256_hash),
              sig.get(), sig_len, key.get());
        })) {
      fprintf(stderr, "RSA_verify failed.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    results.Print(name + " verify (same key)");

    if (!TimeFunction(&results,
                      [&key, &fake_sha256_hash, &sig, sig_len]() -> bool {
          // Usually during RSA verification we have to parse an RSA key from a
          // certificate or similar, in which case we'd need to construct a new
          // RSA key, with a new |BN_MONT_CTX| for the public modulus. If we
          // were to use |key| directly instead, then these costs wouldn't be
          // accounted for.
		  BM_NAMESPACE::UniquePtr<RSA> verify_key(RSA_new());
          if (!verify_key) {
            return false;
          }
#if defined(OPENSSL_1_0_BENCHMARK)
          const BIGNUM *temp_n = key.get()->n;
          const BIGNUM *temp_e = key.get()->e;
          verify_key.get()->n = BN_dup(temp_n);
          verify_key.get()->e = BN_dup(temp_e);
#else
          const BIGNUM *temp_n = NULL;
          const BIGNUM *temp_e = NULL;

          RSA_get0_key(key.get(), &temp_n, &temp_e, NULL);
          RSA_set0_key(verify_key.get(), BN_dup(temp_n), BN_dup(temp_e), NULL);
#endif

          return RSA_verify(NID_sha256, fake_sha256_hash,
                            sizeof(fake_sha256_hash), sig.get(), sig_len,
                            verify_key.get());
        })) {
      fprintf(stderr, "RSA_verify failed.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    results.Print(name + " verify (fresh key)");

// |RSA_private_key_from_bytes| is not available in OpenSSL.
// TODO: Add support for OpenSSL RSA private key parsing benchmarks. Tracked in
//       CryptoAlg-1092.
#if !defined(OPENSSL_BENCHMARK)
    if (!TimeFunction(&results, [&]() -> bool {
          return BM_NAMESPACE::UniquePtr<RSA>(RSA_private_key_from_bytes(
                     kRSAKeys[i].key, kRSAKeys[i].key_len)) != nullptr;
        })) {
      fprintf(stderr, "Failed to parse %s key.\n", name.c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }
    results.Print(name + " private key parse");
#endif
  }

  return true;
}

static bool SpeedRSAKeyGen(bool is_fips, const std::string &selected) {
  if (!selected.empty() && selected.find("RSAKeyGen") == std::string::npos) {
    return true;
  }

  BM_NAMESPACE::UniquePtr<BIGNUM> e(BN_new());
  if (!BN_set_word(e.get(), 65537)) {
    return false;
  }

  const std::vector<int> kSizes = {2048, 3072, 4096};
  for (int size : kSizes) {
    const uint64_t start = time_now();
    uint64_t num_calls = 0;
    uint64_t us;
    std::vector<uint64_t> durations;

    for (;;) {
      BM_NAMESPACE::UniquePtr<RSA> rsa(RSA_new());

      const uint64_t iteration_start = time_now();
      if(is_fips){
#if !defined(OPENSSL_BENCHMARK)
        // RSA_generate_key_fips is AWS-LC specific.
        if (!RSA_generate_key_fips(rsa.get(), size, nullptr)) {
          fprintf(stderr, "RSA_generate_key_fips failed.\n");
          ERR_print_errors_fp(stderr);
          return false;
        }
#else
        return true;
#endif
      }
      else {
        if (!RSA_generate_key_ex(rsa.get(), size, e.get(), nullptr)) {
          fprintf(stderr, "RSA_generate_key_ex failed.\n");
          ERR_print_errors_fp(stderr);
          return false;
        }
      }
      const uint64_t iteration_end = time_now();

      num_calls++;
      durations.push_back(iteration_end - iteration_start);

      us = iteration_end - start;
      if (us > 30 * 1000000 /* 30 secs */) {
        break;
      }
    }

    std::sort(durations.begin(), durations.end());
    std::string rsa_type = std::string("RSA ");
    if (is_fips) {
      rsa_type += "FIPS ";
    }
    const std::string description =
        rsa_type + std::to_string(size) + std::string(" key-gen");
    const TimeResults results = {num_calls, us};
    results.Print(description);
    const size_t n = durations.size();
    assert(n > 0);

    // Distribution information is useful, but doesn't fit into the standard
    // format used by |g_print_json|.
    if (!g_print_json) {
      uint64_t min = durations[0];
      uint64_t median = n & 1 ? durations[n / 2]
                              : (durations[n / 2 - 1] + durations[n / 2]) / 2;
      uint64_t max = durations[n - 1];
      printf("  min: %" PRIu64 "us, median: %" PRIu64 "us, max: %" PRIu64
             "us\n",
             min, median, max);
    }
  }

  return true;
}

static bool SpeedEvpGenericChunk(const EVP_CIPHER *cipher, std::string name,
                             size_t chunk_byte_len, size_t ad_len, bool encrypt) {
  int len, result;
  int* len_ptr = &len;
  const size_t key_len = EVP_CIPHER_key_length(cipher);
  static const unsigned kAlignment = 16;
  const size_t iv_len = EVP_CIPHER_iv_length(cipher);
  // GCM uses 16 byte tags
  const size_t overhead_len = 16;
  std::unique_ptr<uint8_t[]> key(new uint8_t[key_len]);
  BM_memset(key.get(), 0, key_len);
  std::unique_ptr<uint8_t[]> nonce(new uint8_t[iv_len]);
  BM_memset(nonce.get(), 0, iv_len);
  std::unique_ptr<uint8_t[]> plaintext_storage(new uint8_t[chunk_byte_len + kAlignment]);
  std::unique_ptr<uint8_t[]> ciphertext_storage(new uint8_t[chunk_byte_len + overhead_len + kAlignment]);
  std::unique_ptr<uint8_t[]> in2_storage(new uint8_t[chunk_byte_len + overhead_len + kAlignment]);
  std::unique_ptr<uint8_t[]> ad(new uint8_t[ad_len]);
  BM_memset(ad.get(), 0, ad_len);
  std::unique_ptr<uint8_t[]> tag_storage(new uint8_t[overhead_len + kAlignment]);

  uint8_t *const plaintext = static_cast<uint8_t *>(align_pointer(plaintext_storage.get(), kAlignment));
  BM_memset(plaintext, 0, chunk_byte_len);
  uint8_t *const ciphertext = static_cast<uint8_t *>(align_pointer(ciphertext_storage.get(), kAlignment));
  BM_memset(ciphertext, 0, chunk_byte_len + overhead_len);
  uint8_t *const tag = static_cast<uint8_t *>(align_pointer(tag_storage.get(), kAlignment));
  BM_memset(tag, 0, overhead_len);

  BM_NAMESPACE::UniquePtr<EVP_CIPHER_CTX> ctx(EVP_CIPHER_CTX_new());

  bool isAead = EVP_CIPHER_flags(cipher) & EVP_CIPH_FLAG_AEAD_CIPHER;
  if (encrypt) {
    std::string encryptName = name + " encrypt";
    TimeResults encryptResults;

    // Call EVP_EncryptInit_ex once with the cipher and key, the benchmark loop will reuse both
    if (!EVP_EncryptInit_ex(ctx.get(), cipher, NULL, key.get(), nonce.get())){
      fprintf(stderr, "Failed to configure encryption context.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    if (!TimeFunction(&encryptResults, [&ctx, chunk_byte_len, plaintext, ciphertext, len_ptr, tag, &nonce, &ad, ad_len, &isAead, &result]() -> bool {
      result = EVP_EncryptInit_ex(ctx.get(), NULL, NULL, NULL, nonce.get());
      if (isAead) {
        result &= EVP_EncryptUpdate(ctx.get(), NULL, len_ptr, ad.get(), ad_len);
      }
      result &= EVP_EncryptUpdate(ctx.get(), ciphertext, len_ptr, plaintext, chunk_byte_len);
      result &= EVP_EncryptFinal_ex(ctx.get(), ciphertext + *len_ptr, len_ptr);
      if (isAead) {
        result &= EVP_CIPHER_CTX_ctrl(ctx.get(), EVP_CTRL_GCM_GET_TAG, 16, tag);
      }
      return result;
    })) {
      fprintf(stderr, "%s failed.\n", encryptName.c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }

    encryptResults.PrintWithBytes(encryptName, chunk_byte_len);
  }
  else {
    result =  EVP_EncryptInit_ex(ctx.get(), cipher, NULL, key.get(), nonce.get());
    if (isAead) {
      result &= EVP_EncryptUpdate(ctx.get(), NULL, len_ptr, ad.get(), ad_len);
    }
    result &= EVP_EncryptUpdate(ctx.get(), ciphertext, len_ptr, plaintext, chunk_byte_len);
    int ciphertext_len = *len_ptr;
    result &= EVP_EncryptFinal_ex(ctx.get(), ciphertext + *len_ptr, len_ptr);
    ciphertext_len += *len_ptr;
    if(isAead) {
      result &= EVP_CIPHER_CTX_ctrl(ctx.get(), EVP_CTRL_GCM_GET_TAG, 16, tag);
    }

    if (!result) {
      fprintf(stderr, "Failed to perform one encryption.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    std::string decryptName = name + " decrypt";
    TimeResults decryptResults;
    // Call EVP_DecryptInit_ex once with the cipher and key, the benchmark loop will reuse both
    if (!EVP_DecryptInit_ex(ctx.get(), cipher, NULL, key.get(), nonce.get())){
      fprintf(stderr, "Failed to configure decryption context.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    if (!TimeFunction(&decryptResults, [&ctx, plaintext, ciphertext, len_ptr, tag, &nonce, &ad, ad_len, &isAead, &result, &ciphertext_len]() -> bool {
      result = EVP_DecryptInit_ex(ctx.get(), NULL, NULL, NULL, nonce.get());
      if(isAead) {
        result &= EVP_DecryptUpdate(ctx.get(), NULL, len_ptr, ad.get(), ad_len);
      }
      result &= EVP_DecryptUpdate(ctx.get(), plaintext, len_ptr, ciphertext, ciphertext_len);
      if (isAead) {
        result &= EVP_CIPHER_CTX_ctrl(ctx.get(), EVP_CTRL_GCM_SET_TAG, 16, tag);
      }
      result &= EVP_DecryptFinal_ex(ctx.get(), plaintext + *len_ptr, len_ptr);
      return result;
    })) {
      fprintf(stderr, "%s failed.\n", decryptName.c_str());
      ERR_print_errors_fp(stderr);
      return false;
    }
    decryptResults.PrintWithBytes(decryptName, chunk_byte_len);
  }

  return true;
}
static bool SpeedEvpCipherGeneric(const EVP_CIPHER *cipher,
                                  const std::string &name, size_t ad_len,
                                  const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  TimeResults results;
  BM_NAMESPACE::UniquePtr<EVP_CIPHER_CTX> ctx(EVP_CIPHER_CTX_new());
  const size_t key_len = EVP_CIPHER_key_length(cipher);
  std::unique_ptr<uint8_t[]> key(new uint8_t[key_len]);
  const size_t iv_len = EVP_CIPHER_iv_length(cipher);
  std::unique_ptr<uint8_t[]> nonce(new uint8_t[iv_len]);
  if (!TimeFunction(&results, [&]() -> bool {
        return EVP_EncryptInit_ex(ctx.get(), cipher, NULL, key.get(), nonce.get());})) {
    fprintf(stderr, "EVP_EncryptInit_ex failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
  results.Print(name +  " encrypt init");

  for (size_t chunk_byte_len : g_chunk_lengths) {
    if (!SpeedEvpGenericChunk(cipher, name, chunk_byte_len, ad_len,
                              /*encrypt*/ true)) {
      return false;
    }
  }

  if (!TimeFunction(&results, [&]() -> bool {
        return EVP_DecryptInit_ex(ctx.get(), cipher, NULL, key.get(), nonce.get());})) {
    fprintf(stderr, "EVP_DecryptInit_ex failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
  results.Print(name +  " decrypt init");
  for (size_t chunk_byte_len : g_chunk_lengths) {
    if (!SpeedEvpGenericChunk(cipher, name, chunk_byte_len, ad_len, false)) {
      return false;
    }
  }

  return true;
}

#if !defined(OPENSSL_BENCHMARK)
static bool SpeedAEADChunk(const EVP_AEAD *aead, std::string name,
                           size_t chunk_len, size_t ad_len,
                           evp_aead_direction_t direction) {
  static const unsigned kAlignment = 16;

  BM_NAMESPACE::ScopedEVP_AEAD_CTX ctx;
  const size_t key_len = EVP_AEAD_key_length(aead);
  const size_t nonce_len = EVP_AEAD_nonce_length(aead);
  const size_t overhead_len = EVP_AEAD_max_overhead(aead);

  std::unique_ptr<uint8_t[]> key(new uint8_t[key_len]);
  BM_memset(key.get(), 0, key_len);
  std::unique_ptr<uint8_t[]> nonce(new uint8_t[nonce_len]);
  BM_memset(nonce.get(), 0, nonce_len);
  std::unique_ptr<uint8_t[]> in_storage(new uint8_t[chunk_len + kAlignment]);
  // N.B. for EVP_AEAD_CTX_seal_scatter the input and output buffers may be the
  // same size. However, in the direction == evp_aead_open case we still use
  // non-scattering seal, hence we add overhead_len to the size of this buffer.
  std::unique_ptr<uint8_t[]> out_storage(
      new uint8_t[chunk_len + overhead_len + kAlignment]);
  std::unique_ptr<uint8_t[]> in2_storage(
      new uint8_t[chunk_len + overhead_len + kAlignment]);
  std::unique_ptr<uint8_t[]> ad(new uint8_t[ad_len]);
  BM_memset(ad.get(), 0, ad_len);
  std::unique_ptr<uint8_t[]> tag_storage(
      new uint8_t[overhead_len + kAlignment]);

  uint8_t *const in =
      static_cast<uint8_t *>(align_pointer(in_storage.get(), kAlignment));
  BM_memset(in, 0, chunk_len);
  uint8_t *const out =
      static_cast<uint8_t *>(align_pointer(out_storage.get(), kAlignment));
  BM_memset(out, 0, chunk_len + overhead_len);
  uint8_t *const tag =
      static_cast<uint8_t *>(align_pointer(tag_storage.get(), kAlignment));
  BM_memset(tag, 0, overhead_len);
  uint8_t *const in2 =
      static_cast<uint8_t *>(align_pointer(in2_storage.get(), kAlignment));

  if (!EVP_AEAD_CTX_init_with_direction(ctx.get(), aead, key.get(), key_len,
                                        EVP_AEAD_DEFAULT_TAG_LENGTH,
                                        evp_aead_seal)) {
    fprintf(stderr, "Failed to create EVP_AEAD_CTX.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  TimeResults results;
  if (direction == evp_aead_seal) {
    if (!TimeFunction(&results,
                      [chunk_len, nonce_len, ad_len, overhead_len, in, out, tag,
                       &ctx, &nonce, &ad]() -> bool {
                        size_t tag_len;
                        return EVP_AEAD_CTX_seal_scatter(
                            ctx.get(), out, tag, &tag_len, overhead_len,
                            nonce.get(), nonce_len, in, chunk_len, nullptr, 0,
                            ad.get(), ad_len);
                      })) {
      fprintf(stderr, "EVP_AEAD_CTX_seal failed.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
  } else {
    size_t out_len;
    EVP_AEAD_CTX_seal(ctx.get(), out, &out_len, chunk_len + overhead_len,
                      nonce.get(), nonce_len, in, chunk_len, ad.get(), ad_len);

    ctx.Reset();
    if (!EVP_AEAD_CTX_init_with_direction(ctx.get(), aead, key.get(), key_len,
                                          EVP_AEAD_DEFAULT_TAG_LENGTH,
                                          evp_aead_open)) {
      fprintf(stderr, "Failed to create EVP_AEAD_CTX.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }

    if (!TimeFunction(&results,
                      [chunk_len, overhead_len, nonce_len, ad_len, in2, out,
                       out_len, &ctx, &nonce, &ad]() -> bool {
                        size_t in2_len;
                        // N.B. EVP_AEAD_CTX_open_gather is not implemented for
                        // all AEADs.
                        return EVP_AEAD_CTX_open(ctx.get(), in2, &in2_len,
                                                 chunk_len + overhead_len,
                                                 nonce.get(), nonce_len, out,
                                                 out_len, ad.get(), ad_len);
                      })) {
      fprintf(stderr, "EVP_AEAD_CTX_open failed.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
  }

  results.PrintWithBytes(
      name + (direction == evp_aead_seal ? " seal" : " open"), chunk_len);
  return true;
}

static bool SpeedAEAD(const EVP_AEAD *aead, const std::string &name,
                      size_t ad_len, const std::string &selected, enum evp_aead_direction_t dir) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  TimeResults results;
  const size_t key_len = EVP_AEAD_key_length(aead);
  std::unique_ptr<uint8_t[]> key(new uint8_t[key_len]);

  if (!TimeFunction(&results, [&]() -> bool {
        BM_NAMESPACE::ScopedEVP_AEAD_CTX ctx;
        return EVP_AEAD_CTX_init_with_direction(
            ctx.get(), aead, key.get(), key_len, EVP_AEAD_DEFAULT_TAG_LENGTH,
            evp_aead_seal);
  })) {
    fprintf(stderr, "EVP_AEAD_CTX_init_with_direction failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
  results.Print(name + (dir == evp_aead_seal ? " seal " : " open ") + "init");

  for (size_t chunk_len : g_chunk_lengths) {
    if (!SpeedAEADChunk(aead, name, chunk_len, ad_len, dir)) {
      return false;
    }
  }
  return true;
}

static bool SpeedAEADOpen(const EVP_AEAD *aead, const std::string &name,
                          size_t ad_len, const std::string &selected) {
  return SpeedAEAD(aead, name, ad_len, selected, evp_aead_open);
}

static bool SpeedAEADSeal(const EVP_AEAD *aead, const std::string &name,
                          size_t ad_len, const std::string &selected) {
  return SpeedAEAD(aead, name, ad_len, selected, evp_aead_seal);
}
#if AWSLC_API_VERSION > 16
static bool SpeedSingleKEM(const std::string &name, int nid, const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }
  // Key generation (Alice).
  BM_NAMESPACE::UniquePtr<EVP_PKEY_CTX> a_ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_KEM, nullptr));
  if (!a_ctx ||
      !EVP_PKEY_CTX_kem_set_params(a_ctx.get(), nid) ||
      !EVP_PKEY_keygen_init(a_ctx.get())) {
    return false;
  }

  EVP_PKEY *key = EVP_PKEY_new();
  TimeResults results;
  if (!TimeFunction(&results, [&a_ctx, &key]() -> bool {
        return EVP_PKEY_keygen(a_ctx.get(), &key);
      })) {
    return false;
  }
  results.Print(name + " keygen");

  // Encapsulation setup (Bob).
  BM_NAMESPACE::UniquePtr<EVP_PKEY_CTX> b_ctx(EVP_PKEY_CTX_new(key, nullptr));

  size_t b_ss_len, b_ct_len;
  if (!EVP_PKEY_encapsulate(b_ctx.get(), NULL, &b_ct_len, NULL, &b_ss_len)) {
    return false;
  }
  std::unique_ptr<uint8_t[]> b_ct(new uint8_t[b_ct_len]);
  std::unique_ptr<uint8_t[]> b_ss(new uint8_t[b_ss_len]);

  // Decapsulation setup (Alice).
  a_ctx.reset(EVP_PKEY_CTX_new(key, nullptr));

  size_t a_ss_len;
  if (!EVP_PKEY_decapsulate(a_ctx.get(), NULL, &a_ss_len, NULL, 0)) {
    return false;
  }
  std::unique_ptr<uint8_t[]> a_ss(new uint8_t[a_ss_len]);

  // Sanity check (encaps/decaps gives the same shared secret).
  if (!EVP_PKEY_encapsulate(b_ctx.get(), b_ct.get(), &b_ct_len, b_ss.get(), &b_ss_len) ||
      !EVP_PKEY_decapsulate(a_ctx.get(), a_ss.get(), &a_ss_len, b_ct.get(), b_ct_len) ||
      (a_ss_len != b_ss_len)) {
    return false;
  }
  for (size_t i = 0; i < a_ss_len; i++) {
    if (a_ss.get()[i] != b_ss.get()[i]) {
        return false;
    }
  }

  // Measure encapsulation and decapsulation performance.
  if (!TimeFunction(&results, [&b_ct, &b_ct_len, &b_ss, &b_ss_len, &b_ctx]() -> bool {
        return EVP_PKEY_encapsulate(b_ctx.get(), b_ct.get(), &b_ct_len, b_ss.get(), &b_ss_len);
      })) {
    return false;
  }
  results.Print(name + " encaps");

  if (!TimeFunction(&results, [&b_ct, &b_ct_len, &a_ss, &a_ss_len, &a_ctx]() -> bool {
        return EVP_PKEY_decapsulate(a_ctx.get(), a_ss.get(), &a_ss_len, b_ct.get(), b_ct_len);
      })) {
    return false;
  }
  results.Print(name + " decaps");

  EVP_PKEY_free(key);

  return true;
}

static bool SpeedKEM(std::string selected) {
  return
#if AWSLC_API_VERSION >= 30
         SpeedSingleKEM("ML-KEM-512", NID_MLKEM512, selected) &&
         SpeedSingleKEM("ML-KEM-768", NID_MLKEM768, selected) &&
         SpeedSingleKEM("ML-KEM-1024", NID_MLKEM1024, selected) &&
#endif
         SpeedSingleKEM("Kyber512_R3", NID_KYBER512_R3, selected) &&
         SpeedSingleKEM("Kyber768_R3", NID_KYBER768_R3, selected) &&
         SpeedSingleKEM("Kyber1024_R3", NID_KYBER1024_R3, selected);
}

#if AWSLC_API_VERSION > 31

static bool SpeedDigestSignNID(const std::string &name, int nid,
                            const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  // Setup CTX for Sign/Verify Operations of type EVP_PKEY_PQDSA
  BM_NAMESPACE::UniquePtr<EVP_PKEY_CTX> pkey_ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_PQDSA, nullptr));

  // Setup CTX for specific signature alg NID
  EVP_PKEY_CTX_pqdsa_set_params(pkey_ctx.get(), nid);

  // Setup CTX for Keygen Operations
  if (!pkey_ctx || EVP_PKEY_keygen_init(pkey_ctx.get()) != 1) {
    return false;
  }

  EVP_PKEY *key = NULL;

  TimeResults results;
  if (!TimeFunction(&results, [&pkey_ctx, &key]() -> bool {
        return EVP_PKEY_keygen(pkey_ctx.get(), &key);
      })) {
    return false;
  }
  results.Print(name + " keygen");

  // Setup CTX for Sign operations
  bssl::ScopedEVP_MD_CTX md_ctx;

  // message to be signed
  static const uint8_t msg[32] = {0};
  size_t msg_len = 32;

  // to keep this function generic, we obtain the signature size (different for
  // each algorithm) at run time by attempting a sign with a NULL signature.
  // The sign algorithm must support calling NULL to obtain the signature length
  size_t sig_len = 0;
  EVP_DigestSignInit(md_ctx.get(), NULL, NULL, NULL, key);
  EVP_DigestSign(md_ctx.get(), NULL, &sig_len, msg, msg_len);
  std::unique_ptr<uint8_t[]> signature(new uint8_t[sig_len]);


  if (!TimeFunction(&results, [&md_ctx, &signature, &sig_len, msg_len ]() -> bool {
        return EVP_DigestSign(md_ctx.get(), signature.get(), &sig_len, msg, msg_len);
      })) {
    return false;
  }
  results.Print(name + " signing");

  // Verify
  if (!TimeFunction(&results, [&md_ctx, &signature, &sig_len, msg_len ]() -> bool {
        return EVP_DigestVerify(md_ctx.get(), signature.get(), sig_len, msg, msg_len);
      })) {
    return false;
  }
  results.Print(name + " verify");

  EVP_PKEY_free(key);
  md_ctx.Reset();
  return true;
}

static bool SpeedDigestSign(const std::string &selected) {
  return SpeedDigestSignNID("MLDSA44", NID_MLDSA44, selected) &&
         SpeedDigestSignNID("MLDSA65", NID_MLDSA65, selected) &&
         SpeedDigestSignNID("MLDSA87", NID_MLDSA87, selected);
}

#endif

#endif
#endif

static bool SpeedAESBlock(const std::string &name, unsigned bits,
                          const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  static const uint8_t kZero[32] = {0};

  {
    TimeResults results;
    if (!TimeFunction(&results, [&]() -> bool {
          AES_KEY key;
          return AES_set_encrypt_key(kZero, bits, &key) == 0;
        })) {
      fprintf(stderr, "AES_set_encrypt_key failed.\n");
      return false;
    }
    results.Print(name + " encrypt setup");
  }

  {
    AES_KEY key;
    if (AES_set_encrypt_key(kZero, bits, &key) != 0) {
      return false;
    }
    uint8_t block[16] = {0};
    TimeResults results;
    if (!TimeFunction(&results, [&]() -> bool {
          AES_encrypt(block, block, &key);
          return true;
        })) {
      fprintf(stderr, "AES_encrypt failed.\n");
      return false;
    }
    results.Print(name + " encrypt");
  }

  {
    TimeResults results;
    if (!TimeFunction(&results, [&]() -> bool {
          AES_KEY key;
          return AES_set_decrypt_key(kZero, bits, &key) == 0;
        })) {
      fprintf(stderr, "AES_set_decrypt_key failed.\n");
      return false;
    }
    results.Print(name + " decrypt setup");
  }

  {
    AES_KEY key;
    if (AES_set_decrypt_key(kZero, bits, &key) != 0) {
      return false;
    }
    uint8_t block[16] = {0};
    TimeResults results;
    if (!TimeFunction(&results, [&]() -> bool {
          AES_decrypt(block, block, &key);
          return true;
        })) {
      fprintf(stderr, "AES_decrypt failed.\n");
      return false;
    }
    results.Print(name + " decrypt");
  }

  return true;
}

static bool SpeedAES256XTS(const std::string &name, //const size_t in_len,
                           const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  const EVP_CIPHER *cipher = EVP_aes_256_xts();
  const size_t key_len = EVP_CIPHER_key_length(cipher);
  const size_t iv_len = EVP_CIPHER_iv_length(cipher);

  std::vector<uint8_t> key(key_len);
  std::vector<uint8_t> iv(iv_len, 9);
  std::vector<uint8_t> in, out;

  // key = key1||key2 and key1 should not equal key2
  std::generate(key.begin(), key.end(), [] {
    static uint8_t i = 0;
    return i++;
  });

  BM_NAMESPACE::UniquePtr<EVP_CIPHER_CTX> ctx(EVP_CIPHER_CTX_new());
  TimeResults results;

  // Benchmark just EVP_EncryptInit_ex with the cipher and key, the encrypt benchmark loop will reuse both
  if (!TimeFunction(&results, [&]() -> bool {
        return EVP_EncryptInit_ex(ctx.get(), cipher, nullptr, key.data(),
                                  iv.data());
      })) {
    fprintf(stderr, "EVP_EncryptInit_ex failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
  results.Print(name + " encrypt init");

  // Benchmark initialisation and encryption
  for (size_t in_len : g_chunk_lengths) {
    if (in_len < AES_BLOCK_SIZE) {
      // AES-XTS requires encrypting at least the block size
      continue;
    }
    in.resize(in_len);
    out.resize(in_len);
    std::fill(in.begin(), in.end(), 0x5a);
    int len;
    if (!TimeFunction(&results, [&]() -> bool {
          if (!EVP_EncryptInit_ex(ctx.get(), nullptr, nullptr, nullptr,
                                  iv.data()) ||
              !EVP_EncryptUpdate(ctx.get(), out.data(), &len, in.data(),
                                 in.size())) {
            return false;
          }
          return true;
        })) {
      fprintf(stderr, "AES-256-XTS initialisation or encryption failed.\n");
      return false;
    }
    results.PrintWithBytes(name + " encrypt", in_len);
  }

  // Benchmark initialisation and decryption
  // Benchmark just EVP_DecryptInit_ex with the cipher and key, the decrypt benchmark loop will reuse both
  if (!TimeFunction(&results, [&]() -> bool {
        return EVP_DecryptInit_ex(ctx.get(), cipher, nullptr, key.data(),
                                  iv.data());
      })) {
    fprintf(stderr, "EVP_DecryptInit_ex failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
  results.Print(name + " decrypt init");

  for (size_t in_len : g_chunk_lengths) {
    if (in_len < AES_BLOCK_SIZE) {
      // AES-XTS requires decrypting at least the block size
      continue;
    }
    in.resize(in_len);
    out.resize(in_len);
    std::fill(in.begin(), in.end(), 0x5a);
    int len;
    if (!TimeFunction(&results, [&]() -> bool {
          if (!EVP_DecryptInit_ex(ctx.get(), nullptr, nullptr, nullptr,
                                  iv.data()) ||
              !EVP_DecryptUpdate(ctx.get(), out.data(), &len, in.data(),
                                 in.size())) {
            return false;
          }
          return true;
        })) {
      fprintf(stderr, "AES-256-XTS initialisation or decryption failed.\n");
      return false;
    }
    results.PrintWithBytes(name + " decrypt", in_len);
  }

  return true;
}

static bool SpeedHashChunk(const EVP_MD *md, std::string name,
                           size_t chunk_len) {
  // OpenSSL 1.0.x has a different API to create an EVP_MD_CTX
#if defined(OPENSSL_1_0_BENCHMARK)
  BM_NAMESPACE::UniquePtr<EVP_MD_CTX> ctx(EVP_MD_CTX_create());
#else
  BM_NAMESPACE::UniquePtr<EVP_MD_CTX> ctx(EVP_MD_CTX_new());
#endif
  std::unique_ptr<uint8_t[]> input(new uint8_t[chunk_len]);

  TimeResults results;
  if (!TimeFunction(&results, [&ctx, md, chunk_len, &input]() -> bool {
        uint8_t digest[EVP_MAX_MD_SIZE];
        unsigned int md_len;

        return EVP_DigestInit_ex(ctx.get(), md, NULL /* ENGINE */) &&
               EVP_DigestUpdate(ctx.get(), input.get(), chunk_len) &&
#if (!defined(OPENSSL_1_0_BENCHMARK) && !defined(BORINGSSL_BENCHMARK) && !defined(OPENSSL_IS_AWSLC)) || AWSLC_API_VERSION >= 22
               (EVP_MD_flags(md) & EVP_MD_FLAG_XOF) ?
                 EVP_DigestFinalXOF(ctx.get(), digest, 32) : EVP_DigestFinal_ex(ctx.get(), digest, &md_len);
#else
               EVP_DigestFinal_ex(ctx.get(), digest, &md_len);
#endif
      })) {
    fprintf(stderr, "EVP_DigestInit_ex failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  results.PrintWithBytes(name, chunk_len);
  return true;
}

static bool SpeedHash(const EVP_MD *md, const std::string &name,
                      const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  for (size_t chunk_len : g_chunk_lengths) {
    if (!SpeedHashChunk(md, name, chunk_len)) {
      return false;
    }
  }

  return true;
}

static bool SpeedHmacChunk(const EVP_MD *md, std::string name,
                           size_t chunk_len) {
  // OpenSSL 1.0.x doesn't have a function that creates a new,
  // properly initialized HMAC pointer so we need to create
  // the pointer and then do the initialization logic ourselves
#if defined(OPENSSL_1_0_BENCHMARK)
  BM_NAMESPACE::UniquePtr<HMAC_CTX> ctx(new HMAC_CTX);
  HMAC_CTX_init(ctx.get());
#else
  BM_NAMESPACE::UniquePtr<HMAC_CTX> ctx(HMAC_CTX_new());
#endif
  std::unique_ptr<uint8_t[]> input(new uint8_t[chunk_len]);
  const size_t key_len = EVP_MD_size(md);
  std::unique_ptr<uint8_t[]> key(new uint8_t[key_len]);
  BM_memset(key.get(), 0, key_len);

  if (!HMAC_Init_ex(ctx.get(), key.get(), key_len, md, NULL /* ENGINE */)) {
    fprintf(stderr, "Failed to create HMAC_CTX.\n");
  }
  TimeResults results;
  if (!TimeFunction(&results, [&ctx, chunk_len, &input]() -> bool {
        uint8_t digest[EVP_MAX_MD_SIZE];
        unsigned int md_len;

        return HMAC_Init_ex(ctx.get(), NULL, 0, NULL, NULL) &&
               HMAC_Update(ctx.get(), input.get(), chunk_len) &&
               HMAC_Final(ctx.get(), digest, &md_len);
      })) {
    fprintf(stderr, "HMAC_Final failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  results.PrintWithBytes(name, chunk_len);
  return true;
}

static bool SpeedHmac(const EVP_MD *md, const std::string &name,
                      const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }
  TimeResults results;
  const size_t key_len = EVP_MD_size(md);
  std::unique_ptr<uint8_t[]> key(new uint8_t[key_len]);
  BM_memset(key.get(), 0, key_len);
#if defined(OPENSSL_1_0_BENCHMARK)
  BM_NAMESPACE::UniquePtr<HMAC_CTX> ctx(new HMAC_CTX);
  HMAC_CTX_init(ctx.get());
#else
  BM_NAMESPACE::UniquePtr<HMAC_CTX> ctx(HMAC_CTX_new());
#endif
  if (!TimeFunction(&results, [&]() -> bool {
        return HMAC_Init_ex(ctx.get(), key.get(), key_len, md, NULL /* ENGINE */);
      })) {
    fprintf(stderr, "HMAC_Init_ex failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }
  results.Print(name + " init");

  for (size_t chunk_len : g_chunk_lengths) {
    if (!SpeedHmacChunk(md, name, chunk_len)) {
      return false;
    }
  }

  return true;
}

static bool SpeedHmacChunkOneShot(const EVP_MD *md, std::string name,
                           size_t chunk_len) {
  std::unique_ptr<uint8_t[]> input(new uint8_t[chunk_len]);
  const size_t key_len = EVP_MD_size(md);
  std::unique_ptr<uint8_t[]> key(new uint8_t[key_len]);
  BM_memset(key.get(), 0, key_len);


  TimeResults results;
  if (!TimeFunction(&results, [&key, key_len, md, chunk_len, &input]() -> bool {

        uint8_t digest[EVP_MAX_MD_SIZE] = {0};
        unsigned int md_len = EVP_MAX_MD_SIZE;

        return HMAC(md, key.get(), key_len, input.get(), chunk_len, digest, &md_len) != nullptr;
      })) {
    fprintf(stderr, "HMAC_Final failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  results.PrintWithBytes(name, chunk_len);
  return true;
}

static bool SpeedHmacOneShot(const EVP_MD *md, const std::string &name,
                      const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  for (size_t chunk_len : g_chunk_lengths) {
    if (!SpeedHmacChunkOneShot(md, name, chunk_len)) {
      return false;
    }
  }

  return true;
}

#if !defined(OPENSSL_1_0_BENCHMARK)
static bool SpeedCmacChunk(const EVP_CIPHER *cipher, std::string name,
                           size_t chunk_len) {
  BM_NAMESPACE::UniquePtr<CMAC_CTX> ctx(CMAC_CTX_new());
  std::unique_ptr<uint8_t[]> input(new uint8_t[chunk_len]);
  const size_t key_len = EVP_CIPHER_key_length(cipher);
  std::unique_ptr<uint8_t[]> key(new uint8_t[key_len]);
  BM_memset(key.get(), 0, key_len);

  if (!CMAC_Init(ctx.get(), key.get(), key_len, cipher, NULL /* ENGINE */)) {
    fprintf(stderr, "Failed to create CMAC_CTX.\n");
  }
  TimeResults results;
  if (!TimeFunction(&results, [&ctx, chunk_len, &input]() -> bool {
        uint8_t digest[EVP_MAX_MD_SIZE];
        size_t out_len;

        return
#if defined(OPENSSL_IS_AWSLC) || defined(OPENSSL_IS_BORINGSSL)
               CMAC_Reset(ctx.get()) &&
#else
               CMAC_Init(ctx.get(), nullptr, 0, nullptr, nullptr /* ENGINE */) &&
#endif
               CMAC_Update(ctx.get(), input.get(), chunk_len) &&
               CMAC_Final(ctx.get(), digest, &out_len);
      })) {
    fprintf(stderr, "CMAC_Final failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  results.PrintWithBytes(name, chunk_len);
  return true;
}

static bool SpeedCmac(const EVP_CIPHER *cipher, const std::string &name, const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }
  TimeResults results;
  const size_t key_len = EVP_CIPHER_key_length(cipher);
  std::unique_ptr<uint8_t[]> key(new uint8_t[key_len]);
  BM_memset(key.get(), 0, key_len);
  BM_NAMESPACE::UniquePtr<CMAC_CTX> ctx(CMAC_CTX_new());
  if (!TimeFunction(&results, [&]() -> bool {
        return CMAC_Init(ctx.get(), key.get(), key_len, cipher,
                         nullptr /* ENGINE */);
      })) {
    fprintf(stderr, "CMAC_Init failed.\n");
    ERR_print_errors_fp(stderr);
    return false;
      }
  results.Print(name + " init");

  for (size_t chunk_len : g_chunk_lengths) {
    if (!SpeedCmacChunk(cipher, name, chunk_len)) {
      return false;
    }
  }

  return true;
}

#endif

using RandomFunction = std::function<void(uint8_t *, size_t)>;
static bool SpeedRandomChunk(RandomFunction function, std::string name, size_t chunk_len) {
  std::unique_ptr<uint8_t[]> output(new uint8_t[chunk_len]);

  TimeResults results;
  if (!TimeFunction(&results, [chunk_len, &output, &function]() -> bool {
        function(output.get(), chunk_len);
        return true;
      })) {
    return false;
  }

  results.PrintWithBytes(name, chunk_len);
  return true;
}

static bool SpeedRandom(RandomFunction function, const std::string &name, const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  for (size_t chunk_len : g_chunk_lengths) {
    if (!SpeedRandomChunk(function, name, chunk_len)) {
      return false;
    }
  }

  return true;
}

struct curve_config {
  std::string name;
  int nid;
};

curve_config supported_curves[] = {{"P-224", NID_secp224r1},
                                   {"P-256", NID_X9_62_prime256v1},
                                   {"P-384", NID_secp384r1},
                                   {"P-521", NID_secp521r1},
#if (!defined(OPENSSL_IS_BORINGSSL) && !defined(OPENSSL_IS_AWSLC)) || AWSLC_API_VERSION > 16
                                   {"secp256k1", NID_secp256k1},
#endif
};

static bool SpeedECDHCurve(const std::string &name, int nid,
                           const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  BM_NAMESPACE::UniquePtr<EC_KEY> peer_key(EC_KEY_new_by_curve_name(nid));
  if (!peer_key ||
      !EC_KEY_generate_key(peer_key.get())) {
    fprintf(stderr, "NID %d for %s not supported.\n", nid, name.c_str());
    return false;
  }

  size_t peer_value_len = EC_POINT_point2oct(
      EC_KEY_get0_group(peer_key.get()), EC_KEY_get0_public_key(peer_key.get()),
      POINT_CONVERSION_UNCOMPRESSED, nullptr, 0, nullptr);
  if (peer_value_len == 0) {
    return false;
  }
  std::unique_ptr<uint8_t[]> peer_value(new uint8_t[peer_value_len]);
  peer_value_len = EC_POINT_point2oct(
      EC_KEY_get0_group(peer_key.get()), EC_KEY_get0_public_key(peer_key.get()),
      POINT_CONVERSION_UNCOMPRESSED, peer_value.get(), peer_value_len, nullptr);
  if (peer_value_len == 0) {
    return false;
  }

  TimeResults results;
  if (!TimeFunction(&results, [nid, peer_value_len, &peer_value]() -> bool {
        BM_NAMESPACE::UniquePtr<EC_KEY> key(EC_KEY_new_by_curve_name(nid));
        if (!key ||
            !EC_KEY_generate_key(key.get())) {
          return false;
        }
        const EC_GROUP *const group = EC_KEY_get0_group(key.get());
        BM_NAMESPACE::UniquePtr<EC_POINT> point(EC_POINT_new(group));
        BM_NAMESPACE::UniquePtr<EC_POINT> peer_point(EC_POINT_new(group));
        BM_NAMESPACE::UniquePtr<BN_CTX> ctx(BN_CTX_new());
        BM_NAMESPACE::UniquePtr<BIGNUM> x(BN_new());
        if (!point || !peer_point || !ctx || !x ||
            !EC_POINT_oct2point(group, peer_point.get(), peer_value.get(),
                                peer_value_len, ctx.get()) ||
            !EC_POINT_mul(group, point.get(), nullptr, peer_point.get(),
                          EC_KEY_get0_private_key(key.get()), ctx.get()) ||
            !EC_POINT_get_affine_coordinates_GFp(group, point.get(), x.get(),
                                                 nullptr, ctx.get())) {
          return false;
        }

        return true;
      })) {
    return false;
  }

  results.Print(name);
  return true;
}


static bool SpeedECKeyGenerateKey(bool is_fips, const std::string &name,
                                      int nid, const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }
  BM_NAMESPACE::UniquePtr<EC_KEY> key(EC_KEY_new_by_curve_name(nid));

  TimeResults results;
  if (is_fips) {
#if !defined(OPENSSL_BENCHMARK)
    if (!TimeFunction(&results, [&key]() -> bool {
          return EC_KEY_generate_key_fips(key.get()) == 1;
        })) {
      return false;
    }
#else
    return true;
#endif
  } else {
    if (!TimeFunction(&results, [&key]() -> bool {
          return EC_KEY_generate_key(key.get()) == 1;
        })) {
      return false;
    }
  }
  results.Print(is_fips ? name + " with EC_KEY_generate_key_fips"
                        : name + " with EC_KEY_generate_key");
  return true;
}

static bool SpeedECKeyGenCurve(const std::string &name, int nid,
                            const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  // Setup CTX for EC Operations
  BM_NAMESPACE::UniquePtr<EVP_PKEY_CTX> pkey_ctx(EVP_PKEY_CTX_new_id(EVP_PKEY_EC, nullptr));

  // Setup CTX for Keygen Operations
  if (!pkey_ctx || EVP_PKEY_keygen_init(pkey_ctx.get()) != 1) {
    return false;
  }

  // Set CTX to use our curve
  if (EVP_PKEY_CTX_set_ec_paramgen_curve_nid(pkey_ctx.get(), nid) != 1) {
    return false;
  }

  EVP_PKEY *key = EVP_PKEY_new();

  TimeResults results;
  if (!TimeFunction(&results, [&pkey_ctx, &key]() -> bool {
        return EVP_PKEY_keygen(pkey_ctx.get(), &key);
      })) {
      return false;
  }
  EVP_PKEY_free(key);
  results.Print(name + " with EVP_PKEY_keygen");
  return true;
}

static bool SpeedECDSACurve(const std::string &name, int nid,
                            const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  BM_NAMESPACE::UniquePtr<EC_KEY> key(EC_KEY_new_by_curve_name(nid));
  if (!key ||
      !EC_KEY_generate_key(key.get())) {
    return false;
  }

  uint8_t signature[256];
  if (BM_ECDSA_size(key.get()) > sizeof(signature)) {
    return false;
  }
  uint8_t digest[20];
  BM_memset(digest, 42, sizeof(digest));
  unsigned sig_len;

  TimeResults results;
  if (!TimeFunction(&results, [&key, &signature, &digest, &sig_len]() -> bool {
        return ECDSA_sign(0, digest, sizeof(digest), signature, &sig_len,
                          key.get()) == 1;
      })) {
    return false;
  }

  results.Print(name + " signing");

  if (!TimeFunction(&results, [&key, &signature, &digest, sig_len]() -> bool {
        return ECDSA_verify(0, digest, sizeof(digest), signature, sig_len,
                            key.get()) == 1;
      })) {
    return false;
  }

  results.Print(name + " verify");

  return true;
}

static bool SpeedECKeyGenerateKey(bool is_fips, const std::string &selected) {
  for (const auto& config : supported_curves) {
    std::string message = "Generate " + config.name;
    if(!SpeedECKeyGenerateKey(is_fips, message, config.nid, selected)) {
      return false;
    }
  }
  return true;
}

static bool SpeedECDH(const std::string &selected) {
  for (const auto& config : supported_curves) {
    std::string message = "ECDH " + config.name;
    if(!SpeedECDHCurve(message, config.nid, selected)) {
      return false;
    }
  }
  return true;
}

static bool SpeedECKeyGen(const std::string &selected) {
  for (const auto& config : supported_curves) {
    std::string message = "Generate " + config.name;
    if(!SpeedECKeyGenCurve(message, config.nid, selected)) {
      return false;
    }
  }
  return true;
}

static bool SpeedECDSA(const std::string &selected) {
  for (const auto& config : supported_curves) {
    std::string message = "ECDSA " + config.name;
    if(!SpeedECDSACurve(message, config.nid, selected)) {
      return false;
    }
  }
  return true;
}

#if !defined(OPENSSL_1_0_BENCHMARK)
static EVP_PKEY * evp_generate_key(const int curve_nid) {

  // P NIST curves are abstracted under the same virtual function table which
  // is configured using |EVP_PKEY_EC|.
  int local_nid = curve_nid;
  if (curve_nid != NID_X25519) {
    local_nid = EVP_PKEY_EC;
  }

  BM_NAMESPACE::UniquePtr<EVP_PKEY_CTX> evp_pkey_ctx(EVP_PKEY_CTX_new_id(local_nid, nullptr));

  if (local_nid == EVP_PKEY_EC) {
    // Since P NIST curves are abstracted under the same virtual function table,
    // we haven't actually loaded the group yet. This must be done before we can
    // generate the key.
    EVP_PKEY *curve = nullptr;
    if (!EVP_PKEY_paramgen_init(evp_pkey_ctx.get()) ||
        !EVP_PKEY_CTX_set_ec_paramgen_curve_nid(evp_pkey_ctx.get(), curve_nid) ||
        !EVP_PKEY_paramgen(evp_pkey_ctx.get(), &curve) ||
        curve == nullptr) {
      return nullptr;
    }
    BM_NAMESPACE::UniquePtr<EVP_PKEY> curve_uniqueptr(curve);
    evp_pkey_ctx.reset(EVP_PKEY_CTX_new(curve_uniqueptr.get(), NULL));
    if (evp_pkey_ctx == nullptr) {
      return nullptr;
    }
  }

  EVP_PKEY *key = nullptr;
  if (!EVP_PKEY_keygen_init(evp_pkey_ctx.get()) ||
      !EVP_PKEY_keygen(evp_pkey_ctx.get(), &key)) {
    return nullptr;
  }

  return key;
}

// One could model serialisation as well using
// |EVP_PKEY_{get,set}1_tls_encodedpoint|. But that pair of functions only
// support a subset of curve types. |SpeedECDH| includes deserialisation of the
// peer key. Leaving this out doesn't bias measurements though.
static bool SpeedEvpEcdhCurve(const std::string &name, int nid,
                           const std::string &selected) {

  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  // First we need a peer key that we are going to re-use for all iterations.
  BM_NAMESPACE::UniquePtr<EVP_PKEY> peer_key(evp_generate_key(nid));
  if (peer_key == nullptr) {
    return false;
  }

  if (nid != NID_X25519) {
    // To model deriving an ECDHE shared secret, we need the peer key. But void
    // the private part, to avoid biasing measurements. For example, when
    // performing key validation. Currently, this is only a problem for the
    // P NIST curve types.
    BM_NAMESPACE::UniquePtr<EVP_PKEY> only_public_key_evp_pkey(EVP_PKEY_new());
    BM_NAMESPACE::UniquePtr<EC_KEY> only_public_key_ec_key(EC_KEY_new_by_curve_name(nid));
    if (only_public_key_ec_key == nullptr ||
        only_public_key_evp_pkey == nullptr) {
      return false;
    }
    // Non-owning reference.
    const EC_KEY *peer_key_ec_key = EVP_PKEY_get0_EC_KEY(peer_key.get());
    if (peer_key_ec_key == nullptr ||
        !EC_KEY_set_public_key(only_public_key_ec_key.get(),
          EC_KEY_get0_public_key(peer_key_ec_key)) ||
        !EVP_PKEY_assign_EC_KEY(only_public_key_evp_pkey.get(), only_public_key_ec_key.release())) {
      return false;
    }
    peer_key.reset(only_public_key_evp_pkey.release());
  }

  TimeResults results;
  if (!TimeFunction(&results, [nid, &peer_key]() -> bool {
    BM_NAMESPACE::UniquePtr<EVP_PKEY> my_key(evp_generate_key(nid));

#if defined(OPENSSL_BENCHMARK)
    // For AWS-LC EVP_PKEY_derive() calls ECDH_compute_shared_secret() that
    // performs the public key check.
    if (nid != NID_X25519) {
      // For the supported P NIST curves, the peer public key must be validated
      // to ensure proper computation.
      if (!EC_KEY_check_key(EVP_PKEY_get0_EC_KEY(peer_key.get()))) {
        return false;
      }
    }
#endif

    BM_NAMESPACE::UniquePtr<EVP_PKEY_CTX> derive_ctx(EVP_PKEY_CTX_new(my_key.get(), NULL));
    if (derive_ctx == nullptr) {
      return false;
    }

    size_t shared_secret_size = 0;
    if (!EVP_PKEY_derive_init(derive_ctx.get()) ||
        !EVP_PKEY_derive_set_peer(derive_ctx.get(), peer_key.get()) ||
        !EVP_PKEY_derive(derive_ctx.get(), NULL, &shared_secret_size) ||
        (shared_secret_size == 0)) {
      return false;
    }

    std::unique_ptr<uint8_t[]> shared_secret(new uint8_t[shared_secret_size]);
    if (!EVP_PKEY_derive(derive_ctx.get(), shared_secret.get(), &shared_secret_size)) {
      return false;
    }

    return true;
    })) {
      return false;
  }

  results.Print(name);
  return true;
}

static bool SpeedEvpEcdh(const std::string &selected) {
  for (const auto& config : supported_curves) {
      std::string message = "EVP ECDH " + config.name;
      if(!SpeedEvpEcdhCurve(message, config.nid, selected)) {
        return false;
      }
  }
  return SpeedEvpEcdhCurve("EVP ECDH X25519", NID_X25519, selected);
}

static bool SpeedECPOINTCurve(const std::string &name, int nid,
                       const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  BM_NAMESPACE::UniquePtr<EC_GROUP> group(EC_GROUP_new_by_curve_name(nid));
  BM_NAMESPACE::UniquePtr<BN_CTX> ctx(BN_CTX_new());
  BM_NAMESPACE::UniquePtr<BIGNUM> scalar0(BN_new());
  BM_NAMESPACE::UniquePtr<BIGNUM> scalar1(BN_new());
  BM_NAMESPACE::UniquePtr<EC_POINT> pin0(EC_POINT_new(group.get()));
  BM_NAMESPACE::UniquePtr<EC_POINT> pin1(EC_POINT_new(group.get()));
  BM_NAMESPACE::UniquePtr<EC_POINT> pout(EC_POINT_new(group.get()));


  // Generate two random scalars modulo the EC group order.
  if (!BN_rand_range(scalar0.get(), EC_GROUP_get0_order(group.get())) ||
      !BN_rand_range(scalar1.get(), EC_GROUP_get0_order(group.get()))) {
      return false;
  }

  // Generate two random EC point.
  EC_POINT_mul(group.get(), pin0.get(), scalar0.get(), nullptr, nullptr, ctx.get());
  EC_POINT_mul(group.get(), pin1.get(), scalar1.get(), nullptr, nullptr, ctx.get());

  TimeResults results;

  // Measure point doubling.
  if (!TimeFunction(&results, [&group, &pout, &ctx, &pin0]() -> bool {
        if (!EC_POINT_dbl(group.get(), pout.get(), pin0.get(), ctx.get())) {
          return false;
        }

        return true;
      })) {
    return false;
  }
  results.Print(name + " dbl");

  // Measure point addition.
  if (!TimeFunction(&results, [&group, &pout, &ctx, &pin0, &pin1]() -> bool {
        if (!EC_POINT_add(group.get(), pout.get(), pin0.get(), pin1.get(), ctx.get())) {
          return false;
        }

        return true;
      })) {
    return false;
  }
  results.Print(name + " add");

  // Measure scalar multiplication of an arbitrary curve point.
  if (!TimeFunction(&results, [&group, &pout, &ctx, &pin0, &scalar0]() -> bool {
        if (!EC_POINT_mul(group.get(), pout.get(), nullptr, pin0.get(), scalar0.get(), ctx.get())) {
          return false;
        }

        return true;
      })) {
    return false;
  }
  results.Print(name + " mul");

  // Measure scalar multiplication of the curve based point.
  if (!TimeFunction(&results, [&group, &pout, &ctx, &scalar0]() -> bool {
        if (!EC_POINT_mul(group.get(), pout.get(), scalar0.get(), nullptr, nullptr, ctx.get())) {
          return false;
        }

        return true;
      })) {
    return false;
  }
  results.Print(name + " mul base");

  // Measure scalar multiplication of based point and arbitrary point.
  if (!TimeFunction(&results, [&group, &pout, &pin0, &ctx, &scalar0, &scalar1]() -> bool {
        if (!EC_POINT_mul(group.get(), pout.get(), scalar1.get(), pin0.get(), scalar0.get(), ctx.get())) {
          return false;
        }

        return true;
      })) {
    return false;
  }
  results.Print(name + " mul public");

  return true;
}

static bool SpeedECPOINT(const std::string &selected) {
  for (const auto& config : supported_curves) {
    std::string message = "EC POINT " + config.name;
    if(!SpeedECPOINTCurve(message, config.nid, selected)) {
      return false;
    }
  }
  return true;
}

#endif // !defined(OPENSSL_1_0_BENCHMARK)

// Only new AWS-LC (>= 22) and new OpenSSL (>= 1.1.1) support FFDH
#if (!defined(OPENSSL_1_0_BENCHMARK) && !defined(BORINGSSL_BENCHMARK) && !defined(OPENSSL_IS_AWSLC)) || AWSLC_API_VERSION >= 22
static bool SpeedFFDHGroup(const std::string &name, int nid,
                           const std::string &selected) {
  if (!selected.empty() && name.find(selected) == std::string::npos) {
    return true;
  }

  BM_NAMESPACE::UniquePtr<DH> server_dh(DH_new_by_nid(nid));
  if(!DH_generate_key(server_dh.get())) {
    return false;
  }
  const BIGNUM *server_pub = DH_get0_pub_key(server_dh.get());

  int dh_size = DH_size(server_dh.get());
  std::unique_ptr<uint8_t[]> shared_secret(new uint8_t[dh_size]);

  TimeResults results;
  if (!TimeFunction(&results, [&shared_secret, &server_pub, &dh_size, &nid]() -> bool {
        BM_NAMESPACE::UniquePtr<DH> client_dh(DH_new_by_nid(nid));
        return DH_generate_key(client_dh.get()) &&
               dh_size == DH_compute_key_padded(shared_secret.get(), server_pub, client_dh.get());
      })) {
    return false;
  }

  results.Print(name);
  return true;
}

static bool SpeedFFDH(const std::string &selected) {
  return SpeedFFDHGroup("FFDH 2048", NID_ffdhe2048, selected) &&
         SpeedFFDHGroup("FFDH 4096", NID_ffdhe4096, selected);
}
#endif //(!defined(OPENSSL_1_0_BENCHMARK) && !defined(BORINGSSL_BENCHMARK) && !defined(OPENSSL_IS_AWSLC)) || AWSLC_API_VERSION >= 22

#if !defined(OPENSSL_BENCHMARK)
static bool Speed25519(const std::string &selected) {
  if (!selected.empty() && selected.find("25519") == std::string::npos) {
    return true;
  }

  TimeResults results;

  uint8_t public_key[32], private_key[64];

  if (!TimeFunction(&results, [&public_key, &private_key]() -> bool {
        ED25519_keypair(public_key, private_key);
        return true;
      })) {
    return false;
  }

  results.Print("Ed25519 key generation");

  static const uint8_t kMessage[] = {0, 1, 2, 3, 4, 5};
  uint8_t signature[64];

  if (!TimeFunction(&results, [&private_key, &signature]() -> bool {
        return ED25519_sign(signature, kMessage, sizeof(kMessage),
                            private_key) == 1;
      })) {
    return false;
  }

  results.Print("Ed25519 signing");

  if (!TimeFunction(&results, [&public_key, &signature]() -> bool {
        return ED25519_verify(kMessage, sizeof(kMessage), signature,
                              public_key) == 1;
      })) {
    fprintf(stderr, "Ed25519 verify failed.\n");
    return false;
  }

  results.Print("Ed25519 verify");

  if (!TimeFunction(&results, []() -> bool {
        uint8_t out[32], in[32];
        BM_memset(in, 0, sizeof(in));
        X25519_public_from_private(out, in);
        return true;
      })) {
    fprintf(stderr, "Curve25519 base-point multiplication failed.\n");
    return false;
  }

  results.Print("Curve25519 base-point multiplication");

  if (!TimeFunction(&results, []() -> bool {
        uint8_t out[32], in1[32], in2[32];
        BM_memset(in1, 0, sizeof(in1));
        BM_memset(in2, 0, sizeof(in2));
        in1[0] = 1;
        in2[0] = 9;
        return X25519(out, in1, in2) == 1;
      })) {
    fprintf(stderr, "Curve25519 arbitrary point multiplication failed.\n");
    return false;
  }

  results.Print("Curve25519 arbitrary point multiplication");

  if (!TimeFunction(&results, []() -> bool {
        uint8_t out_base[32], in_base[32];
        BM_memset(in_base, 0, sizeof(in_base));
        X25519_public_from_private(out_base, in_base);

        uint8_t out[32], in1[32], in2[32];
        BM_memset(in1, 0, sizeof(in1));
        BM_memset(in2, 0, sizeof(in2));
        in1[0] = 1;
        in2[0] = 9;
        return X25519(out, in1, in2) == 1;
      })) {
    fprintf(stderr, "ECDH X25519 failed.\n");
    return false;
  }

  results.Print("ECDH X25519");

  return true;
}

static bool SpeedSPAKE2(const std::string &selected) {
  if (!selected.empty() && selected.find("SPAKE2") == std::string::npos) {
    return true;
  }

  TimeResults results;

  static const uint8_t kAliceName[] = {'A'};
  static const uint8_t kBobName[] = {'B'};
  static const uint8_t kPassword[] = "password";
  BM_NAMESPACE::UniquePtr<SPAKE2_CTX> alice(SPAKE2_CTX_new(spake2_role_alice,
                                    kAliceName, sizeof(kAliceName), kBobName,
                                    sizeof(kBobName)));
  uint8_t alice_msg[SPAKE2_MAX_MSG_SIZE];
  size_t alice_msg_len;

  if (!SPAKE2_generate_msg(alice.get(), alice_msg, &alice_msg_len,
                           sizeof(alice_msg),
                           kPassword, sizeof(kPassword))) {
    fprintf(stderr, "SPAKE2_generate_msg failed.\n");
    return false;
  }

  if (!TimeFunction(&results, [&alice_msg, alice_msg_len]() -> bool {
        BM_NAMESPACE::UniquePtr<SPAKE2_CTX> bob(SPAKE2_CTX_new(spake2_role_bob,
                                        kBobName, sizeof(kBobName), kAliceName,
                                        sizeof(kAliceName)));
        uint8_t bob_msg[SPAKE2_MAX_MSG_SIZE], bob_key[64];
        size_t bob_msg_len, bob_key_len;
        if (!SPAKE2_generate_msg(bob.get(), bob_msg, &bob_msg_len,
                                 sizeof(bob_msg), kPassword,
                                 sizeof(kPassword)) ||
            !SPAKE2_process_msg(bob.get(), bob_key, &bob_key_len,
                                sizeof(bob_key), alice_msg, alice_msg_len)) {
          return false;
        }

        return true;
      })) {
    fprintf(stderr, "SPAKE2 failed.\n");
  }

  results.Print("SPAKE2 over Ed25519");

  return true;
}
#endif

#if !defined(OPENSSL_1_0_BENCHMARK)
static bool SpeedScrypt(const std::string &selected) {
  if (!selected.empty() && selected.find("scrypt") == std::string::npos) {
    return true;
  }

  TimeResults results;

  static const char kPassword[] = "passwordPASSWORD";
  static const uint8_t kSalt[] = "NaClSodiumChloride";

  if (!TimeFunction(&results, [&]() -> bool {
        uint8_t out[64];
        return !!EVP_PBE_scrypt(kPassword, sizeof(kPassword) - 1, kSalt,
                                sizeof(kSalt) - 1, 1024, 8, 16, 0 /* max_mem */,
                                out, sizeof(out));
      })) {
    fprintf(stderr, "scrypt failed.\n");
    return false;
  }
  results.Print("scrypt (N = 1024, r = 8, p = 16)");

  if (!TimeFunction(&results, [&]() -> bool {
        uint8_t out[64];
        return !!EVP_PBE_scrypt(kPassword, sizeof(kPassword) - 1, kSalt,
                                sizeof(kSalt) - 1, 16384, 8, 1, 0 /* max_mem */,
                                out, sizeof(out));
      })) {
    fprintf(stderr, "scrypt failed.\n");
    return false;
  }
  results.Print("scrypt (N = 16384, r = 8, p = 1)");

  return true;
}
#endif

#if !defined(OPENSSL_BENCHMARK)
static bool SpeedHRSS(const std::string &selected) {
  if (!selected.empty() && selected != "HRSS") {
    return true;
  }

  TimeResults results;

  if (!TimeFunction(&results, []() -> bool {
        struct HRSS_public_key pub;
        struct HRSS_private_key priv;
        uint8_t entropy[HRSS_GENERATE_KEY_BYTES];
        RAND_bytes(entropy, sizeof(entropy));
        return HRSS_generate_key(&pub, &priv, entropy);
      })) {
    fprintf(stderr, "Failed to time HRSS_generate_key.\n");
    return false;
  }

  results.Print("HRSS generate");

  struct HRSS_public_key pub;
  struct HRSS_private_key priv;
  uint8_t key_entropy[HRSS_GENERATE_KEY_BYTES];
  RAND_bytes(key_entropy, sizeof(key_entropy));
  if (!HRSS_generate_key(&pub, &priv, key_entropy)) {
    return false;
  }

  uint8_t ciphertext[HRSS_CIPHERTEXT_BYTES];
  if (!TimeFunction(&results, [&pub, &ciphertext]() -> bool {
        uint8_t entropy[HRSS_ENCAP_BYTES];
        uint8_t shared_key[HRSS_KEY_BYTES];
        RAND_bytes(entropy, sizeof(entropy));
        return HRSS_encap(ciphertext, shared_key, &pub, entropy);
      })) {
    fprintf(stderr, "Failed to time HRSS_encap.\n");
    return false;
  }

  results.Print("HRSS encap");

  if (!TimeFunction(&results, [&priv, &ciphertext]() -> bool {
        uint8_t shared_key[HRSS_KEY_BYTES];
        return HRSS_decap(shared_key, &priv, ciphertext, sizeof(ciphertext));
      })) {
    fprintf(stderr, "Failed to time HRSS_encap.\n");
    return false;
  }

  results.Print("HRSS decap");

  return true;
}

#if defined(INTERNAL_TOOL)
static bool SpeedHashToCurve(const std::string &selected) {
  if (!selected.empty() && selected.find("hashtocurve") == std::string::npos) {
    return true;
  }

  uint8_t input[64];
  RAND_bytes(input, sizeof(input));

  static const uint8_t kLabel[] = "label";

  TimeResults results;
  {
    if (!TimeFunction(&results, [&]() -> bool {
          EC_JACOBIAN out;
          return ec_hash_to_curve_p256_xmd_sha256_sswu(EC_group_p256(), &out,
                                                       kLabel, sizeof(kLabel),
                                                       input, sizeof(input));
        })) {
      fprintf(stderr, "hash-to-curve failed.\n");
      return false;
    }
    results.Print("hash-to-curve P256_XMD:SHA-256_SSWU_RO_");

    if (!TimeFunction(&results, [&]() -> bool {
          EC_JACOBIAN out;
          return ec_hash_to_curve_p384_xmd_sha384_sswu(EC_group_p384(), &out,
                                                       kLabel, sizeof(kLabel),
                                                       input, sizeof(input));
        })) {
      fprintf(stderr, "hash-to-curve failed.\n");
      return false;
    }
    results.Print("hash-to-curve P384_XMD:SHA-384_SSWU_RO_");

    if (!TimeFunction(&results, [&]() -> bool {
          EC_SCALAR out;
          return ec_hash_to_scalar_p384_xmd_sha512_draft07(
              EC_group_p384(), &out, kLabel, sizeof(kLabel), input,
              sizeof(input));
        })) {
      fprintf(stderr, "hash-to-scalar failed.\n");
      return false;
    }
    results.Print("hash-to-scalar P384_XMD:SHA-512");
  }

  return true;
}
#endif

static bool SpeedBase64(const std::string &selected) {
  if (!selected.empty() && selected.find("base64") == std::string::npos) {
    return true;
  }

  static const char kInput[] =
    "MIIDtTCCAp2gAwIBAgIJALW2IrlaBKUhMA0GCSqGSIb3DQEBCwUAMEUxCzAJBgNV"
    "BAYTAkFVMRMwEQYDVQQIEwpTb21lLVN0YXRlMSEwHwYDVQQKExhJbnRlcm5ldCBX"
    "aWRnaXRzIFB0eSBMdGQwHhcNMTYwNzA5MDQzODA5WhcNMTYwODA4MDQzODA5WjBF"
    "MQswCQYDVQQGEwJBVTETMBEGA1UECBMKU29tZS1TdGF0ZTEhMB8GA1UEChMYSW50"
    "ZXJuZXQgV2lkZ2l0cyBQdHkgTHRkMIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIB"
    "CgKCAQEAugvahBkSAUF1fC49vb1bvlPrcl80kop1iLpiuYoz4Qptwy57+EWssZBc"
    "HprZ5BkWf6PeGZ7F5AX1PyJbGHZLqvMCvViP6pd4MFox/igESISEHEixoiXCzepB"
    "rhtp5UQSjHD4D4hKtgdMgVxX+LRtwgW3mnu/vBu7rzpr/DS8io99p3lqZ1Aky+aN"
    "lcMj6MYy8U+YFEevb/V0lRY9oqwmW7BHnXikm/vi6sjIS350U8zb/mRzYeIs2R65"
    "LUduTL50+UMgat9ocewI2dv8aO9Dph+8NdGtg8LFYyTTHcUxJoMr1PTOgnmET19W"
    "JH4PrFwk7ZE1QJQQ1L4iKmPeQistuQIDAQABo4GnMIGkMB0GA1UdDgQWBBT5m6Vv"
    "zYjVYHG30iBE+j2XDhUE8jB1BgNVHSMEbjBsgBT5m6VvzYjVYHG30iBE+j2XDhUE"
    "8qFJpEcwRTELMAkGA1UEBhMCQVUxEzARBgNVBAgTClNvbWUtU3RhdGUxITAfBgNV"
    "BAoTGEludGVybmV0IFdpZGdpdHMgUHR5IEx0ZIIJALW2IrlaBKUhMAwGA1UdEwQF"
    "MAMBAf8wDQYJKoZIhvcNAQELBQADggEBAD7Jg68SArYWlcoHfZAB90Pmyrt5H6D8"
    "LRi+W2Ri1fBNxREELnezWJ2scjl4UMcsKYp4Pi950gVN+62IgrImcCNvtb5I1Cfy"
    "/MNNur9ffas6X334D0hYVIQTePyFk3umI+2mJQrtZZyMPIKSY/sYGQHhGGX6wGK+"
    "GO/og0PQk/Vu6D+GU2XRnDV0YZg1lsAsHd21XryK6fDmNkEMwbIWrts4xc7scRrG"
    "HWy+iMf6/7p/Ak/SIicM4XSwmlQ8pPxAZPr+E2LoVd9pMpWUwpW2UbtO5wsGTrY5"
    "sO45tFNN/y+jtUheB1C2ijObG/tXELaiyCdM+S/waeuv0MXtI4xnn1A=";

  std::vector<uint8_t> out(strlen(kInput));
  size_t len;
  TimeResults results;
  if (!TimeFunction(&results, [&]() -> bool {
        return EVP_DecodeBase64(out.data(), &len, out.size(),
                                reinterpret_cast<const uint8_t *>(kInput),
                                strlen(kInput));
      })) {
    fprintf(stderr, "base64 decode failed.\n");
    return false;
  }
  results.PrintWithBytes("base64 decode", strlen(kInput));
  return true;
}

static bool SpeedSipHash(const std::string &selected) {
  if (!selected.empty() && selected.find("siphash") == std::string::npos) {
    return true;
  }

  uint64_t key[2] = {0};
  for (size_t len : g_chunk_lengths) {
    std::vector<uint8_t> input(len);
    TimeResults results;
    if (!TimeFunction(&results, [&]() -> bool {
          SIPHASH_24(key, input.data(), input.size());
          return true;
        })) {
      fprintf(stderr, "SIPHASH_24 failed.\n");
      ERR_print_errors_fp(stderr);
      return false;
    }
    results.PrintWithBytes("SipHash-2-4", len);
  }

  return true;
}

#if defined(INTERNAL_TOOL)
static TRUST_TOKEN_PRETOKEN *trust_token_pretoken_dup(
    const TRUST_TOKEN_PRETOKEN *in) {
  return static_cast<TRUST_TOKEN_PRETOKEN *>(
      OPENSSL_memdup(in, sizeof(TRUST_TOKEN_PRETOKEN)));
}

static bool SpeedTrustToken(std::string name, const TRUST_TOKEN_METHOD *method,
                            size_t batchsize, const std::string &selected) {
  if (!selected.empty() && selected.find("trusttoken") == std::string::npos) {
    return true;
  }

  TimeResults results;
  if (!TimeFunction(&results, [&]() -> bool {
        uint8_t priv_key[TRUST_TOKEN_MAX_PRIVATE_KEY_SIZE];
        uint8_t pub_key[TRUST_TOKEN_MAX_PUBLIC_KEY_SIZE];
        size_t priv_key_len, pub_key_len;
        return TRUST_TOKEN_generate_key(
            method, priv_key, &priv_key_len, TRUST_TOKEN_MAX_PRIVATE_KEY_SIZE,
            pub_key, &pub_key_len, TRUST_TOKEN_MAX_PUBLIC_KEY_SIZE, 0);
      })) {
    fprintf(stderr, "TRUST_TOKEN_generate_key failed.\n");
    return false;
  }
  results.Print(name + " generate_key");

  BM_NAMESPACE::UniquePtr<TRUST_TOKEN_CLIENT> client(
      TRUST_TOKEN_CLIENT_new(method, batchsize));
  BM_NAMESPACE::UniquePtr<TRUST_TOKEN_ISSUER> issuer(
      TRUST_TOKEN_ISSUER_new(method, batchsize));
  uint8_t priv_key[TRUST_TOKEN_MAX_PRIVATE_KEY_SIZE];
  uint8_t pub_key[TRUST_TOKEN_MAX_PUBLIC_KEY_SIZE];
  size_t priv_key_len, pub_key_len, key_index;
  if (!client || !issuer ||
      !TRUST_TOKEN_generate_key(
          method, priv_key, &priv_key_len, TRUST_TOKEN_MAX_PRIVATE_KEY_SIZE,
          pub_key, &pub_key_len, TRUST_TOKEN_MAX_PUBLIC_KEY_SIZE, 0) ||
      !TRUST_TOKEN_CLIENT_add_key(client.get(), &key_index, pub_key,
                                  pub_key_len) ||
      !TRUST_TOKEN_ISSUER_add_key(issuer.get(), priv_key, priv_key_len)) {
    fprintf(stderr, "failed to generate trust token key.\n");
    return false;
  }

  uint8_t public_key[32], private_key[64];
  ED25519_keypair(public_key, private_key);
  BM_NAMESPACE::UniquePtr<EVP_PKEY> priv(
      EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519, nullptr, private_key, 32));
  BM_NAMESPACE::UniquePtr<EVP_PKEY> pub(
      EVP_PKEY_new_raw_public_key(EVP_PKEY_ED25519, nullptr, public_key, 32));
  if (!priv || !pub) {
    fprintf(stderr, "failed to generate trust token SRR key.\n");
    return false;
  }

  TRUST_TOKEN_CLIENT_set_srr_key(client.get(), pub.get());
  TRUST_TOKEN_ISSUER_set_srr_key(issuer.get(), priv.get());
  uint8_t metadata_key[32];
  RAND_bytes(metadata_key, sizeof(metadata_key));
  if (!TRUST_TOKEN_ISSUER_set_metadata_key(issuer.get(), metadata_key,
                                           sizeof(metadata_key))) {
    fprintf(stderr, "failed to generate trust token metadata key.\n");
    return false;
  }

  if (!TimeFunction(&results, [&]() -> bool {
        uint8_t *issue_msg = NULL;
        size_t msg_len;
        int ok = TRUST_TOKEN_CLIENT_begin_issuance(client.get(), &issue_msg,
                                                   &msg_len, batchsize);
        OPENSSL_free(issue_msg);
        // Clear pretokens.
        sk_TRUST_TOKEN_PRETOKEN_pop_free(client->pretokens,
                                         TRUST_TOKEN_PRETOKEN_free);
        client->pretokens = sk_TRUST_TOKEN_PRETOKEN_new_null();
        return ok;
      })) {
    fprintf(stderr, "TRUST_TOKEN_CLIENT_begin_issuance failed.\n");
    return false;
  }
  results.Print(name + " begin_issuance");

  uint8_t *issue_msg = NULL;
  size_t msg_len;
  if (!TRUST_TOKEN_CLIENT_begin_issuance(client.get(), &issue_msg, &msg_len,
                                         batchsize)) {
    fprintf(stderr, "TRUST_TOKEN_CLIENT_begin_issuance failed.\n");
    return false;
  }
  BM_NAMESPACE::UniquePtr<uint8_t> free_issue_msg(issue_msg);

  BM_NAMESPACE::UniquePtr<STACK_OF(TRUST_TOKEN_PRETOKEN)> pretokens(
      sk_TRUST_TOKEN_PRETOKEN_deep_copy(client->pretokens,
                                        trust_token_pretoken_dup,
                                        TRUST_TOKEN_PRETOKEN_free));

  if (!TimeFunction(&results, [&]() -> bool {
        uint8_t *issue_resp = NULL;
        size_t resp_len, tokens_issued;
        int ok = TRUST_TOKEN_ISSUER_issue(issuer.get(), &issue_resp, &resp_len,
                                          &tokens_issued, issue_msg, msg_len,
                                          /*public_metadata=*/0,
                                          /*private_metadata=*/0,
                                          /*max_issuance=*/batchsize);
        OPENSSL_free(issue_resp);
        return ok;
      })) {
    fprintf(stderr, "TRUST_TOKEN_ISSUER_issue failed.\n");
    return false;
  }
  results.Print(name + " issue");

  uint8_t *issue_resp = NULL;
  size_t resp_len, tokens_issued;
  if (!TRUST_TOKEN_ISSUER_issue(issuer.get(), &issue_resp, &resp_len,
                                &tokens_issued, issue_msg, msg_len,
                                /*public_metadata=*/0, /*private_metadata=*/0,
                                /*max_issuance=*/batchsize)) {
    fprintf(stderr, "TRUST_TOKEN_ISSUER_issue failed.\n");
    return false;
  }
  BM_NAMESPACE::UniquePtr<uint8_t> free_issue_resp(issue_resp);

  if (!TimeFunction(&results, [&]() -> bool {
        size_t key_index2;
        BM_NAMESPACE::UniquePtr<STACK_OF(TRUST_TOKEN)> tokens(
            TRUST_TOKEN_CLIENT_finish_issuance(client.get(), &key_index2,
                                               issue_resp, resp_len));

        // Reset pretokens.
        client->pretokens = sk_TRUST_TOKEN_PRETOKEN_deep_copy(
            pretokens.get(), trust_token_pretoken_dup,
            TRUST_TOKEN_PRETOKEN_free);
        return !!tokens;
      })) {
    fprintf(stderr, "TRUST_TOKEN_CLIENT_finish_issuance failed.\n");
    return false;
  }
  results.Print(name + " finish_issuance");

  BM_NAMESPACE::UniquePtr<STACK_OF(TRUST_TOKEN)> tokens(
      TRUST_TOKEN_CLIENT_finish_issuance(client.get(), &key_index, issue_resp,
                                         resp_len));
  if (!tokens || sk_TRUST_TOKEN_num(tokens.get()) < 1) {
    fprintf(stderr, "TRUST_TOKEN_CLIENT_finish_issuance failed.\n");
    return false;
  }

  const TRUST_TOKEN *token = sk_TRUST_TOKEN_value(tokens.get(), 0);

  const uint8_t kClientData[] = "\x70TEST CLIENT DATA";
  uint64_t kRedemptionTime = 13374242;

  if (!TimeFunction(&results, [&]() -> bool {
        uint8_t *redeem_msg = NULL;
        size_t redeem_msg_len;
        int ok = TRUST_TOKEN_CLIENT_begin_redemption(
            client.get(), &redeem_msg, &redeem_msg_len, token, kClientData,
            sizeof(kClientData) - 1, kRedemptionTime);
        OPENSSL_free(redeem_msg);
        return ok;
      })) {
    fprintf(stderr, "TRUST_TOKEN_CLIENT_begin_redemption failed.\n");
    return false;
  }
  results.Print(name + " begin_redemption");

  uint8_t *redeem_msg = NULL;
  size_t redeem_msg_len;
  if (!TRUST_TOKEN_CLIENT_begin_redemption(
          client.get(), &redeem_msg, &redeem_msg_len, token, kClientData,
          sizeof(kClientData) - 1, kRedemptionTime)) {
    fprintf(stderr, "TRUST_TOKEN_CLIENT_begin_redemption failed.\n");
    return false;
  }
  BM_NAMESPACE::UniquePtr<uint8_t> free_redeem_msg(redeem_msg);

  if (!TimeFunction(&results, [&]() -> bool {
        uint32_t public_value;
        uint8_t private_value;
        TRUST_TOKEN *rtoken;
        uint8_t *client_data = NULL;
        size_t client_data_len;
        int ok = TRUST_TOKEN_ISSUER_redeem(
            issuer.get(), &public_value, &private_value, &rtoken, &client_data,
            &client_data_len, redeem_msg, redeem_msg_len);
        OPENSSL_free(client_data);
        TRUST_TOKEN_free(rtoken);
        return ok;
      })) {
    fprintf(stderr, "TRUST_TOKEN_ISSUER_redeem failed.\n");
    return false;
  }
  results.Print(name + " redeem");

  uint32_t public_value;
  uint8_t private_value;
  TRUST_TOKEN *rtoken;
  uint8_t *client_data = NULL;
  size_t client_data_len;
  if (!TRUST_TOKEN_ISSUER_redeem(issuer.get(), &public_value, &private_value,
                                 &rtoken, &client_data, &client_data_len,
                                 redeem_msg, redeem_msg_len)) {
    fprintf(stderr, "TRUST_TOKEN_ISSUER_redeem failed.\n");
    return false;
  }
  BM_NAMESPACE::UniquePtr<uint8_t> free_client_data(client_data);
  BM_NAMESPACE::UniquePtr<TRUST_TOKEN> free_rtoken(rtoken);

  return true;
}
#endif
#endif

#if defined(AWSLC_FIPS)
static bool SpeedSelfTest(const std::string &selected) {
  if (!selected.empty() && selected.find("self-test") == std::string::npos) {
    return true;
  }

  TimeResults results;
  if (!TimeFunction(&results, []() -> bool { return BORINGSSL_self_test(); })) {
    fprintf(stderr, "BORINGSSL_self_test faileid.\n");
    ERR_print_errors_fp(stderr);
    return false;
  }

  results.Print("self-test");
  return true;
}

#if defined(FIPS_ENTROPY_SOURCE_JITTER_CPU)
static bool SpeedJitter(size_t chunk_size) {
  struct rand_data *jitter_ec = jent_entropy_collector_alloc(0, JENT_FORCE_FIPS);

  std::unique_ptr<char[]> input(new char[chunk_size]);
  TimeResults results;

  if (!TimeFunction(&results, [&jitter_ec, &input, chunk_size]() -> bool {
        size_t bytes =
            jent_read_entropy(jitter_ec, input.get(), chunk_size);
        if (bytes != chunk_size) {
          return false;
        }
        return true;
      })){
    jent_entropy_collector_free(jitter_ec);

    return false;
  }
  results.PrintWithBytes("Jitter", chunk_size);

  jent_entropy_collector_free(jitter_ec);
  return true;
}

static bool SpeedJitter(std::string selected) {
  if (!selected.empty() && selected.find("Jitter") == std::string::npos) {
    return true;
  }
  for (size_t chunk_size : g_chunk_lengths) {
    if (!SpeedJitter(chunk_size)) {
      return false;
    }
  }
  return true;
}
#endif
#endif

static bool SpeedDHcheck(size_t prime_bit_length) {

  TimeResults results;
  BM_NAMESPACE::UniquePtr<DH> dh_params(DH_new());
  if (dh_params == nullptr) {
    return false;
  }

  // DH_generate_parameters_ex grows exponentially slower as prime length grows.
  if (DH_generate_parameters_ex(dh_params.get(), prime_bit_length,
    DH_GENERATOR_2, nullptr) != 1) {
    return false;
  }

  if (!TimeFunction(&results, [&dh_params]() -> bool {
        int result = 0;
        if (DH_check(dh_params.get(), &result) != 1) {
          return false;
        }
        return true;
      })) {
    return false;
  }

  results.PrintWithPrimes("DH check(s)", prime_bit_length);
  return true;
}

static bool SpeedDHcheck(std::string selected) {
  // Don't run this by default because it's so slow.
  if (selected != "dhcheck") {
    return true;
  }

  uint64_t maybe_reset_timeout = g_timeout_ms;
  if (g_timeout_ms == TIMEOUT_MS_DEFAULT) {
    g_timeout_ms = 10000;
  }

  for (size_t prime_bit_length : g_prime_bit_lengths) {
    if (!SpeedDHcheck(prime_bit_length)) {
      return false;
    }
  }

  g_timeout_ms = maybe_reset_timeout;

  return true;
}

#if AWSLC_API_VERSION > 16
static bool SpeedPKCS8(const std::string &selected) {
  if (!selected.empty() && selected.find("pkcs8") == std::string::npos) {
    return true;
  }

  uint8_t pubkey[ED25519_PUBLIC_KEY_LEN];
  uint8_t privkey[ED25519_PRIVATE_KEY_LEN];

  ED25519_keypair(pubkey, privkey);

  BM_NAMESPACE::UniquePtr<EVP_PKEY> key(EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519, nullptr, &privkey[0], ED25519_PRIVATE_KEY_SEED_LEN));

  if(!key) {
    return false;
  }

  CBB out;
  uint8_t buffer[1024];

  TimeResults results;
  if (!TimeFunction(&results, [&out, &key, &buffer]() -> bool {
        if (!CBB_init_fixed(&out, buffer, 1024) ||
            !EVP_marshal_private_key(&out, key.get())) {
          return false;
        }
        return true;
      })) {
    return false;
  }
  results.Print("Ed25519 PKCS#8 v1 encode");

  CBS in;

  if (!TimeFunction(&results, [&in, &out]() -> bool {
        CBS_init(&in, CBB_data(&out), CBB_len(&out));
        EVP_PKEY *parsed = EVP_parse_private_key(&in);
        bool result = parsed != NULL;
        EVP_PKEY_free(parsed);
        return result;
      })) {
    return false;
  }
  results.Print("Ed25519 PKCS#8 v1 decode");

  CBB_cleanup(&out);


  if (!TimeFunction(&results, [&out, &key, &buffer]() -> bool {
        if (!CBB_init_fixed(&out, buffer, 1024) ||
            !EVP_marshal_private_key_v2(&out, key.get())) {
          return false;
        }
        return true;
      })) {
    CBB_cleanup(&out);
    return false;
  }
  results.Print("Ed25519 PKCS#8 v2 encode");

  if (!TimeFunction(&results, [&in, &out]() -> bool {
        CBS_init(&in, CBB_data(&out), CBB_len(&out));
        EVP_PKEY *parsed = EVP_parse_private_key(&in);
        bool result = parsed != NULL;
        EVP_PKEY_free(parsed);
        return result;
      })) {
    CBB_cleanup(&out);
    return false;
  }
  results.Print("Ed25519 PKCS#8 v2 decode");
  CBB_cleanup(&out);
  return true;
}
#endif

#if defined(OPENSSL_IS_AWSLC)
static bool SpeedRefcountThreads(std::string name, size_t num_threads) {
  CRYPTO_refcount_t refcount = 0;
  size_t iterations_per_thread = 1000;
  auto thread_func = [&refcount, &iterations_per_thread]() -> bool {
    for (size_t i = 0; i < iterations_per_thread; ++i) {
      CRYPTO_refcount_inc(&refcount);
    }
    return true;
  };

  TimeResults results;
  if (!TimeFunction(&results, [&num_threads, &thread_func]() -> bool {
        std::vector<std::thread> threads;
        for (size_t i = 0; i < num_threads; i++) {
          threads.emplace_back(thread_func);
        }
        for (auto &t : threads) {
          t.join();
        }
        return true;
      })) {
    return false;
  }
  std::stringstream ss;
  ss << name <<" " << iterations_per_thread << " iterations with " << num_threads << " threads";

  results.Print(ss.str());
  return true;
}

static bool SpeedRefcount(const std::string &selected) {
  if (!selected.empty() && selected.find("CRYPTO_refcount_inc") == std::string::npos) {
    return true;
  }

  for (size_t num_threads : g_threads) {
    if (!SpeedRefcountThreads("CRYPTO_refcount_inc", num_threads)) {
      return false;
    }
  }

  return true;
}
#endif

static const argument_t kArguments[] = {
    {
        "-filter",
        kOptionalArgument,
        "A comma-separated list of filters on the speed tests to run. "
        "Each filter is applied in independent runs.",
    },
    {
        "-timeout",
        kOptionalArgument,
        "The number of seconds to run each test for (default is 1)",
    },
    {
        "-timeout_ms",
        kOptionalArgument,
        "The number of milliseconds to run each test for (default is 1000)",
    },
    {
        "-chunks",
        kOptionalArgument,
        "A comma-separated list of input sizes to run tests at (default is "
        "16,256,1350,8192,16384)",
    },
    {
        "-threads",
        kOptionalArgument,
        "A comma-separated list of number of threads to test multithreaded"
        "benchmarks with (default is 1,2,4,8,16,32,64)",
    },
    {
        "-primes",
        kOptionalArgument,
        "A comma-separated list of prime input sizes (bits) to run tests at "
        "(default is 2048,3072)",
    },
    {
        "-json",
        kBooleanArgument,
        "If this flag is set, speed will print the output of each benchmark in "
        "JSON format as follows: \"{\"description\": "
        "\"descriptionOfOperation\", \"numCalls\": 1234, "
        "\"timeInMicroseconds\": 1234567, \"bytesPerCall\": 1234}\". When "
        "there is no information about the bytes per call for an  operation, "
        "the JSON field for bytesPerCall will be omitted.",
    },
#if defined(DIT_OPTION)
    {
        "-dit",
        kBooleanArgument,
        "If this flag is set, the DIT flag is set before benchmarking and"
        "reset at the end."
    },
#endif
    {
        "",
        kOptionalArgument,
        "",
    },
};

// parseCommaArgument clears |vector| and parses comma-separated input for the
// argument |arg_name| in |args_map|.
static bool parseCommaArgument(std::vector<std::string> &vector,
  std::map<std::string, std::string> &args_map, const std::string &arg_name) {

  vector.clear();
  const char *start = args_map[arg_name.c_str()].data();
  const char *end = start + args_map[arg_name.c_str()].size();
  const char* current = start;
  while (current < end) {
    const char* comma = std::find(current, end, ',');
    if (comma == current) {
      // Empty argument found e.g. arg1,arg2,,arg3
      fprintf(stderr, "Error parsing %s argument\n", arg_name.c_str());
      return false;
    }
    vector.emplace_back(current, comma);
    current = (comma == end) ? end : comma + 1;
  }

  return true;
}

// parseStringVectorToIntegerVector attempts to parse each element of
// |in_vector| as a size_t integer and adds the result to |out_vector|. Clears
// |out_vector|.
static bool parseStringVectorToIntegerVector(
  std::vector<std::string> &in_vector, std::vector<size_t> &out_vector) {

  out_vector.clear();
  for (const std::string &str : in_vector) {
    errno = 0;
    char *ptr;
    unsigned long long int integer_value = strtoull(str.data(), &ptr, 10);
    if (ptr == str.data() /* no numeric characters found */ ||
        errno == ERANGE /* overflow */ ||
        static_cast<size_t>(integer_value) != integer_value) {
      fprintf(stderr, "Error parsing %s argument\n", str.c_str());
      return false;
    }
    out_vector.push_back(static_cast<size_t>(integer_value));
  }
  return true;
}

bool Speed(const std::vector<std::string> &args) {
#if AWSLC_API_VERSION > 27
  OPENSSL_BEGIN_ALLOW_DEPRECATED
  // We started marking this as deprecated.
  EVP_MD_unstable_sha3_enable(true);
  OPENSSL_END_ALLOW_DEPRECATED
#elif AWSLC_API_VERSION > 16
  // For mainline AWS-LC this is a no-op, however if speed.cc built with an old
  // branch of AWS-LC SHA3 might be disabled by default and fail the benchmark.
  EVP_MD_unstable_sha3_enable(true);
#endif
  std::map<std::string, std::string> args_map;
  args_list_t extra_args;
  if (!ParseKeyValueArguments(args_map, extra_args, args, kArguments) ||
      extra_args.size() > 0) {
    PrintUsage(kArguments);
    return false;
  }

  if (args_map.count("-filter") != 0) {
    if (!parseCommaArgument(g_filters, args_map, "-filter")) {
      return false;
    }
  }

#if defined(DIT_OPTION)
  if (args_map.count("-dit") != 0) {
    g_dit = true;
  }
#endif

  if (args_map.count("-json") != 0) {
    g_print_json = true;
  }

  if (args_map.count("-timeout") != 0 && args_map.count("-timeout_ms") != 0) {
    puts("'-timeout' and '-timeout_ms' are mutually exclusive");
    PrintUsage(kArguments);
    return false;
  }

  if (args_map.count("-timeout") != 0) {
    int timeout = atoi(args_map["-timeout"].c_str());
    if (1 > timeout) {
      puts("'-timeout' must be positive");
      PrintUsage(kArguments);
      return false;
    }
    g_timeout_ms = ((uint64_t)timeout) * 1000;
  }

  if (args_map.count("-timeout_ms") != 0) {
    int timeout_ms = atoi(args_map["-timeout_ms"].c_str());
    if (1 > timeout_ms) {
      puts("'-timeout_ms' must be positive");
      PrintUsage(kArguments);
      return false;
    }
    g_timeout_ms = timeout_ms;
  }

  if (args_map.count("-chunks") != 0) {
    std::vector<std::string> chunkVector;
    if (!parseCommaArgument(chunkVector,
        args_map, "-chunks")) {
      return false;
    }
    if (!parseStringVectorToIntegerVector(chunkVector, g_chunk_lengths)) {
      return false;
    }
  }

  if (args_map.count("-threads") != 0) {
    std::vector<std::string> threadVector;
    if (!parseCommaArgument(threadVector,
                            args_map, "-threads")) {
      return false;
    }
    if (!parseStringVectorToIntegerVector(threadVector, g_threads)) {
      return false;
    }
  }

  if (args_map.count("-primes") != 0) {
    std::vector<std::string> primeVector;
    if (!parseCommaArgument(primeVector,
        args_map, "-primes")) {
      return false;
    }
    if (!parseStringVectorToIntegerVector(primeVector, g_prime_bit_lengths)) {
      return false;
    }
  }
#if defined(DIT_OPTION)
  armv8_disable_dit(); // disable DIT capability at run-time
  armv8_enable_dit();  // enable back DIT capability at run-time
  uint64_t original_dit = 0;
  if (g_dit)
  {
    original_dit = armv8_set_dit();
  }
#endif

  // kTLSADLen is the number of bytes of additional data that TLS passes to
  // AEADs.
  static const size_t kTLSADLen = 13;
#if !defined(OPENSSL_BENCHMARK)

  // kLegacyADLen is the number of bytes that TLS passes to the "legacy" AEADs.
  // These are AEADs that weren't originally defined as AEADs, but which we use
  // via the AEAD interface. In order for that to work, they have some TLS
  // knowledge in them and construct a couple of the AD bytes internally.
  static const size_t kLegacyADLen = kTLSADLen - 2;
#endif

#if defined(CMAKE_BUILD_TYPE_DEBUG)
  printf("Benchmarking in debug mode.\n");
#endif

  if (g_print_json) {
    puts("[");
  }

  for (std::string selected : g_filters) {
    if(!SpeedAESBlock("AES-128", 128, selected) ||
       !SpeedAESBlock("AES-192", 192, selected) ||
       !SpeedAESBlock("AES-256", 256, selected) ||
       !SpeedEvpCipherGeneric(EVP_aes_128_gcm(), "EVP-AES-128-GCM", kTLSADLen, selected) ||
       !SpeedEvpCipherGeneric(EVP_aes_192_gcm(), "EVP-AES-192-GCM", kTLSADLen, selected) ||
       !SpeedEvpCipherGeneric(EVP_aes_256_gcm(), "EVP-AES-256-GCM", kTLSADLen, selected) ||
       !SpeedEvpCipherGeneric(EVP_aes_128_ctr(), "EVP-AES-128-CTR", kTLSADLen, selected) ||
       !SpeedEvpCipherGeneric(EVP_aes_192_ctr(), "EVP-AES-192-CTR", kTLSADLen, selected) ||
       !SpeedEvpCipherGeneric(EVP_aes_256_ctr(), "EVP-AES-256-CTR", kTLSADLen, selected) ||
       !SpeedEvpCipherGeneric(EVP_aes_128_cbc(), "EVP-AES-128-CBC", kTLSADLen, selected) ||
       !SpeedEvpCipherGeneric(EVP_aes_192_cbc(), "EVP-AES-192-CBC", kTLSADLen, selected) ||
       !SpeedEvpCipherGeneric(EVP_aes_256_cbc(), "EVP-AES-256-CBC", kTLSADLen, selected) ||
       !SpeedAES256XTS("AES-256-XTS", selected) ||
#if !defined(OPENSSL_3_0_BENCHMARK)
       // OpenSSL 3.0 deprecated RC4
       !SpeedEvpCipherGeneric(EVP_rc4(), "EVP-RC4", kTLSADLen, selected) ||
#endif
#if !defined(OPENSSL_3_0_BENCHMARK)
       // OpenSSL 3.0 doesn't allow MD4 calls
       !SpeedHash(EVP_md4(), "MD4", selected) ||
#endif
       !SpeedHash(EVP_md5(), "MD5", selected) ||
       !SpeedHash(EVP_sha1(), "SHA-1", selected) ||
       !SpeedHash(EVP_sha224(), "SHA-224", selected) ||
       !SpeedHash(EVP_sha256(), "SHA-256", selected) ||
       !SpeedHash(EVP_sha384(), "SHA-384", selected) ||
       !SpeedHash(EVP_sha512(), "SHA-512", selected) ||
       // OpenSSL 1.0 and BoringSSL don't support SHA3.
#if (!defined(OPENSSL_1_0_BENCHMARK) && !defined(BORINGSSL_BENCHMARK) && !defined(OPENSSL_IS_AWSLC)) || AWSLC_API_VERSION > 16
       !SpeedHash(EVP_sha3_224(), "SHA3-224", selected) ||
       !SpeedHash(EVP_sha3_256(), "SHA3-256", selected) ||
       !SpeedHash(EVP_sha3_384(), "SHA3-384", selected) ||
       !SpeedHash(EVP_sha3_512(), "SHA3-512", selected) ||
#endif
#if (!defined(OPENSSL_1_0_BENCHMARK) && !defined(BORINGSSL_BENCHMARK) && !defined(OPENSSL_IS_AWSLC)) || AWSLC_API_VERSION >= 22
       // OpenSSL 1.0 and BoringSSL don't support SHAKE
       !SpeedHash(EVP_shake128(), "SHAKE-128", selected) ||
       !SpeedHash(EVP_shake256(), "SHAKE-256", selected) ||
#endif
#if (!defined(BORINGSSL_BENCHMARK) && !defined(OPENSSL_IS_AWSLC)) || AWSLC_API_VERSION >= 20
       // BoringSSL doesn't support ripemd160
       !SpeedHash(EVP_ripemd160(), "RIPEMD-160", selected) ||
#endif
#if !defined(OPENSSL_1_0_BENCHMARK)
       !SpeedHash(EVP_md5_sha1(), "MD5-SHA-1", selected) ||
#endif
       !SpeedHmac(EVP_md5(), "HMAC-MD5", selected) ||
       !SpeedHmac(EVP_sha1(), "HMAC-SHA1", selected) ||
       !SpeedHmac(EVP_sha256(), "HMAC-SHA256", selected) ||
       !SpeedHmac(EVP_sha384(), "HMAC-SHA384", selected) ||
       !SpeedHmac(EVP_sha512(), "HMAC-SHA512", selected) ||
       !SpeedHmacOneShot(EVP_md5(), "HMAC-MD5-OneShot", selected) ||
       !SpeedHmacOneShot(EVP_sha1(), "HMAC-SHA1-OneShot", selected) ||
       !SpeedHmacOneShot(EVP_sha256(), "HMAC-SHA256-OneShot", selected) ||
       !SpeedHmacOneShot(EVP_sha384(), "HMAC-SHA384-OneShot", selected) ||
       !SpeedHmacOneShot(EVP_sha512(), "HMAC-SHA512-OneShot", selected) ||
#if !defined(OPENSSL_1_0_BENCHMARK)
       !SpeedCmac(EVP_aes_128_cbc(), "CMAC-AES-128-CBC", selected) ||
       !SpeedCmac(EVP_aes_256_cbc(), "CMAC-AES-256-CBC", selected) ||
#endif
       !SpeedRandom(RAND_bytes, "RNG", selected) ||
       !SpeedECDH(selected) ||
       !SpeedECDSA(selected) ||
       !SpeedECKeyGen(selected) ||
       !SpeedECKeyGenerateKey(false, selected) ||
#if !defined(OPENSSL_1_0_BENCHMARK)
       // OpenSSL 1.0.2 is missing functions e.g. |EVP_PKEY_get0_EC_KEY| and
       // doesn't implement X255519 either.
       !SpeedEvpEcdh(selected) ||
       !SpeedECPOINT(selected) ||
       // OpenSSL 1.0 doesn't support Scrypt
       !SpeedScrypt(selected) ||
#endif
#if (!defined(OPENSSL_1_0_BENCHMARK) && !defined(BORINGSSL_BENCHMARK) && !defined(OPENSSL_IS_AWSLC)) || AWSLC_API_VERSION >= 24
        // BoringSSL doesn't support ChaCha through the EVP_CIPHER API,
        // OpenSSL 1.0 doesn't support ChaCha at all,
        // AWS-LC only after API version 24
       !SpeedEvpCipherGeneric(EVP_chacha20_poly1305(), "EVP-ChaCha20-Poly1305", kTLSADLen, selected) ||
#endif
#if (!defined(OPENSSL_1_0_BENCHMARK) && !defined(BORINGSSL_BENCHMARK) && !defined(OPENSSL_IS_AWSLC)) || AWSLC_API_VERSION >= 22
       // OpenSSL 1.0 and BoringSSL don't support DH_new_by_nid, NID_ffdhe2048, or NID_ffdhe4096
       !SpeedFFDH(selected) ||
#endif
       !SpeedRSA(selected) ||
       !SpeedRSAKeyGen(false, selected) ||
       !SpeedDHcheck(selected)
#if !defined(OPENSSL_BENCHMARK)
       ||
#if AWSLC_API_VERSION > 16
       !SpeedKEM(selected) ||
#endif
#if AWSLC_API_VERSION > 31
       !SpeedDigestSign(selected) ||
#endif
       !SpeedAEADSeal(EVP_aead_aes_128_gcm(), "AEAD-AES-128-GCM", kTLSADLen, selected) ||
       !SpeedAEADOpen(EVP_aead_aes_128_gcm(), "AEAD-AES-128-GCM", kTLSADLen, selected) ||
       !SpeedAEADSeal(EVP_aead_aes_256_gcm(), "AEAD-AES-256-GCM", kTLSADLen, selected) ||
       !SpeedAEADOpen(EVP_aead_aes_256_gcm(), "AEAD-AES-256-GCM", kTLSADLen, selected) ||
       !SpeedAEADSeal(EVP_aead_chacha20_poly1305(), "AEAD-ChaCha20-Poly1305", kTLSADLen, selected) ||
       !SpeedAEADSeal(EVP_aead_des_ede3_cbc_sha1_tls(), "AEAD-DES-EDE3-CBC-SHA1",kLegacyADLen, selected) ||
       !SpeedAEADSeal(EVP_aead_aes_128_cbc_sha1_tls(), "AEAD-AES-128-CBC-SHA1",kLegacyADLen, selected) ||
       !SpeedAEADSeal(EVP_aead_aes_256_cbc_sha1_tls(), "AEAD-AES-256-CBC-SHA1",kLegacyADLen, selected) ||
       !SpeedAEADOpen(EVP_aead_aes_128_cbc_sha1_tls(), "AEAD-AES-128-CBC-SHA1", kLegacyADLen, selected) ||
       !SpeedAEADOpen(EVP_aead_aes_256_cbc_sha1_tls(), "AEAD-AES-256-CBC-SHA1", kLegacyADLen, selected) ||
       !SpeedAEADSeal(EVP_aead_aes_128_gcm_siv(), "AEAD-AES-128-GCM-SIV",kTLSADLen, selected) ||
       !SpeedAEADSeal(EVP_aead_aes_256_gcm_siv(), "AEAD-AES-256-GCM-SIV",kTLSADLen, selected) ||
       !SpeedAEADOpen(EVP_aead_aes_128_gcm_siv(), "AEAD-AES-128-GCM-SIV", kTLSADLen, selected) ||
       !SpeedAEADOpen(EVP_aead_aes_256_gcm_siv(), "AEAD-AES-256-GCM-SIV", kTLSADLen, selected) ||
       !SpeedAEADSeal(EVP_aead_aes_128_ccm_bluetooth(),"AEAD-AES-128-CCM-Bluetooth", kTLSADLen, selected) ||
       !Speed25519(selected) ||
       !SpeedSPAKE2(selected) ||
       !SpeedRSAKeyGen(true, selected) ||
       !SpeedHRSS(selected) ||
       !SpeedHash(EVP_blake2b256(), "BLAKE2b-256", selected) ||
       !SpeedECKeyGenerateKey(true, selected) ||
#if defined(OPENSSL_IS_AWSLC)
       !SpeedRefcount(selected) ||
#endif
#if defined(INTERNAL_TOOL)
       !SpeedRandom(CRYPTO_sysrand, "CRYPTO_sysrand", selected) ||
       !SpeedRandom(CRYPTO_sysrand_for_seed, "CRYPTO_sysrand_for_seed", selected) ||
       !SpeedHashToCurve(selected) ||
       !SpeedTrustToken("TrustToken-Exp1-Batch1", TRUST_TOKEN_experiment_v1(), 1, selected) ||
       !SpeedTrustToken("TrustToken-Exp1-Batch10", TRUST_TOKEN_experiment_v1(), 10, selected) ||
       !SpeedTrustToken("TrustToken-Exp2VOfPRF-Batch1", TRUST_TOKEN_experiment_v2_voprf(), 1, selected) ||
       !SpeedTrustToken("TrustToken-Exp2VOPRF-Batch10", TRUST_TOKEN_experiment_v2_voprf(), 10, selected) ||
       !SpeedTrustToken("TrustToken-Exp2PMB-Batch1", TRUST_TOKEN_experiment_v2_pmb(), 1, selected) ||
       !SpeedTrustToken("TrustToken-Exp2PMB-Batch10", TRUST_TOKEN_experiment_v2_pmb(), 10, selected) ||
#endif
#if AWSLC_API_VERSION > 16
       !SpeedPKCS8(selected) ||
#endif
       !SpeedBase64(selected) ||
       !SpeedSipHash(selected)
#endif
       ) {
      return false;
    }

#if defined(AWSLC_FIPS)
    if (!SpeedSelfTest(selected)) {
      return false;
    }
#if defined(FIPS_ENTROPY_SOURCE_JITTER_CPU)
    if (!SpeedJitter(selected)) {
      return false;
    }
#endif
#endif
  }

  if (g_print_json) {
    puts("\n]");
  }

#if defined(DIT_OPTION  )
  if (g_dit)
  {
    armv8_restore_dit(&original_dit);
  }
#endif
  return true;
}
