// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENSSL_HEADER_TOOL_OSSLBM_H
#define OPENSSL_HEADER_TOOL_OSSLBM_H

#include <openssl/aes.h>
#include <openssl/bn.h>
#include <openssl/crypto.h>
#include <openssl/ec.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>

#define BM_NAMESPACE ossl

#if defined(_WIN32)
#define OPENSSL_WINDOWS
#endif
// OPENSSL_MSVC_PRAGMA emits a pragma on MSVC and nothing on other compilers.
#if defined(_MSC_VER)
#define OPENSSL_MSVC_PRAGMA(arg) __pragma(arg)
#else
#define OPENSSL_MSVC_PRAGMA(arg)
#endif

inline size_t BM_ECDSA_size(EC_KEY *key) {
  const int key_size = ECDSA_size(key);
  assert(key_size >= 0);
  return (size_t) key_size;
}

// Rather than depend on headers of AWS-LC the below code is modified from
// include/base.h, see that file for detailed comments.
namespace ossl {
namespace internal {
template <typename T, typename Enable = void> struct DeleterImpl {
};

template <typename T> struct Deleter {
  void operator()(T *ptr) { DeleterImpl<T>::Free(ptr); }
};

#define OSSL_MAKE_DELETER(type, deleter)              \
    namespace internal {                              \
    template <> struct DeleterImpl<type> {            \
        static void Free(type *ptr) { deleter(ptr); } \
    };                                                \
    }
} // namespace internal
template <typename T> using UniquePtr = std::unique_ptr<T, internal::Deleter<T>>;

OSSL_MAKE_DELETER(RSA, RSA_free)
OSSL_MAKE_DELETER(BIGNUM, BN_free)
OSSL_MAKE_DELETER(EC_KEY, EC_KEY_free)
OSSL_MAKE_DELETER(EC_POINT, EC_POINT_free)
OSSL_MAKE_DELETER(BN_CTX, BN_CTX_free)
OSSL_MAKE_DELETER(EVP_CIPHER_CTX, EVP_CIPHER_CTX_free)

// OpenSSL 1.0.x has different APIs for EVP_MD_CTX and HMAC
// We need to add more custom logic to HMAC to let it properly delete the
// pointer we create and we need to specify the seperate API for EVP here
#if !defined(OPENSSL_1_0_BENCHMARK)
OSSL_MAKE_DELETER(EVP_MD_CTX, EVP_MD_CTX_free)
OSSL_MAKE_DELETER(HMAC_CTX, HMAC_CTX_free)
#else
OSSL_MAKE_DELETER(EVP_MD_CTX, EVP_MD_CTX_destroy)
// This code lets us properly cleanup and delete HMAC_CTX ptrs
    namespace internal {
    template <> struct DeleterImpl<HMAC_CTX> {
        static void Free(HMAC_CTX *ptr) { 
	    HMAC_CTX_cleanup(ptr); 
	    delete ptr;
	}
    };
    }
#endif
} // namespace ossl

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

#endif //OPENSSL_HEADER_TOOL_OSSLBM_H
