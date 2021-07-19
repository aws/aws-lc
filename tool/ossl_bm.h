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
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>

#define BM_NAMESPACE ossl

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
OSSL_MAKE_DELETER(EVP_MD_CTX, EVP_MD_CTX_free)
} // namespace ossl

#endif //OPENSSL_HEADER_TOOL_OSSLBM_H