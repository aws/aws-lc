#include <openssl/aead.h>
#include <openssl/aes.h>
#include <openssl/bn.h>
#include <openssl/curve25519.h>
#include <openssl/crypto.h>
#include <openssl/digest.h>
#include <openssl/err.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/ec_key.h>
#include <openssl/evp.h>
#include <openssl/hrss.h>
#include <openssl/mem.h>
#include <openssl/nid.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/trust_token.h>

#define BM_NAMESPACE          ossl

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