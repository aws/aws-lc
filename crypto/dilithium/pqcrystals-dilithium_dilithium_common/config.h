#ifndef CONFIG_H
#define CONFIG_H

#include <openssl/base.h>

//#define DILITHIUM_MODE 2
//#define DILITHIUM_USE_AES
//#define DILITHIUM_RANDOMIZED_SIGNING
//#define USE_RDPMC
//#define DBENCH

#ifndef DILITHIUM_MODE
#define DILITHIUM_MODE 3
#endif

#ifdef DILITHIUM_USE_AES
#if DILITHIUM_MODE == 2
#define CRYPTO_ALGNAME "Dilithium2-AES"
#define DILITHIUM_VARIANTTOP pqcrystals_dilithium2aes_ref
#define DILITHIUM_VARIANT(s) pqcrystals_dilithium2aes_ref_##s
#elif DILITHIUM_MODE == 3
#define CRYPTO_ALGNAME "Dilithium3-AES"
#define DILITHIUM_VARIANTTOP pqcrystals_dilithium3aes_ref
#define DILITHIUM_VARIANT(s) pqcrystals_dilithium3aes_ref_##s
#elif DILITHIUM_MODE == 5
#define CRYPTO_ALGNAME "Dilithium5-AES"
#define DILITHIUM_VARIANTTOP pqcrystals_dilithium5aes_ref
#define DILITHIUM_VARIANT(s) pqcrystals_dilithium5aes_ref_##s
#endif
#else
#if DILITHIUM_MODE == 2
#define CRYPTO_ALGNAME "Dilithium2"
#define DILITHIUM_VARIANTTOP pqcrystals_dilithium2_ref
#define DILITHIUM_VARIANT(s) pqcrystals_dilithium2_ref_##s
#elif DILITHIUM_MODE == 3
#define CRYPTO_ALGNAME "Dilithium3"
#define DILITHIUM_VARIANTTOP pqcrystals_dilithium3_ref
#define DILITHIUM_VARIANT(s) pqcrystals_dilithium3_ref_##s
#elif DILITHIUM_MODE == 5
#define CRYPTO_ALGNAME "Dilithium5"
#define DILITHIUM_VARIANTTOP pqcrystals_dilithium5_ref
#define DILITHIUM_VARIANT(s) pqcrystals_dilithium5_ref_##s
#endif
#endif

#ifdef BORINGSSL_PREFIX
#define DILITHIUM_NAMESPACE(s) BORINGSSL_ADD_PREFIX(BORINGSSL_PREFIX, DILITHIUM_VARIANT(s))
#define DILITHIUM_NAMESPACETOP BORINGSSL_ADD_PREFIX(BORINGSSL_PREFIX, DILITHIUM_VARIANTTOP)
#else
#define DILITHIUM_NAMESPACE(s) DILITHIUM_VARIANT(s)
#define DILITHIUM_NAMESPACETOP DILITHIUM_VARIANTTOP
#endif

#endif
