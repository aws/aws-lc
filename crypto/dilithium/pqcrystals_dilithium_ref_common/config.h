#ifndef CONFIG_H
#define CONFIG_H

#include <openssl/base.h>

#ifndef DILITHIUM_MODE
#define DILITHIUM_MODE 3
#endif

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

#ifdef BORINGSSL_PREFIX
#define DILITHIUM_NAMESPACE(s) BORINGSSL_ADD_PREFIX(BORINGSSL_PREFIX, DILITHIUM_VARIANT(s))
#define DILITHIUM_NAMESPACETOP BORINGSSL_ADD_PREFIX(BORINGSSL_PREFIX, DILITHIUM_VARIANTTOP)
#else
#define DILITHIUM_NAMESPACE(s) DILITHIUM_VARIANT(s)
#define DILITHIUM_NAMESPACETOP DILITHIUM_VARIANTTOP
#endif

#endif
