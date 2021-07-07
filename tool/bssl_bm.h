#ifndef OPENSSL_HEADER_TOOL_BSSLBM_H
#define OPENSSL_HEADER_TOOL_BSSLBM_H

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
#include <openssl/cipher.h>

#include <../crypto/ec_extra/internal.h>
#include <../crypto/trust_token/internal.h>

#define BM_NAMESPACE bssl
#define BM_ECDSA_size(key) ECDSA_size(key)

#endif //OPENSSL_HEADER_TOOL_BSSLBM_H
