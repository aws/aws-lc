// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_TOOL_BSSLBM_H
#define OPENSSL_HEADER_TOOL_BSSLBM_H

#include <openssl/aead.h>
#include <openssl/aes.h>
#include <openssl/base64.h>
#include <openssl/bn.h>
#include <openssl/curve25519.h>
#include <openssl/crypto.h>
#include <openssl/dh.h>
#include <openssl/digest.h>
#include <openssl/err.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/ec_key.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/hrss.h>
#include <openssl/mem.h>
#include <openssl/nid.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/siphash.h>
#include <openssl/trust_token.h>
#include <openssl/cipher.h>

#if defined(INTERNAL_TOOL)
#include <../crypto/ec_extra/internal.h>
#include <../crypto/trust_token/internal.h>
#include "../third_party/jitterentropy/jitterentropy-library/jitterentropy.h"
#endif // INTERNAL_TOOL

#define BM_NAMESPACE bssl
#define BM_ECDSA_size(key) ECDSA_size(key)

#endif //OPENSSL_HEADER_TOOL_BSSLBM_H
