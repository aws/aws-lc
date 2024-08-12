// Prefix some symbols.
// Delete when promoting "new rand" to default choice.

#ifndef OPENSSL_HEADER_CRYPTO_RAND_LOCAL_PREFIX_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RAND_LOCAL_PREFIX_INTERNAL_H

#include <openssl/base.h>

#define NR_CONCAT(x,y) x##_##y
#define NR_PREFIX(x) NR_CONCAT(new_rand,x)

#endif // OPENSSL_HEADER_CRYPTO_RAND_LOCAL_PREFIX_INTERNAL_H
