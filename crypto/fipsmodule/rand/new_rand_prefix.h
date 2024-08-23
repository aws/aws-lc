// Prefix some symbols.
// Delete when promoting "new rand" to default choice.

#ifndef OPENSSL_HEADER_CRYPTO_RAND_LOCAL_PREFIX_INTERNAL_H
#define OPENSSL_HEADER_CRYPTO_RAND_LOCAL_PREFIX_INTERNAL_H

#include <openssl/base.h>

#define NR_CONCAT(x,y) x##_##y
#define NR_PREFIX(x) NR_CONCAT(new_rand,x)

#endif // OPENSSL_HEADER_CRYPTO_RAND_LOCAL_PREFIX_INTERNAL_H

#if defined(COMPILATION_UNIT_NR_PREFIX)

#define RAND_bytes_with_additional_data NR_PREFIX(RAND_bytes_with_additional_data)
#define RAND_bytes NR_PREFIX(RAND_bytes)
#define RAND_priv_bytes NR_PREFIX(RAND_priv_bytes)
#define RAND_pseudo_bytes NR_PREFIX(RAND_pseudo_bytes)

#endif // defined(COMPILATION_UNIT_NR_PREFIX)
