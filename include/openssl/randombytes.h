#ifndef RANDOMBYTES_H
#define RANDOMBYTES_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <stddef.h>
#include <stdint.h>
#include <openssl/base.h>

OPENSSL_EXPORT void use_deterministic_randombytes_for_testing(void);

OPENSSL_EXPORT void randombytes_init_for_testing(const uint8_t *seed);

int randombytes(uint8_t *random_array, size_t num_bytes);

#if defined(__cplusplus)
}
#endif

#endif
