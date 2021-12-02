#ifndef RANDOMBYTES_H
#define RANDOMBYTES_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <stddef.h>
#include <stdint.h>

void randombytes_init(const uint8_t *seed, size_t num_bytes);

int randombytes(uint8_t *random_array, size_t num_bytes);

#if defined(__cplusplus)
}
#endif

#endif
