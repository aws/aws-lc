#ifndef RANDOMBYTES_H
#define RANDOMBYTES_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <stddef.h>
#include <stdint.h>

int randombytes(uint8_t *random_array, size_t num_bytes);

#if defined(__cplusplus)
}
#endif

#endif
