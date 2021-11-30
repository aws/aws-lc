#include <stddef.h>
#include <stdint.h>
#include "randombytes.h"
#include "openssl/rand.h"

int randombytes(uint8_t *random_array, size_t num_bytes) {
  return RAND_bytes(random_array, num_bytes);
}
