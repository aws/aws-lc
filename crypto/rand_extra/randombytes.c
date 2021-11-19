#include <stddef.h>
#include <stdint.h>
#include <openssl/rand.h>
#include <openssl/randombytes.h>

void randombytes_init(const uint8_t *seed, size_t num_bytes)
{
  uint8_t unused;
  RAND_bytes(&unused, sizeof(unused));
}

int randombytes(uint8_t *random_array, size_t num_bytes) {
  return RAND_bytes(random_array, num_bytes);
}
