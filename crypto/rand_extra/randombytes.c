#include <openssl/rand.h>
#include <openssl/randombytes.h>
#include <stddef.h>
#include <stdint.h>
#include "../fipsmodule/rand/internal.h"

static int use_deterministic_randombytes = 0;
static CTR_DRBG_STATE drbg_state;
static int *use_deterministic_randombytes_get(void)
{
  return &use_deterministic_randombytes;
}

void use_deterministic_randombytes_for_testing(void)
{
  *use_deterministic_randombytes_get() = 1;
}

static void drbg_randombytes_init(const uint8_t *seed)
{
  CTR_DRBG_init(&drbg_state, seed, NULL, 0);
}

static int drbg_randombytes(uint8_t *random_array, size_t num_bytes)
{
  return CTR_DRBG_generate(&drbg_state, random_array, num_bytes, NULL, 0);
}

static int default_randombytes(uint8_t *random_array, size_t num_bytes)
{
  return RAND_bytes(random_array, num_bytes);
}

void randombytes_init_for_testing(const uint8_t *seed)
{
  if (*use_deterministic_randombytes_get() == 1)
  {
    drbg_randombytes_init(seed);
  }
}

int randombytes(uint8_t *random_array, size_t num_bytes)
{
  if (*use_deterministic_randombytes_get() == 1)
  {
    return drbg_randombytes(random_array, num_bytes);
  }
  else
  {
    return default_randombytes(random_array, num_bytes);
  }
}
