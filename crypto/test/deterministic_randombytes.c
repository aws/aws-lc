#include <assert.h>
#include <openssl/conf.h>
#include <openssl/evp.h>
#include <openssl/randombytes.h>
#include <string.h>

typedef struct {
  uint8_t key[32];
  uint8_t v[16];
  int reseed_counter;
} AES256_CTR_DRBG_struct;
static AES256_CTR_DRBG_struct DRBG_ctx;

static void AES256_ECB(uint8_t *out, const uint8_t *key, const uint8_t *ctr)
{
  EVP_CIPHER_CTX *ctx;
  int len;

  if((ctx = EVP_CIPHER_CTX_new()) &&
     EVP_EncryptInit_ex(ctx, EVP_aes_256_ecb(), NULL, key, NULL))
  {
    EVP_EncryptUpdate(ctx, out, &len, ctr, 16);
  }

  EVP_CIPHER_CTX_free(ctx);
}

static void increment_v(uint8_t *v, int num_bytes)
{
  for (int i = num_bytes-1; i >= 0; i--)
  {
    if ( v[i] == 0xFF )
    {
      v[i] = 0x00;
    }
    else
    {
      v[i]++;
      break;
    }
  }
}

static void AES256_CTR_DRBG_Update(uint8_t *key,
                                   uint8_t *v,
                                   const uint8_t *provided_data)
{
  uint8_t temp[48];
  
  for (int i = 0; i < 3; i++)
  {
    increment_v(v, 16);
    AES256_ECB(temp+16*i, key, v);
  }

  if ( provided_data != NULL )
  {
    for (int i = 0; i < 48; i++)
    {
      temp[i] ^= provided_data[i];
    }
  }
  memcpy(key, temp, 32);
  memcpy(v, temp+32, 16);
}

void randombytes_init(const uint8_t *seed, size_t num_bytes)
{
  assert(num_bytes == 48);
  uint8_t seed_material[48];

  memcpy(seed_material, seed, 48);
  memset(DRBG_ctx.key, 0x00, 32);
  memset(DRBG_ctx.v, 0x00, 16);
  AES256_CTR_DRBG_Update(DRBG_ctx.key, DRBG_ctx.v, seed_material);
  DRBG_ctx.reseed_counter = 1;
}

int randombytes(uint8_t *random_array, size_t num_bytes)
{
  uint8_t block[16];
  int i = 0;

  while ( num_bytes > 0 )
  {
    increment_v(DRBG_ctx.v, 16);
    AES256_ECB(block, DRBG_ctx.key, DRBG_ctx.v);
    if ( num_bytes > 15 )
    {
      memcpy(random_array+i, block, 16);
      i += 16;
      num_bytes -= 16;
    }
    else
    {
      memcpy(random_array+i, block, num_bytes);
      num_bytes = 0;
    }
  }
  AES256_CTR_DRBG_Update(DRBG_ctx.key, DRBG_ctx.v, NULL);
  DRBG_ctx.reseed_counter++;

  return 1;
}
