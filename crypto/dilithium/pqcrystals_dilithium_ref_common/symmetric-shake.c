#include <stdint.h>
#include "params.h"
#include "symmetric.h"

/*************************************************
* Name:        dilithium_shake128_stream_init
*
* Description: Initalise and absorb step of SHAKE128 specialized for ML-DSA
*              context. Takes an uninitialized state |ctx| and initializes an
*              output stream of SHAKE128(seed|nonce) using |seed| and |nonce|.
*
* Arguments:   - KECCAK1600_CTX *ctx: pointer to input/output Keccak state
*              - const uint8_t seed[]: byte array with seed of length CRHBYTES
*              - uint16_t nonce: 2-byte nonce
*
**************************************************/
void dilithium_shake128_stream_init(KECCAK1600_CTX *ctx, const uint8_t seed[SEEDBYTES], uint16_t nonce)
{
  uint8_t t[2];
  t[0] = nonce;
  t[1] = nonce >> 8;

  SHAKE_Init(ctx, SHAKE128_BLOCKSIZE);
  SHA3_Update(ctx, seed, SEEDBYTES);
  SHA3_Update(ctx, t, 2);
}

/*************************************************
* Name:        dilithium_shake256_stream_init
*
* Description: Initalise and absorb step of SHAKE256 specialized for ML-DSA
*              context. Takes an uninitialized state |ctx| and initializes an
*              output stream of SHAKE256(seed|nonce) using |seed| and |nonce|.
*
* Arguments:   - KECCAK1600_CTX *ctx: pointer to input/output Keccak state
*              - const uint8_t seed[]: byte array with seed of length CRHBYTES
*              - uint16_t nonce: 2-byte nonce
*
**************************************************/
void dilithium_shake256_stream_init(KECCAK1600_CTX *ctx, const uint8_t seed[CRHBYTES], uint16_t nonce)
{
  uint8_t t[2];
  t[0] = nonce;
  t[1] = nonce >> 8;

  SHAKE_Init(ctx, SHAKE256_BLOCKSIZE);
  SHA3_Update(ctx, seed, CRHBYTES);
  SHA3_Update(ctx, t, 2);
}
