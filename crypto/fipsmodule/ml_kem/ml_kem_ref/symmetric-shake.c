#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "params.h"
#include "symmetric.h"

/*************************************************
* Name:        kyber_shake128_absorb
*
* Description: Absorb step of the SHAKE128 specialized for the Kyber context.
*
* Arguments:   - KECCAK1600_CTX *ctx: pointer to (uninitialized) output Keccak state
*              - const uint8_t *seed: pointer to KYBER_SYMBYTES input to be absorbed into state
*              - uint8_t i: additional byte of input
*              - uint8_t j: additional byte of input
**************************************************/
void kyber_shake128_absorb(KECCAK1600_CTX *ctx,
                           const uint8_t seed[KYBER_SYMBYTES],
                           uint8_t x,
                           uint8_t y)
{
  uint8_t extseed[KYBER_SYMBYTES+2];

  memcpy(extseed, seed, KYBER_SYMBYTES);
  extseed[KYBER_SYMBYTES+0] = x;
  extseed[KYBER_SYMBYTES+1] = y;

  // Return code checks can be omitted
  // SHAKE_Init always returns 1 when called with correct block size value
  SHAKE_Init(ctx, SHAKE128_BLOCKSIZE);

  // SHAKE_Absorb always returns 1 on first call of sizeof(extseed) (34 bytes)
  SHAKE_Absorb(ctx, extseed, sizeof(extseed));
}

/*************************************************
* Name:        kyber_shake128_squeeze
*
* Description: Squeeze step of SHAKE128 XOF. Squeezes full blocks of
*              SHAKE128_BLOCKSIZE bytes each. Can be called multiple times
*              to keep squeezing. Assumes new block has not yet been
*              started.
*
* Arguments:   - uint8_t *out: pointer to output blocks
*              - size_t nblocks: number of blocks to be squeezed (written to output)
*              - KECCAK1600_CTX *ctx: pointer to input/output Keccak state
**************************************************/
void kyber_shake128_squeeze(KECCAK1600_CTX *ctx, uint8_t *out, int nblocks)
{
  // Return code checks can be omitted
  // SHAKE_Squeeze always returns 1 when |ctx->state| flag is different 
  // from |KECCAK1600_STATE_FINAL|
  SHAKE_Squeeze(out, ctx, nblocks * SHAKE128_BLOCKSIZE);
}

/*************************************************
* Name:        kyber_shake256_prf
*
* Description: Usage of SHAKE256 as a PRF, concatenates secret and public input
*              and then generates outlen bytes of SHAKE256 output
*
* Arguments:   - uint8_t *out: pointer to output
*              - size_t outlen: number of requested output bytes
*              - const uint8_t *key: pointer to the key (of length KYBER_SYMBYTES)
*              - uint8_t nonce: single-byte nonce (public PRF input)
**************************************************/
void kyber_shake256_prf(uint8_t *out, size_t outlen, const uint8_t key[KYBER_SYMBYTES], uint8_t nonce)
{
  uint8_t extkey[KYBER_SYMBYTES+1];

  memcpy(extkey, key, KYBER_SYMBYTES);
  extkey[KYBER_SYMBYTES] = nonce;

  // Return code checks can be omitted
  // SHAKE256 never returns NULL when the internal SHAKE_Init is called with correct block size value
  SHAKE256(extkey, sizeof(extkey), out, outlen);
}

/*************************************************
* Name:        kyber_shake256_prf
*
* Description: Usage of SHAKE256 as a PRF, concatenates secret and public input
*              and then generates outlen bytes of SHAKE256 output
*
* Arguments:   - uint8_t *out: pointer to output
*              - size_t outlen: number of requested output bytes
*              - const uint8_t *key: pointer to the key (of length KYBER_SYMBYTES)
*              - uint8_t nonce: single-byte nonce (public PRF input)
**************************************************/
void kyber_shake256_rkprf(ml_kem_params *params, uint8_t out[KYBER_SSBYTES], const uint8_t key[KYBER_SYMBYTES], const uint8_t *input)
{
  KECCAK1600_CTX ctx;

  // Return code checks can be omitted
  // SHAKE_Init always returns 1 when called with correct block size value
  SHAKE_Init(&ctx, SHAKE256_BLOCKSIZE);

  // SHAKE_Absorb always returns 1 on first call of KYBER_SYMBYTES (32 bytes)
  SHAKE_Absorb(&ctx, key, KYBER_SYMBYTES);

  // SHAKE_Absorb always returns 1 processing all data blocks that don't need pad
  SHAKE_Absorb(&ctx, input, params->ciphertext_bytes);

  // SHAKE_Final always returns 1 when |ctx->state| flag is set to  
  // |KECCAK1600_STATE_ABSORB| (no previous calls to SHAKE_Final)
  SHAKE_Final(out, &ctx, KYBER_SSBYTES);
}
