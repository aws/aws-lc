#ifndef ML_KEM_SYMMETRIC_H
#define ML_KEM_SYMMETRIC_H

#include <stddef.h>
#include <stdint.h>
#include "params.h"

#include "../../sha/internal.h"

#define kyber_shake128_absorb KYBER_NAMESPACE(kyber_shake128_absorb)
void kyber_shake128_absorb(KECCAK1600_CTX *ctx,
                           const uint8_t seed[KYBER_SYMBYTES],
                           uint8_t x,
                           uint8_t y);

#define kyber_shake256_prf KYBER_NAMESPACE(kyber_shake256_prf)
void kyber_shake256_prf(uint8_t *out, size_t outlen, const uint8_t key[KYBER_SYMBYTES], uint8_t nonce);

#define kyber_shake256_rkprf KYBER_NAMESPACE(kyber_shake256_rkprf)
void kyber_shake256_rkprf(ml_kem_params *params, uint8_t out[KYBER_SSBYTES], const uint8_t key[KYBER_SYMBYTES], const uint8_t *input);

#define kyber_shake128_squeeze KYBER_NAMESPACE(kyber_shake128_squeeze)
void kyber_shake128_squeeze(KECCAK1600_CTX *ctx, uint8_t *out, int nblocks);

#define hash_h(OUT, IN, INBYTES) SHA3_256(IN, INBYTES, OUT)
#define hash_g(OUT, IN, INBYTES) SHA3_512(IN, INBYTES, OUT)
#define xof_absorb(STATE, SEED, X, Y) kyber_shake128_absorb(STATE, SEED, X, Y)
#define xof_squeezeblocks(OUT, OUTBLOCKS, STATE) kyber_shake128_squeeze(STATE, OUT, OUTBLOCKS)
#define prf(OUT, OUTBYTES, KEY, NONCE) kyber_shake256_prf(OUT, OUTBYTES, KEY, NONCE)
#define rkprf(PARAMS, OUT, KEY, INPUT) kyber_shake256_rkprf(PARAMS, OUT, KEY, INPUT)

#endif /* SYMMETRIC_H */
