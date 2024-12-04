#ifndef SYMMETRIC_H
#define SYMMETRIC_H

#include <stdint.h>
#include "params.h"
#include "../../fipsmodule/sha/internal.h"

typedef KECCAK1600_CTX stream128_state;
typedef KECCAK1600_CTX stream256_state;

void dilithium_shake128_stream_init(KECCAK1600_CTX *state,
                                    const uint8_t seed[SEEDBYTES],
                                    uint16_t nonce);


void dilithium_shake256_stream_init(KECCAK1600_CTX *state,
                                    const uint8_t seed[CRHBYTES],
                                    uint16_t nonce);


#define STREAM128_BLOCKBYTES SHAKE128_RATE
#define STREAM256_BLOCKBYTES SHAKE256_RATE

#define stream128_init(STATE, SEED, NONCE) \
dilithium_shake128_stream_init(STATE, SEED, NONCE)
#define stream256_init(STATE, SEED, NONCE) \
dilithium_shake256_stream_init(STATE, SEED, NONCE)

#endif
