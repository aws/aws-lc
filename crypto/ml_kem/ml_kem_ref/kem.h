#ifndef KEM_H
#define KEM_H

#include <stdint.h>
#include "params.h"

#define crypto_kem_keypair_derand KYBER_NAMESPACE(keypair_derand)
int crypto_kem_keypair_derand(ml_kem_params *params, uint8_t *pk, uint8_t *sk, const uint8_t *coins);

#define crypto_kem_keypair KYBER_NAMESPACE(keypair)
int crypto_kem_keypair(ml_kem_params *params, uint8_t *pk, uint8_t *sk);

#define crypto_kem_enc_derand KYBER_NAMESPACE(enc_derand)
int crypto_kem_enc_derand(ml_kem_params * params, uint8_t *ct, uint8_t *ss, const uint8_t *pk, const uint8_t *coins);

#define crypto_kem_enc KYBER_NAMESPACE(enc)
int crypto_kem_enc(ml_kem_params * params, uint8_t *ct, uint8_t *ss, const uint8_t *pk);

#define crypto_kem_dec KYBER_NAMESPACE(dec)
int crypto_kem_dec(ml_kem_params * params, uint8_t *ss, const uint8_t *ct, const uint8_t *sk);

#endif
