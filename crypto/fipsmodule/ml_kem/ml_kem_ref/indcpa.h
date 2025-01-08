#ifndef ML_KEM_INDCPA_H
#define ML_KEM_INDCPA_H

#include <stdint.h>
#include "params.h"
#include "polyvec.h"

#define gen_matrix KYBER_NAMESPACE(gen_matrix)
void gen_matrix(ml_kem_params *params, polyvec *a, const uint8_t seed[KYBER_SYMBYTES], int transposed);

#define indcpa_keypair_derand KYBER_NAMESPACE(indcpa_keypair_derand)
void indcpa_keypair_derand(ml_kem_params *params,
                           uint8_t *pk,
                           uint8_t *sk,
                           const uint8_t coins[KYBER_SYMBYTES]);

#define indcpa_enc KYBER_NAMESPACE(indcpa_enc)
void indcpa_enc(ml_kem_params *params,
                uint8_t *c,
                const uint8_t *m,
                const uint8_t *pk,
                const uint8_t coins[KYBER_SYMBYTES]);

#define indcpa_dec KYBER_NAMESPACE(indcpa_dec)
void indcpa_dec(ml_kem_params *params,
                uint8_t *m,
                const uint8_t *c,
                const uint8_t *sk);

#endif
