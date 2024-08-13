#ifndef INDCPA_H
#define INDCPA_H

#include <stdint.h>
#include "params.h"
#include "polyvec.h"

void gen_matrix(ml_kem_params *params, polyvec *a, const uint8_t *seed, int transposed);

void indcpa_keypair_derand(ml_kem_params *params,
                           uint8_t *pk,
                           uint8_t *sk,
                           const uint8_t *coins);

void indcpa_enc(ml_kem_params *params,
                uint8_t *c,
                const uint8_t *m,
                const uint8_t *pk,
                const uint8_t *coins);

void indcpa_dec(ml_kem_params *params,
                uint8_t *m,
                const uint8_t *c,
                const uint8_t *sk);

#endif
