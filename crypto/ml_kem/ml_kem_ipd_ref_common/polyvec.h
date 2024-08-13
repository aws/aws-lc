#ifndef POLYVEC_H
#define POLYVEC_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

typedef struct{
  poly vec[KYBER_K_MAX];
} polyvec;

void polyvec_compress(ml_kem_params *params, uint8_t *r, const polyvec *a);
void polyvec_decompress(ml_kem_params *params, polyvec *r, const uint8_t *a);

void polyvec_tobytes(ml_kem_params *params, uint8_t *r, const polyvec *a);
void polyvec_frombytes(ml_kem_params *params, polyvec *r, const uint8_t *a);

void polyvec_ntt(ml_kem_params *params, polyvec *r);
void polyvec_invntt_tomont(ml_kem_params *params, polyvec *r);

void polyvec_basemul_acc_montgomery(ml_kem_params *params, poly *r, const polyvec *a, const polyvec *b);

void polyvec_reduce(ml_kem_params *params, polyvec *r);

void polyvec_add(ml_kem_params *params, polyvec *r, const polyvec *a, const polyvec *b);

#endif
