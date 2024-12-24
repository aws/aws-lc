#ifndef ML_DSA_POLY_H
#define ML_DSA_POLY_H

#include <stdint.h>
#include "params.h"

typedef struct {
  int32_t coeffs[ML_DSA_N];
} poly;

void ml_dsa_poly_reduce(poly *a);

void ml_dsa_poly_caddq(poly *a);

void ml_dsa_poly_add(poly *c, const poly *a, const poly *b);

void ml_dsa_poly_sub(poly *c, const poly *a, const poly *b);

void ml_dsa_poly_shiftl(poly *a);

void ml_dsa_poly_ntt(poly *a);

void ml_dsa_poly_invntt_tomont(poly *a);

void ml_dsa_poly_pointwise_montgomery(poly *c, const poly *a, const poly *b);

void ml_dsa_poly_power2round(poly *a1, poly *a0, const poly *a);

void ml_dsa_poly_decompose(ml_dsa_params *params, poly *a1, poly *a0, const poly *a);

unsigned int ml_dsa_poly_make_hint(ml_dsa_params *params,
                                   poly *h,
                                   const poly *a0,
                                   const poly *a1);

void ml_dsa_poly_use_hint(ml_dsa_params *params, poly *b, const poly *a, const poly *h);

int ml_dsa_poly_chknorm(const poly *a, int32_t B);

void ml_dsa_poly_uniform(poly *a,
                         const uint8_t seed[ML_DSA_SEEDBYTES],
                         uint16_t nonce);

void ml_dsa_poly_uniform_eta(ml_dsa_params *params,
                             poly *a,
                             const uint8_t seed[ML_DSA_CRHBYTES],
                             uint16_t nonce);

void ml_dsa_poly_uniform_gamma1(ml_dsa_params *params,
                               poly *a,
                               const uint8_t seed[ML_DSA_CRHBYTES],
                               uint16_t nonce);

void ml_dsa_poly_challenge(ml_dsa_params *params, poly *c, const uint8_t *seed);

void ml_dsa_polyeta_pack(ml_dsa_params *params, uint8_t *r, const poly *a);

void ml_dsa_polyeta_unpack(ml_dsa_params *params, poly *r, const uint8_t *a);

void ml_dsa_polyt1_pack(uint8_t *r, const poly *a);

void ml_dsa_polyt1_unpack(poly *r, const uint8_t *a);

void ml_dsa_polyt0_pack(uint8_t *r, const poly *a);

void ml_dsa_polyt0_unpack(poly *r, const uint8_t *a);

void ml_dsa_polyz_pack(ml_dsa_params *params, uint8_t *r, const poly *a);

void ml_dsa_polyz_unpack(ml_dsa_params *params, poly *r, const uint8_t *a);

void ml_dsa_polyw1_pack(ml_dsa_params *params, uint8_t *r, const poly *a);

#endif
