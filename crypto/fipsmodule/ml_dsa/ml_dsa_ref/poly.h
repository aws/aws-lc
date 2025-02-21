#ifndef ML_DSA_POLY_H
#define ML_DSA_POLY_H

#include <stdint.h>
#include "params.h"

typedef struct {
  int32_t coeffs[ML_DSA_N];
} ml_dsa_poly;

void ml_dsa_poly_reduce(ml_dsa_poly *a);

void ml_dsa_poly_caddq(ml_dsa_poly *a);

void ml_dsa_poly_add(ml_dsa_poly *c, const ml_dsa_poly *a, const ml_dsa_poly *b);

void ml_dsa_poly_sub(ml_dsa_poly *c, const ml_dsa_poly *a, const ml_dsa_poly *b);

void ml_dsa_poly_shiftl(ml_dsa_poly *a);

void ml_dsa_poly_ntt(ml_dsa_poly *a);

void ml_dsa_poly_invntt_tomont(ml_dsa_poly *a);

void ml_dsa_poly_pointwise_montgomery(ml_dsa_poly *c,
                                     const ml_dsa_poly *a,
                                     const ml_dsa_poly *b);

void ml_dsa_poly_power2round(ml_dsa_poly *a1, ml_dsa_poly *a0, const ml_dsa_poly *a);

void ml_dsa_poly_decompose(ml_dsa_params *params,
                           ml_dsa_poly *a1,
                           ml_dsa_poly *a0,
                           const ml_dsa_poly *a);

unsigned int ml_dsa_poly_make_hint(ml_dsa_params *params,
                                   ml_dsa_poly *h,
                                   const ml_dsa_poly *a0,
                                   const ml_dsa_poly *a1);

void ml_dsa_poly_use_hint(ml_dsa_params *params,
                          ml_dsa_poly *b,
                          const ml_dsa_poly *a,
                          const ml_dsa_poly *h);

int ml_dsa_poly_chknorm(const ml_dsa_poly *a, int32_t B);

void ml_dsa_poly_uniform(ml_dsa_poly *a,
                         const uint8_t seed[ML_DSA_SEEDBYTES],
                         uint16_t nonce);

void ml_dsa_poly_uniform_eta(ml_dsa_params *params,
                             ml_dsa_poly *a,
                             const uint8_t seed[ML_DSA_CRHBYTES],
                             uint16_t nonce);

void ml_dsa_poly_uniform_gamma1(ml_dsa_params *params,
                               ml_dsa_poly *a,
                               const uint8_t seed[ML_DSA_CRHBYTES],
                               uint16_t nonce);

void ml_dsa_poly_challenge(ml_dsa_params *params, ml_dsa_poly *c, const uint8_t *seed);

void ml_dsa_polyeta_pack(ml_dsa_params *params, uint8_t *r, const ml_dsa_poly *a);

void ml_dsa_polyeta_unpack(ml_dsa_params *params, ml_dsa_poly *r, const uint8_t *a);

void ml_dsa_polyt1_pack(uint8_t *r, const ml_dsa_poly *a);

void ml_dsa_polyt1_unpack(ml_dsa_poly *r, const uint8_t *a);

void ml_dsa_polyt0_pack(uint8_t *r, const ml_dsa_poly *a);

void ml_dsa_polyt0_unpack(ml_dsa_poly *r, const uint8_t *a);

void ml_dsa_polyz_pack(ml_dsa_params *params, uint8_t *r, const ml_dsa_poly *a);

void ml_dsa_polyz_unpack(ml_dsa_params *params, ml_dsa_poly *r, const uint8_t *a);

void ml_dsa_polyw1_pack(ml_dsa_params *params, uint8_t *r, const ml_dsa_poly *a);

#endif
