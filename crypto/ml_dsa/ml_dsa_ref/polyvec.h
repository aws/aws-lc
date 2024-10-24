#ifndef POLYVEC_H
#define POLYVEC_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

/* Vectors of polynomials of length L */
typedef struct {
  poly vec[DILITHIUM_L_MAX];
} polyvecl;

void polyvecl_uniform_eta(ml_dsa_params *params,
                          polyvecl *v,
                          const uint8_t seed[CRHBYTES],
                          uint16_t nonce);

void polyvecl_uniform_gamma1(ml_dsa_params *params,
                             polyvecl *v,
                             const uint8_t seed[CRHBYTES],
                             uint16_t nonce);

void polyvecl_reduce(ml_dsa_params *params, polyvecl *v);

void polyvecl_add(ml_dsa_params *params,
                  polyvecl *w,
                  const polyvecl *u,
                  const polyvecl *v);

void polyvecl_ntt(ml_dsa_params *params, polyvecl *v);

void polyvecl_invntt_tomont(ml_dsa_params *params, polyvecl *v);

void polyvecl_pointwise_poly_montgomery(ml_dsa_params *params,
                                        polyvecl *r,
                                        const poly *a,
                                        const polyvecl *v);

void polyvecl_pointwise_acc_montgomery(ml_dsa_params *params,
                                       poly *w,
                                       const polyvecl *u,
                                       const polyvecl *v);

int polyvecl_chknorm(ml_dsa_params *params, const polyvecl *v, int32_t B);

typedef struct {
  poly vec[DILITHIUM_K_MAX];
} polyveck;

void polyveck_uniform_eta(ml_dsa_params *params,
                          polyveck *v,
                          const uint8_t seed[CRHBYTES],
                          uint16_t nonce);

void polyveck_reduce(ml_dsa_params *params, polyveck *v);

void polyveck_caddq(ml_dsa_params *params, polyveck *v);

void polyveck_add(ml_dsa_params *params,
                  polyveck *w,
                  const polyveck *u,
                  const polyveck *v);

void polyveck_sub(ml_dsa_params *params,
                  polyveck *w,
                  const polyveck *u,
                  const polyveck *v);

void polyveck_shiftl(ml_dsa_params *params, polyveck *v);

void polyveck_ntt(ml_dsa_params *params, polyveck *v);

void polyveck_invntt_tomont(ml_dsa_params *params, polyveck *v);

void polyveck_pointwise_poly_montgomery(ml_dsa_params *params,
                                        polyveck *r,
                                        const poly *a,
                                        const polyveck *v);

int polyveck_chknorm(ml_dsa_params *params, const polyveck *v, int32_t B);

void polyveck_power2round(ml_dsa_params *params,
                          polyveck *v1,
                          polyveck *v0,
                          const polyveck *v);

void polyveck_decompose(ml_dsa_params *params,
                        polyveck *v1,
                        polyveck *v0,
                        const polyveck *v);

unsigned int polyveck_make_hint(ml_dsa_params *params,
                                polyveck *h,
                                const polyveck *v0,
                                const polyveck *v1);

void polyveck_use_hint(ml_dsa_params *params,
                       polyveck *w,
                       const polyveck *v,
                       const polyveck *h);

void polyveck_pack_w1(ml_dsa_params *params,
                      uint8_t *r,
                      const polyveck *w1);

void polyvec_matrix_expand(ml_dsa_params *params,
                           polyvecl *mat,
                           const uint8_t rho[SEEDBYTES]);

void polyvec_matrix_pointwise_montgomery(ml_dsa_params *params,
                                         polyveck *t,
                                         const polyvecl *mat,
                                         const polyvecl *v);

#endif
