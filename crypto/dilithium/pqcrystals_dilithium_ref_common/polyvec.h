#ifndef ML_DSA_POLYVEC_H
#define ML_DSA_POLYVEC_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

/* Vectors of polynomials of length L */
typedef struct {
  ml_dsa_poly vec[ML_DSA_L_MAX];
} polyvecl;

void ml_dsa_polyvecl_uniform_eta(ml_dsa_params *params,
                                 polyvecl *v,
                                 const uint8_t seed[ML_DSA_CRHBYTES],
                                 uint16_t nonce);

void ml_dsa_polyvecl_uniform_gamma1(ml_dsa_params *params,
                                    polyvecl *v,
                                    const uint8_t seed[ML_DSA_CRHBYTES],
                                    uint16_t nonce);

void ml_dsa_polyvecl_reduce(ml_dsa_params *params, polyvecl *v);

void ml_dsa_polyvecl_add(ml_dsa_params *params,
                        polyvecl *w,
                        const polyvecl *u,
                        const polyvecl *v);

void ml_dsa_polyvecl_ntt(ml_dsa_params *params, polyvecl *v);

void ml_dsa_polyvecl_invntt_tomont(ml_dsa_params *params, polyvecl *v);

void ml_dsa_polyvecl_pointwise_poly_montgomery(ml_dsa_params *params,
                                               polyvecl *r,
                                               const ml_dsa_poly *a,
                                               const polyvecl *v);

void ml_dsa_polyvecl_pointwise_acc_montgomery(ml_dsa_params *params,
                                              ml_dsa_poly *w,
                                              const polyvecl *u,
                                              const polyvecl *v);

int ml_dsa_polyvecl_chknorm(ml_dsa_params *params, const polyvecl *v, int32_t B);

typedef struct {
  ml_dsa_poly vec[ML_DSA_K_MAX];
} polyveck;

void ml_dsa_polyveck_uniform_eta(ml_dsa_params *params,
                                 polyveck *v,
                                 const uint8_t seed[ML_DSA_CRHBYTES],
                                 uint16_t nonce);

void ml_dsa_polyveck_reduce(ml_dsa_params *params, polyveck *v);

void ml_dsa_polyveck_caddq(ml_dsa_params *params, polyveck *v);

void ml_dsa_polyveck_add(ml_dsa_params *params,
                         polyveck *w,
                         const polyveck *u,
                         const polyveck *v);

void ml_dsa_polyveck_sub(ml_dsa_params *params,
                        polyveck *w,
                        const polyveck *u,
                        const polyveck *v);

void ml_dsa_polyveck_shiftl(ml_dsa_params *params, polyveck *v);

void ml_dsa_polyveck_ntt(ml_dsa_params *params, polyveck *v);

void ml_dsa_polyveck_invntt_tomont(ml_dsa_params *params, polyveck *v);

void ml_dsa_polyveck_pointwise_poly_montgomery(ml_dsa_params *params,
                                               polyveck *r,
                                               const ml_dsa_poly *a,
                                               const polyveck *v);

int ml_dsa_polyveck_chknorm(ml_dsa_params *params, const polyveck *v, int32_t B);

void ml_dsa_polyveck_power2round(ml_dsa_params *params,
                                 polyveck *v1,
                                 polyveck *v0,
                                 const polyveck *v);

void ml_dsa_polyveck_decompose(ml_dsa_params *params,
                               polyveck *v1,
                               polyveck *v0,
                               const polyveck *v);

unsigned int ml_dsa_polyveck_make_hint(ml_dsa_params *params,
                                       polyveck *h,
                                       const polyveck *v0,
                                       const polyveck *v1);

void ml_dsa_polyveck_use_hint(ml_dsa_params *params,
                              polyveck *w,
                              const polyveck *v,
                              const polyveck *h);

void ml_dsa_polyveck_pack_w1(ml_dsa_params *params,
                             uint8_t *r,
                             const polyveck *w1);

void ml_dsa_polyvec_matrix_expand(ml_dsa_params *params,
                                  polyvecl *mat,
                                  const uint8_t rho[ML_DSA_SEEDBYTES]);

void ml_dsa_polyvec_matrix_pointwise_montgomery(ml_dsa_params *params,
                                                polyveck *t,
                                                const polyvecl *mat,
                                                const polyvecl *v);

#endif
