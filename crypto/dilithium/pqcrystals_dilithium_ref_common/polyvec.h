#ifndef POLYVEC_H
#define POLYVEC_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

/* Vectors of polynomials of length L */
typedef struct {
  poly vec[DILITHIUM_L_MAX];
} polyvecl;

#define polyvecl_uniform_eta DILITHIUM_NAMESPACE(polyvecl_uniform_eta)
void polyvecl_uniform_eta(ml_dsa_params *params,
                          polyvecl *v,
                          const uint8_t seed[CRHBYTES],
                          uint16_t nonce);

#define polyvecl_uniform_gamma1 DILITHIUM_NAMESPACE(polyvecl_uniform_gamma1)
void polyvecl_uniform_gamma1(ml_dsa_params *params,
                             polyvecl *v,
                             const uint8_t seed[CRHBYTES],
                             uint16_t nonce);

#define polyvecl_reduce DILITHIUM_NAMESPACE(polyvecl_reduce)
void polyvecl_reduce(ml_dsa_params *params, polyvecl *v);

#define polyvecl_add DILITHIUM_NAMESPACE(polyvecl_add)
void polyvecl_add(ml_dsa_params *params,
                  polyvecl *w,
                  const polyvecl *u,
                  const polyvecl *v);

#define polyvecl_ntt DILITHIUM_NAMESPACE(polyvecl_ntt)
void polyvecl_ntt(ml_dsa_params *params, polyvecl *v);
#define polyvecl_invntt_tomont DILITHIUM_NAMESPACE(polyvecl_invntt_tomont)
void polyvecl_invntt_tomont(ml_dsa_params *params, polyvecl *v);
#define polyvecl_pointwise_poly_montgomery DILITHIUM_NAMESPACE(polyvecl_pointwise_poly_montgomery)
void polyvecl_pointwise_poly_montgomery(ml_dsa_params *params,
                                        polyvecl *r,
                                        const poly *a,
                                        const polyvecl *v);
#define polyvecl_pointwise_acc_montgomery \
        DILITHIUM_NAMESPACE(polyvecl_pointwise_acc_montgomery)
void polyvecl_pointwise_acc_montgomery(ml_dsa_params *params,
                                       poly *w,
                                       const polyvecl *u,
                                       const polyvecl *v);


#define polyvecl_chknorm DILITHIUM_NAMESPACE(polyvecl_chknorm)
int polyvecl_chknorm(ml_dsa_params *params, const polyvecl *v, int32_t B);



/* Vectors of polynomials of length K */
typedef struct {
  poly vec[DILITHIUM_K_MAX];
} polyveck;

#define polyveck_uniform_eta DILITHIUM_NAMESPACE(polyveck_uniform_eta)
void polyveck_uniform_eta(ml_dsa_params *params,
                          polyveck *v,
                          const uint8_t seed[CRHBYTES],
                          uint16_t nonce);

#define polyveck_reduce DILITHIUM_NAMESPACE(polyveck_reduce)
void polyveck_reduce(ml_dsa_params *params, polyveck *v);
#define polyveck_caddq DILITHIUM_NAMESPACE(polyveck_caddq)
void polyveck_caddq(ml_dsa_params *params, polyveck *v);

#define polyveck_add DILITHIUM_NAMESPACE(polyveck_add)
void polyveck_add(ml_dsa_params *params,
                  polyveck *w,
                  const polyveck *u,
                  const polyveck *v);
#define polyveck_sub DILITHIUM_NAMESPACE(polyveck_sub)
void polyveck_sub(ml_dsa_params *params,
                  polyveck *w,
                  const polyveck *u,
                  const polyveck *v);
#define polyveck_shiftl DILITHIUM_NAMESPACE(polyveck_shiftl)
void polyveck_shiftl(ml_dsa_params *params, polyveck *v);

#define polyveck_ntt DILITHIUM_NAMESPACE(polyveck_ntt)
void polyveck_ntt(ml_dsa_params *params, polyveck *v);
#define polyveck_invntt_tomont DILITHIUM_NAMESPACE(polyveck_invntt_tomont)
void polyveck_invntt_tomont(ml_dsa_params *params, polyveck *v);
#define polyveck_pointwise_poly_montgomery DILITHIUM_NAMESPACE(polyveck_pointwise_poly_montgomery)
void polyveck_pointwise_poly_montgomery(ml_dsa_params *params,
                                        polyveck *r,
                                        const poly *a,
                                        const polyveck *v);

#define polyveck_chknorm DILITHIUM_NAMESPACE(polyveck_chknorm)
int polyveck_chknorm(ml_dsa_params *params, const polyveck *v, int32_t B);

#define polyveck_power2round DILITHIUM_NAMESPACE(polyveck_power2round)
void polyveck_power2round(ml_dsa_params *params,
                          polyveck *v1,
                          polyveck *v0,
                          const polyveck *v);
#define polyveck_decompose DILITHIUM_NAMESPACE(polyveck_decompose)
void polyveck_decompose(ml_dsa_params *params,
                        polyveck *v1,
                        polyveck *v0,
                        const polyveck *v);
#define polyveck_make_hint DILITHIUM_NAMESPACE(polyveck_make_hint)
unsigned int polyveck_make_hint(ml_dsa_params *params,
                                polyveck *h,
                                const polyveck *v0,
                                const polyveck *v1);
#define polyveck_use_hint DILITHIUM_NAMESPACE(polyveck_use_hint)
void polyveck_use_hint(ml_dsa_params *params,
                       polyveck *w,
                       const polyveck *v,
                       const polyveck *h);

#define polyveck_pack_w1 DILITHIUM_NAMESPACE(polyveck_pack_w1)
void polyveck_pack_w1(ml_dsa_params *params,
                      uint8_t *r,
                      const polyveck *w1);

#define polyvec_matrix_expand DILITHIUM_NAMESPACE(polyvec_matrix_expand)
void polyvec_matrix_expand(ml_dsa_params *params,
                           polyvecl *mat,
                           const uint8_t rho[SEEDBYTES]);

#define polyvec_matrix_pointwise_montgomery DILITHIUM_NAMESPACE(polyvec_matrix_pointwise_montgomery)
void polyvec_matrix_pointwise_montgomery(ml_dsa_params *params,
                                         polyveck *t,
                                         const polyvecl *mat,
                                         const polyvecl *v);

#endif
