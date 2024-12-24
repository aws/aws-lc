#include <stdint.h>
#include "params.h"
#include "polyvec.h"
#include "poly.h"

/*************************************************
* Name:        ml_dsa_polyvec_matrix_expand
*
* Description: FIPS 204: Algorithm 32 ExpandA.
*              Generates matrix A with uniformly
*              random coefficients a_{i,j} by performing rejection
*              sampling on the output stream of SHAKE128(rho|j|i)
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyvecl mat: pointer to output matrix
*              - const uint8_t rho[]: byte array containing seed rho
**************************************************/
void ml_dsa_polyvec_matrix_expand(ml_dsa_params *params,
                                  polyvecl *mat,
                                  const uint8_t rho[ML_DSA_SEEDBYTES]) {
  unsigned int i, j;
  for(i = 0; i < params->k; ++i) {
    for(j = 0; j < params->l; ++j) {
      ml_dsa_poly_uniform(&mat[i].vec[j], rho, (i << 8) + j);
    }
  }
}

/*************************************************
* Name:        ml_dsa_polyvec_matrix_pointwise_montgomery
*
* Description: Pointwise multiply vectors of polynomials of length K,
*              wrapper for polyvecl_pointwise_acc_montgomery.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck t: pointer to output polynomial
*              - polyvecl mat: pointer to first input vector
*              - polyvecl v: pointer to second input vector
**************************************************/
void ml_dsa_polyvec_matrix_pointwise_montgomery(ml_dsa_params *params,
                                                polyveck *t,
                                                const polyvecl *mat,
                                                const polyvecl *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_polyvecl_pointwise_acc_montgomery(params, &t->vec[i], &mat[i], v);
  }
}

/**************************************************************/
/************ Vectors of polynomials of length L **************/
/**************************************************************/

/*************************************************
* Name:        ml_dsa_polyvecl_uniform_eta
*
* Description: FIPS 204: Algorithm 33 ExpandS (for vectors l).
*              Samples vector v with polynomial coordinates whose
*              coefficients are in [-eta, eta].
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyvecl v: pointer to output vector
*              - const uint8_t seed: byte array containing seed
*              - uint16_t nonce: 2-byte nonce
**************************************************/
void ml_dsa_polyvecl_uniform_eta(ml_dsa_params *params,
                                 polyvecl *v,
                                 const uint8_t seed[ML_DSA_CRHBYTES],
                                 uint16_t nonce) {
  unsigned int i;
  for(i = 0; i < params->l; ++i)
    ml_dsa_poly_uniform_eta(params, &v->vec[i], seed, nonce++);
}

/*************************************************
* Name:        ml_dsa_polyvecl_uniform_gamma1
*
* Description: FIPS 204: Algorithm 34 ExpandMask.
*              Samples vector v with polynomial coordinates whose
*              coefficients are in [-gamma1 + 1, gamma1].
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyvecl v: pointer to output vector
*              - const uint8_t seed: byte array containing seed
*              - uint16_t nonce: 2-byte nonce
**************************************************/
void ml_dsa_polyvecl_uniform_gamma1(ml_dsa_params *params,
                                    polyvecl *v,
                                    const uint8_t seed[ML_DSA_CRHBYTES],
                                    uint16_t nonce) {
  unsigned int i;
  for(i = 0; i < params->l; ++i) {
    ml_dsa_poly_uniform_gamma1(params, &v->vec[i], seed, params->l*nonce + i);
  }
}

/*************************************************
* Name:        ml_dsa_polyvecl_reduce
*
* Description: Reduce coefficients of polynomials in vector of length L
*              to representatives in [-6283009,6283007].
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *v: pointer to input/output vector
**************************************************/
void ml_dsa_polyvecl_reduce(ml_dsa_params *params, polyvecl *v) {
  unsigned int i;
  for(i = 0; i < params->l; ++i) {
    ml_dsa_poly_reduce(&v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyvecl_add
*
* Description: Add vectors of polynomials of length L.
*              No modular reduction is performed.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyvecl *w: pointer to output vector
*              - const polyvecl *u: pointer to first summand
*              - const polyvecl *v: pointer to second summand
**************************************************/
void ml_dsa_polyvecl_add(ml_dsa_params *params,
                         polyvecl *w,
                         const polyvecl *u,
                         const polyvecl *v) {
  unsigned int i;
  for(i = 0; i < params->l; ++i) {
    ml_dsa_poly_add(&w->vec[i], &u->vec[i], &v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyvecl_ntt
*
* Description: Forward NTT of all polynomials in vector of length L. Output
*              coefficients can be up to 16*Q larger than input coefficients.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyvecl *v: pointer to input/output vector
**************************************************/
void ml_dsa_polyvecl_ntt(ml_dsa_params *params, polyvecl *v) {
  unsigned int i;
  for(i = 0; i < params->l; ++i) {
    ml_dsa_poly_ntt(&v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyvecl_invntt_tomont
*
* Description: Inverse NTT and multiplication by 2^{32} of polynomials
*              in vector of length l. Input coefficients need to be less
*              than 2*Q.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyvecl *v: pointer to input/output vector
**************************************************/
void ml_dsa_polyvecl_invntt_tomont(ml_dsa_params *params, polyvecl *v) {
  unsigned int i;
  for(i = 0; i < params->l; ++i) {
    ml_dsa_poly_invntt_tomont(&v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyvecl_pointwise_poly_montgomery
*
* Description: Pointwise multiplication of polynomials in NTT domain
*              representation and multiplication of resulting polynomial
*              by 2^{-32}.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyvecl *r: pointer to output polynomial
*              - const poly *a: pointer to input polynomial
*              - const polyvecl *v: pointer to input vector
**************************************************/
void ml_dsa_polyvecl_pointwise_poly_montgomery(ml_dsa_params *params,
                                               polyvecl *r,
                                               const ml_dsa_poly *a,
                                               const polyvecl *v) {
  unsigned int i;
  for(i = 0; i < params->l; ++i) {
    ml_dsa_poly_pointwise_montgomery(&r->vec[i], a, &v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyvecl_pointwise_acc_montgomery
*
* Description: Pointwise multiply vectors of polynomials of length L, multiply
*              resulting vector by 2^{-32} and add (accumulate) polynomials
*              in it. Input/output vectors are in NTT domain representation.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - poly *w: output polynomial
*              - const polyvecl *u: pointer to first input vector
*              - const polyvecl *v: pointer to second input vector
**************************************************/
void ml_dsa_polyvecl_pointwise_acc_montgomery(ml_dsa_params *params,
                                              ml_dsa_poly *w,
                                              const polyvecl *u,
                                              const polyvecl *v)
{
  unsigned int i;
  ml_dsa_poly t;
  ml_dsa_poly_pointwise_montgomery(w, &u->vec[0], &v->vec[0]);
  for(i = 1; i < params->l; ++i) {
    ml_dsa_poly_pointwise_montgomery(&t, &u->vec[i], &v->vec[i]);
    ml_dsa_poly_add(w, w, &t);
  }
}

/*************************************************
* Name:        ml_dsa_polyvecl_chknorm
*
* Description: Check infinity norm of polynomials in vector of length L.
*              Assumes input polyvecl to be reduced by polyvecl_reduce().
*
* Arguments:   - ml_dsa_params: parameter struct
*              - const polyvecl *v: pointer to vector
*              - int32_t B: norm bound
*
* Returns 0 if norm of all polynomials is strictly smaller than B <= (Q-1)/8
* and 1 otherwise.
**************************************************/
int ml_dsa_polyvecl_chknorm(ml_dsa_params *params, const polyvecl *v, int32_t bound)  {
  unsigned int i;
  for(i = 0; i < params->l; ++i) {
    if(ml_dsa_poly_chknorm(&v->vec[i], bound)) {
      return 1;
    }
  }
  return 0;
}

/**************************************************************/
/************ Vectors of polynomials of length K **************/
/**************************************************************/

/*************************************************
* Name:        ml_dsa_polyvecl_uniform_eta
*
* Description: FIPS 204: Algorithm 33 ExpandS (for vectors k).
*              Samples vector v with polynomial coordinates whose
*              coefficients are in [-eta, eta].
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck v: pointer to output vector
*              - const uint8_t seed: byte array containing seed
*              - uint16_t nonce: 2-byte nonce
**************************************************/
void ml_dsa_polyveck_uniform_eta(ml_dsa_params *params,
                                 polyveck *v,
                                 const uint8_t seed[ML_DSA_CRHBYTES],
                                 uint16_t nonce) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_uniform_eta(params, &v->vec[i], seed, nonce++);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_reduce
*
* Description: Reduce coefficients of polynomials in vector of length K
*              to representatives in [-6283009,6283007].
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *v: pointer to input/output vector
**************************************************/
void ml_dsa_polyveck_reduce(ml_dsa_params *params, polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_reduce(&v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_caddq
*
* Description: For all coefficients of polynomials in vector of length K
*              add Q if coefficient is negative.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *v: pointer to input/output vector
**************************************************/
void ml_dsa_polyveck_caddq(ml_dsa_params *params, polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_caddq(&v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_add
*
* Description: Add vectors of polynomials of length K.
*              No modular reduction is performed.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *w: pointer to output vector
*              - const polyveck *u: pointer to first summand
*              - const polyveck *v: pointer to second summand
**************************************************/
void ml_dsa_polyveck_add(ml_dsa_params *params,
                         polyveck *w,
                         const polyveck *u,
                         const polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_add(&w->vec[i], &u->vec[i], &v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_sub
*
* Description: Subtract vectors of polynomials of length K.
*              No modular reduction is performed.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *w: pointer to output vector
*              - const polyveck *u: pointer to first input vector
*              - const polyveck *v: pointer to second input vector to be
*                                   subtracted from first input vector
**************************************************/
void ml_dsa_polyveck_sub(ml_dsa_params *params,
                         polyveck *w,
                         const polyveck *u,
                         const polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_sub(&w->vec[i], &u->vec[i], &v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_shiftl
*
* Description: Multiply vector of polynomials of Length K by 2^D without modular
*              reduction. Assumes input coefficients to be less than 2^{31-D}.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *v: pointer to input/output vector
**************************************************/
void ml_dsa_polyveck_shiftl(ml_dsa_params *params, polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_shiftl(&v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_ntt
*
* Description: Forward NTT of all polynomials in vector of length K. Output
*              coefficients can be up to 16*Q larger than input coefficients.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *v: pointer to input/output vector
**************************************************/
void ml_dsa_polyveck_ntt(ml_dsa_params *params, polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_ntt(&v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_invntt_tomont
*
* Description: Inverse NTT and multiplication by 2^{32} of polynomials
*              in vector of length K. Input coefficients need to be less
*              than 2*Q.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *v: pointer to input/output vector
**************************************************/
void ml_dsa_polyveck_invntt_tomont(ml_dsa_params *params, polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_invntt_tomont(&v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_pointwise_poly_montgomery
*
* Description: Pointwise multiplication of polynomials in NTT domain
*              representation and multiplication of resulting polynomial
*              by 2^{-32}.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *r: pointer to output polynomial
*              - const poly *a: pointer to input polynomial
*              - const polyveck *v: pointer to input vector
**************************************************/
void ml_dsa_polyveck_pointwise_poly_montgomery(ml_dsa_params *params,
                                               polyveck *r,
                                               const ml_dsa_poly *a,
                                               const polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_pointwise_montgomery(&r->vec[i], a, &v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_chknorm
*
* Description: Check infinity norm of polynomials in vector of length K.
*              Assumes input polyveck to be reduced by polyveck_reduce().
*
* Arguments:   - ml_dsa_params: parameter struct
*              - const polyveck *v: pointer to vector
*              - int32_t B: norm bound
*
* Returns 0 if norm of all polynomials are strictly smaller than B <= (Q-1)/8
* and 1 otherwise.
**************************************************/
int ml_dsa_polyveck_chknorm(ml_dsa_params *params, const polyveck *v, int32_t bound) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    if(ml_dsa_poly_chknorm(&v->vec[i], bound)) {
      return 1;
    }
  }
  return 0;
}

/*************************************************
* Name:        ml_dsa_polyveck_power2round
*
* Description: For all coefficients a of polynomials in vector of length K,
*              compute a0, a1 such that a mod^+ Q = a1*2^D + a0
*              with -2^{D-1} < a0 <= 2^{D-1}. Assumes coefficients to be
*              standard representatives.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *v1: pointer to output vector of polynomials with
*                              coefficients a1
*              - polyveck *v0: pointer to output vector of polynomials with
*                              coefficients a0
*              - const polyveck *v: pointer to input vector
**************************************************/
void ml_dsa_polyveck_power2round(ml_dsa_params *params,
                                 polyveck *v1,
                                 polyveck *v0,
                                 const polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_power2round(&v1->vec[i], &v0->vec[i], &v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_decompose
*
* Description: For all coefficients a of polynomials in vector of length K,
*              compute high and low bits a0, a1 such a mod^+ Q = a1*ALPHA + a0
*              with -ALPHA/2 < a0 <= ALPHA/2 except a1 = (Q-1)/ALPHA where we
*              set a1 = 0 and -ALPHA/2 <= a0 = a mod Q - Q < 0.
*              Assumes coefficients to be standard representatives.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *v1: pointer to output vector of polynomials with
*                              coefficients a1
*              - polyveck *v0: pointer to output vector of polynomials with
*                              coefficients a0
*              - const polyveck *v: pointer to input vector
**************************************************/
void ml_dsa_polyveck_decompose(ml_dsa_params *params,
                               polyveck *v1,
                               polyveck *v0,
                               const polyveck *v) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_decompose(params, &v1->vec[i], &v0->vec[i], &v->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_make_hint
*
* Description: Compute hint vector.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *h: pointer to output vector
*              - const polyveck *v0: pointer to low part of input vector
*              - const polyveck *v1: pointer to high part of input vector
*
* Returns number of 1 bits.
**************************************************/
unsigned int ml_dsa_polyveck_make_hint(ml_dsa_params *params,
                                       polyveck *h,
                                       const polyveck *v0,
                                       const polyveck *v1)
{
  unsigned int i, s = 0;
  for(i = 0; i < params->k; ++i) {
    s += ml_dsa_poly_make_hint(params, &h->vec[i], &v0->vec[i], &v1->vec[i]);
  }
  return s;
}

/*************************************************
* Name:        ml_dsa_polyveck_use_hint
*
* Description: Use hint vector to correct the high bits of input vector.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - polyveck *w: pointer to output vector of polynomials with
*                             corrected high bits
*              - const polyveck *u: pointer to input vector
*              - const polyveck *h: pointer to input hint vector
**************************************************/
void ml_dsa_polyveck_use_hint(ml_dsa_params *params,
                              polyveck *w,
                              const polyveck *u,
                              const polyveck *h) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_poly_use_hint(params, &w->vec[i], &u->vec[i], &h->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_polyveck_pack_w1
*
* Description: FIPS 204: Algorithm 28 w1Encode.
*              Encodes a polynomial vector |w1| into a byte string.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t *r: pointer to output byte array with at least
*                            POLYW1_PACKEDBYTES bytes
*              - const polyvecl *w1: pointer to vector w1
**************************************************/
void ml_dsa_polyveck_pack_w1(ml_dsa_params *params,
                             uint8_t *r,
                             const polyveck *w1) {
  unsigned int i;
  for(i = 0; i < params->k; ++i) {
    ml_dsa_polyw1_pack(params, &r[i*params->poly_w1_packed_bytes], &w1->vec[i]);
  }
}
