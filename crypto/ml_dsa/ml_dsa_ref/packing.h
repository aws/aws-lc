#ifndef ML_DSA_PACKING_H
#define ML_DSA_PACKING_H

#include <stdint.h>
#include "params.h"
#include "polyvec.h"

int ml_dsa_pack_pk_from_sk(ml_dsa_params *params,
                           uint8_t *pk,
                           const uint8_t *sk);

void ml_dsa_pack_pk(ml_dsa_params *params,
                    uint8_t *pk,
                    const uint8_t rho[ML_DSA_SEEDBYTES],
                    const polyveck *t1);

void ml_dsa_pack_sk(ml_dsa_params *params,
                    uint8_t *sk,
                    const uint8_t rho[ML_DSA_SEEDBYTES],
                    const uint8_t tr[ML_DSA_TRBYTES],
                    const uint8_t key[ML_DSA_SEEDBYTES],
                    const polyveck *t0,
                    const polyvecl *s1,
                    const polyveck *s2);

void ml_dsa_pack_sig(ml_dsa_params *params,
                    uint8_t *sig,
                    const uint8_t *c,
                    const polyvecl *z,
                    const polyveck *h);

void ml_dsa_unpack_pk(ml_dsa_params *params,
                      uint8_t rho[ML_DSA_SEEDBYTES],
                      polyveck *t1,
                      const uint8_t *pk);

void ml_dsa_unpack_sk(ml_dsa_params *params,
                      uint8_t rho[ML_DSA_SEEDBYTES],
                      uint8_t tr[ML_DSA_TRBYTES],
                      uint8_t key[ML_DSA_SEEDBYTES],
                      polyveck *t0,
                      polyvecl *s1,
                      polyveck *s2,
                      const uint8_t *sk);

int ml_dsa_unpack_sig(ml_dsa_params *params,
                      uint8_t *c,
                      polyvecl *z,
                      polyveck *h,
                      const uint8_t *sig);

#endif
