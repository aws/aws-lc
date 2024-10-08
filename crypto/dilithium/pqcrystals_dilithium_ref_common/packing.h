#ifndef PACKING_H
#define PACKING_H

#include <stdint.h>
#include "params.h"
#include "polyvec.h"

void pack_pk(ml_dsa_params *params,
             uint8_t *pk,
             const uint8_t rho[SEEDBYTES],
             const polyveck *t1);

void pack_sk(ml_dsa_params *params,
             uint8_t *sk,
             const uint8_t rho[SEEDBYTES],
             const uint8_t tr[TRBYTES],
             const uint8_t key[SEEDBYTES],
             const polyveck *t0,
             const polyvecl *s1,
             const polyveck *s2);

void pack_sig(ml_dsa_params *params,
              uint8_t *sig,
              const uint8_t *c,
              const polyvecl *z,
              const polyveck *h);

void unpack_pk(ml_dsa_params *params,
               uint8_t rho[SEEDBYTES],
               polyveck *t1,
               const uint8_t *pk);

void unpack_sk(ml_dsa_params *params,
               uint8_t rho[SEEDBYTES],
               uint8_t tr[TRBYTES],
               uint8_t key[SEEDBYTES],
               polyveck *t0,
               polyvecl *s1,
               polyveck *s2,
               const uint8_t *sk);

int unpack_sig(ml_dsa_params *params,
               uint8_t *c,
               polyvecl *z,
               polyveck *h,
               const uint8_t *sig);

#endif
