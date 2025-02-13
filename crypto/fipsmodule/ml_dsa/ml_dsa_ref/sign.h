#ifndef ML_DSA_SIGN_H
#define ML_DSA_SIGN_H

#include <stddef.h>
#include <stdint.h>
#include "params.h"

int ml_dsa_keypair(ml_dsa_params *params,
                   uint8_t *pk,
                   uint8_t *sk,
                   uint8_t *seed);

int ml_dsa_keypair_internal(ml_dsa_params *params,
                            uint8_t *pk,
                            uint8_t *sk,
                            const uint8_t *seed);

int ml_dsa_sign(ml_dsa_params *params,
                uint8_t *sig, size_t *siglen,
                const uint8_t *m, size_t mlen,
                const uint8_t *ctx, size_t ctxlen,
                const uint8_t *sk);

int ml_dsa_extmu_sign(ml_dsa_params *params,
                      uint8_t *sig, size_t *siglen,
                      const uint8_t *mu, size_t mulen,
                      const uint8_t *sk);

int ml_dsa_sign_internal(ml_dsa_params *params,
                         uint8_t *sig, size_t *siglen,
                         const uint8_t *m, size_t mlen,
                         const uint8_t *pre, size_t prelen,
                         const uint8_t *rnd,
                         const uint8_t *sk,
                         int external_mu);

int ml_dsa_sign_message(ml_dsa_params *params,
                        uint8_t *sm, size_t *smlen,
                        const uint8_t *m, size_t mlen,
                        const uint8_t *ctx, size_t ctxlen,
                        const uint8_t *sk);

int ml_dsa_verify(ml_dsa_params *params,
                  const uint8_t *sig, size_t siglen,
                  const uint8_t *m, size_t mlen,
                  const uint8_t *ctx, size_t ctxlen,
                  const uint8_t *pk);

int ml_dsa_verify_internal(ml_dsa_params *params,
                           const uint8_t *sig, size_t siglen,
                           const uint8_t *m, size_t mlen,
                           const uint8_t *pre, size_t prelen,
                           const uint8_t *pk,
                           int external_mu);

int ml_dsa_verify_message(ml_dsa_params *params,
                          uint8_t *m, size_t *mlen,
                          const uint8_t *sm, size_t smlen,
                          const uint8_t *ctx, size_t ctxlen,
                          const uint8_t *pk);

#endif
