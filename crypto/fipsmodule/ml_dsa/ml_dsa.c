// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "../../evp_extra/internal.h"
#include "../evp/internal.h"
#include "ml_dsa.h"
#include "ml_dsa_ref/params.h"
#include "ml_dsa_ref/sign.h"

// These includes are required to compile ML-DSA. These can be moved to bcm.c
// when ML-DSA is added to the fipsmodule directory.
#include "./ml_dsa_ref/ntt.c"
#include "./ml_dsa_ref/packing.c"
#include "./ml_dsa_ref/params.c"
#include "./ml_dsa_ref/poly.c"
#include "./ml_dsa_ref/polyvec.c"
#include "./ml_dsa_ref/reduce.c"
#include "./ml_dsa_ref/rounding.c"
#include "./ml_dsa_ref/sign.c"

// Note: These methods currently default to using the reference code for
// ML-DSA. In a future where AWS-LC has optimized options available,
// those can be conditionally (or based on compile-time flags) called here,
// depending on platform support.

int ml_dsa_44_keypair_internal(uint8_t *public_key   /* OUT */,
                               uint8_t *private_key  /* OUT */,
                               const uint8_t *seed   /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  return ml_dsa_44_keypair_internal_no_self_test(public_key, private_key, seed);
}

int ml_dsa_44_keypair_internal_no_self_test(uint8_t *public_key   /* OUT */,
                                            uint8_t *private_key  /* OUT */,
                                            const uint8_t *seed   /* IN */) {
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_keypair_internal(&params, public_key, private_key, seed) == 0;
}

int ml_dsa_44_keypair(uint8_t *public_key   /* OUT */,
                      uint8_t *private_key  /* OUT */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return (ml_dsa_keypair(&params, public_key, private_key) == 0);
}

int ml_dsa_44_pack_pk_from_sk(uint8_t *public_key          /* OUT */,
                              const uint8_t *private_key   /* IN  */) {

  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_pack_pk_from_sk(&params, public_key, private_key) == 0;
}

int ml_dsa_44_sign(const uint8_t *private_key /* IN */,
                   uint8_t *sig               /* OUT */,
                   size_t *sig_len            /* OUT */,
                   const uint8_t *message     /* IN */,
                   size_t message_len         /* IN */,
                   const uint8_t *ctx_string  /* IN */,
                   size_t ctx_string_len      /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_sign(&params, sig, sig_len, message, message_len,
                     ctx_string, ctx_string_len, private_key) == 0;
}

int ml_dsa_extmu_44_sign(const uint8_t *private_key /* IN */,
                         uint8_t *sig               /* OUT */,
                         size_t *sig_len            /* OUT */,
                         const uint8_t *mu          /* IN */,
                         size_t mu_len              /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_extmu_sign(&params, sig, sig_len, mu, mu_len, private_key) == 0;
}

int ml_dsa_44_sign_internal(const uint8_t *private_key  /* IN */,
                            uint8_t *sig                /* OUT */,
                            size_t *sig_len             /* OUT */,
                            const uint8_t *message      /* IN */,
                            size_t message_len          /* IN */,
                            const uint8_t *pre          /* IN */,
                            size_t pre_len              /* IN */,
                            const uint8_t *rnd          /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  return ml_dsa_44_sign_internal_no_self_test(private_key, sig, sig_len, message,
                                              message_len, pre, pre_len, rnd);
}

int ml_dsa_44_sign_internal_no_self_test(const uint8_t *private_key  /* IN */,
                                         uint8_t *sig                /* OUT */,
                                         size_t *sig_len             /* OUT */,
                                         const uint8_t *message      /* IN */,
                                         size_t message_len          /* IN */,
                                         const uint8_t *pre          /* IN */,
                                         size_t pre_len              /* IN */,
                                         const uint8_t *rnd          /* IN */) {
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_sign_internal(&params, sig, sig_len, message, message_len,
                              pre, pre_len, rnd, private_key, 0) == 0;
}

int ml_dsa_extmu_44_sign_internal(const uint8_t *private_key  /* IN */,
                                  uint8_t *sig                /* OUT */,
                                  size_t *sig_len             /* OUT */,
                                  const uint8_t *mu           /* IN */,
                                  size_t mu_len               /* IN */,
                                  const uint8_t *pre          /* IN */,
                                  size_t pre_len              /* IN */,
                                  const uint8_t *rnd          /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_sign_internal(&params, sig, sig_len, mu, mu_len,
                              pre, pre_len, rnd, private_key, 1) == 0;
}

int ml_dsa_44_verify(const uint8_t *public_key /* IN */,
                     const uint8_t *sig        /* IN */,
                     size_t sig_len            /* IN */,
                     const uint8_t *message    /* IN */,
                     size_t message_len        /* IN */,
                     const uint8_t *ctx_string /* IN */,
                     size_t ctx_string_len     /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_verify(&params, sig, sig_len, message, message_len,
                       ctx_string, ctx_string_len, public_key) == 0;
}

int ml_dsa_extmu_44_verify(const uint8_t *public_key /* IN */,
                           const uint8_t *sig        /* IN */,
                           size_t sig_len            /* IN */,
                           const uint8_t *mu         /* IN */,
                           size_t mu_len             /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_verify_internal(&params, sig, sig_len, mu, mu_len, NULL, 0, public_key, 1) == 0;
}

int ml_dsa_44_verify_internal(const uint8_t *public_key /* IN */,
                              const uint8_t *sig        /* IN */,
                              size_t sig_len            /* IN */,
                              const uint8_t *message    /* IN */,
                              size_t message_len        /* IN */,
                              const uint8_t *pre        /* IN */,
                              size_t pre_len            /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  return ml_dsa_44_verify_internal_no_self_test(public_key, sig, sig_len, message,
                                                message_len, pre, pre_len);
}

int ml_dsa_44_verify_internal_no_self_test(const uint8_t *public_key /* IN */,
                                           const uint8_t *sig        /* IN */,
                                           size_t sig_len            /* IN */,
                                           const uint8_t *message    /* IN */,
                                           size_t message_len        /* IN */,
                                           const uint8_t *pre        /* IN */,
                                           size_t pre_len            /* IN */) {
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_verify_internal(&params, sig, sig_len, message, message_len,
                                pre, pre_len, public_key, 0) == 0;
}

int ml_dsa_extmu_44_verify_internal(const uint8_t *public_key /* IN */,
                                    const uint8_t *sig        /* IN */,
                                    size_t sig_len            /* IN */,
                                    const uint8_t *mu           /* IN */,
                                    size_t mu_len               /* IN */,
                                    const uint8_t *pre        /* IN */,
                                    size_t pre_len            /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_44_params_init(&params);
  return ml_dsa_verify_internal(&params, sig, sig_len, mu, mu_len,
                                pre, pre_len, public_key, 1) == 0;
}

int ml_dsa_65_keypair(uint8_t *public_key   /* OUT */,
                      uint8_t *private_key  /* OUT */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return (ml_dsa_keypair(&params, public_key, private_key) == 0);
}

int ml_dsa_65_pack_pk_from_sk(uint8_t *public_key          /* OUT */,
                              const uint8_t *private_key   /* IN  */) {
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_pack_pk_from_sk(&params, public_key, private_key) == 0;
}

int ml_dsa_65_keypair_internal(uint8_t *public_key   /* OUT */,
                               uint8_t *private_key  /* OUT */,
                               const uint8_t *seed   /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_keypair_internal(&params, public_key, private_key, seed) == 0;
}

int ml_dsa_65_sign(const uint8_t *private_key /* IN */,
                   uint8_t *sig               /* OUT */,
                   size_t *sig_len            /* OUT */,
                   const uint8_t *message     /* IN */,
                   size_t message_len         /* IN */,
                   const uint8_t *ctx_string  /* IN */,
                   size_t ctx_string_len      /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_sign(&params, sig, sig_len, message, message_len,
                     ctx_string, ctx_string_len, private_key) == 0;
}

int ml_dsa_extmu_65_sign(const uint8_t *private_key /* IN */,
                         uint8_t *sig               /* OUT */,
                         size_t *sig_len            /* OUT */,
                         const uint8_t *mu          /* IN */,
                         size_t mu_len              /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_extmu_sign(&params, sig, sig_len, mu, mu_len, private_key) == 0;
}

int ml_dsa_65_sign_internal(const uint8_t *private_key  /* IN */,
                            uint8_t *sig                /* OUT */,
                            size_t *sig_len             /* OUT */,
                            const uint8_t *message      /* IN */,
                            size_t message_len          /* IN */,
                            const uint8_t *pre          /* IN */,
                            size_t pre_len              /* IN */,
                            const uint8_t *rnd          /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_sign_internal(&params, sig, sig_len, message, message_len,
                              pre, pre_len, rnd, private_key, 0) == 0;
}

int ml_dsa_extmu_65_sign_internal(const uint8_t *private_key  /* IN */,
                                  uint8_t *sig                /* OUT */,
                                  size_t *sig_len             /* OUT */,
                                  const uint8_t *mu           /* IN */,
                                  size_t mu_len               /* IN */,
                                  const uint8_t *pre          /* IN */,
                                  size_t pre_len              /* IN */,
                                  const uint8_t *rnd          /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_sign_internal(&params, sig, sig_len, mu, mu_len,
                              pre, pre_len, rnd, private_key, 1) == 0;
}

int ml_dsa_65_verify(const uint8_t *public_key /* IN */,
                     const uint8_t *sig        /* IN */,
                     size_t sig_len            /* IN */,
                     const uint8_t *message    /* IN */,
                     size_t message_len        /* IN */,
                     const uint8_t *ctx_string /* IN */,
                     size_t ctx_string_len     /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_verify(&params, sig, sig_len, message, message_len,
                       ctx_string, ctx_string_len, public_key) == 0;
}

int ml_dsa_extmu_65_verify(const uint8_t *public_key /* IN */,
                           const uint8_t *sig        /* IN */,
                           size_t sig_len            /* IN */,
                           const uint8_t *mu         /* IN */,
                           size_t mu_len             /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_verify_internal(&params, sig, sig_len, mu, mu_len, NULL, 0, public_key, 1) == 0;
}

int ml_dsa_65_verify_internal(const uint8_t *public_key /* IN */,
                              const uint8_t *sig        /* IN */,
                              size_t sig_len            /* IN */,
                              const uint8_t *message    /* IN */,
                              size_t message_len        /* IN */,
                              const uint8_t *pre        /* IN */,
                              size_t pre_len            /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_verify_internal(&params, sig, sig_len, message, message_len,
                                pre, pre_len, public_key, 0) == 0;
}

int ml_dsa_extmu_65_verify_internal(const uint8_t *public_key /* IN */,
                                    const uint8_t *sig        /* IN */,
                                    size_t sig_len            /* IN */,
                                    const uint8_t *mu         /* IN */,
                                    size_t mu_len             /* IN */,
                                    const uint8_t *pre        /* IN */,
                                    size_t pre_len            /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_65_params_init(&params);
  return ml_dsa_verify_internal(&params, sig, sig_len, mu, mu_len,
                                pre, pre_len, public_key, 1) == 0;
}

int ml_dsa_87_keypair(uint8_t *public_key   /* OUT */,
                      uint8_t *private_key  /* OUT */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return (ml_dsa_keypair(&params, public_key, private_key) == 0);
}

int ml_dsa_87_pack_pk_from_sk(uint8_t *public_key          /* OUT */,
                              const uint8_t *private_key   /* IN  */) {

  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_pack_pk_from_sk(&params, public_key, private_key) == 0;
}

int ml_dsa_87_keypair_internal(uint8_t *public_key   /* OUT */,
                               uint8_t *private_key  /* OUT */,
                               const uint8_t *seed   /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_keypair_internal(&params, public_key, private_key, seed) == 0;
}

int ml_dsa_87_sign(const uint8_t *private_key /* IN */,
                   uint8_t *sig               /* OUT */,
                   size_t *sig_len            /* OUT */,
                   const uint8_t *message     /* IN */,
                   size_t message_len         /* IN */,
                   const uint8_t *ctx_string  /* IN */,
                   size_t ctx_string_len      /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_sign(&params, sig, sig_len, message, message_len,
                     ctx_string, ctx_string_len, private_key) == 0;
}

int ml_dsa_extmu_87_sign(const uint8_t *private_key /* IN */,
                         uint8_t *sig               /* OUT */,
                         size_t *sig_len            /* OUT */,
                         const uint8_t *mu          /* IN */,
                         size_t mu_len              /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_extmu_sign(&params, sig, sig_len, mu, mu_len, private_key) == 0;
}

int ml_dsa_87_sign_internal(const uint8_t *private_key  /* IN */,
                            uint8_t *sig                /* OUT */,
                            size_t *sig_len             /* OUT */,
                            const uint8_t *message      /* IN */,
                            size_t message_len          /* IN */,
                            const uint8_t *pre          /* IN */,
                            size_t pre_len              /* IN */,
                            const uint8_t *rnd          /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_sign_internal(&params, sig, sig_len, message, message_len,
                              pre, pre_len, rnd, private_key, 0) == 0;
}

int ml_dsa_extmu_87_sign_internal(const uint8_t *private_key  /* IN */,
                                  uint8_t *sig                /* OUT */,
                                  size_t *sig_len             /* OUT */,
                                  const uint8_t *mu           /* IN */,
                                  size_t mu_len               /* IN */,
                                  const uint8_t *pre          /* IN */,
                                  size_t pre_len              /* IN */,
                                  const uint8_t *rnd          /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_sign_internal(&params, sig, sig_len, mu, mu_len,
                              pre, pre_len, rnd, private_key, 1) == 0;
}

int ml_dsa_87_verify(const uint8_t *public_key /* IN */,
                     const uint8_t *sig        /* IN */,
                     size_t sig_len            /* IN */,
                     const uint8_t *message    /* IN */,
                     size_t message_len        /* IN */,
                     const uint8_t *ctx_string /* IN */,
                     size_t ctx_string_len     /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_verify(&params, sig, sig_len, message, message_len,
                       ctx_string, ctx_string_len, public_key) == 0;
}

int ml_dsa_extmu_87_verify(const uint8_t *public_key /* IN */,
                           const uint8_t *sig        /* IN */,
                           size_t sig_len            /* IN */,
                           const uint8_t *mu         /* IN */,
                           size_t mu_len             /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_verify_internal(&params, sig, sig_len, mu, mu_len, NULL, 0, public_key, 1) == 0;
}

int ml_dsa_87_verify_internal(const uint8_t *public_key /* IN */,
                              const uint8_t *sig        /* IN */,
                              size_t sig_len            /* IN */,
                              const uint8_t *message    /* IN */,
                              size_t message_len        /* IN */,
                              const uint8_t *pre        /* IN */,
                              size_t pre_len            /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_verify_internal(&params, sig, sig_len, message, message_len,
                                pre, pre_len, public_key, 0) == 0;
}

int ml_dsa_extmu_87_verify_internal(const uint8_t *public_key /* IN */,
                                    const uint8_t *sig        /* IN */,
                                    size_t sig_len            /* IN */,
                                    const uint8_t *mu         /* IN */,
                                    size_t mu_len             /* IN */,
                                    const uint8_t *pre        /* IN */,
                                    size_t pre_len            /* IN */) {
  boringssl_ensure_ml_dsa_self_test();
  ml_dsa_params params;
  ml_dsa_87_params_init(&params);
  return ml_dsa_verify_internal(&params, sig, sig_len, mu, mu_len,
                                pre, pre_len, public_key, 1) == 0;
}
