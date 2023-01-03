// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

//  --------------------------------------------------------------------
// | THIS IS JUST A PLACEHOLDER FILE TO SHOWCASE HOW THE KEM API WORKS. |
//  --------------------------------------------------------------------

#include <openssl/base.h>

#include "../fipsmodule/delocate.h"
#include "../internal.h"
#include "internal.h"

#include "../kyber/kem_kyber.h"

static int kyber512_keygen_placeholder(uint8_t *public_key,
                                       uint8_t *secret_key) {
  return kyber512_keypair(public_key, secret_key) == 0;
}

static int kyber512_encaps_placeholder(uint8_t *ciphertext,
                                       uint8_t *shared_secret,
                                       const uint8_t *public_key) {
  return kyber512_encapsulate(ciphertext, shared_secret, public_key) == 0;
}

static int kyber512_decaps_placeholder(uint8_t *shared_secret,
                                       const uint8_t *ciphertext,
                                       const uint8_t *secret_key) {
  return kyber512_decapsulate(shared_secret, ciphertext, secret_key) == 0;
}

const KEM_METHOD kem_kyber512_method = {
  kyber512_keygen_placeholder,
  kyber512_encaps_placeholder,
  kyber512_decaps_placeholder,
};

// Example how adding new KEM_METHOD looks like:
//
// static int kyber768_keygen_placeholder(uint8_t *public_key,
//                                 uint8_t *secret_key) {
//   return 1;
// }
// 
// static int kyber768_encaps_placeholder(uint8_t *ciphertext,
//                                 uint8_t *shared_secret,
//                                 const uint8_t *public_key) {
//   return 1;
// }
// 
// static int kyber768_decaps_placeholder(uint8_t *shared_secret,
//                                 const uint8_t *ciphertext,
//                                 const uint8_t *secret_key) {
//   return 1;
// }
// 
// const KEM_METHOD kem_kyber768_method = {
//   kyber768_keygen_placeholder,
//   kyber768_encaps_placeholder,
//   kyber768_decaps_placeholder,
// };

