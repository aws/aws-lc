#include "kem_kyber.h"
#include "pqcrystals-kyber_kyber512_ref/api.h"

int kyber_512_keypair(uint8_t *public_key, uint8_t *secret_key) {
  return pqcrystals_kyber512_ref_keypair(public_key, secret_key);
}
