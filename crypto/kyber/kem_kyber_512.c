#include "kem_kyber.h"
#include "pqcrystals-kyber_kyber512_ref/api.h"

int kyber_512_keypair(uint8_t *public_key, uint8_t *secret_key)
{
  return pqcrystals_kyber512_ref_keypair(public_key, secret_key);
}

int kyber_512_enc(uint8_t *ciphertext, uint8_t *shared_secret, const uint8_t *public_key)
{
  return pqcrystals_kyber512_ref_enc(ciphertext, shared_secret, public_key);
}

int kyber_512_dec(uint8_t *shared_secret, const uint8_t *ciphertext, const uint8_t *secret_key)
{
  return pqcrystals_kyber512_ref_dec(shared_secret, ciphertext, secret_key);
}
