#ifndef KEM_KYBER_H
#define KEM_KYBER_H

#include <stdint.h>

int kyber_512_keypair(uint8_t *public_key, uint8_t *secret_key);
int kyber_512_enc(uint8_t *ciphertext, uint8_t *shared_secret, const uint8_t *public_key);
int kyber_512_dec(uint8_t *shared_secret, const uint8_t *ciphertext, const uint8_t *secret_key);
#endif

