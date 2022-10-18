#ifndef KEM_KYBER_H
#define KEM_KYBER_H

#include <stddef.h>
#include <stdint.h>
#include <openssl/base.h>
#include <openssl/evp.h>

// The values below are taken from the |api.h| file in the
// |crypto/kyber/pqcrystals-kyber_kyber512_ref| directory.
#define KYBER512_PUBLIC_KEY_BYTES 800
#define KYBER512_SECRET_KEY_BYTES 1632
#define KYBER512_CIPHERTEXT_BYTES 768
#define KYBER512_SHARED_SECRET_BYTES 32

int kyber512_keypair(uint8_t *public_key /* OUT */,
                     uint8_t *secret_key /* OUT */);

int kyber512_encapsulate(uint8_t *ciphertext       /* OUT */,
                         uint8_t *shared_secret    /* OUT */,
                         const uint8_t *public_key /* IN  */);

int kyber512_decapsulate(uint8_t *shared_secret    /* OUT */,
                         const uint8_t *ciphertext /* IN  */,
                         const uint8_t *secret_key /* IN  */);

#endif

