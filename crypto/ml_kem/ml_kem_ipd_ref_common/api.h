#ifndef API_H
#define API_H

#include <stdint.h>

#define ml_kem_512_SECRETKEYBYTES 1632
#define ml_kem_512_PUBLICKEYBYTES 800
#define ml_kem_512_CIPHERTEXTBYTES 768
#define ml_kem_512_KEYPAIRCOINBYTES 64
#define ml_kem_512_ENCCOINBYTES 32
#define ml_kem_512_BYTES 32

#define ml_kem_512_ref_SECRETKEYBYTES pqcrystals_kyber512_SECRETKEYBYTES
#define ml_kem_512_ref_PUBLICKEYBYTES pqcrystals_kyber512_PUBLICKEYBYTES
#define ml_kem_512_ref_CIPHERTEXTBYTES pqcrystals_kyber512_CIPHERTEXTBYTES
#define ml_kem_512_ref_KEYPAIRCOINBYTES pqcrystals_kyber512_KEYPAIRCOINBYTES
#define ml_kem_512_ref_ENCCOINBYTES pqcrystals_kyber512_ENCCOINBYTES
#define ml_kem_512_ref_BYTES pqcrystals_kyber512_BYTES

int ml_kem_512_ref_keypair_derand(uint8_t *pk, uint8_t *sk, const uint8_t *coins);
int ml_kem_512_ref_keypair(uint8_t *pk, uint8_t *sk);
int ml_kem_512_ref_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk, const uint8_t *coins);
int ml_kem_512_ref_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk);
int ml_kem_512_ref_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk);

#define ml_kem_768_SECRETKEYBYTES 2400
#define ml_kem_768_PUBLICKEYBYTES 1184
#define ml_kem_768_CIPHERTEXTBYTES 1088
#define ml_kem_768_KEYPAIRCOINBYTES 64
#define ml_kem_768_ENCCOINBYTES 32
#define ml_kem_768_BYTES 32

#define ml_kem_768_ref_SECRETKEYBYTES pqcrystals_kyber768_SECRETKEYBYTES
#define ml_kem_768_ref_PUBLICKEYBYTES pqcrystals_kyber768_PUBLICKEYBYTES
#define ml_kem_768_ref_CIPHERTEXTBYTES pqcrystals_kyber768_CIPHERTEXTBYTES
#define ml_kem_768_ref_KEYPAIRCOINBYTES pqcrystals_kyber768_KEYPAIRCOINBYTES
#define ml_kem_768_ref_ENCCOINBYTES pqcrystals_kyber768_ENCCOINBYTES
#define ml_kem_768_ref_BYTES pqcrystals_kyber768_BYTES

int ml_kem_768_ref_keypair_derand(uint8_t *pk, uint8_t *sk, const uint8_t *coins);
int ml_kem_768_ref_keypair(uint8_t *pk, uint8_t *sk);
int ml_kem_768_ref_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk, const uint8_t *coins);
int ml_kem_768_ref_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk);
int ml_kem_768_ref_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk);

#define ml_kem_1024_SECRETKEYBYTES 3168
#define ml_kem_1024_PUBLICKEYBYTES 1568
#define ml_kem_1024_CIPHERTEXTBYTES 1568
#define ml_kem_1024_KEYPAIRCOINBYTES 64
#define ml_kem_1024_ENCCOINBYTES 32
#define ml_kem_1024_BYTES 32

#define ml_kem_1024_ref_SECRETKEYBYTES pqcrystals_kyber1024_SECRETKEYBYTES
#define ml_kem_1024_ref_PUBLICKEYBYTES pqcrystals_kyber1024_PUBLICKEYBYTES
#define ml_kem_1024_ref_CIPHERTEXTBYTES pqcrystals_kyber1024_CIPHERTEXTBYTES
#define ml_kem_1024_ref_KEYPAIRCOINBYTES pqcrystals_kyber1024_KEYPAIRCOINBYTES
#define ml_kem_1024_ref_ENCCOINBYTES pqcrystals_kyber1024_ENCCOINBYTES
#define ml_kem_1024_ref_BYTES pqcrystals_kyber1024_BYTES

int ml_kem_1024_ref_keypair_derand(uint8_t *pk, uint8_t *sk, const uint8_t *coins);
int ml_kem_1024_ref_keypair(uint8_t *pk, uint8_t *sk);
int ml_kem_1024_ref_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk, const uint8_t *coins);
int ml_kem_1024_ref_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk);
int ml_kem_1024_ref_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk);

#endif
