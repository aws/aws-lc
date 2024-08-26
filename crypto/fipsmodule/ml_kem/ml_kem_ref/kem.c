#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "params.h"
#include "kem.h"
#include "indcpa.h"
#include "verify.h"
#include "symmetric.h"
#include "openssl/rand.h"

/*************************************************
* Name:        crypto_kem_keypair_derand
*
* Description: Generates public and private key
*              for CCA-secure Kyber key encapsulation mechanism
*
* Arguments:   - uint8_t *pk: pointer to output public key
*                (an already allocated array of KYBER_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key
*                (an already allocated array of KYBER_SECRETKEYBYTES bytes)
*              - uint8_t *coins: pointer to input randomness
*                (an already allocated array filled with 2*KYBER_SYMBYTES random bytes)
**
* Returns 0 (success)
**************************************************/
int crypto_kem_keypair_derand(ml_kem_params *params,
                              uint8_t *pk,
                              uint8_t *sk,
                              const uint8_t *coins)
{
  indcpa_keypair_derand(params, pk, sk, coins);
  memcpy(sk+params->indcpa_secret_key_bytes, pk, params->public_key_bytes);
  hash_h(sk+params->secret_key_bytes-2*KYBER_SYMBYTES, pk, params->public_key_bytes);
  /* Value z for pseudo-random output on reject */
  memcpy(sk+params->secret_key_bytes-KYBER_SYMBYTES, coins+KYBER_SYMBYTES, KYBER_SYMBYTES);
  return 0;
}

/*************************************************
* Name:        crypto_kem_keypair
*
* Description: Generates public and private key
*              for CCA-secure Kyber key encapsulation mechanism
*
* Arguments:   - uint8_t *pk: pointer to output public key
*                (an already allocated array of KYBER_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key
*                (an already allocated array of KYBER_SECRETKEYBYTES bytes)
*
* Returns 0 (success)
**************************************************/
int crypto_kem_keypair(ml_kem_params *params,
                       uint8_t *pk,
                       uint8_t *sk)
{
  uint8_t coins[2*KYBER_SYMBYTES];
  RAND_bytes(coins, 2*KYBER_SYMBYTES);
  crypto_kem_keypair_derand(params, pk, sk, coins);
  return 0;
}

/*************************************************
* Name:        crypto_kem_enc_derand
*
* Description: Generates cipher text and shared
*              secret for given public key
*
* Arguments:   - uint8_t *ct: pointer to output cipher text
*                (an already allocated array of KYBER_CIPHERTEXTBYTES bytes)
*              - uint8_t *ss: pointer to output shared secret
*                (an already allocated array of KYBER_SSBYTES bytes)
*              - const uint8_t *pk: pointer to input public key
*                (an already allocated array of KYBER_PUBLICKEYBYTES bytes)
*              - const uint8_t *coins: pointer to input randomness
*                (an already allocated array filled with KYBER_SYMBYTES random bytes)
**
* Returns 0 (success)
**************************************************/
int crypto_kem_enc_derand(ml_kem_params *params,
                          uint8_t *ct,
                          uint8_t *ss,
                          const uint8_t *pk,
                          const uint8_t *coins)
{
  uint8_t buf[2*KYBER_SYMBYTES];
  /* Will contain key, coins */
  uint8_t kr[2*KYBER_SYMBYTES];

  memcpy(buf, coins, KYBER_SYMBYTES);

  /* Multitarget countermeasure for coins + contributory KEM */
  hash_h(buf+KYBER_SYMBYTES, pk, params->public_key_bytes);
  hash_g(kr, buf, 2*KYBER_SYMBYTES);

  /* coins are in kr+KYBER_SYMBYTES */
  indcpa_enc(params, ct, buf, pk, kr+KYBER_SYMBYTES);

  memcpy(ss,kr,KYBER_SYMBYTES);
  return 0;
}

/*************************************************
* Name:        crypto_kem_enc
*
* Description: Generates cipher text and shared
*              secret for given public key
*
* Arguments:   - uint8_t *ct: pointer to output cipher text
*                (an already allocated array of KYBER_CIPHERTEXTBYTES bytes)
*              - uint8_t *ss: pointer to output shared secret
*                (an already allocated array of KYBER_SSBYTES bytes)
*              - const uint8_t *pk: pointer to input public key
*                (an already allocated array of KYBER_PUBLICKEYBYTES bytes)
*
* Returns 0 (success)
**************************************************/
int crypto_kem_enc(ml_kem_params *params,
                   uint8_t *ct,
                   uint8_t *ss,
                   const uint8_t *pk)
{
  uint8_t coins[KYBER_SYMBYTES];
  RAND_bytes(coins, KYBER_SYMBYTES);
  crypto_kem_enc_derand(params, ct, ss, pk, coins);
  return 0;
}

/*************************************************
* Name:        crypto_kem_dec
*
* Description: Generates shared secret for given
*              cipher text and private key
*
* Arguments:   - uint8_t *ss: pointer to output shared secret
*                (an already allocated array of KYBER_SSBYTES bytes)
*              - const uint8_t *ct: pointer to input cipher text
*                (an already allocated array of KYBER_CIPHERTEXTBYTES bytes)
*              - const uint8_t *sk: pointer to input private key
*                (an already allocated array of KYBER_SECRETKEYBYTES bytes)
*
* Returns 0.
*
* On failure, ss will contain a pseudo-random value.
**************************************************/
int crypto_kem_dec(ml_kem_params *params,
                   uint8_t *ss,
                   const uint8_t *ct,
                   const uint8_t *sk)
{
  int fail;
  uint8_t buf[2*KYBER_SYMBYTES];
  /* Will contain key, coins */
  uint8_t kr[2*KYBER_SYMBYTES];
  uint8_t cmp[KYBER_CIPHERTEXTBYTES_MAX+KYBER_SYMBYTES];
  const uint8_t *pk = sk+params->indcpa_secret_key_bytes;

  indcpa_dec(params, buf, ct, sk);

  /* Multitarget countermeasure for coins + contributory KEM */
  memcpy(buf+KYBER_SYMBYTES, sk+params->secret_key_bytes-2*KYBER_SYMBYTES, KYBER_SYMBYTES);
  hash_g(kr, buf, 2*KYBER_SYMBYTES);

  /* coins are in kr+KYBER_SYMBYTES */
  indcpa_enc(params, cmp, buf, pk, kr+KYBER_SYMBYTES);

  fail = verify(ct, cmp, params->ciphertext_bytes);

  /* Compute rejection key */
  rkprf(params, ss,sk+params->secret_key_bytes-KYBER_SYMBYTES,ct);

  /* Copy true key to return buffer if fail is false */
  cmov(ss,kr,KYBER_SYMBYTES,!fail);

  return 0;
}
