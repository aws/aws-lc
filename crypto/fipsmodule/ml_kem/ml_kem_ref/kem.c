#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "./params.h"
#include "./kem.h"
#include "./indcpa.h"
#include "./verify.h"
#include "./reduce.h"
#include "./symmetric.h"

#include "openssl/rand.h"

#if defined(AWSLC_FIPS)
// FIPS 203. Pair-wise Consistency Test (PCT) required per [FIPS 140-3 IG](https://csrc.nist.gov/csrc/media/Projects/cryptographic-module-validation-program/documents/fips%20140-3/FIPS%20140-3%20IG.pdf):
// The PCT consists of applying the encapsulation key to encapsulate a shared
// secret leading to ciphertext, and then applying decapsulation key to
// retrieve the same shared secret. Returns 0 if the PCT passes, 1 otherwise.
static int keygen_pct(ml_kem_params *params, const uint8_t *ek, const uint8_t *dk) {
  uint8_t ct[KYBER_CIPHERTEXTBYTES_MAX];
  uint8_t ss_enc[KYBER_SSBYTES];
  uint8_t ss_dec[KYBER_SSBYTES];

  crypto_kem_enc(params, ct, ss_enc, ek);
  crypto_kem_dec(params, ss_dec, ct, dk);

  if (boringssl_fips_break_test("MLKEM_PWCT")) {
    ss_enc[0] = ~ss_enc[0];
  }

  return verify(ss_enc, ss_dec, KYBER_SSBYTES);
}
#endif

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
*
* Returns:     - 0 on success
*              - -1 upon PCT failure (if AWSLC_FIPS is set)
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

#if defined(AWSLC_FIPS)
  // Abort in case of PCT failure.
  if (keygen_pct(params, pk, sk)) {
    return -1;
  }
#endif
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
* Returns:     - 0 on success
*              - -1 upon PCT failure (if AWSLC_FIPS is set)
**************************************************/
int crypto_kem_keypair(ml_kem_params *params,
                       uint8_t *pk,
                       uint8_t *sk)
{
  uint8_t coins[2*KYBER_SYMBYTES];
  RAND_bytes(coins, 2*KYBER_SYMBYTES);
  int res = crypto_kem_keypair_derand(params, pk, sk, coins);

  // FIPS 203. Section 3.3 Destruction of intermediate values.
  OPENSSL_cleanse(coins, sizeof(coins));

  return res;
}

// Converts a centered representative |in| which is an integer in
// {-(q-1)/2, ..., (q-1)/2}, to a positive representative in {0, ..., q-1}.
// It implements in constant-time the following operation:
//   return (in < 0) ? in + KYBER_Q : in;
static int16_t centered_to_positive_representative(int16_t in) {
  // mask = (in < 0) ? b11..11 : b00..00;
  crypto_word_t mask = constant_time_is_zero_w(in >> 15);
  int16_t in_fixed = in + KYBER_Q;
  return constant_time_select_int(mask, in, in_fixed);
}

#define BYTE_ENCODE_12_IN_SIZE  (256)
#define BYTE_ENCODE_12_OUT_SIZE (32 * 12)
#define BYTE_DECODE_12_OUT_SIZE (BYTE_ENCODE_12_IN_SIZE)
#define BYTE_DECODE_12_IN_SIZE  (BYTE_ENCODE_12_OUT_SIZE)

// FIPS 203. Algorithm 5 ByteEncode_12
// Encodes an array of 256 12-bit integers into a byte array.
// Intuition for the implementation:
//   in:  |xxxxxxxxyyyy| |yyyyzzzzzzzz| ...
//   out: |xxxxxxxx| |yyyyyyyy| |zzzzzzzz| ...
// We divide the input in pairs of elements (2 x 12 bits = 24 bits),
// and the output in triplets (3 x 8 bits = 24 bits). For each pair/triplet we:
//   - out0 <-- first eight bits of in0,
//   - out1 <-- concatenate last 4 bits of in0 and first 4 bits of in1,
//   - out2 <-- last 8 bits of in1.
static void byte_encode_12(uint8_t out[BYTE_ENCODE_12_OUT_SIZE],
                           const int16_t in[BYTE_ENCODE_12_IN_SIZE]) {
  for (size_t i = 0; i < BYTE_ENCODE_12_IN_SIZE / 2; i++) {
    int16_t in0 = in[2 * i];
    int16_t in1 = in[2 * i + 1];
    out[3 * i]     = in0 & 0xff;
    out[3 * i + 1] = ((in0 >> 8) & 0xf) | ((in1 & 0xf) << 4);
    out[3 * i + 2] = (in1 >> 4) & 0xff;
  }
}

// FIPS 203. Algorithm 6 ByteDecode_12
// Decodes a byte array into an array of 256 12-bit integers.
// Intuition for the implementation:
//   in:  |xxxxxxxx| |yyyyyyyy| |zzzzzzzz| ...
//   out: |xxxxxxxxyyyy| |yyyyzzzzzzzz| ...
// We divide the input in triplets of elements (3 x 8 bits = 24 bits),
// and the output in pairs (2 x 12 bits = 24 bits). For each pair/triplet we:
//   - out[0] <-- concatenate eight bits of in[0] and first 4 bits of in[1],
//   - out[1] <-- concatenate last 4 bits of in[1] and 8 bits of in[2].
// Additionally we reduce the output elements mod Q as specified in FIPS 203.
static void byte_decode_12(int16_t out[BYTE_DECODE_12_OUT_SIZE],
                           const uint8_t in[BYTE_DECODE_12_IN_SIZE]) {
  for(size_t i = 0; i < BYTE_DECODE_12_OUT_SIZE / 2; i++) {
    // Cast to 16-bit wide uint's to avoid any issues
    // with shifting and implicit casting.
    uint16_t in0 = (uint16_t) in[3 * i];
    uint16_t in1 = (uint16_t) in[3 * i + 1];
    uint16_t in2 = (uint16_t) in[3 * i + 2];

    // Build the output pair.
    uint16_t out0 = in0 | ((in1 & 0xf) << 8);
    uint16_t out1 = (in1 >> 4) | (in2 << 4);

    // Reduce mod Q.
    out[2 * i] = centered_to_positive_representative(barrett_reduce(out0));
    out[2 * i + 1] = centered_to_positive_representative(barrett_reduce(out1));
  }
}

#define ENCAPS_KEY_ENCODED_MAX_SIZE (BYTE_ENCODE_12_OUT_SIZE * KYBER_K_MAX)
#define ENCAPS_KEY_DECODED_MAX_SIZE (BYTE_DECODE_12_OUT_SIZE * KYBER_K_MAX)

// FIPS 203. Section 7.2 Encapsulation key check.
// This function implements the encapsulation key modulus check. The other
// check specified in Section 7.2 is a type check the key. We can safely omit
// that check here because it is done in higher level functions. The required
// lengths for all variants of ML-KEM are hard-coded in: fipsmodule/kem/kem.c.
// If a key is generated by aws-lc then it satisfies the length requirements.
// If a key is generated outside of aws-lc, it has to be imported into an
// `EVP_PKEY` object to be used within aws-lc. We provide only these three
// functions to do that:  `EVP_PKEY_kem_new_raw_key`,
// `EVP_PKEY_kem_new_raw_secret_key`, `EVP_PKEY_kem_new_raw_public_key`.
// The lengths are checked in all three functions.
static int encapsulation_key_modulus_check(ml_kem_params *params, const uint8_t *ek) {

  int16_t ek_decoded[ENCAPS_KEY_DECODED_MAX_SIZE];
  uint8_t ek_recoded[ENCAPS_KEY_ENCODED_MAX_SIZE];

  for (size_t i = 0; i < params->k; i++) {
    byte_decode_12(&ek_decoded[i * BYTE_DECODE_12_OUT_SIZE], &ek[i * BYTE_DECODE_12_IN_SIZE]);
    byte_encode_12(&ek_recoded[i * BYTE_ENCODE_12_OUT_SIZE], &ek_decoded[i * BYTE_ENCODE_12_IN_SIZE]);
  }

  return verify(ek_recoded, ek, params->k * BYTE_ENCODE_12_OUT_SIZE);
}

// FIPS 203. Section 7.3 Decapsulation key hash check
// The spec defines the decapsulation key as following:
//   dk <-- (dk_pke || ek || H(ek) || z).
// This check takes |ek| out of |dk|, computes H(ek), and verifies that it is
// the same as the H(ek) portion stored in |dk|.
//
// This function implements the decapsulation key hash check. The other checks
// specified in Section 7.3 are the ciphertext and the key type check. We can
// safely omit those checks here because they are done in higher level functions.
// The required lengths for all variants of ML-KEM are hard-coded in
// fipsmodule/kem/kem.c. If a key is generated by aws-lc then it satisfies
// the length requirements. If a key is generated outside of aws-lc, it has to
// be imported into an `EVP_PKEY` object to be used within aws-lc. We provide
// only these three functions to do that:  `EVP_PKEY_kem_new_raw_key`,
// `EVP_PKEY_kem_new_raw_secret_key`, `EVP_PKEY_kem_new_raw_public_key`.
// The lengths are checked in all three functions. Additionally, the ciphertext
// length is checked in function pkey_kem_decapsulate in fipsmodule/evp/p_kem.c.
static int decapsulation_key_hash_check(ml_kem_params *params, const uint8_t *dk) {
  uint8_t dk_pke_hash_computed[KYBER_SYMBYTES] = {0};

  hash_h(dk_pke_hash_computed, &dk[params->indcpa_secret_key_bytes],
                               params->indcpa_public_key_bytes);
  const uint8_t *dk_pke_hash_expected = &dk[params->indcpa_secret_key_bytes +
                                            params->indcpa_public_key_bytes];

  return verify(dk_pke_hash_computed, dk_pke_hash_expected, KYBER_SYMBYTES);
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

  // FIPS 203. Section 3.3 Destruction of intermediate values.
  OPENSSL_cleanse(buf, sizeof(buf));
  OPENSSL_cleanse(kr, sizeof(kr));
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
* Returns 0 (success), or 1 when the encapsulation key check fails.
**************************************************/
int crypto_kem_enc(ml_kem_params *params,
                   uint8_t *ct,
                   uint8_t *ss,
                   const uint8_t *pk)
{
  if (encapsulation_key_modulus_check(params, pk) != 0) {
    return 1;
  }

  uint8_t coins[KYBER_SYMBYTES];
  RAND_bytes(coins, KYBER_SYMBYTES);
  crypto_kem_enc_derand(params, ct, ss, pk, coins);

  // FIPS 203. Section 3.3 Destruction of intermediate values.
  OPENSSL_cleanse(coins, sizeof(coins));
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
  if (decapsulation_key_hash_check(params, sk) != 0) {
    return 1;
  }

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

  // FIPS 203. Section 3.3 Destruction of intermediate values.
  OPENSSL_cleanse(buf, sizeof(buf));
  OPENSSL_cleanse(kr, sizeof(kr));
  OPENSSL_cleanse(cmp, sizeof(cmp));
  return 0;
}
