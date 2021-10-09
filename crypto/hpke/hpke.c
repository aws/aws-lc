/* Copyright (c) 2020, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include <openssl/hpke.h>

#include <assert.h>
#include <string.h>

#include <openssl/aead.h>
#include <openssl/bytestring.h>
#include <openssl/curve25519.h>

#include "../internal.h"

#include <openssl/digest.h>
#include <openssl/err.h>
#include <openssl/evp_errors.h>
#include <openssl/hkdf.h>
#include <openssl/rand.h>
#include <openssl/sha.h>
#include <openssl/cpucycles.h>

//TEMPORARY!! WILL REMOVE AND CHANGE THE CODE IF WE WORK WITH AWS-LC/pq-crypto
//NOTE: RETURN VALUES FROM SIKE SUBROUTINES DIFFER FOR sike and pq-crypto DIRS !!!! 
//FOR NOW CHANGE THE CHECK TO if(sike_keypair(.., ..)<0), 
//PREVIOUS WAS if(!sike_keypair(.., ..))
#define sike_p434_r3_crypto_kem_keypair crypto_kem_keypair_SIKEp434
#define sike_p434_r3_crypto_kem_enc crypto_kem_enc_SIKEp434
#define sike_p434_r3_crypto_kem_dec crypto_kem_dec_SIKEp434


// This file implements draft-irtf-cfrg-hpke-08.
#if HPKE_VERSION_PQ == 0
#define MAX_SEED_LEN X25519_PRIVATE_KEY_LEN
#define MAX_SHARED_SECRET_LEN SHA256_DIGEST_LENGTH
#endif
#if HPKE_VERSION_PQ == 1
#define MAX_SEED_LEN SIKE_P434_R3_PRIVATE_KEY_BYTES
#define MAX_SHARED_SECRET_LEN SIKE_P434_R3_SHARED_SECRET_BYTES
#endif
#if HPKE_VERSION_PQ == 2
#define MAX_SEED_LEN X25519_PRIVATE_KEY_LEN // I dont use seed for SIKE
#define MAX_SHARED_SECRET_LEN SHA256_DIGEST_LENGTH + SIKE_P434_R3_SHARED_SECRET_BYTES
#endif
#if HPKE_VERSION_PQ == 3
#define MAX_SEED_LEN X25519_PRIVATE_KEY_LEN // I dont use seed for KYBER
#define MAX_SHARED_SECRET_LEN KYBER_SSBYTES
#endif
#if HPKE_VERSION_PQ == 4
#define MAX_SEED_LEN X25519_PRIVATE_KEY_LEN // I dont use seed for KYBER
#define MAX_SHARED_SECRET_LEN SHA256_DIGEST_LENGTH + KYBER_SSBYTES
#endif

//can keep like that or can also change -> can make another struct for a hpke_kem_st for hybrid specific ??? 
struct evp_hpke_kem_st {
  uint16_t id;
  size_t public_key_len;
  size_t private_key_len;
  size_t seed_len; //THIS SEED SHOULD BE REMOVED IMO

  //ADDING ECC+SIKE EXPRTIMENTAL

  size_t PQ_public_key_len;
  size_t PQ_private_key_len;
  size_t PQ_ciphertext_len;
  size_t PQ_shared_secret_len;

  
  int (*init_key)(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                  size_t priv_key_len);
  int (*generate_key)(EVP_HPKE_KEY *key);
  int (*encap_with_seed)(const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
                         size_t *out_shared_secret_len, uint8_t *out_enc,
                         size_t *out_enc_len, size_t max_enc,
                         const uint8_t *peer_public_key,
                         size_t peer_public_key_len, const uint8_t *seed,
                         size_t seed_len);
  int (*decap)(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
               size_t *out_shared_secret_len, const uint8_t *enc,
               size_t enc_len);
};

struct evp_hpke_kdf_st {
  uint16_t id;
  // We only support HKDF-based KDFs.
  const EVP_MD *(*hkdf_md_func)(void);
};

struct evp_hpke_aead_st {
  uint16_t id;
  const EVP_AEAD *(*aead_func)(void);
};


// Low-level labeled KDF functions.

static const char kHpkeVersionId[] = "HPKE-v1";

static int add_label_string(CBB *cbb, const char *label) {
  return CBB_add_bytes(cbb, (const uint8_t *)label, strlen(label));
}

static int hpke_labeled_extract(const EVP_MD *hkdf_md, uint8_t *out_key,
                                size_t *out_len, const uint8_t *salt,
                                size_t salt_len, const uint8_t *suite_id,
                                size_t suite_id_len, const char *label,
                                const uint8_t *ikm, size_t ikm_len) {
  // labeledIKM = concat("HPKE-v1", suite_id, label, IKM)
  CBB labeled_ikm;
  int ok = CBB_init(&labeled_ikm, 0) &&
           add_label_string(&labeled_ikm, kHpkeVersionId) &&
           CBB_add_bytes(&labeled_ikm, suite_id, suite_id_len) &&
           add_label_string(&labeled_ikm, label) &&
           CBB_add_bytes(&labeled_ikm, ikm, ikm_len) &&
           HKDF_extract(out_key, out_len, hkdf_md, CBB_data(&labeled_ikm),
                        CBB_len(&labeled_ikm), salt, salt_len);
  CBB_cleanup(&labeled_ikm);
  return ok;
}

static int hpke_labeled_expand(const EVP_MD *hkdf_md, uint8_t *out_key,
                               size_t out_len, const uint8_t *prk,
                               size_t prk_len, const uint8_t *suite_id,
                               size_t suite_id_len, const char *label,
                               const uint8_t *info, size_t info_len) {
  // labeledInfo = concat(I2OSP(L, 2), "HPKE-v1", suite_id, label, info)
  CBB labeled_info;
  int ok = CBB_init(&labeled_info, 0) &&
           CBB_add_u16(&labeled_info, out_len) &&
           add_label_string(&labeled_info, kHpkeVersionId) &&
           CBB_add_bytes(&labeled_info, suite_id, suite_id_len) &&
           add_label_string(&labeled_info, label) &&
           CBB_add_bytes(&labeled_info, info, info_len) &&
           HKDF_expand(out_key, out_len, hkdf_md, prk, prk_len,
                       CBB_data(&labeled_info), CBB_len(&labeled_info));
  CBB_cleanup(&labeled_info);
  return ok;
}


// KEM implementations.

// dhkem_extract_and_expand implements the ExtractAndExpand operation in the
// DHKEM construction. See section 4.1 of draft-irtf-cfrg-hpke-08.
static int dhkem_extract_and_expand(uint16_t kem_id, const EVP_MD *hkdf_md,
                                    uint8_t *out_key, size_t out_len,
                                    const uint8_t *dh, size_t dh_len,
                                    const uint8_t *kem_context,
                                    size_t kem_context_len) {
  // concat("KEM", I2OSP(kem_id, 2))
  uint8_t suite_id[5] = {'K', 'E', 'M', kem_id >> 8, kem_id & 0xff};
  uint8_t prk[EVP_MAX_MD_SIZE];
  size_t prk_len;
  return hpke_labeled_extract(hkdf_md, prk, &prk_len, NULL, 0, suite_id,
                              sizeof(suite_id), "eae_prk", dh, dh_len) &&
         hpke_labeled_expand(hkdf_md, out_key, out_len, prk, prk_len, suite_id,
                             sizeof(suite_id), "shared_secret", kem_context,
                             kem_context_len);
}



static int x25519_init_key(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                           size_t priv_key_len) {
  if (priv_key_len != X25519_PRIVATE_KEY_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  OPENSSL_memcpy(key->private_key, priv_key, priv_key_len);
  X25519_public_from_private(key->public_key, priv_key);
  return 1;
}


static int SIKE_init_key(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                           size_t priv_key_len) {


  if (priv_key_len != SIKE_P434_R3_PRIVATE_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  //OPENSSL_memcpy(key->private_key, priv_key, priv_key_len);
  unsigned long long cycles1, cycles2;
  cycles1=cpucycles();
  //sike_p434_r3_crypto_kem_keypair(key->public_key, (unsigned char *) key->private_key);
  crypto_kem_keypair_SIKEp434(key->public_key, (unsigned char *) key->private_key);
  //crypto_kem_keypair_SIKEp434(key->public_key, (unsigned char *) key->private_key);
  cycles2=cpucycles();
  printf("crypto_keypair %llu \n", (cycles2-cycles1));

  return 1;
}

static int Kyber_init_key(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                           size_t priv_key_len) {


  if (priv_key_len != KYBER_SECRETKEYBYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  crypto_kem_keypair_kyber(key->public_key, (unsigned char *) key->private_key);
  return 1;
}



static int Hybrid_init_key(EVP_HPKE_KEY *key, const uint8_t *priv_key,
                           size_t priv_key_len) {

   
  if (priv_key_len != key->kem->private_key_len + key->kem->PQ_private_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  //I want to change that to NOT PASSING THE SECRET KEY!!!
  OPENSSL_memcpy(key->private_key, priv_key, priv_key_len);
  X25519_public_from_private(key->public_key, priv_key);

  //OPENSSL_memcpy(key->private_key, priv_key, priv_key_len);
  switch(HPKE_VERSION_PQ){
    case 2:
          sike_p434_r3_crypto_kem_keypair(key->public_key + key->kem->public_key_len, (unsigned char *) key->private_key + key->kem->private_key_len);
    break;
    case 4:
    crypto_kem_keypair_kyber(key->public_key + key->kem->public_key_len, (unsigned char *) key->private_key + key->kem->private_key_len);
    break;
    default:
    //SHOULD COMPLETE
    break;
  }
  return 1;
}




static int x25519_generate_key(EVP_HPKE_KEY *key) {
    //Benchmarking vars
  X25519_keypair(key->public_key, key->private_key);
  return 1;
}


static int SIKE_generate_key(EVP_HPKE_KEY *key) {

  //unsigned long long cycles1, cycles2;
  //cycles1=cpucycles();
  sike_p434_r3_crypto_kem_keypair((unsigned char *)key->public_key , (unsigned char *)key->private_key);
  //cycles2=cpucycles();
  //printf("crypto_keypair %llu \n", (cycles2-cycles1));
  
  return 1;
}

static int Kyber_generate_key(EVP_HPKE_KEY *key) {

  crypto_kem_keypair_kyber((unsigned char *)key->public_key , (unsigned char *)key->private_key);
  
  return 1;
}



static int Hybrid_generate_key(EVP_HPKE_KEY *key) {
  X25519_keypair(key->public_key, key->private_key);
  switch(HPKE_VERSION_PQ){
    case 2:
          sike_p434_r3_crypto_kem_keypair((unsigned char *)key->public_key + key->kem->public_key_len, (unsigned char *) key->private_key + key->kem->private_key_len);
    break;
    case 4:
          crypto_kem_keypair_kyber((unsigned char *)key->public_key + key->kem->public_key_len, (unsigned char *) key->private_key + key->kem->private_key_len);
    break;
    default:
    //SHOULD COMPLETE
    break;
  }
  return 1;

}


static int x25519_encap_with_seed(
    const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
    size_t *out_shared_secret_len, uint8_t *out_enc, size_t *out_enc_len,
    size_t max_enc, const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *seed, size_t seed_len) {
  if (max_enc < X25519_PUBLIC_VALUE_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  if (seed_len != X25519_PRIVATE_KEY_LEN) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }
  X25519_public_from_private(out_enc, seed);

  uint8_t dh[X25519_SHARED_KEY_LEN];
  if (peer_public_key_len != X25519_PUBLIC_VALUE_LEN ||
      !X25519(dh, seed, peer_public_key)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  uint8_t kem_context[2 * X25519_PUBLIC_VALUE_LEN];
  OPENSSL_memcpy(kem_context, out_enc, X25519_PUBLIC_VALUE_LEN);
  OPENSSL_memcpy(kem_context + X25519_PUBLIC_VALUE_LEN, peer_public_key,
                 X25519_PUBLIC_VALUE_LEN);
  if (!dhkem_extract_and_expand(kem->id, EVP_sha256(), out_shared_secret,
                                SHA256_DIGEST_LENGTH, dh, sizeof(dh),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }

  *out_enc_len = X25519_PUBLIC_VALUE_LEN;
  *out_shared_secret_len = SHA256_DIGEST_LENGTH;
  return 1;
}






static int SIKE_encap_with_seed(
    const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
    size_t *out_shared_secret_len, uint8_t *out_enc, size_t *out_enc_len,
    size_t max_enc, const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *seed, size_t seed_len) {
      
  if (max_enc < SIKE_P434_R3_PUBLIC_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);

    return 0;
  }
  if (seed_len != SIKE_P434_R3_PRIVATE_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  uint8_t ss_sike[SIKE_P434_R3_SHARED_SECRET_BYTES];
  //uint8_t ct_sike[SIKE_P434_R3_CIPHERTEXT_BYTES];
  //if (peer_public_key_len != SIKE_P434_R3_PUBLIC_KEY_BYTES || sike_p434_r3_crypto_kem_enc(out_enc, ss_sike, peer_public_key)<0) {
  if (peer_public_key_len != SIKE_P434_R3_PUBLIC_KEY_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }
  //unsigned long long cycles1, cycles2;
  //cycles1=cpucycles();
  int sike_res=sike_p434_r3_crypto_kem_enc(out_enc, ss_sike, peer_public_key);
  //cycles2=cpucycles();
  //printf("crypto_enc %llu \n", (cycles2-cycles1));
  if (sike_res<0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }


  uint8_t kem_context[2 * SIKE_P434_R3_PUBLIC_KEY_BYTES];
  OPENSSL_memcpy(kem_context, out_enc, SIKE_P434_R3_PUBLIC_KEY_BYTES);
  OPENSSL_memcpy(kem_context + SIKE_P434_R3_PUBLIC_KEY_BYTES, peer_public_key,
                 SIKE_P434_R3_PUBLIC_KEY_BYTES);
  
  if (!dhkem_extract_and_expand(kem->id, EVP_sha256(), out_shared_secret,
                                SIKE_P434_R3_SHARED_SECRET_BYTES, ss_sike, sizeof(ss_sike),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }
  
  *out_enc_len = SIKE_P434_R3_CIPHERTEXT_BYTES;
  *out_shared_secret_len = SIKE_P434_R3_SHARED_SECRET_BYTES;   
  return 1;
}




static int Kyber_encap_with_seed(
    const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
    size_t *out_shared_secret_len, uint8_t *out_enc, size_t *out_enc_len,
    size_t max_enc, const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *seed, size_t seed_len) {
   

  if (max_enc < KYBER_CIPHERTEXTBYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }

  if (seed_len != KYBER_SECRETKEYBYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  uint8_t ss_kyber[KYBER_SSBYTES];
  if (peer_public_key_len != KYBER_PUBLICKEYBYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  int kyber_res=crypto_kem_enc_kyber(out_enc, ss_kyber, peer_public_key);

  if (kyber_res<0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  uint8_t kem_context[2 * KYBER_PUBLICKEYBYTES];
  OPENSSL_memcpy(kem_context, out_enc, KYBER_PUBLICKEYBYTES);
  OPENSSL_memcpy(kem_context + KYBER_PUBLICKEYBYTES, peer_public_key,
                 KYBER_PUBLICKEYBYTES);
  
  if (!dhkem_extract_and_expand(kem->id, EVP_sha256(), out_shared_secret,
                                KYBER_SSBYTES, ss_kyber, sizeof(ss_kyber),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }
  
  *out_enc_len = KYBER_CIPHERTEXTBYTES;
  *out_shared_secret_len = KYBER_SSBYTES;  
  return 1;
}


static int Hybrid_encap_with_seed(
    const EVP_HPKE_KEM *kem, uint8_t *out_shared_secret,
    size_t *out_shared_secret_len, uint8_t *out_enc, size_t *out_enc_len,
    size_t max_enc, const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *seed, size_t seed_len) { 

  if (max_enc < kem->public_key_len + kem->PQ_ciphertext_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }

  if (seed_len != kem->private_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_DECODE_ERROR);
    return 0;
  }

  //create the public key for ECC
  X25519_public_from_private(out_enc, seed);

  // create the shared secret from ECC
  uint8_t *hybrid_ss = malloc(sizeof(uint8_t)*(kem->public_key_len + kem->PQ_shared_secret_len));
  if (peer_public_key_len != kem->public_key_len + kem->PQ_public_key_len ||
      !X25519(hybrid_ss, seed, peer_public_key)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

//add space for the SIKE pk's to the kem_context

  uint8_t *kem_context = malloc(sizeof(uint8_t)*(2 * kem->public_key_len + 2 * kem->PQ_public_key_len));
  OPENSSL_memcpy(kem_context, out_enc, kem->public_key_len);
  OPENSSL_memcpy(kem_context + kem->public_key_len, peer_public_key,
                 kem->public_key_len);


  //uint8_t ct_sike[SIKE_P434_R3_CIPHERTEXT_BYTES];
  if (peer_public_key_len != kem->public_key_len + kem->PQ_public_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  int enc_res = 0;
  switch(HPKE_VERSION_PQ){
    case 2:
         enc_res = sike_p434_r3_crypto_kem_enc(out_enc + kem->public_key_len, hybrid_ss + kem->public_key_len, peer_public_key + kem->public_key_len);
    break;
    case 4:
         enc_res = crypto_kem_enc_kyber(out_enc + kem->public_key_len, hybrid_ss + kem->public_key_len, peer_public_key + kem->public_key_len);
    break;
    default:
    //SHOULD COMPLETE
    break;
  }

  if (enc_res<0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }
  
  OPENSSL_memcpy(kem_context + 2 * kem->public_key_len, out_enc + kem->public_key_len , kem->PQ_public_key_len);
  OPENSSL_memcpy(kem_context + 2 * kem->public_key_len + kem->PQ_public_key_len, peer_public_key + kem->public_key_len,
                 kem->PQ_public_key_len);

               
  
  if (!dhkem_extract_and_expand(kem->id, EVP_sha256(), out_shared_secret,
                                kem->public_key_len + kem->PQ_shared_secret_len, hybrid_ss, sizeof(hybrid_ss),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }

  *out_enc_len = kem->public_key_len + kem->PQ_ciphertext_len;
  *out_shared_secret_len = kem->public_key_len + kem->PQ_shared_secret_len;

  free(hybrid_ss);
  free(kem_context);
  return 1;
}




static int x25519_decap(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
                        size_t *out_shared_secret_len, const uint8_t *enc,
                        size_t enc_len) {
  uint8_t dh[X25519_SHARED_KEY_LEN];
  if (enc_len != X25519_PUBLIC_VALUE_LEN ||
      !X25519(dh, key->private_key, enc)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  uint8_t kem_context[2 * X25519_PUBLIC_VALUE_LEN];
  OPENSSL_memcpy(kem_context, enc, X25519_PUBLIC_VALUE_LEN);
  OPENSSL_memcpy(kem_context + X25519_PUBLIC_VALUE_LEN, key->public_key,
                 X25519_PUBLIC_VALUE_LEN);
  if (!dhkem_extract_and_expand(key->kem->id, EVP_sha256(), out_shared_secret,
                                SHA256_DIGEST_LENGTH, dh, sizeof(dh),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }

  *out_shared_secret_len = SHA256_DIGEST_LENGTH;
  return 1;
}




static int SIKE_decap(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
                        size_t *out_shared_secret_len, const uint8_t *enc,
                        size_t enc_len) {
  uint8_t ss_sike[SIKE_P434_R3_SHARED_SECRET_BYTES];
  if (enc_len != SIKE_P434_R3_CIPHERTEXT_BYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  //unsigned long long cycles1, cycles2;
  //cycles1=cpucycles();
  int sike_res=sike_p434_r3_crypto_kem_dec(ss_sike, enc, key->private_key);
  //cycles2=cpucycles();
  //printf("crypto_dec %llu \n\n\n", (cycles2-cycles1));

  //if (sike_p434_r3_crypto_kem_dec(ss_sike, enc, key->private_key)<0) {
  if (sike_res<0) {
     //printf("sike_p434_r3_crypto_kem_dec");
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }



  uint8_t kem_context[2 * SIKE_P434_R3_PUBLIC_KEY_BYTES];
  OPENSSL_memcpy(kem_context, enc, SIKE_P434_R3_PUBLIC_KEY_BYTES);
  OPENSSL_memcpy(kem_context + SIKE_P434_R3_PUBLIC_KEY_BYTES, key->public_key,
                 SIKE_P434_R3_PUBLIC_KEY_BYTES);
  if (!dhkem_extract_and_expand(key->kem->id, EVP_sha256(), out_shared_secret,
                                SIKE_P434_R3_SHARED_SECRET_BYTES, ss_sike, sizeof(ss_sike),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }

  *out_shared_secret_len = SIKE_P434_R3_SHARED_SECRET_BYTES;
  return 1;
}


static int Kyber_decap(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
                        size_t *out_shared_secret_len, const uint8_t *enc,
                        size_t enc_len) {
  uint8_t ss_kyber[KYBER_SSBYTES];
  if (enc_len != KYBER_CIPHERTEXTBYTES) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }
  int kyber_res=crypto_kem_dec_kyber(ss_kyber, enc, key->private_key);
  //cycles2=cpucycles();
  //printf("crypto_dec %llu \n\n\n", (cycles2-cycles1));

  //if (sike_p434_r3_crypto_kem_dec(ss_sike, enc, key->private_key)<0) {
  if (kyber_res<0) {
     printf("kyber_r3_crypto_kem_dec");
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }



  uint8_t kem_context[2 * KYBER_PUBLICKEYBYTES];
  OPENSSL_memcpy(kem_context, enc, KYBER_PUBLICKEYBYTES);
  OPENSSL_memcpy(kem_context + KYBER_PUBLICKEYBYTES, key->public_key,
                 KYBER_PUBLICKEYBYTES);
  if (!dhkem_extract_and_expand(key->kem->id, EVP_sha256(), out_shared_secret,
                                KYBER_SSBYTES, ss_kyber, sizeof(ss_kyber),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }

  *out_shared_secret_len = KYBER_SSBYTES;
  return 1;
}


static int Hybrid_decap(const EVP_HPKE_KEY *key, uint8_t *out_shared_secret,
                        size_t *out_shared_secret_len, const uint8_t *enc,
                        size_t enc_len) {


  uint8_t *hybrid_ss= malloc(sizeof(uint8_t)*(key->kem->public_key_len + key->kem->PQ_shared_secret_len));
  if (enc_len != key->kem->public_key_len + key->kem->PQ_ciphertext_len||
      !X25519(hybrid_ss, key->private_key, enc)) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }
  uint8_t *kem_context= malloc(sizeof(uint8_t)*(2 * key->kem->public_key_len + 2 * key->kem->PQ_public_key_len));
  OPENSSL_memcpy(kem_context, enc, key->kem->public_key_len);
  OPENSSL_memcpy(kem_context + key->kem->public_key_len, key->public_key,
                 key->kem->public_key_len);

  
  int enc_res = 0;
  switch(HPKE_VERSION_PQ){
    case 2:
         enc_res = sike_p434_r3_crypto_kem_dec(hybrid_ss + key->kem->public_key_len, enc + key->kem->public_key_len, key->private_key + key->kem->private_key_len);
    break;
    case 4:
          enc_res = crypto_kem_dec_kyber(hybrid_ss + key->kem->public_key_len, enc + key->kem->public_key_len, key->private_key + key->kem->private_key_len);
    break;
    default:
    //SHOULD COMPLETE
    break;
  }


  if (enc_res<0) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_PEER_KEY);
    return 0;
  }

  OPENSSL_memcpy(kem_context + 2 * key->kem->public_key_len, enc + key->kem->public_key_len, key->kem->PQ_public_key_len);
  OPENSSL_memcpy(kem_context + 2 * key->kem->public_key_len + key->kem->PQ_public_key_len, key->public_key + key->kem->public_key_len,
                 key->kem->PQ_public_key_len);
  if (!dhkem_extract_and_expand(key->kem->id, EVP_sha256(), out_shared_secret,
                                key->kem->public_key_len + key->kem->PQ_shared_secret_len, hybrid_ss, sizeof(hybrid_ss),
                                kem_context, sizeof(kem_context))) {
    return 0;
  }
/*
for (int i =  0 ; i < 2* X25519_PUBLIC_VALUE_LEN + 2* SIKE_P434_R3_PUBLIC_KEY_BYTES; i++)
  {
    printf("SIKE_ss_receiver %x \n", (kem_context)[i]);
  }
  */

  *out_shared_secret_len = SHA256_DIGEST_LENGTH + SIKE_P434_R3_SHARED_SECRET_BYTES;

  free(hybrid_ss);
  free(kem_context);
  return 1;
}


const EVP_HPKE_KEM *EVP_hpke_x25519_hkdf_sha256(void) {
  static const EVP_HPKE_KEM kKEM = {
      /*id=*/EVP_HPKE_DHKEM_X25519_HKDF_SHA256,
      /*public_key_len=*/X25519_PUBLIC_VALUE_LEN,
      /*private_key_len=*/X25519_PRIVATE_KEY_LEN,
      /*seed_len=*/X25519_PRIVATE_KEY_LEN, //REMOVE IT!!

      //USING NEW STRUCT FOR THE KEM -> WITH 2 MORE LENGTHS OF THE KEYS
      /*PQ_public_key_len=*/0,
      /*PQ_private_key_len=*/0,
      /*PQ_ciphertext_len=*/0,
      /*PQ_shared_secret_len=*/0,

      x25519_init_key,
      x25519_generate_key,
      x25519_encap_with_seed,
      x25519_decap,
  };
  return &kKEM;
}



//EXPERIMENTAL SIKE
const EVP_HPKE_KEM *EVP_hpke_SIKE_hkdf_sha256(void) {
  static const EVP_HPKE_KEM kKEM = {
      /*id=*/EVP_HPKE_PQKEM_SIKE_HKDF_SHA256,
      //USING NEW STRUCT FOR THE KEM -> WITH 2 MORE LENGTHS OF THE KEYS
      /*public_key_len=*/0,
      /*private_key_len=*/0,
      /*seed_len=*/SIKE_P434_R3_PRIVATE_KEY_BYTES, //REMOVE !!

      /*PQ_public_key_len=*/SIKE_P434_R3_PUBLIC_KEY_BYTES,
      /*PQ_private_key_len=*/SIKE_P434_R3_PRIVATE_KEY_BYTES, 
      /*PQ_ciphertext_len=*/SIKE_P434_R3_CIPHERTEXT_BYTES,
      /*PQ_shared_secret_len=*/SIKE_P434_R3_SHARED_SECRET_BYTES,

      SIKE_init_key,
      SIKE_generate_key,
      SIKE_encap_with_seed,
      SIKE_decap,
  };
  return &kKEM;
}

//EXPERIMENTAL HYBRID X25519+SIKE
const EVP_HPKE_KEM *EVP_hpke_x25519_SIKE_hkdf_sha256(void) {
  static const EVP_HPKE_KEM kKEM = {
      /*id=*/EVP_HPKE_KEM_X25519_SIKE_HKDF_SHA256, //not sure exactly what is that 
      /*public_key_len=*/X25519_PUBLIC_VALUE_LEN,
      /*private_key_len=*/X25519_PRIVATE_KEY_LEN,
      /*seed_len=*/X25519_PRIVATE_KEY_LEN, //REMOVE !!

      //USING NEW STRUCT FOR THE KEM -> WITH 2 MORE LENGTHS OF THE KEYS
      /*PQ_public_key_len=*/SIKE_P434_R3_PUBLIC_KEY_BYTES,
      /*PQ_private_key_len=*/SIKE_P434_R3_PRIVATE_KEY_BYTES,
      /*PQ_ciphertext_len=*/SIKE_P434_R3_CIPHERTEXT_BYTES,
      /*PQ_shared_secret_len=*/SIKE_P434_R3_SHARED_SECRET_BYTES,

      Hybrid_init_key,
      Hybrid_generate_key,
      Hybrid_encap_with_seed,
      Hybrid_decap,
  };
  return &kKEM;
}


//EXPERIMENTAL Kyber
const EVP_HPKE_KEM *EVP_hpke_KYBER_hkdf_sha256(void) {
  static const EVP_HPKE_KEM kKEM = {
      /*id=*/EVP_HPKE_PQKEM_KYBER_HKDF_SHA256,
      //USING NEW STRUCT FOR THE KEM -> WITH 2 MORE LENGTHS OF THE KEYS
      /*public_key_len=*/0,
      /*private_key_len=*/0,
      /*seed_len=*/KYBER_SECRETKEYBYTES, // REMOVE !!!!
      /*PQ_public_key_len=*/KYBER_PUBLICKEYBYTES,
      /*PQ_private_key_len=*/X25519_PRIVATE_KEY_LEN,


      /*PQ_ciphertext_len=*/KYBER_CIPHERTEXTBYTES,
      /*PQ_shared_secret_len=*/KYBER_SSBYTES,
      
      Kyber_init_key,
      Kyber_generate_key,
      Kyber_encap_with_seed,
      Kyber_decap,
  };
  return &kKEM;
}

//EXPERIMENTAL Kyber
const EVP_HPKE_KEM *EVP_hpke_x25519_KYBER_hkdf_sha256(void) {
  static const EVP_HPKE_KEM kKEM = {
      /*id=*/EVP_HPKE_PQKEM_KYBER_HKDF_SHA256,
      //USING NEW STRUCT FOR THE KEM -> WITH 2 MORE LENGTHS OF THE KEYS
      /*public_key_len=*/X25519_PUBLIC_VALUE_LEN,
      /*private_key_len=*/X25519_PRIVATE_KEY_LEN,
      /*seed_len=*/X25519_PRIVATE_KEY_LEN, // REMOVE !!!!
      
      /*PQ_public_key_len=*/KYBER_PUBLICKEYBYTES,
      /*PQ_private_key_len=*/KYBER_SECRETKEYBYTES,
      /*PQ_ciphertext_len=*/KYBER_CIPHERTEXTBYTES,
      /*PQ_shared_secret_len=*/KYBER_SSBYTES,
      
      Hybrid_init_key,
      Hybrid_generate_key,
      Hybrid_encap_with_seed,
      Hybrid_decap,
  };
  return &kKEM;
}





uint16_t EVP_HPKE_KEM_id(const EVP_HPKE_KEM *kem) { return kem->id; }

void EVP_HPKE_KEY_zero(EVP_HPKE_KEY *key) {
  OPENSSL_memset(key, 0, sizeof(EVP_HPKE_KEY));
}

void EVP_HPKE_KEY_cleanup(EVP_HPKE_KEY *key) {
  // Nothing to clean up for now, but we may introduce a cleanup process in the
  // future.
}

int EVP_HPKE_KEY_copy(EVP_HPKE_KEY *dst, const EVP_HPKE_KEY *src) {
  // For now, |EVP_HPKE_KEY| is trivially copyable.
  OPENSSL_memcpy(dst, src, sizeof(EVP_HPKE_KEY));
  return 1;
}

int EVP_HPKE_KEY_init(EVP_HPKE_KEY *key, const EVP_HPKE_KEM *kem,
                      const uint8_t *priv_key, size_t priv_key_len) {
  EVP_HPKE_KEY_zero(key);
  key->kem = kem;
  if (!kem->init_key(key, priv_key, priv_key_len)) {
    key->kem = NULL;
    return 0;
  }
  return 1;
}

int EVP_HPKE_KEY_generate(EVP_HPKE_KEY *key, const EVP_HPKE_KEM *kem) {
  EVP_HPKE_KEY_zero(key);
  key->kem = kem;
  if (!kem->generate_key(key)) {
    key->kem = NULL;
    return 0;
  }
  return 1;
}

const EVP_HPKE_KEM *EVP_HPKE_KEY_kem(const EVP_HPKE_KEY *key) {
  return key->kem;
}

int EVP_HPKE_KEY_public_key(const EVP_HPKE_KEY *key, uint8_t *out,
                            size_t *out_len, size_t max_out) {
  if (max_out < key->kem->public_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  OPENSSL_memcpy(out, key->public_key, key->kem->public_key_len + key->kem->PQ_public_key_len);
  *out_len = key->kem->public_key_len + key->kem->PQ_public_key_len;
  return 1;
}

int EVP_HPKE_KEY_private_key(const EVP_HPKE_KEY *key, uint8_t *out,
                            size_t *out_len, size_t max_out) {
  if (max_out < key->kem->private_key_len) {
    OPENSSL_PUT_ERROR(EVP, EVP_R_INVALID_BUFFER_SIZE);
    return 0;
  }
  OPENSSL_memcpy(out, key->private_key, key->kem->private_key_len);
  *out_len = key->kem->private_key_len;
  return 1;
}


// Supported KDFs and AEADs.

const EVP_HPKE_KDF *EVP_hpke_hkdf_sha256(void) {
  static const EVP_HPKE_KDF kKDF = {EVP_HPKE_HKDF_SHA256, &EVP_sha256};
  return &kKDF;
}

uint16_t EVP_HPKE_KDF_id(const EVP_HPKE_KDF *kdf) { return kdf->id; }

const EVP_HPKE_AEAD *EVP_hpke_aes_128_gcm(void) {
  static const EVP_HPKE_AEAD kAEAD = {EVP_HPKE_AES_128_GCM,
                                      &EVP_aead_aes_128_gcm};
  return &kAEAD;
}

const EVP_HPKE_AEAD *EVP_hpke_aes_256_gcm(void) {
  static const EVP_HPKE_AEAD kAEAD = {EVP_HPKE_AES_256_GCM,
                                      &EVP_aead_aes_256_gcm};
  return &kAEAD;
}

const EVP_HPKE_AEAD *EVP_hpke_chacha20_poly1305(void) {
  static const EVP_HPKE_AEAD kAEAD = {EVP_HPKE_CHACHA20_POLY1305,
                                      &EVP_aead_chacha20_poly1305};
  return &kAEAD;
}

uint16_t EVP_HPKE_AEAD_id(const EVP_HPKE_AEAD *aead) { return aead->id; }

const EVP_AEAD *EVP_HPKE_AEAD_aead(const EVP_HPKE_AEAD *aead) {
  return aead->aead_func();
}


// HPKE implementation.

// This is strlen("HPKE") + 3 * sizeof(uint16_t).
#define HPKE_SUITE_ID_LEN 10

// The suite_id for non-KEM pieces of HPKE is defined as concat("HPKE",
// I2OSP(kem_id, 2), I2OSP(kdf_id, 2), I2OSP(aead_id, 2)).
static int hpke_build_suite_id(const EVP_HPKE_CTX *ctx,
                               uint8_t out[HPKE_SUITE_ID_LEN]) {
  CBB cbb;
  int ret = CBB_init_fixed(&cbb, out, HPKE_SUITE_ID_LEN) &&
            add_label_string(&cbb, "HPKE") &&
            CBB_add_u16(&cbb, EVP_HPKE_DHKEM_X25519_HKDF_SHA256) &&
            CBB_add_u16(&cbb, ctx->kdf->id) &&
            CBB_add_u16(&cbb, ctx->aead->id);
  CBB_cleanup(&cbb);
  return ret;
}

#define HPKE_MODE_BASE 0

static int hpke_key_schedule(EVP_HPKE_CTX *ctx, const uint8_t *shared_secret,
                             size_t shared_secret_len, const uint8_t *info,
                             size_t info_len) {
  uint8_t suite_id[HPKE_SUITE_ID_LEN];
  if (!hpke_build_suite_id(ctx, suite_id)) {
    return 0;
  }

  // psk_id_hash = LabeledExtract("", "psk_id_hash", psk_id)
  // TODO(davidben): Precompute this value and store it with the EVP_HPKE_KDF.
  const EVP_MD *hkdf_md = ctx->kdf->hkdf_md_func();
  uint8_t psk_id_hash[EVP_MAX_MD_SIZE];
  size_t psk_id_hash_len;
  if (!hpke_labeled_extract(hkdf_md, psk_id_hash, &psk_id_hash_len, NULL, 0,
                            suite_id, sizeof(suite_id), "psk_id_hash", NULL,
                            0)) {
    return 0;
  }

  // info_hash = LabeledExtract("", "info_hash", info)
  uint8_t info_hash[EVP_MAX_MD_SIZE];
  size_t info_hash_len;
  if (!hpke_labeled_extract(hkdf_md, info_hash, &info_hash_len, NULL, 0,
                            suite_id, sizeof(suite_id), "info_hash", info,
                            info_len)) {
    return 0;
  }

  // key_schedule_context = concat(mode, psk_id_hash, info_hash)
  uint8_t context[sizeof(uint8_t) + 2 * EVP_MAX_MD_SIZE];
  size_t context_len;
  CBB context_cbb;
  if (!CBB_init_fixed(&context_cbb, context, sizeof(context)) ||
      !CBB_add_u8(&context_cbb, HPKE_MODE_BASE) ||
      !CBB_add_bytes(&context_cbb, psk_id_hash, psk_id_hash_len) ||
      !CBB_add_bytes(&context_cbb, info_hash, info_hash_len) ||
      !CBB_finish(&context_cbb, NULL, &context_len)) {
    return 0;
  }

  // secret = LabeledExtract(shared_secret, "secret", psk)
  uint8_t secret[EVP_MAX_MD_SIZE];
  size_t secret_len;
  if (!hpke_labeled_extract(hkdf_md, secret, &secret_len, shared_secret,
                            shared_secret_len, suite_id, sizeof(suite_id),
                            "secret", NULL, 0)) {
    return 0;
  }

  // key = LabeledExpand(secret, "key", key_schedule_context, Nk)
  const EVP_AEAD *aead = EVP_HPKE_AEAD_aead(ctx->aead);
  uint8_t key[EVP_AEAD_MAX_KEY_LENGTH];
  const size_t kKeyLen = EVP_AEAD_key_length(aead);
  if (!hpke_labeled_expand(hkdf_md, key, kKeyLen, secret, secret_len, suite_id,
                           sizeof(suite_id), "key", context, context_len) ||
      !EVP_AEAD_CTX_init(&ctx->aead_ctx, aead, key, kKeyLen,
                         EVP_AEAD_DEFAULT_TAG_LENGTH, NULL)) {
    return 0;
  }

  // base_nonce = LabeledExpand(secret, "base_nonce", key_schedule_context, Nn)
  if (!hpke_labeled_expand(hkdf_md, ctx->base_nonce,
                           EVP_AEAD_nonce_length(aead), secret, secret_len,
                           suite_id, sizeof(suite_id), "base_nonce", context,
                           context_len)) {
    return 0;
  }

  // exporter_secret = LabeledExpand(secret, "exp", key_schedule_context, Nh)
  if (!hpke_labeled_expand(hkdf_md, ctx->exporter_secret, EVP_MD_size(hkdf_md),
                           secret, secret_len, suite_id, sizeof(suite_id),
                           "exp", context, context_len)) {
    return 0;
  }

  return 1;
}

void EVP_HPKE_CTX_zero(EVP_HPKE_CTX *ctx) {
  OPENSSL_memset(ctx, 0, sizeof(EVP_HPKE_CTX));
  EVP_AEAD_CTX_zero(&ctx->aead_ctx);
}

void EVP_HPKE_CTX_cleanup(EVP_HPKE_CTX *ctx) {
  EVP_AEAD_CTX_cleanup(&ctx->aead_ctx);
}

int EVP_HPKE_CTX_setup_sender(EVP_HPKE_CTX *ctx, uint8_t *out_enc,
                              size_t *out_enc_len, size_t max_enc,
                              const EVP_HPKE_KEM *kem, const EVP_HPKE_KDF *kdf,
                              const EVP_HPKE_AEAD *aead,
                              const uint8_t *peer_public_key,
                              size_t peer_public_key_len, const uint8_t *info,
                              size_t info_len) {
                               
  uint8_t seed[MAX_SEED_LEN];
  RAND_bytes(seed, kem->seed_len);
  
      return EVP_HPKE_CTX_setup_sender_with_seed_for_testing(
      ctx, out_enc, out_enc_len, max_enc, kem, kdf, aead, peer_public_key,
      peer_public_key_len, info, info_len, seed, kem->seed_len);
}

int EVP_HPKE_CTX_setup_sender_with_seed_for_testing(
    EVP_HPKE_CTX *ctx, uint8_t *out_enc, size_t *out_enc_len, size_t max_enc,
    const EVP_HPKE_KEM *kem, const EVP_HPKE_KDF *kdf, const EVP_HPKE_AEAD *aead,
    const uint8_t *peer_public_key, size_t peer_public_key_len,
    const uint8_t *info, size_t info_len, const uint8_t *seed,
    size_t seed_len) {
  EVP_HPKE_CTX_zero(ctx);
  
  ctx->is_sender = 1;
  ctx->kdf = kdf;
  ctx->aead = aead;

   uint8_t *shared_secret;
   size_t shared_secret_len;
  

  switch (HPKE_VERSION_PQ)
  {
  case 0:
    //classical crytpo ECC
    shared_secret=malloc(sizeof(uint8_t)*X25519_SHARED_KEY_LEN);
   
    break;
  case 1:
  //PQ crypto experimental SIKE
    shared_secret=malloc(sizeof(uint8_t)*SIKE_P434_R3_SHARED_SECRET_BYTES);
   
    break;
  case 2: 
  case 4: 
  //Hybrid crypto experimental ECC+SIKE
    shared_secret=malloc(sizeof(uint8_t)*(kem->PQ_shared_secret_len + kem->public_key_len));
   
    break;
    case 3:
  //Hybrid crypto experimental ECC+SIKE
    shared_secret=malloc(sizeof(uint8_t)*(KYBER_SSBYTES));
   
    break;
  
  default:
  ///SHOULD ADD HERE!!!
    break;
  }

  if (!kem->encap_with_seed(kem, shared_secret, &shared_secret_len, out_enc,
                            out_enc_len, max_enc, peer_public_key,
                            peer_public_key_len, seed, seed_len) ||
      !hpke_key_schedule(ctx, shared_secret, shared_secret_len, info,
                         info_len)) {               
    EVP_HPKE_CTX_cleanup(ctx);
    return 0;
  }
  return 1;
}

int EVP_HPKE_CTX_setup_recipient(EVP_HPKE_CTX *ctx, const EVP_HPKE_KEY *key,
                                 const EVP_HPKE_KDF *kdf,
                                 const EVP_HPKE_AEAD *aead, const uint8_t *enc,
                                 size_t enc_len, const uint8_t *info,
                                 size_t info_len) {
  EVP_HPKE_CTX_zero(ctx);
  ctx->is_sender = 0;
  ctx->kdf = kdf;
  ctx->aead = aead;
  uint8_t shared_secret[MAX_SHARED_SECRET_LEN];
  size_t shared_secret_len;
  if (!key->kem->decap(key, shared_secret, &shared_secret_len, enc, enc_len) ||
      !hpke_key_schedule(ctx, shared_secret, sizeof(shared_secret), info,
                         info_len)) {
    EVP_HPKE_CTX_cleanup(ctx);
    return 0;
  }
  return 1;
}

static void hpke_nonce(const EVP_HPKE_CTX *ctx, uint8_t *out_nonce,
                       size_t nonce_len) {
  assert(nonce_len >= 8);

  // Write padded big-endian bytes of |ctx->seq| to |out_nonce|.
  OPENSSL_memset(out_nonce, 0, nonce_len);
  uint64_t seq_copy = ctx->seq;
  for (size_t i = 0; i < 8; i++) {
    out_nonce[nonce_len - i - 1] = seq_copy & 0xff;
    seq_copy >>= 8;
  }

  // XOR the encoded sequence with the |ctx->base_nonce|.
  for (size_t i = 0; i < nonce_len; i++) {
    out_nonce[i] ^= ctx->base_nonce[i];
  }
}

int EVP_HPKE_CTX_open(EVP_HPKE_CTX *ctx, uint8_t *out, size_t *out_len,
                      size_t max_out_len, const uint8_t *in, size_t in_len,
                      const uint8_t *ad, size_t ad_len) {
  if (ctx->is_sender) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
    return 0;
  }
  if (ctx->seq == UINT64_MAX) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_OVERFLOW);
    return 0;
  }

  uint8_t nonce[EVP_AEAD_MAX_NONCE_LENGTH];
  const size_t nonce_len = EVP_AEAD_nonce_length(ctx->aead_ctx.aead);
  hpke_nonce(ctx, nonce, nonce_len);

  if (!EVP_AEAD_CTX_open(&ctx->aead_ctx, out, out_len, max_out_len, nonce,
                         nonce_len, in, in_len, ad, ad_len)) {
    return 0;
  }
  ctx->seq++;
  return 1;
}

int EVP_HPKE_CTX_seal(EVP_HPKE_CTX *ctx, uint8_t *out, size_t *out_len,
                      size_t max_out_len, const uint8_t *in, size_t in_len,
                      const uint8_t *ad, size_t ad_len) {
  if (!ctx->is_sender) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_SHOULD_NOT_HAVE_BEEN_CALLED);
    return 0;
  }
  if (ctx->seq == UINT64_MAX) {
    OPENSSL_PUT_ERROR(EVP, ERR_R_OVERFLOW);
    return 0;
  }

  uint8_t nonce[EVP_AEAD_MAX_NONCE_LENGTH];
  const size_t nonce_len = EVP_AEAD_nonce_length(ctx->aead_ctx.aead);
  hpke_nonce(ctx, nonce, nonce_len);

  if (!EVP_AEAD_CTX_seal(&ctx->aead_ctx, out, out_len, max_out_len, nonce,
                         nonce_len, in, in_len, ad, ad_len)) {
    return 0;
  }
  ctx->seq++;
  return 1;
}

int EVP_HPKE_CTX_export(const EVP_HPKE_CTX *ctx, uint8_t *out,
                        size_t secret_len, const uint8_t *context,
                        size_t context_len) {
  uint8_t suite_id[HPKE_SUITE_ID_LEN];
  if (!hpke_build_suite_id(ctx, suite_id)) {
    return 0;
  }
  const EVP_MD *hkdf_md = ctx->kdf->hkdf_md_func();
  if (!hpke_labeled_expand(hkdf_md, out, secret_len, ctx->exporter_secret,
                           EVP_MD_size(hkdf_md), suite_id, sizeof(suite_id),
                           "sec", context, context_len)) {
    return 0;
  }
  return 1;
}

size_t EVP_HPKE_CTX_max_overhead(const EVP_HPKE_CTX *ctx) {
  assert(ctx->is_sender);
  return EVP_AEAD_max_overhead(EVP_AEAD_CTX_aead(&ctx->aead_ctx));
}

const EVP_HPKE_AEAD *EVP_HPKE_CTX_aead(const EVP_HPKE_CTX *ctx) {
  return ctx->aead;
}

const EVP_HPKE_KDF *EVP_HPKE_CTX_kdf(const EVP_HPKE_CTX *ctx) {
  return ctx->kdf;
}
