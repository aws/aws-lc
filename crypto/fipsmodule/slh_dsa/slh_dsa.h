// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef OPENSSL_HEADER_CRYPTO_FIPSMODULE_SLH_DSA_H
#define OPENSSL_HEADER_CRYPTO_FIPSMODULE_SLH_DSA_H

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif

// SLH-DSA (FIPS 205), SHAKE parameter sets.
//
// This is the FIPS module's interface to SLH-DSA. See README.md.
//
// All functions return 1 on success (or a valid signature) and 0 otherwise.
// Every buffer is passed with its length. Key, seed, signature and digest
// buffers must be exactly the size given by the corresponding |slh_dsa_*_bytes|
// function. Output buffers are left unmodified on failure and must not overlap
// any input.

#define SLHDSA_SHAKE_128S_PUBLIC_KEY_BYTES 32
#define SLHDSA_SHAKE_128S_PRIVATE_KEY_BYTES 64
#define SLHDSA_SHAKE_128S_SIGNATURE_BYTES 7856
#define SLHDSA_SHAKE_128S_SEED_BYTES 48

#define SLHDSA_SHAKE_192S_PUBLIC_KEY_BYTES 48
#define SLHDSA_SHAKE_192S_PRIVATE_KEY_BYTES 96
#define SLHDSA_SHAKE_192S_SIGNATURE_BYTES 16224
#define SLHDSA_SHAKE_192S_SEED_BYTES 72

#define SLHDSA_SHAKE_256S_PUBLIC_KEY_BYTES 64
#define SLHDSA_SHAKE_256S_PRIVATE_KEY_BYTES 128
#define SLHDSA_SHAKE_256S_SIGNATURE_BYTES 29792
#define SLHDSA_SHAKE_256S_SEED_BYTES 96

// SLHDSA_MAX_SIGNATURE_BYTES is the largest signature of any supported
// parameter set.
#define SLHDSA_MAX_SIGNATURE_BYTES SLHDSA_SHAKE_256S_SIGNATURE_BYTES

// SLHDSA_MAX_CONTEXT_BYTES is the maximum length of a context string.
#define SLHDSA_MAX_CONTEXT_BYTES 255

// SLHDSA_MAX_PREHASH_DIGEST_BYTES is the largest digest signed by HashSLH-DSA.
#define SLHDSA_MAX_PREHASH_DIGEST_BYTES 64

// SLHDSA_PARAMS identifies a parameter set (FIPS 205, Table 2).
typedef struct slh_dsa_params_st SLHDSA_PARAMS;

OPENSSL_EXPORT const SLHDSA_PARAMS *slh_dsa_shake_128s_params(void);
OPENSSL_EXPORT const SLHDSA_PARAMS *slh_dsa_shake_192s_params(void);
OPENSSL_EXPORT const SLHDSA_PARAMS *slh_dsa_shake_256s_params(void);

// Sizes in bytes. The private key is SK.seed || SK.prf || PK.seed || PK.root
// and the public key is PK.seed || PK.root (FIPS 205, Section 9.1). The seed
// is SK.seed || SK.prf || PK.seed, the input to |slh_dsa_keypair_internal|.
OPENSSL_EXPORT size_t slh_dsa_public_key_bytes(const SLHDSA_PARAMS *params);
OPENSSL_EXPORT size_t slh_dsa_private_key_bytes(const SLHDSA_PARAMS *params);
OPENSSL_EXPORT size_t slh_dsa_signature_bytes(const SLHDSA_PARAMS *params);
OPENSSL_EXPORT size_t slh_dsa_seed_bytes(const SLHDSA_PARAMS *params);


// Key generation.

// slh_dsa_keypair generates a key pair (FIPS 205, Algorithm 21).
OPENSSL_EXPORT int slh_dsa_keypair(const SLHDSA_PARAMS *params,
                                   uint8_t *out_public_key,
                                   size_t public_key_len,
                                   uint8_t *out_private_key,
                                   size_t private_key_len);

// slh_dsa_check_private_key checks that PK.root in |private_key| is the root
// of the top XMSS tree of SK.seed and PK.seed. This regenerates the key pair
// to assure possession of the private key (FIPS 205, Sections 3.1 and 9.1),
// and costs about as much as key generation. It returns one if the key is
// consistent and zero otherwise.
OPENSSL_EXPORT int slh_dsa_check_private_key(const SLHDSA_PARAMS *params,
                                             const uint8_t *private_key,
                                             size_t private_key_len);

// slh_dsa_public_from_private writes the public key embedded in
// |private_key| to |out_public_key|. It first checks |private_key| with
// |slh_dsa_check_private_key|, and returns zero if that fails.
OPENSSL_EXPORT int slh_dsa_public_from_private(const SLHDSA_PARAMS *params,
                                               uint8_t *out_public_key,
                                               size_t public_key_len,
                                               const uint8_t *private_key,
                                               size_t private_key_len);


// Pure SLH-DSA.
//
// These sign and verify |message| itself. |context| is the context string,
// at most |SLHDSA_MAX_CONTEXT_BYTES| long. It may be NULL if |context_len| is
// zero. Signing is hedged: it uses fresh randomness from the RBG.

// slh_dsa_sign implements slh_sign (FIPS 205, Algorithm 22).
OPENSSL_EXPORT int slh_dsa_sign(const SLHDSA_PARAMS *params, uint8_t *out_sig,
                                size_t sig_len, const uint8_t *private_key,
                                size_t private_key_len, const uint8_t *message,
                                size_t message_len, const uint8_t *context,
                                size_t context_len);

// slh_dsa_verify implements slh_verify (FIPS 205, Algorithm 24).
OPENSSL_EXPORT int slh_dsa_verify(const SLHDSA_PARAMS *params,
                                  const uint8_t *sig, size_t sig_len,
                                  const uint8_t *public_key,
                                  size_t public_key_len, const uint8_t *message,
                                  size_t message_len, const uint8_t *context,
                                  size_t context_len);


// HashSLH-DSA.
//
// These sign and verify the digest of a message (FIPS 205, Section 10.2.2).
// |hash_nid| is the pre-hash function, |NID_shake128| or |NID_shake256|, which
// produce SHAKE128(M, 256) and SHAKE256(M, 512). SHAKE128 is only appropriate
// for parameter sets in security category 1 (FIPS 205, Section 10.2.2), so it
// is supported only with SLH-DSA-SHAKE-128s. The |_digest| variants take the
// digest instead of the message. Context strings and randomness are as for
// pure SLH-DSA.

// slh_dsa_prehash_digest_bytes returns the length of the digest for the
// pre-hash function |hash_nid| with |params|, or zero if the combination is not
// supported.
OPENSSL_EXPORT size_t slh_dsa_prehash_digest_bytes(const SLHDSA_PARAMS *params,
                                                   int hash_nid);

// slh_dsa_prehash_sign implements hash_slh_sign (FIPS 205, Algorithm 23).
OPENSSL_EXPORT int slh_dsa_prehash_sign(
    const SLHDSA_PARAMS *params, uint8_t *out_sig, size_t sig_len,
    const uint8_t *private_key, size_t private_key_len, int hash_nid,
    const uint8_t *message, size_t message_len, const uint8_t *context,
    size_t context_len);

OPENSSL_EXPORT int slh_dsa_prehash_sign_digest(
    const SLHDSA_PARAMS *params, uint8_t *out_sig, size_t sig_len,
    const uint8_t *private_key, size_t private_key_len, int hash_nid,
    const uint8_t *digest, size_t digest_len, const uint8_t *context,
    size_t context_len);

// slh_dsa_prehash_verify implements hash_slh_verify (FIPS 205, Algorithm 25).
OPENSSL_EXPORT int slh_dsa_prehash_verify(
    const SLHDSA_PARAMS *params, const uint8_t *sig, size_t sig_len,
    const uint8_t *public_key, size_t public_key_len, int hash_nid,
    const uint8_t *message, size_t message_len, const uint8_t *context,
    size_t context_len);

OPENSSL_EXPORT int slh_dsa_prehash_verify_digest(
    const SLHDSA_PARAMS *params, const uint8_t *sig, size_t sig_len,
    const uint8_t *public_key, size_t public_key_len, int hash_nid,
    const uint8_t *digest, size_t digest_len, const uint8_t *context,
    size_t context_len);


// Internal functions.
//
// These implement FIPS 205, Section 9, and take all randomness as explicit
// inputs. They exist only for tests and the ACVP modulewrapper. FIPS 205,
// Section 9 says they should not be made available to applications, because
// the random values for key generation and signing shall be generated by the
// module. They are therefore not part of the public API, are not reachable
// through EVP, and are not approved services.

// slh_dsa_keypair_internal implements slh_keygen_internal (FIPS 205,
// Algorithm 18). |seed| is SK.seed || SK.prf || PK.seed.
OPENSSL_EXPORT int slh_dsa_keypair_internal(
    const SLHDSA_PARAMS *params, uint8_t *out_public_key, size_t public_key_len,
    uint8_t *out_private_key, size_t private_key_len, const uint8_t *seed,
    size_t seed_len);

// slh_dsa_sign_internal implements slh_sign_internal (FIPS 205, Algorithm 19)
// on the message M = |pre| || |message|. |pre| lets a caller supply the
// domain-separation prefix of Algorithms 22 and 23 without copying the
// message. It may be NULL if |pre_len| is zero. |addrnd| is the n-byte
// additional randomness for the hedged variant. NULL, with |addrnd_len|
// zero, selects the deterministic variant, which uses PK.seed in its place.
OPENSSL_EXPORT int slh_dsa_sign_internal(
    const SLHDSA_PARAMS *params, uint8_t *out_sig, size_t sig_len,
    const uint8_t *private_key, size_t private_key_len, const uint8_t *pre,
    size_t pre_len, const uint8_t *message, size_t message_len,
    const uint8_t *addrnd, size_t addrnd_len);

// slh_dsa_verify_internal implements slh_verify_internal (FIPS 205,
// Algorithm 20) on the message M = |pre| || |message|.
OPENSSL_EXPORT int slh_dsa_verify_internal(
    const SLHDSA_PARAMS *params, const uint8_t *sig, size_t sig_len,
    const uint8_t *public_key, size_t public_key_len, const uint8_t *pre,
    size_t pre_len, const uint8_t *message, size_t message_len);

#if defined(__cplusplus)
}  // extern C
#endif

#endif  // OPENSSL_HEADER_CRYPTO_FIPSMODULE_SLH_DSA_H
