/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [FIPS204]
 *   FIPS 204 Module-Lattice-Based Digital Signature Standard
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/pubs/fips/204/final
 */

#ifndef MLD_H
#define MLD_H

/******************************************************************************
 *
 * Public API for mldsa-native
 *
 * This header defines the public API of a single build of mldsa-native.
 *
 * # Examples
 *
 * See [examples/basic] for examples of how to use this header.
 *
 * # Usage
 *
 * To use this header, configure the following options:
 *
 * - MLD_CONFIG_API_PARAMETER_SET [required]
 *
 *   The parameter set used for the build; 44, 65, or 87.
 *
 * - MLD_CONFIG_API_NAMESPACE_PREFIX [required]
 *
 *   The namespace prefix used for the build.
 *
 *   NOTE:
 *   For a multi-level build, you must include the 44/65/87 suffixes
 *   in MLD_CONFIG_API_NAMESPACE_PREFIX.
 *
 * - MLD_CONFIG_API_NO_SUPERCOP [optional]
 *
 *   By default, this header will also expose the mldsa-native API in the
 *   SUPERCOP naming convention crypto_sign_xxx. If you don't want/need this,
 *   set MLD_CONFIG_API_NO_SUPERCOP. You must set this for a multi-level build.
 *
 * - MLD_CONFIG_API_CONSTANTS_ONLY [optional]
 *
 *   If you don't want this header to expose any function declarations,
 *   but only constants for the sizes of key material, set
 *   MLD_CONFIG_API_CONSTANTS_ONLY. In this case, you don't need to set
 *   MLD_CONFIG_API_PARAMETER_SET or MLD_CONFIG_API_NAMESPACE_PREFIX,
 *   nor include a configuration.
 *
 * # Multi-level builds
 *
 * This header specifies a build of mldsa-native for a fixed security level.
 * If you need multiple builds, e.g. to build a library offering multiple
 * security levels, you need multiple instances of this header.
 *
 * NOTE: In this case, you must rename or #undef the MLD_H header guard
 *       prior to subsequent inclusions of this file.
 *
 ******************************************************************************/

/******************************* Key sizes ************************************/

/* Sizes of cryptographic material, per parameter set */
/* See mldsa/src/params.h for the arithmetic expressions giving rise to these */
/* check-magic: off */
#define MLDSA44_SECRETKEYBYTES 2560
#define MLDSA44_PUBLICKEYBYTES 1312
#define MLDSA44_BYTES 2420

#define MLDSA65_SECRETKEYBYTES 4032
#define MLDSA65_PUBLICKEYBYTES 1952
#define MLDSA65_BYTES 3309

#define MLDSA87_SECRETKEYBYTES 4896
#define MLDSA87_PUBLICKEYBYTES 2592
#define MLDSA87_BYTES 4627
/* check-magic: on */

/* Size of seed and randomness in bytes (level-independent) */
#define MLDSA_SEEDBYTES 32
#define MLDSA44_SEEDBYTES MLDSA_SEEDBYTES
#define MLDSA65_SEEDBYTES MLDSA_SEEDBYTES
#define MLDSA87_SEEDBYTES MLDSA_SEEDBYTES

/* Size of CRH output in bytes (level-independent) */
#define MLDSA_CRHBYTES 64
#define MLDSA44_CRHBYTES MLDSA_CRHBYTES
#define MLDSA65_CRHBYTES MLDSA_CRHBYTES
#define MLDSA87_CRHBYTES MLDSA_CRHBYTES

/* Size of TR output in bytes (level-independent) */
#define MLDSA_TRBYTES 64
#define MLDSA44_TRBYTES MLDSA_TRBYTES
#define MLDSA65_TRBYTES MLDSA_TRBYTES
#define MLDSA87_TRBYTES MLDSA_TRBYTES

/* Size of randomness for signing in bytes (level-independent) */
#define MLDSA_RNDBYTES 32
#define MLDSA44_RNDBYTES MLDSA_RNDBYTES
#define MLDSA65_RNDBYTES MLDSA_RNDBYTES
#define MLDSA87_RNDBYTES MLDSA_RNDBYTES

/* Sizes of cryptographic material, as a function of LVL=44,65,87 */
#define MLDSA_SECRETKEYBYTES_(LVL) MLDSA##LVL##_SECRETKEYBYTES
#define MLDSA_PUBLICKEYBYTES_(LVL) MLDSA##LVL##_PUBLICKEYBYTES
#define MLDSA_BYTES_(LVL) MLDSA##LVL##_BYTES
#define MLDSA_SECRETKEYBYTES(LVL) MLDSA_SECRETKEYBYTES_(LVL)
#define MLDSA_PUBLICKEYBYTES(LVL) MLDSA_PUBLICKEYBYTES_(LVL)
#define MLDSA_BYTES(LVL) MLDSA_BYTES_(LVL)

/****************************** Function API **********************************/

#if !defined(MLD_CONFIG_API_CONSTANTS_ONLY)

#if !defined(MLD_CONFIG_API_PARAMETER_SET)
#error MLD_CONFIG_API_PARAMETER_SET not defined
#endif
#if !defined(MLD_CONFIG_API_NAMESPACE_PREFIX)
#error MLD_CONFIG_API_NAMESPACE_PREFIX not defined
#endif

/* Validate parameter set */
#if MLD_CONFIG_API_PARAMETER_SET != 44 && \
    MLD_CONFIG_API_PARAMETER_SET != 65 && MLD_CONFIG_API_PARAMETER_SET != 87
#error MLD_CONFIG_API_PARAMETER_SET must be 44, 65, or 87
#endif

/* Derive namespacing macro */
#define MLD_API_CONCAT_(x, y) x##y
#define MLD_API_CONCAT(x, y) MLD_API_CONCAT_(x, y)
#define MLD_API_CONCAT_UNDERSCORE(x, y) MLD_API_CONCAT(MLD_API_CONCAT(x, _), y)
#define MLD_API_NAMESPACE(sym) \
  MLD_API_CONCAT_UNDERSCORE(MLD_CONFIG_API_NAMESPACE_PREFIX, sym)

#if defined(__GNUC__) || defined(clang)
#define MLD_API_MUST_CHECK_RETURN_VALUE __attribute__((warn_unused_result))
#else
#define MLD_API_MUST_CHECK_RETURN_VALUE
#endif

#include <stddef.h>
#include <stdint.h>

/*************************************************
 * Name:        crypto_sign_keypair_internal
 *
 * Description: Generates public and private key. Internal API.
 *              When MLD_CONFIG_KEYGEN_PCT is set, performs a Pairwise
 *              Consistency Test (PCT) as required by FIPS 140-3 IG.
 *
 * Arguments:
 *     - uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *           output public key
 *     - uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *           output private key
 *     - const uint8_t seed[MLDSA_SEEDBYTES]:
 *           input random seed
 *
 * Returns 0 (success) or -1 (PCT failure)
 *
 * Specification: Implements @[FIPS204 Algorithm 6 (ML-DSA.KeyGen_internal)]
 *
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(keypair_internal)(
    uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)],
    uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)],
    const uint8_t seed[MLDSA_SEEDBYTES]);

/*************************************************
 * Name:        crypto_sign_keypair
 *
 * Description: Generates public and private key.
 *              When MLD_CONFIG_KEYGEN_PCT is set, performs a Pairwise
 *              Consistency Test (PCT) as required by FIPS 140-3 IG.
 *
 * Arguments:
 *     - uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *           output public key
 *     - uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *           output private key
 *
 * Returns 0 (success) or -1 (PCT failure)
 *
 * Specification: Implements @[FIPS204 Algorithm 1 (ML-DSA.KeyGen)]
 *
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(keypair)(
    uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)],
    uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]);

/*************************************************
 * Name:        crypto_sign_signature_internal
 *
 * Description: Computes signature. Internal API.
 *
 * Arguments:
 *     - uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           output signature
 *     - size_t *siglen:     pointer to output length of signature
 *     - const uint8_t *m:   pointer to message to be signed
 *     - size_t mlen:        length of message
 *     - const uint8_t *pre: pointer to prefix string
 *     - size_t prelen:      length of prefix string
 *     - const uint8_t rnd[MLDSA_RNDBYTES]:
 *                           random seed
 *     - const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           bit-packed secret key
 *     - int externalmu:     indicates input message m is processed as mu
 *
 * Returns 0 (success) or -1 (indicating nonce exhaustion)
 *
 * If the returned value is -1, then the values of *sig and
 * *siglen should not be referenced.
 *
 * Reference: This code differs from the reference implementation
 *            in that it adds an explicit check for nonce exhaustion
 *            and can return -1 in that case.
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(signature_internal)(
    uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)], size_t *siglen,
    const uint8_t *m, size_t mlen, const uint8_t *pre, size_t prelen,
    const uint8_t rnd[MLDSA_RNDBYTES],
    const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)],
    int externalmu);

/*************************************************
 * Name:        crypto_sign_signature
 *
 * Description: Computes signature. This function implements the randomized
 *              variant of ML-DSA. If you require the deterministic variant,
 *              use crypto_sign_signature_internal directly.
 *
 * Arguments:
 *     - uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           output signature
 *     - size_t *siglen:     pointer to output length of signature
 *     - const uint8_t *m:   pointer to message to be signed
 *     - size_t mlen:        length of message
 *     - const uint8_t *ctx: pointer to context string.
 *                           May be NULL if ctxlen == 0.
 *     - size_t ctxlen:      length of context string.
 *                           Should be <= 255.
 *     - const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           bit-packed secret key
 *
 * Returns 0 (success) or -1 (context string too long OR nonce exhaustion)
 *
 * Specification: Implements @[FIPS204 Algorithm 2 (ML-DSA.Sign)]
 *
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(signature)(
    uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)], size_t *siglen,
    const uint8_t *m, size_t mlen, const uint8_t *ctx, size_t ctxlen,
    const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]);

/*************************************************
 * Name:        crypto_sign_signature_extmu
 *
 * Description: Computes signature.
 *
 * Arguments:
 *     - uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                       output signature
 *     - size_t *siglen: pointer to output length of signature
 *     - const uint8_t mu[MLDSA_CRHBYTES]:
 *                       input mu to be signed
 *     - const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                       bit-packed secret key
 *
 * Returns 0 (success) or -1 (context string too long OR nonce exhaustion)
 *
 * Specification: Implements @[FIPS204 Algorithm 2 (ML-DSA.Sign external mu
 *                variant)]
 *
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(signature_extmu)(
    uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)], size_t *siglen,
    const uint8_t mu[MLDSA_CRHBYTES],
    const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]);

/*************************************************
 * Name:        crypto_sign
 *
 * Description: Computes signature. This function implements the randomized
 *              variant of ML-DSA. If you require the deterministic variant,
 *              use crypto_sign_signature_internal directly.
 *
 * Arguments:
 *     - uint8_t *sm:        pointer to output signed message (allocated array
 *                           with MLDSA{44,65,87}_BYTES + mlen bytes), can be
 *                           equal to m
 *     - size_t *smlen:      pointer to output length of signed message
 *     - const uint8_t *m:   pointer to message to be signed
 *     - size_t mlen:        length of message
 *     - const uint8_t *ctx: pointer to context string
 *     - size_t ctxlen:      length of context string
 *     - const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           bit-packed secret key
 *
 * Returns 0 (success) or -1 (context string too long OR nonce exhausted)
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(sign)(
    uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen,
    const uint8_t *ctx, size_t ctxlen,
    const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]);

/*************************************************
 * Name:        crypto_sign_verify_internal
 *
 * Description: Verifies signature. Internal API.
 *
 * Arguments:
 *     - const uint8_t *sig: pointer to input signature
 *     - size_t siglen:      length of signature
 *     - const uint8_t *m:   pointer to message
 *     - size_t mlen:        length of message
 *     - const uint8_t *pre: pointer to prefix string
 *     - size_t prelen:      length of prefix string
 *     - const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           bit-packed public key
 *     - int externalmu:     indicates input message m is processed as mu
 *
 * Returns 0 if signature could be verified correctly and -1 otherwise
 *
 * Specification: Implements @[FIPS204 Algorithm 8 (ML-DSA.Verify_internal)]
 *
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(verify_internal)(
    const uint8_t *sig, size_t siglen, const uint8_t *m, size_t mlen,
    const uint8_t *pre, size_t prelen,
    const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)],
    int externalmu);

/*************************************************
 * Name:        crypto_sign_verify
 *
 * Description: Verifies signature.
 *
 * Arguments:
 *     - const uint8_t *sig: pointer to input signature
 *     - size_t siglen:      length of signature
 *     - const uint8_t *m:   pointer to message
 *     - size_t mlen:        length of message
 *     - const uint8_t *ctx: pointer to context string.
 *                           May be NULL if ctxlen == 0.
 *     - size_t ctxlen:      length of context string
 *     - const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           bit-packed public key
 *
 * Returns 0 if signature could be verified correctly and -1 otherwise
 *
 * Specification: Implements @[FIPS204 Algorithm 3 (ML-DSA.Verify)]
 *
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(verify)(
    const uint8_t *sig, size_t siglen, const uint8_t *m, size_t mlen,
    const uint8_t *ctx, size_t ctxlen,
    const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]);

/*************************************************
 * Name:        crypto_sign_verify_extmu
 *
 * Description: Verifies signature.
 *
 * Arguments:
 *     - const uint8_t *sig: pointer to input signature
 *     - size_t siglen:      length of signature
 *     - const uint8_t mu[MLDSA_CRHBYTES]:
 *                           input mu
 *     - const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           bit-packed public key
 *
 * Returns 0 if signature could be verified correctly and -1 otherwise
 *
 * Specification: Implements @[FIPS204 Algorithm 3 (ML-DSA.Verify external mu
 *                variant)]
 *
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(verify_extmu)(
    const uint8_t *sig, size_t siglen, const uint8_t mu[MLDSA_CRHBYTES],
    const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]);

/*************************************************
 * Name:        crypto_sign_open
 *
 * Description: Verify signed message.
 *
 * Arguments:
 *     - uint8_t *m:         pointer to output message (allocated array with
 *                           smlen bytes), can be equal to sm
 *     - size_t *mlen:       pointer to output length of message
 *     - const uint8_t *sm:  pointer to signed message
 *     - size_t smlen:       length of signed message
 *     - const uint8_t *ctx: pointer to context string
 *     - size_t ctxlen:      length of context string
 *     - const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           bit-packed public key
 *
 * Returns 0 if signed message could be verified correctly and -1 otherwise
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(open)(
    uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen,
    const uint8_t *ctx, size_t ctxlen,
    const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]);

/*************************************************
 * Hash algorithm constants for domain separation
 **************************************************/
#define MLD_PREHASH_NONE 0
#define MLD_PREHASH_SHA2_224 1
#define MLD_PREHASH_SHA2_256 2
#define MLD_PREHASH_SHA2_384 3
#define MLD_PREHASH_SHA2_512 4
#define MLD_PREHASH_SHA2_512_224 5
#define MLD_PREHASH_SHA2_512_256 6
#define MLD_PREHASH_SHA3_224 7
#define MLD_PREHASH_SHA3_256 8
#define MLD_PREHASH_SHA3_384 9
#define MLD_PREHASH_SHA3_512 10
#define MLD_PREHASH_SHAKE_128 11
#define MLD_PREHASH_SHAKE_256 12

/*************************************************
 * Name:        crypto_sign_signature_pre_hash_internal
 *
 * Description: FIPS 204: Algorithm 4 HashML-DSA.Sign.
 *              Computes signature with pre-hashed message.
 *
 * Arguments:
 *     - uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                               output signature
 *     - size_t *siglen:         pointer to output length of signature
 *     - const uint8_t *ph:      pointer to pre-hashed message
 *     - size_t phlen:           length of pre-hashed message
 *     - const uint8_t *ctx:     pointer to context string
 *     - size_t ctxlen:          length of context string
 *     - const uint8_t rnd[MLDSA_RNDBYTES]:
 *                               random seed
 *     - const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                               bit-packed secret key
 *     - int hashalg:            hash algorithm constant (one of MLD_PREHASH_*)
 *
 * Supported hash algorithm constants:
 *   MLD_PREHASH_SHA2_224, MLD_PREHASH_SHA2_256, MLD_PREHASH_SHA2_384,
 *   MLD_PREHASH_SHA2_512, MLD_PREHASH_SHA2_512_224, MLD_PREHASH_SHA2_512_256,
 *   MLD_PREHASH_SHA3_224, MLD_PREHASH_SHA3_256, MLD_PREHASH_SHA3_384,
 *   MLD_PREHASH_SHA3_512, MLD_PREHASH_SHAKE_128, MLD_PREHASH_SHAKE_256
 *
 * Warning: This is an unstable API that may change in the future. If you need
 * a stable API use crypto_sign_signature_pre_hash_shake256.
 *
 * Returns 0 (success) or -1 (context string too long OR invalid phlen OR nonce
 * exhaustion)
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(signature_pre_hash_internal)(
    uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)], size_t *siglen,
    const uint8_t *ph, size_t phlen, const uint8_t *ctx, size_t ctxlen,
    const uint8_t rnd[MLDSA_RNDBYTES],
    const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)],
    int hashalg);

/*************************************************
 * Name:        crypto_sign_verify_pre_hash_internal
 *
 * Description: FIPS 204: Algorithm 5 HashML-DSA.Verify.
 *              Verifies signature with pre-hashed message.
 *
 * Arguments:
 *     - const uint8_t *sig:     pointer to input signature
 *     - size_t siglen:          length of signature
 *     - const uint8_t *ph:      pointer to pre-hashed message
 *     - size_t phlen:           length of pre-hashed message
 *     - const uint8_t *ctx:     pointer to context string
 *     - size_t ctxlen:          length of context string
 *     - const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                               bit-packed public key
 *     - int hashalg:            hash algorithm constant (one of MLD_PREHASH_*)
 *
 * Supported hash algorithm constants:
 *   MLD_PREHASH_SHA2_224, MLD_PREHASH_SHA2_256, MLD_PREHASH_SHA2_384,
 *   MLD_PREHASH_SHA2_512, MLD_PREHASH_SHA2_512_224, MLD_PREHASH_SHA2_512_256,
 *   MLD_PREHASH_SHA3_224, MLD_PREHASH_SHA3_256, MLD_PREHASH_SHA3_384,
 *   MLD_PREHASH_SHA3_512, MLD_PREHASH_SHAKE_128, MLD_PREHASH_SHAKE_256
 *
 * Warning: This is an unstable API that may change in the future. If you need
 * a stable API use crypto_sign_verify_pre_hash_shake256.
 *
 * Returns 0 if signature could be verified correctly and -1 otherwise
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(verify_pre_hash_internal)(
    const uint8_t *sig, size_t siglen, const uint8_t *ph, size_t phlen,
    const uint8_t *ctx, size_t ctxlen,
    const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)],
    int hashalg);

/*************************************************
 * Name:        crypto_sign_signature_pre_hash_shake256
 *
 * Description: FIPS 204: Algorithm 4 HashML-DSA.Sign with SHAKE256.
 *              Computes signature with pre-hashed message using SHAKE256.
 *              This function computes the SHAKE256 hash of the message
 *              internally.
 *
 * Arguments:
 *     - uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           output signature
 *     - size_t *siglen:     pointer to output length of signature
 *     - const uint8_t *m:   pointer to message to be hashed and signed
 *     - size_t mlen:        length of message
 *     - const uint8_t *ctx: pointer to context string
 *     - size_t ctxlen:      length of context string
 *     - const uint8_t rnd[MLDSA_RNDBYTES]:
 *                           random seed
 *     - const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           bit-packed secret key
 *
 * Returns 0 (success) or -1 (context string too long OR nonce exhaustion)
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(signature_pre_hash_shake256)(
    uint8_t sig[MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)], size_t *siglen,
    const uint8_t *m, size_t mlen, const uint8_t *ctx, size_t ctxlen,
    const uint8_t rnd[MLDSA_RNDBYTES],
    const uint8_t sk[MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]);

/*************************************************
 * Name:        crypto_sign_verify_pre_hash_shake256
 *
 * Description: FIPS 204: Algorithm 5 HashML-DSA.Verify with SHAKE256.
 *              Verifies signature with pre-hashed message using SHAKE256.
 *              This function computes the SHAKE256 hash of the message
 *internally.
 *
 * Arguments:
 *     - const uint8_t *sig: pointer to input signature
 *     - size_t siglen:      length of signature
 *     - const uint8_t *m:   pointer to message to be hashed and verified
 *     - size_t mlen:        length of message
 *     - const uint8_t *ctx: pointer to context string
 *     - size_t ctxlen:      length of context string
 *     - const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]:
 *                           bit-packed public key
 *
 * Returns 0 if signature could be verified correctly and -1 otherwise
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
int MLD_API_NAMESPACE(verify_pre_hash_shake256)(
    const uint8_t *sig, size_t siglen, const uint8_t *m, size_t mlen,
    const uint8_t *ctx, size_t ctxlen,
    const uint8_t pk[MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)]);

/* Maximum formatted domain separation message length */
#define MLD_DOMAIN_SEPARATION_MAX_BYTES (2 + 255 + 11 + 64)

/*************************************************
 * Name:        mld_prepare_domain_separation_prefix
 *
 * Description: Prepares domain separation prefix for ML-DSA signing.
 *              For pure ML-DSA (hashalg == MLD_PREHASH_NONE):
 *                Format: 0x00 || ctxlen (1 byte) || ctx
 *              For HashML-DSA (hashalg != MLD_PREHASH_NONE):
 *                Format: 0x01 || ctxlen (1 byte) || ctx || oid (11 bytes) || ph
 *
 * Arguments:   - uint8_t prefix[MLD_DOMAIN_SEPARATION_MAX_BYTES]:
 *                output domain separation prefix buffer
 *              - const uint8_t *ph: pointer to pre-hashed message
 *                (ignored for pure ML-DSA)
 *              - size_t phlen: length of pre-hashed message
 *                (ignored for pure ML-DSA)
 *              - const uint8_t *ctx: pointer to context string (may be NULL)
 *              - size_t ctxlen: length of context string
 *              - int hashalg: hash algorithm constant
 *                (MLD_PREHASH_NONE for pure ML-DSA, or MLD_PREHASH_* for
 *                 HashML-DSA)
 *
 * Returns the total length of the formatted prefix, or 0 on error.
 *
 * This function is useful for building incremental signing APIs.
 *
 * Specification:
 * - For HashML-DSA (hashalg != MLD_PREHASH_NONE), implements
 *   @[FIPS204, Algorithm 4, L23]
 * - For Pure ML-DSA (hashalg == MLD_PREHASH_NONE), implements
 *    ```
 *       M' <- BytesToBits(IntegerToBytes(0, 1)
 *              || IntegerToBytes(|ctx|, 1)
 *              || ctx
 *    ```
 *    which is part of @[FIPS204, Algorithm 2 (ML-DSA.Sign), L10] and
 *    @[FIPS204, Algorithm 3 (ML-DSA.Verify), L5].
 *
 **************************************************/
MLD_API_MUST_CHECK_RETURN_VALUE
size_t MLD_API_NAMESPACE(prepare_domain_separation_prefix)(
    uint8_t prefix[MLD_DOMAIN_SEPARATION_MAX_BYTES], const uint8_t *ph,
    size_t phlen, const uint8_t *ctx, size_t ctxlen, int hashalg);

/****************************** SUPERCOP API *********************************/

#if !defined(MLD_CONFIG_API_NO_SUPERCOP)
/* Export API in SUPERCOP naming scheme CRYPTO_xxx / crypto_sign_xxx */
#define CRYPTO_SECRETKEYBYTES MLDSA_SECRETKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)
#define CRYPTO_PUBLICKEYBYTES MLDSA_PUBLICKEYBYTES(MLD_CONFIG_API_PARAMETER_SET)
#define CRYPTO_BYTES MLDSA_BYTES(MLD_CONFIG_API_PARAMETER_SET)

#define crypto_sign_keypair MLD_API_NAMESPACE(keypair)
#define crypto_sign_signature MLD_API_NAMESPACE(signature)
#define crypto_sign MLD_API_NAMESPACE(sign)
#define crypto_sign_verify MLD_API_NAMESPACE(verify)
#define crypto_sign_open MLD_API_NAMESPACE(open)

#else /* !MLD_CONFIG_API_NO_SUPERCOP */

/* If the SUPERCOP API is not needed, we can undefine the various helper macros
 * above. Otherwise, they are needed for lazy evaluation of crypto_sign_xxx. */
#undef MLD_API_CONCAT
#undef MLD_API_CONCAT_
#undef MLD_API_CONCAT_UNDERSCORE
#undef MLD_API_NAMESPACE
#undef MLD_API_MUST_CHECK_RETURN_VALUE

#endif /* MLD_CONFIG_API_NO_SUPERCOP */
#endif /* !MLD_CONFIG_API_CONSTANTS_ONLY */

#endif /* !MLD_H */
