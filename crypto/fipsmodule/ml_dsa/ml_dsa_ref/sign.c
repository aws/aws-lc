#include "sign.h"
#include <stdint.h>
#include "../../../internal.h"
#include "openssl/rand.h"
#include "packing.h"
#include "params.h"
#include "poly.h"
#include "polyvec.h"

#if defined(AWSLC_FIPS)

/*************************************************
 * [FIPS 140-3 IG](https://csrc.nist.gov/csrc/media/Projects/cryptographic-module-validation-program/documents/fips%20140-3/FIPS%20140-3%20IG.pdf)
 *
 * VE10.35.02: Pair-wise Consistency Test (PCT) for DSA keypairs
 *
 * Purpose: Validates that a generated public/private key pair can correctly
 * sign and verify data. Test performs signature generation using the private
 * key (sk), followed by signature verification using the public key (pk).
 * Returns 1 if the signature was successfully verified, 0 if it cannot.
 *
 * Note: FIPS 204 requires that public/private key pairs are to be used only for
 * the calculation and/of verification of digital signatures.
**************************************************/
static int ml_dsa_keypair_pct(ml_dsa_params *params,
                              uint8_t *pk,
                              uint8_t *sk) {
  uint8_t message[1] = {0};
  uint8_t signature[MLDSA87_SIGNATURE_BYTES];
  int ret = ml_dsa_sign(params, signature, &params->bytes, message, sizeof(message), NULL, 0, sk);
  if (ret < 0) {
    return 0;
  }
  if (boringssl_fips_break_test("MLDSA_PWCT")) {
    message[0] = ~message[0];
  }
  return ml_dsa_verify(params, signature, params->bytes, message, sizeof(message), NULL, 0, pk) == 0;
}
#endif

/*************************************************
 * Name:        ml_dsa_keypair_internal
 *
 * Description: FIPS 204: Algorithm 6 ML-DSA.KeyGen_internal.
 *              Generates public and private key. Internal API.
 *
 * Arguments:   - ml_dsa_params: parameter struct
 *              - uint8_t *pk: pointer to output public key (allocated
 *                             array of CRYPTO_PUBLICKEYBYTES bytes)
 *              - uint8_t *sk: pointer to output private key (allocated
 *                             array of CRYPTO_SECRETKEYBYTES bytes)
 *              - const uint8_t *rnd: pointer to random seed
 *
 * Returns 0 (success)
 **************************************************/
int ml_dsa_keypair_internal(ml_dsa_params *params,
                            uint8_t *pk,
                            uint8_t *sk,
                            const uint8_t *seed) {
  uint8_t seedbuf[2 * ML_DSA_SEEDBYTES + ML_DSA_CRHBYTES];
  uint8_t tr[ML_DSA_TRBYTES];
  const uint8_t *rho, *rhoprime, *key;
  polyvecl mat[ML_DSA_K_MAX];
  polyvecl s1 = {{{{0}}}};
  polyvecl s1hat;
  polyveck s2, t1, t0;

  OPENSSL_memcpy(seedbuf, seed, ML_DSA_SEEDBYTES);
  seedbuf[ML_DSA_SEEDBYTES + 0] = params->k;
  seedbuf[ML_DSA_SEEDBYTES + 1] = params->l;
  SHAKE256(seedbuf, ML_DSA_SEEDBYTES + 2, seedbuf, 2 * ML_DSA_SEEDBYTES + ML_DSA_CRHBYTES);
  rho = seedbuf;
  rhoprime = rho + ML_DSA_SEEDBYTES;
  key = rhoprime + ML_DSA_CRHBYTES;

  /* FIPS 204: line 3 Expand matrix */
  ml_dsa_polyvec_matrix_expand(params, mat, rho);

  /* FIPS 204: line 4 Sample short vectors s1 and s2 */
  ml_dsa_polyvecl_uniform_eta(params, &s1, rhoprime, 0);
  ml_dsa_polyveck_uniform_eta(params, &s2, rhoprime, params->l);

  /* FIPS 204: line 5 Matrix-vector multiplication */
  s1hat = s1;
  ml_dsa_polyvecl_ntt(params, &s1hat);
  ml_dsa_polyvec_matrix_pointwise_montgomery(params, &t1, mat, &s1hat);
  ml_dsa_polyveck_reduce(params, &t1);
  ml_dsa_polyveck_invntt_tomont(params, &t1);

  /* Add error vector s2 */
  ml_dsa_polyveck_add(params, &t1, &t1, &s2);

  /* FIPS 204: line 6 Extract t1 and write public key */
  ml_dsa_polyveck_caddq(params, &t1);
  ml_dsa_polyveck_power2round(params, &t1, &t0, &t1);
  /* FIPS 204: line 8 */
  ml_dsa_pack_pk(params, pk, rho, &t1);

  /* FIPS 204: line 9 Compute H(rho, t1) and line 10 write secret key */
  SHAKE256(pk, params->public_key_bytes, tr, ML_DSA_TRBYTES);
  ml_dsa_pack_sk(params, sk, rho, tr, key, &t0, &s1, &s2);

  /* FIPS 204. Section 3.6.3 Destruction of intermediate values. */
  OPENSSL_cleanse(seedbuf, sizeof(seedbuf));
  OPENSSL_cleanse(tr, sizeof(tr));
  OPENSSL_cleanse(mat, sizeof(mat));
  OPENSSL_cleanse(&s1, sizeof(s1));
  OPENSSL_cleanse(&s1hat, sizeof(s1hat));
  OPENSSL_cleanse(&s2, sizeof(s2));
  OPENSSL_cleanse(&t1, sizeof(t1));
  OPENSSL_cleanse(&t0, sizeof(t0));

#if defined(AWSLC_FIPS)
  // Abort in case of PCT failure.
  if (!ml_dsa_keypair_pct(params, pk, sk)) {
    AWS_LC_FIPS_failure("ML-DSA keygen PCT failed");
  }
#endif
  return 0;
}

/*************************************************
* Name:        ml_dsa_keypair
*
* Description: FIPS 204: Algorithm 1 ML-DSA.KeyGen
*              Generates public and private key.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t *pk: pointer to output public key (allocated
*                             array of CRYPTO_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key (allocated
*                             array of CRYPTO_SECRETKEYBYTES bytes)
*
* Returns 0 (success) -1 on failure
**************************************************/
int ml_dsa_keypair(ml_dsa_params *params, uint8_t *pk, uint8_t *sk) {
  uint8_t seed[ML_DSA_SEEDBYTES];
  if (!RAND_bytes(seed, ML_DSA_SEEDBYTES)) {
    return -1;
  }
  ml_dsa_keypair_internal(params, pk, sk, seed);
  OPENSSL_cleanse(seed, sizeof(seed));
  return 0;
}

/*************************************************
* Name:        ml_dsa_sign_internal
*
* Description: FIPS 204: Algorithm 7 ML-DSA.Sign_internal.
*              Computes signature. Internal API.
*
* Arguments:   - ml_dsa_params:   parameter struct
*              - uint8_t *sig:    pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen:  pointer to output length of signature
*              - uint8_t *m:      pointer to message to be signed
*              - size_t mlen:     length of message
*              - uint8_t *pre:    pointer to prefix string
*              - size_t prelen:   length of prefix string
*              - uint8_t *rnd:    pointer to random seed
*              - uint8_t *sk:     pointer to bit-packed secret key
*              - int external_mu: indicates input message m is to be processed as mu
*
* Returns 0 (success) or -1 (context string too long)
**************************************************/
int ml_dsa_sign_internal(ml_dsa_params *params,
                         uint8_t *sig,
                         size_t *siglen,
                         const uint8_t *m,
                         size_t mlen,
                         const uint8_t *pre,
                         size_t prelen,
                         const uint8_t *rnd,
                         const uint8_t *sk,
                         int external_mu)
{
  unsigned int n;
  uint8_t seedbuf[2*ML_DSA_SEEDBYTES + ML_DSA_TRBYTES + 2*ML_DSA_CRHBYTES];
  uint8_t *rho, *tr, *key, *mu, *rhoprime;
  uint16_t nonce = 0;
  polyvecl mat[ML_DSA_K_MAX], s1, y, z;
  polyveck t0, s2, w1, w0, h;
  ml_dsa_poly cp;
  KECCAK1600_CTX state;

  rho = seedbuf;
  tr = rho + ML_DSA_SEEDBYTES;
  key = tr + ML_DSA_TRBYTES;
  mu = key + ML_DSA_SEEDBYTES;
  rhoprime = mu + ML_DSA_CRHBYTES;
  /* FIPS 204: line 1 */
  ml_dsa_unpack_sk(params, rho, tr, key, &t0, &s1, &s2, sk);

  /* FIPS 204: line 6 Compute mu = CRH(tr, pre, msg) */
  // This differs from FIPS 204 line 6 that performs mu = CRH(tr, M') and the
  // processing of M' in the external function. However, as M' = (pre, msg),
  // mu = CRH(tr, M') = CRH(tr, pre, msg).
  if (!external_mu) {
    //constuct mu = h(tr | m') when not in prehash mode
    SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
    SHA3_Update(&state, tr, ML_DSA_TRBYTES);
    SHA3_Update(&state, pre, prelen);
    SHA3_Update(&state, m, mlen);
    SHAKE_Final(mu, &state, ML_DSA_CRHBYTES);
  }
  else {
    OPENSSL_memcpy(mu, m, mlen);
  }

  /* FIPS 204: line 7 Compute rhoprime = CRH(key, rnd, mu) */
  SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
  SHAKE_Absorb(&state, key, ML_DSA_SEEDBYTES);
  SHAKE_Absorb(&state, rnd, ML_DSA_RNDBYTES);
  SHAKE_Absorb(&state, mu, ML_DSA_CRHBYTES);
  SHAKE_Final(rhoprime, &state, ML_DSA_CRHBYTES);

  /* FIPS 204: line 5 Expand matrix and transform vectors */
  ml_dsa_polyvec_matrix_expand(params, mat, rho);
  ml_dsa_polyvecl_ntt(params, &s1);
  ml_dsa_polyveck_ntt(params, &s2);
  ml_dsa_polyveck_ntt(params, &t0);

rej:
  /* FIPS 204: line 11 Sample intermediate vector y */
  ml_dsa_polyvecl_uniform_gamma1(params, &y, rhoprime, nonce++);

  /* FIPS 204: line 12 Matrix-vector multiplication */
  z = y;
  ml_dsa_polyvecl_ntt(params, &z);
  ml_dsa_polyvec_matrix_pointwise_montgomery(params, &w1, mat, &z);
  ml_dsa_polyveck_reduce(params, &w1);
  ml_dsa_polyveck_invntt_tomont(params, &w1);

  /* FIPS 204: line 13 - 14 Decompose w and call the random oracle */
  ml_dsa_polyveck_caddq(params, &w1);
  ml_dsa_polyveck_decompose(params, &w1, &w0, &w1);
  ml_dsa_polyveck_pack_w1(params, sig, &w1);

  SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
  SHAKE_Absorb(&state, mu, ML_DSA_CRHBYTES);
  SHAKE_Absorb(&state, sig, params->k * params->poly_w1_packed_bytes);
  SHAKE_Final(sig, &state, params->c_tilde_bytes);
  ml_dsa_poly_challenge(params, &cp, sig);
  ml_dsa_poly_ntt(&cp);

  /* FIPS 204: line 20 Compute z, reject if it reveals secret */
  ml_dsa_polyvecl_pointwise_poly_montgomery(params, &z, &cp, &s1);
  ml_dsa_polyvecl_invntt_tomont(params, &z);
  ml_dsa_polyvecl_add(params, &z, &z, &y);
  ml_dsa_polyvecl_reduce(params, &z);
  if(ml_dsa_polyvecl_chknorm(params, &z, params->gamma1 - params->beta)) {
    goto rej;
  }

  /* FIPS 204: line 21 Check that subtracting cs2 does not change high bits of w and low bits
   * do not reveal secret information */
  ml_dsa_polyveck_pointwise_poly_montgomery(params, &h, &cp, &s2);
  ml_dsa_polyveck_invntt_tomont(params, &h);
  ml_dsa_polyveck_sub(params, &w0, &w0, &h);
  ml_dsa_polyveck_reduce(params, &w0);
  if(ml_dsa_polyveck_chknorm(params, &w0, params->gamma2 - params->beta)) {
    goto rej;
  }

  /* FIPS 204: line 25 */
  ml_dsa_polyveck_pointwise_poly_montgomery(params, &h, &cp, &t0);
  ml_dsa_polyveck_invntt_tomont(params, &h);
  ml_dsa_polyveck_reduce(params, &h);
  if(ml_dsa_polyveck_chknorm(params, &h, params->gamma2)) {
    goto rej;
  }

  /* FIPS 204: line 26 Compute signer's hint */
  ml_dsa_polyveck_add(params, &w0, &w0, &h);
  n = ml_dsa_polyveck_make_hint(params, &h, &w0, &w1);
  if(n > params->omega) {
    goto rej;
  }

  /* FIPS 204: line 33 Write signature */
  ml_dsa_pack_sig(params, sig, sig, &z, &h);
  *siglen = params->bytes;

  /* FIPS 204. Section 3.6.3 Destruction of intermediate values. */
  OPENSSL_cleanse(seedbuf, sizeof(seedbuf));
  OPENSSL_cleanse(&nonce, sizeof(nonce));
  OPENSSL_cleanse(mat, sizeof(mat));
  OPENSSL_cleanse(&s1, sizeof(s1));
  OPENSSL_cleanse(&y, sizeof(y));
  OPENSSL_cleanse(&z, sizeof(z));
  OPENSSL_cleanse(&t0, sizeof(t0));
  OPENSSL_cleanse(&s2, sizeof(s2));
  OPENSSL_cleanse(&w1, sizeof(w1));
  OPENSSL_cleanse(&w0, sizeof(w0));
  OPENSSL_cleanse(&h, sizeof(h));
  OPENSSL_cleanse(&cp, sizeof(cp));
  OPENSSL_cleanse(&state, sizeof(state));
  return 0;
}

/*************************************************
* Name:        ml_dsa_sign
*
* Description: FIPS 204: Algorithm 2 ML-DSA.Sign.
*              Computes signature in hedged mode.
*
* Arguments:   - uint8_t *sig:   pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen: pointer to output length of signature
*              - uint8_t *m:     pointer to message to be signed
*              - size_t mlen:    length of message
*              - uint8_t *ctx:   pointer to contex string
*              - size_t ctxlen:  length of contex string
*              - uint8_t *sk:    pointer to bit-packed secret key
*
* Returns 0 (success) or -1 (context string too long)
**************************************************/
int ml_dsa_sign(ml_dsa_params *params,
                uint8_t *sig,
                size_t *siglen,
                const uint8_t *m,
                size_t mlen,
                const uint8_t *ctx,
                size_t ctxlen,
                const uint8_t *sk)
{
  uint8_t pre[257];
  uint8_t rnd[ML_DSA_RNDBYTES];

  if(ctxlen > 255) {
    return -1;
  }
  /* Prepare pre = (0, ctxlen, ctx) */
  pre[0] = 0;
  pre[1] = ctxlen;
  OPENSSL_memcpy(pre + 2 , ctx, ctxlen);

  if (!RAND_bytes(rnd, ML_DSA_RNDBYTES)) {
    return -1;
  }
  ml_dsa_sign_internal(params, sig, siglen, m, mlen, pre, 2 + ctxlen, rnd, sk, 0);

  /* FIPS 204. Section 3.6.3 Destruction of intermediate values. */
  OPENSSL_cleanse(pre, sizeof(pre));
  OPENSSL_cleanse(rnd, sizeof(rnd));
  return 0;
}

/*************************************************
* Name:        ml_dsa_extmu_sign
*
* Description: FIPS 204: Algorithm 2 ML-DSA.Sign external mu variant.
*              Computes signature in hedged mode.
*
* Arguments:   - uint8_t *sig:   pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen: pointer to output length of signature
*              - uint8_t *mu:    pointer to input mu to be signed
*              - size_t mulen:   length of mu
*              - uint8_t *sk:    pointer to bit-packed secret key
*
* Returns 0 (success) or -1 (context string too long)
**************************************************/
int ml_dsa_extmu_sign(ml_dsa_params *params,
                      uint8_t *sig,
                      size_t *siglen,
                      const uint8_t *mu,
                      size_t mulen,
                      const uint8_t *sk)
{
  uint8_t rnd[ML_DSA_RNDBYTES];

  if (!RAND_bytes(rnd, ML_DSA_RNDBYTES)) {
    return -1;
  }
  ml_dsa_sign_internal(params, sig, siglen, mu, mulen, NULL, 0, rnd, sk, 1);

  /* FIPS 204. Section 3.6.3 Destruction of intermediate values. */
  OPENSSL_cleanse(rnd, sizeof(rnd));
  return 0;
}

/*************************************************
* Name:        ml_dsa_sign_message
*
* Description: Compute signed message.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t *sm: pointer to output signed message (allocated
*                             array with CRYPTO_BYTES + mlen bytes),
*                             can be equal to m
*              - size_t *smlen: pointer to output length of signed
*                               message
*              - const uint8_t *m: pointer to message to be signed
*              - size_t mlen: length of message
*              - const uint8_t *ctx: pointer to context string
*              - size_t ctxlen: length of context string
*              - const uint8_t *sk: pointer to bit-packed secret key
*
* Returns 0 (success) or -1 (context string too long)
**************************************************/
int ml_dsa_sign_message(ml_dsa_params *params,
                        uint8_t *sm,
                        size_t *smlen,
                        const uint8_t *m,
                        size_t mlen,
                        const uint8_t *ctx,
                        size_t ctxlen,
                        const uint8_t *sk)
{
  int ret;
  size_t i;

  for(i = 0; i < mlen; ++i) {
    sm[params->bytes + mlen - 1 - i] = m[mlen - 1 - i];
  }
  ret = ml_dsa_sign(params, sm, smlen, sm + params->bytes, mlen, ctx, ctxlen, sk);
  *smlen += mlen;
  return ret;
}

/*************************************************
* Name:        ml_dsa_verify_internal
*
* Description: FIPS 204: Algorithm 8 ML-DSA.Verify_internal.
*              Verifies signature. Internal API.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t *m: pointer to input signature
*              - size_t siglen: length of signature
*              - const uint8_t *m: pointer to message
*              - size_t mlen: length of message
*              - const uint8_t *pre: pointer to prefix string
*              - size_t prelen: length of prefix string
*              - const uint8_t *pk: pointer to bit-packed public key
*              - int external_mu: indicates input message m is to be processed as mu
*
* Returns 0 if signature could be verified correctly and -1 otherwise
**************************************************/
int ml_dsa_verify_internal(ml_dsa_params *params,
                           const uint8_t *sig,
                           size_t siglen,
                           const uint8_t *m,
                           size_t mlen,
                           const uint8_t *pre,
                           size_t prelen,
                           const uint8_t *pk,
                           int external_mu)
{
  unsigned int i;
  uint8_t buf[ML_DSA_K_MAX*ML_DSA_POLYW1_PACKEDBYTES_MAX];
  uint8_t rho[ML_DSA_SEEDBYTES];
  uint8_t mu[ML_DSA_CRHBYTES];
  uint8_t tr[ML_DSA_TRBYTES];
  uint8_t c[ML_DSA_C_TILDE_BYTES_MAX];
  uint8_t c2[ML_DSA_C_TILDE_BYTES_MAX];
  ml_dsa_poly cp;
  polyvecl mat[ML_DSA_K_MAX], z;
  polyveck t1, w1, h;
  KECCAK1600_CTX state;

  if(siglen != params->bytes) {
    return -1;
  }
  /* FIPS 204: line 1 */
  ml_dsa_unpack_pk(params, rho, &t1, pk);
  /* FIPS 204: line 2 */
  if(ml_dsa_unpack_sig(params, c, &z, &h, sig)) {
    return -1;
  }
  if(ml_dsa_polyvecl_chknorm(params, &z, params->gamma1 - params->beta)) {
    return -1;
  }

  if(!external_mu) {
    /* FIPS 204: line 6 Compute tr */
    SHAKE256(pk, params->public_key_bytes, tr, ML_DSA_TRBYTES);
    /* FIPS 204: line 7 Compute mu = H(BytesToBits(tr) || M', 64) */
    // Like crypto_sign_signature_internal, the processing of M' is performed
    // here, as opposed to within the external function.
    SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
    SHA3_Update(&state, tr, ML_DSA_TRBYTES);
    SHA3_Update(&state, pre, prelen);
    SHA3_Update(&state, m, mlen);
    SHAKE_Final(mu, &state, ML_DSA_CRHBYTES);
  }
  else {
    OPENSSL_memcpy(mu, m, mlen);
  }

  /* FIPS 204: line 9 Matrix-vector multiplication; compute Az - c2^dt1 */
  ml_dsa_poly_challenge(params, &cp, c);
  ml_dsa_polyvec_matrix_expand(params, mat, rho);

  ml_dsa_polyvecl_ntt(params, &z);
  ml_dsa_polyvec_matrix_pointwise_montgomery(params, &w1, mat, &z);

  ml_dsa_poly_ntt(&cp);
  ml_dsa_polyveck_shiftl(params, &t1);
  ml_dsa_polyveck_ntt(params, &t1);
  ml_dsa_polyveck_pointwise_poly_montgomery(params, &t1, &cp, &t1);

  ml_dsa_polyveck_sub(params, &w1, &w1, &t1);
  ml_dsa_polyveck_reduce(params, &w1);
  ml_dsa_polyveck_invntt_tomont(params, &w1);

  /* FIPS 204: line 10 Reconstruct w1 */
  ml_dsa_polyveck_caddq(params, &w1);
  ml_dsa_polyveck_use_hint(params, &w1, &w1, &h);
  ml_dsa_polyveck_pack_w1(params, buf, &w1);

  /* FIPS 204: line 12 Call random oracle and verify challenge */
  SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
  SHAKE_Absorb(&state, mu, ML_DSA_CRHBYTES);
  SHAKE_Absorb(&state, buf, params->k * params->poly_w1_packed_bytes);
  SHAKE_Final(c2, &state, params->c_tilde_bytes);

  for(i = 0; i < params->c_tilde_bytes; ++i) {
    if(c[i] != c2[i]) {
      return -1;
    }
  }
  /* FIPS 204. Section 3.6.3 Destruction of intermediate values. */
  OPENSSL_cleanse(buf, sizeof(buf));
  OPENSSL_cleanse(rho, sizeof(rho));
  OPENSSL_cleanse(mu, sizeof(mu));
  OPENSSL_cleanse(tr, sizeof(tr));
  OPENSSL_cleanse(c, sizeof(c));
  OPENSSL_cleanse(c2, sizeof(c2));
  OPENSSL_cleanse(&cp, sizeof(cp));
  OPENSSL_cleanse(mat, sizeof(mat));
  OPENSSL_cleanse(&z, sizeof(z));
  OPENSSL_cleanse(&t1, sizeof(t1));
  OPENSSL_cleanse(&w1, sizeof(w1));
  OPENSSL_cleanse(&h, sizeof(h));
  OPENSSL_cleanse(&state, sizeof(state));
  return 0;
}

/*************************************************
* Name:        ml_dsa_verify
*
* Description: FIPS 204: Algorithm 3 ML-DSA.Verify.
*              Verifies signature.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t *m: pointer to input signature
*              - size_t siglen: length of signature
*              - const uint8_t *m: pointer to message
*              - size_t mlen: length of message
*              - const uint8_t *ctx: pointer to context string
*              - size_t ctxlen: length of context string
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signature could be verified correctly and -1 otherwise
**************************************************/
int ml_dsa_verify(ml_dsa_params *params,
                  const uint8_t *sig,
                  size_t siglen,
                  const uint8_t *m,
                  size_t mlen,
                  const uint8_t *ctx,
                  size_t ctxlen,
                  const uint8_t *pk)
{
  uint8_t pre[257];

  if(ctxlen > 255) {
    return -1;
  }

  pre[0] = 0;
  pre[1] = ctxlen;
  OPENSSL_memcpy(pre + 2 , ctx, ctxlen);
  return ml_dsa_verify_internal(params, sig, siglen, m, mlen, pre, 2 + ctxlen, pk, 0);
}

/*************************************************
* Name:        ml_dsa_verify_message
*
* Description: Verify signed message.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t *m: pointer to output message (allocated
*                            array with smlen bytes), can be equal to sm
*              - size_t *mlen: pointer to output length of message
*              - const uint8_t *sm: pointer to signed message
*              - size_t smlen: length of signed message
*              - const uint8_t *ctx: pointer to context tring
*              - size_t ctxlen: length of context string
*              - const uint8_t *pk: pointer to bit-packed public key
*
* Returns 0 if signed message could be verified correctly and -1 otherwise
**************************************************/
int ml_dsa_verify_message(ml_dsa_params *params,
                          uint8_t *m,
                          size_t *mlen,
                          const uint8_t *sm,
                          size_t smlen,
                          const uint8_t *ctx,
                          size_t ctxlen,
                          const uint8_t *pk)
{

  if(smlen < params->bytes) {
    goto badsig;
  }

  *mlen = smlen - params->bytes;
  if(ml_dsa_verify(params,sm, params->bytes, sm + params->bytes, *mlen, ctx, ctxlen, pk)) {
    goto badsig;
  }
  else {
    /* All good, copy msg, return 0 */
    for(size_t i = 0; i < *mlen; ++i) {
      m[i] = sm[params->bytes + i];
    }
    return 0;
  }

badsig:
  /* Signature verification failed */
  *mlen = 0;
  for(size_t i = 0; i < smlen; ++i) {
    m[i] = 0;
  }

  return -1;
}
