#include "sign.h"
#include <stdint.h>
#include "../../internal.h"
#include "openssl/rand.h"
#include "packing.h"
#include "params.h"
#include "poly.h"
#include "polyvec.h"


/*************************************************
 * Name:        crypto_sign_keypair_internal
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
int crypto_sign_keypair_internal(ml_dsa_params *params,
                                 uint8_t *pk,
                                 uint8_t *sk,
                                 const uint8_t *seed) {
  uint8_t seedbuf[2*SEEDBYTES + CRHBYTES];
  uint8_t tr[TRBYTES];
  const uint8_t *rho, *rhoprime, *key;
  polyvecl mat[DILITHIUM_K_MAX];
  polyvecl s1, s1hat;
  polyveck s2, t1, t0;

  OPENSSL_memcpy(seedbuf, seed, SEEDBYTES);
  seedbuf[SEEDBYTES+0] = params->k;
  seedbuf[SEEDBYTES+1] = params->l;
  SHAKE256(seedbuf, SEEDBYTES + 2, seedbuf, 2 * SEEDBYTES + CRHBYTES);
  rho = seedbuf;
  rhoprime = rho + SEEDBYTES;
  key = rhoprime + CRHBYTES;

  /* FIPS 204: line 3 Expand matrix */
  polyvec_matrix_expand(params, mat, rho);

  /* FIPS 204: line 4 Sample short vectors s1 and s2 */
  polyvecl_uniform_eta(params, &s1, rhoprime, 0);
  polyveck_uniform_eta(params, &s2, rhoprime, params->l);

  /* FIPS 204: line 5 Matrix-vector multiplication */
  s1hat = s1;
  polyvecl_ntt(params, &s1hat);
  polyvec_matrix_pointwise_montgomery(params, &t1, mat, &s1hat);
  polyveck_reduce(params, &t1);
  polyveck_invntt_tomont(params, &t1);

  /* Add error vector s2 */
  polyveck_add(params, &t1, &t1, &s2);

  /* FIPS 204: line 6 Extract t1 and write public key */
  polyveck_caddq(params, &t1);
  polyveck_power2round(params, &t1, &t0, &t1);
  /* FIPS 204: line 8 */
  pack_pk(params, pk, rho, &t1);

  /* FIPS 204: line 9 Compute H(rho, t1) and line 10 write secret key */
  SHAKE256(pk, params->public_key_bytes, tr, TRBYTES);
  pack_sk(params, sk, rho, tr, key, &t0, &s1, &s2);

  /* FIPS 204. Section 3.6.3 Destruction of intermediate values. */
  OPENSSL_cleanse(seedbuf, sizeof(seedbuf));
  OPENSSL_cleanse(tr, sizeof(tr));
  OPENSSL_cleanse(mat, sizeof(mat));
  OPENSSL_cleanse(&s1, sizeof(s1));
  OPENSSL_cleanse(&s1hat, sizeof(s1hat));
  OPENSSL_cleanse(&s2, sizeof(s2));
  OPENSSL_cleanse(&t1, sizeof(t1));
  OPENSSL_cleanse(&t0, sizeof(t0));
  return 0;
}

/*************************************************
* Name:        crypto_sign_keypair
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
int crypto_sign_keypair(ml_dsa_params *params, uint8_t *pk, uint8_t *sk) {
  uint8_t seed[SEEDBYTES];
  if (!RAND_bytes(seed, SEEDBYTES)) {
    return -1;
  }
  crypto_sign_keypair_internal(params, pk, sk, seed);
  OPENSSL_cleanse(seed, sizeof(seed));
  return 0;
}

/*************************************************
* Name:        crypto_sign_signature_internal
*
* Description: FIPS 204: Algorithm 7 ML-DSA.Sign_internal.
*              Computes signature. Internal API.
*
* Arguments:   - ml_dsa_params:  parameter struct
*              - uint8_t *sig:   pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen: pointer to output length of signature
*              - uint8_t *m:     pointer to message to be signed
*              - size_t mlen:    length of message
*              - uint8_t *pre:   pointer to prefix string
*              - size_t prelen:  length of prefix string
*              - uint8_t *rnd:   pointer to random seed
*              - uint8_t *sk:    pointer to bit-packed secret key
*
* Returns 0 (success) or -1 (context string too long)
**************************************************/
int crypto_sign_signature_internal(ml_dsa_params *params,
                                   uint8_t *sig,
                                   size_t *siglen,
                                   const uint8_t *m,
                                   size_t mlen,
                                   const uint8_t *pre,
                                   size_t prelen,
                                   const uint8_t *rnd,
                                   const uint8_t *sk)
{
  unsigned int n;
  uint8_t seedbuf[2*SEEDBYTES + TRBYTES + 2*CRHBYTES];
  uint8_t *rho, *tr, *key, *mu, *rhoprime;
  uint16_t nonce = 0;
  polyvecl mat[DILITHIUM_K_MAX], s1, y, z;
  polyveck t0, s2, w1, w0, h;
  poly cp;
  KECCAK1600_CTX state;

  rho = seedbuf;
  tr = rho + SEEDBYTES;
  key = tr + TRBYTES;
  mu = key + SEEDBYTES;
  rhoprime = mu + CRHBYTES;
  /* FIPS 204: line 1 */
  unpack_sk(params, rho, tr, key, &t0, &s1, &s2, sk);

  /* FIPS 204: line 6 Compute mu = CRH(tr, pre, msg) */
  // This differs from FIPS 204 line 6 that performs mu = CRH(tr, M') and the
  // processing of M' in the external function. However, as M' = (pre, msg),
  // mu = CRH(tr, M') = CRH(tr, pre, msg).
  SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
  SHA3_Update(&state, tr, TRBYTES);
  SHA3_Update(&state, pre, prelen);
  SHA3_Update(&state, m, mlen);
  SHAKE_Final(mu, &state, CRHBYTES);

  /* FIPS 204: line 7 Compute rhoprime = CRH(key, rnd, mu) */
  SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
  SHA3_Update(&state, key, SEEDBYTES);
  SHA3_Update(&state, rnd, RNDBYTES);
  SHA3_Update(&state, mu, CRHBYTES);
  SHAKE_Final(rhoprime, &state, CRHBYTES);

  /* FIPS 204: line 5 Expand matrix and transform vectors */
  polyvec_matrix_expand(params, mat, rho);
  polyvecl_ntt(params, &s1);
  polyveck_ntt(params, &s2);
  polyveck_ntt(params, &t0);

rej:
  /* FIPS 204: line 11 Sample intermediate vector y */
  polyvecl_uniform_gamma1(params, &y, rhoprime, nonce++);

  /* FIPS 204: line 12 Matrix-vector multiplication */
  z = y;
  polyvecl_ntt(params, &z);
  polyvec_matrix_pointwise_montgomery(params, &w1, mat, &z);
  polyveck_reduce(params, &w1);
  polyveck_invntt_tomont(params, &w1);

  /* FIPS 204: line 13 - 14 Decompose w and call the random oracle */
  polyveck_caddq(params, &w1);
  polyveck_decompose(params, &w1, &w0, &w1);
  polyveck_pack_w1(params, sig, &w1);

  SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
  SHA3_Update(&state, mu, CRHBYTES);
  SHA3_Update(&state, sig, params->k * params->poly_w1_packed_bytes);
  SHAKE_Final(sig, &state, params->c_tilde_bytes);
  poly_challenge(params, &cp, sig);
  poly_ntt(&cp);

  /* FIPS 204: line 20 Compute z, reject if it reveals secret */
  polyvecl_pointwise_poly_montgomery(params, &z, &cp, &s1);
  polyvecl_invntt_tomont(params, &z);
  polyvecl_add(params, &z, &z, &y);
  polyvecl_reduce(params, &z);
  if(polyvecl_chknorm(params, &z, params->gamma1 - params->beta)) {
    goto rej;
  }

  /* FIPS 204: line 21 Check that subtracting cs2 does not change high bits of w and low bits
   * do not reveal secret information */
  polyveck_pointwise_poly_montgomery(params, &h, &cp, &s2);
  polyveck_invntt_tomont(params, &h);
  polyveck_sub(params, &w0, &w0, &h);
  polyveck_reduce(params, &w0);
  if(polyveck_chknorm(params, &w0, params->gamma2 - params->beta)) {
    goto rej;
  }

  /* FIPS 204: line 25 */
  polyveck_pointwise_poly_montgomery(params, &h, &cp, &t0);
  polyveck_invntt_tomont(params, &h);
  polyveck_reduce(params, &h);
  if(polyveck_chknorm(params, &h, params->gamma2)) {
    goto rej;
  }

  /* FIPS 204: line 26 Compute signer's hint */
  polyveck_add(params, &w0, &w0, &h);
  n = polyveck_make_hint(params, &h, &w0, &w1);
  if(n > params->omega) {
    goto rej;
  }

  /* FIPS 204: line 33 Write signature */
  pack_sig(params, sig, sig, &z, &h);
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
* Name:        crypto_sign_signature
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
int crypto_sign_signature(ml_dsa_params *params,
                          uint8_t *sig,
                          size_t *siglen,
                          const uint8_t *m,
                          size_t mlen,
                          const uint8_t *ctx,
                          size_t ctxlen,
                          const uint8_t *sk)
{
  uint8_t pre[257];
  uint8_t rnd[RNDBYTES];

  if(ctxlen > 255) {
    return -1;
  }
  /* Prepare pre = (0, ctxlen, ctx) */
  pre[0] = 0;
  pre[1] = ctxlen;
  OPENSSL_memcpy(pre + 2 , ctx, ctxlen);

  if (!RAND_bytes(rnd, RNDBYTES)) {
    return -1;
  }
  crypto_sign_signature_internal(params, sig, siglen, m, mlen, pre, 2 + ctxlen, rnd, sk);

  /* FIPS 204. Section 3.6.3 Destruction of intermediate values. */
  OPENSSL_cleanse(pre, sizeof(pre));
  OPENSSL_cleanse(rnd, sizeof(rnd));
  return 0;
}

/*************************************************
* Name:        crypto_sign
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
int crypto_sign(ml_dsa_params *params,
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
  ret = crypto_sign_signature(params, sm, smlen, sm + params->bytes, mlen, ctx, ctxlen, sk);
  *smlen += mlen;
  return ret;
}

/*************************************************
* Name:        crypto_sign_verify_internal
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
*
* Returns 0 if signature could be verified correctly and -1 otherwise
**************************************************/
int crypto_sign_verify_internal(ml_dsa_params *params,
                                const uint8_t *sig,
                                size_t siglen,
                                const uint8_t *m,
                                size_t mlen,
                                const uint8_t *pre,
                                size_t prelen,
                                const uint8_t *pk)
{
  unsigned int i;
  uint8_t buf[DILITHIUM_K_MAX*DILITHIUM_POLYW1_PACKEDBYTES_MAX];
  uint8_t rho[SEEDBYTES];
  uint8_t mu[CRHBYTES];
  uint8_t tr[TRBYTES];
  uint8_t c[DILITHIUM_C_TILDE_BYTES_MAX];
  uint8_t c2[DILITHIUM_C_TILDE_BYTES_MAX];
  poly cp;
  polyvecl mat[DILITHIUM_K_MAX], z;
  polyveck t1, w1, h;
  KECCAK1600_CTX state;

  if(siglen != params->bytes) {
    return -1;
  }
  /* FIPS 204: line 1 */
  unpack_pk(params, rho, &t1, pk);
  /* FIPS 204: line 2 */
  if(unpack_sig(params, c, &z, &h, sig)) {
    return -1;
  }
  if(polyvecl_chknorm(params, &z, params->gamma1 - params->beta)) {
    return -1;
  }

  /* FIPS 204: line 6 Compute tr */
  SHAKE256(pk, params->public_key_bytes, tr, TRBYTES);
  /* FIPS 204: line 7 Compute mu = H(BytesToBits(tr) || M', 64) */
  // Like crypto_sign_signature_internal, the processing of M' is performed
  // here, as opposed to within the external function.
  SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
  SHA3_Update(&state, tr, TRBYTES);
  SHA3_Update(&state, pre, prelen);
  SHA3_Update(&state, m, mlen);
  SHAKE_Final(mu, &state, CRHBYTES);

  /* FIPS 204: line 9 Matrix-vector multiplication; compute Az - c2^dt1 */
  poly_challenge(params, &cp, c);
  polyvec_matrix_expand(params, mat, rho);

  polyvecl_ntt(params, &z);
  polyvec_matrix_pointwise_montgomery(params, &w1, mat, &z);

  poly_ntt(&cp);
  polyveck_shiftl(params, &t1);
  polyveck_ntt(params, &t1);
  polyveck_pointwise_poly_montgomery(params, &t1, &cp, &t1);

  polyveck_sub(params, &w1, &w1, &t1);
  polyveck_reduce(params, &w1);
  polyveck_invntt_tomont(params, &w1);

  /* FIPS 204: line 10 Reconstruct w1 */
  polyveck_caddq(params, &w1);
  polyveck_use_hint(params, &w1, &w1, &h);
  polyveck_pack_w1(params, buf, &w1);

  /* FIPS 204: line 12 Call random oracle and verify challenge */
  SHAKE_Init(&state, SHAKE256_BLOCKSIZE);
  SHA3_Update(&state, mu, CRHBYTES);
  SHA3_Update(&state, buf, params->k * params->poly_w1_packed_bytes);
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
* Name:        crypto_sign_verify
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
int crypto_sign_verify(ml_dsa_params *params,
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
  return crypto_sign_verify_internal(params, sig, siglen, m, mlen, pre, 2 + ctxlen, pk);
}

/*************************************************
* Name:        crypto_sign_open
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
int crypto_sign_open(ml_dsa_params *params,
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
  if(crypto_sign_verify(params,sm, params->bytes, sm + params->bytes, *mlen, ctx, ctxlen, pk)) {
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
