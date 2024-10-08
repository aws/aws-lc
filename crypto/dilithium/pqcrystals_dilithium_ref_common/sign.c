#include <stdint.h>
#include "params.h"
#include "sign.h"
#include "packing.h"
#include "polyvec.h"
#include "poly.h"
#include "../../rand_extra/pq_custom_randombytes.h"
#include "symmetric.h"
#include "fips202.h"

/*************************************************
* Name:        crypto_sign_keypair
*
* Description: Generates public and private key.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t *pk: pointer to output public key (allocated
*                             array of CRYPTO_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key (allocated
*                             array of CRYPTO_SECRETKEYBYTES bytes)
*
* Returns 0 (success)
**************************************************/
int crypto_sign_keypair(ml_dsa_params *params, uint8_t *pk, uint8_t *sk) {
  uint8_t seedbuf[2*SEEDBYTES + CRHBYTES];
  uint8_t tr[TRBYTES];
  const uint8_t *rho, *rhoprime, *key;
  polyvecl mat[DILITHIUM_K_MAX];
  polyvecl s1, s1hat;
  polyveck s2, t1, t0;

  /* Get randomness for rho, rhoprime and key */
  pq_custom_randombytes(seedbuf, SEEDBYTES);
  seedbuf[SEEDBYTES+0] = params->k;
  seedbuf[SEEDBYTES+1] = params->l;
  shake256(seedbuf, 2*SEEDBYTES + CRHBYTES, seedbuf, SEEDBYTES+2);
  rho = seedbuf;
  rhoprime = rho + SEEDBYTES;
  key = rhoprime + CRHBYTES;

  /* Expand matrix */
  polyvec_matrix_expand(params, mat, rho);

  /* Sample short vectors s1 and s2 */
  polyvecl_uniform_eta(params, &s1, rhoprime, 0);
  polyveck_uniform_eta(params, &s2, rhoprime, params->l);

  /* Matrix-vector multiplication */
  s1hat = s1;
  polyvecl_ntt(params, &s1hat);
  polyvec_matrix_pointwise_montgomery(params, &t1, mat, &s1hat);
  polyveck_reduce(params, &t1);
  polyveck_invntt_tomont(params, &t1);

  /* Add error vector s2 */
  polyveck_add(params, &t1, &t1, &s2);

  /* Extract t1 and write public key */
  polyveck_caddq(params, &t1);
  polyveck_power2round(params, &t1, &t0, &t1);
  pack_pk(params, pk, rho, &t1);

  /* Compute H(rho, t1) and write secret key */
  shake256(tr, TRBYTES, pk, params->public_key_bytes);
  pack_sk(params, sk, rho, tr, key, &t0, &s1, &s2);

  return 0;
}

/*************************************************
* Name:        crypto_sign_signature
*
* Description: Computes signature.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t *sig:   pointer to output signature (of length CRYPTO_BYTES)
*              - size_t *siglen: pointer to output length of signature
*              - uint8_t *m:     pointer to message to be signed
*              - size_t mlen:    length of message
*              - uint8_t *ctx:   pointer to context string
*              - size_t ctxlen:  length of context string
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
  unsigned int n;
  uint8_t seedbuf[2*SEEDBYTES + TRBYTES + RNDBYTES + 2*CRHBYTES];
  uint8_t *rho, *tr, *key, *mu, *rhoprime, *rnd;
  uint16_t nonce = 0;
  polyvecl mat[DILITHIUM_K_MAX], s1, y, z;
  polyveck t0, s2, w1, w0, h;
  poly cp;
  keccak_state state;

  if(ctxlen > 255)
    return -1;

  rho = seedbuf;
  tr = rho + SEEDBYTES;
  key = tr + TRBYTES;
  rnd = key + SEEDBYTES;
  mu = rnd + RNDBYTES;
  rhoprime = mu + CRHBYTES;
  unpack_sk(params, rho, tr, key, &t0, &s1, &s2, sk);

  /* Compute mu = CRH(tr, 0, ctxlen, ctx, msg) */
  mu[0] = 0;
  mu[1] = ctxlen;
  shake256_init(&state);
  shake256_absorb(&state, tr, TRBYTES);
  shake256_absorb(&state, mu, 2);
  shake256_absorb(&state, ctx, ctxlen);
  shake256_absorb(&state, m, mlen);
  shake256_finalize(&state);
  shake256_squeeze(mu, CRHBYTES, &state);

#ifdef DILITHIUM_RANDOMIZED_SIGNING
  pq_custom_randombytes(rnd, RNDBYTES);
#else
  for(n=0;n<RNDBYTES;n++)
    rnd[n] = 0;
#endif
  shake256(rhoprime, CRHBYTES, key, SEEDBYTES + RNDBYTES + CRHBYTES);

  /* Expand matrix and transform vectors */
  polyvec_matrix_expand(params, mat, rho);
  polyvecl_ntt(params, &s1);
  polyveck_ntt(params, &s2);
  polyveck_ntt(params, &t0);

rej:
  /* Sample intermediate vector y */
  polyvecl_uniform_gamma1(params, &y, rhoprime, nonce++);

  /* Matrix-vector multiplication */
  z = y;
  polyvecl_ntt(params, &z);
  polyvec_matrix_pointwise_montgomery(params, &w1, mat, &z);
  polyveck_reduce(params, &w1);
  polyveck_invntt_tomont(params, &w1);

  /* Decompose w and call the random oracle */
  polyveck_caddq(params, &w1);
  polyveck_decompose(params, &w1, &w0, &w1);
  polyveck_pack_w1(params, sig, &w1);

  shake256_init(&state);
  shake256_absorb(&state, mu, CRHBYTES);
  shake256_absorb(&state, sig, params->k*params->poly_w1_packed_bytes);
  shake256_finalize(&state);
  shake256_squeeze(sig, params->c_tilde_bytes, &state);
  poly_challenge(params, &cp, sig);
  poly_ntt(&cp);

  /* Compute z, reject if it reveals secret */
  polyvecl_pointwise_poly_montgomery(params, &z, &cp, &s1);
  polyvecl_invntt_tomont(params, &z);
  polyvecl_add(params, &z, &z, &y);
  polyvecl_reduce(params, &z);
  if(polyvecl_chknorm(params, &z, params->gamma1 - params->beta))
    goto rej;

  /* Check that subtracting cs2 does not change high bits of w and low bits
   * do not reveal secret information */
  polyveck_pointwise_poly_montgomery(params, &h, &cp, &s2);
  polyveck_invntt_tomont(params, &h);
  polyveck_sub(params, &w0, &w0, &h);
  polyveck_reduce(params, &w0);
  if(polyveck_chknorm(params, &w0, params->gamma2 - params->beta))
    goto rej;

  /* Compute hints for w1 */
  polyveck_pointwise_poly_montgomery(params, &h, &cp, &t0);
  polyveck_invntt_tomont(params, &h);
  polyveck_reduce(params, &h);
  if(polyveck_chknorm(params, &h, params->gamma2))
    goto rej;

  polyveck_add(params, &w0, &w0, &h);
  n = polyveck_make_hint(params, &h, &w0, &w1);
  if(n > params->omega)
    goto rej;

  /* Write signature */
  pack_sig(params, sig, sig, &z, &h);
  *siglen = params->bytes;
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

  for(i = 0; i < mlen; ++i)
    sm[params->bytes + mlen - 1 - i] = m[mlen - 1 - i];
  ret = crypto_sign_signature(params, sm, smlen, sm + params->bytes, mlen, ctx, ctxlen, sk);
  *smlen += mlen;
  return ret;
}

/*************************************************
* Name:        crypto_sign_verify
*
* Description: Verifies signature.
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
  unsigned int i;
  uint8_t buf[DILITHIUM_K_MAX*DILITHIUM_POLYW1_PACKEDBYTES_MAX];
  uint8_t rho[SEEDBYTES];
  uint8_t mu[CRHBYTES];
  uint8_t c[DILITHIUM_C_TILDE_BYTES_MAX];
  uint8_t c2[DILITHIUM_C_TILDE_BYTES_MAX];
  poly cp;
  polyvecl mat[DILITHIUM_K_MAX], z;
  polyveck t1, w1, h;
  keccak_state state;

  if(ctxlen > 255 || siglen != params->bytes)
    return -1;

  unpack_pk(params, rho, &t1, pk);
  if(unpack_sig(params, c, &z, &h, sig))
    return -1;
  if(polyvecl_chknorm(params, &z, params->gamma1 - params->beta))
    return -1;

  /* Compute CRH(H(rho, t1), msg) */
  shake256(mu, TRBYTES, pk, params->public_key_bytes);
  shake256_init(&state);
  shake256_absorb(&state, mu, TRBYTES);
  mu[0] = 0;
  mu[1] = ctxlen;
  shake256_absorb(&state, mu, 2);
  shake256_absorb(&state, ctx, ctxlen);
  shake256_absorb(&state, m, mlen);
  shake256_finalize(&state);
  shake256_squeeze(mu, CRHBYTES, &state);

  /* Matrix-vector multiplication; compute Az - c2^dt1 */
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

  /* Reconstruct w1 */
  polyveck_caddq(params, &w1);
  polyveck_use_hint(params, &w1, &w1, &h);
  polyveck_pack_w1(params, buf, &w1);

  /* Call random oracle and verify challenge */
  shake256_init(&state);
  shake256_absorb(&state, mu, CRHBYTES);
  shake256_absorb(&state, buf, params->k*params->poly_w1_packed_bytes);
  shake256_finalize(&state);
  shake256_squeeze(c2, params->c_tilde_bytes, &state);
  for(i = 0; i < params->c_tilde_bytes; ++i)
    if(c[i] != c2[i])
      return -1;

  return 0;
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
  size_t i;

  if(smlen < params->bytes)
    goto badsig;

  *mlen = smlen - params->bytes;
  if(crypto_sign_verify(params,sm, params->bytes, sm + params->bytes, *mlen, ctx, ctxlen, pk))
    goto badsig;
  else {
    /* All good, copy msg, return 0 */
    for(i = 0; i < *mlen; ++i)
      m[i] = sm[params->bytes + i];
    return 0;
  }

badsig:
  /* Signature verification failed */
  *mlen = 0;
  for(i = 0; i < smlen; ++i)
    m[i] = 0;

  return -1;
}
