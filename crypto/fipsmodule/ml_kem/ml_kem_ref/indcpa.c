#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "../../../internal.h"

#include "params.h"
#include "indcpa.h"
#include "polyvec.h"
#include "poly.h"
#include "ntt.h"
#include "symmetric.h"

/*************************************************
* Name:        pack_pk
*
* Description: Serialize the public key as concatenation of the
*              serialized vector of polynomials pk
*              and the public seed used to generate the matrix A.
*
* Arguments:   uint8_t *r: pointer to the output serialized public key
*              polyvec *pk: pointer to the input public-key polyvec
*              const uint8_t *seed: pointer to the input public seed
**************************************************/
static void pack_pk(ml_kem_params *params,
                    uint8_t *r,
                    polyvec *pk,
                    const uint8_t *seed)
{
  polyvec_tobytes(params, r, pk);
  memcpy(r+params->poly_vec_bytes, seed, KYBER_SYMBYTES);
}

/*************************************************
* Name:        unpack_pk
*
* Description: De-serialize public key from a byte array;
*              approximate inverse of pack_pk
*
* Arguments:   - polyvec *pk: pointer to output public-key polynomial vector
*              - uint8_t *seed: pointer to output seed to generate matrix A
*              - const uint8_t *packedpk: pointer to input serialized public key
**************************************************/
static void unpack_pk(ml_kem_params *params,
                      polyvec *pk,
                      uint8_t seed[KYBER_SYMBYTES],
                      const uint8_t *packedpk)
{
  polyvec_frombytes(params, pk, packedpk);
  memcpy(seed, packedpk+params->poly_vec_bytes, KYBER_SYMBYTES);
}

/*************************************************
* Name:        pack_sk
*
* Description: Serialize the secret key
*
* Arguments:   - uint8_t *r: pointer to output serialized secret key
*              - polyvec *sk: pointer to input vector of polynomials (secret key)
**************************************************/
static void pack_sk(ml_kem_params *params, uint8_t *r, polyvec *sk)
{
  polyvec_tobytes(params, r, sk);
}

/*************************************************
* Name:        unpack_sk
*
* Description: De-serialize the secret key; inverse of pack_sk
*
* Arguments:   - polyvec *sk: pointer to output vector of polynomials (secret key)
*              - const uint8_t *packedsk: pointer to input serialized secret key
**************************************************/
static void unpack_sk(ml_kem_params *params, polyvec *sk, const uint8_t *packedsk)
{
  polyvec_frombytes(params, sk, packedsk);
}

/*************************************************
* Name:        pack_ciphertext
*
* Description: Serialize the ciphertext as concatenation of the
*              compressed and serialized vector of polynomials b
*              and the compressed and serialized polynomial v
*
* Arguments:   uint8_t *r: pointer to the output serialized ciphertext
*              poly *pk: pointer to the input vector of polynomials b
*              poly *v: pointer to the input polynomial v
**************************************************/
static void pack_ciphertext(ml_kem_params *params, uint8_t *r, polyvec *b, poly *v)
{
  polyvec_compress(params, r, b);
  poly_compress(params, r+params->poly_vec_compressed_bytes, v);
}

/*************************************************
* Name:        unpack_ciphertext
*
* Description: De-serialize and decompress ciphertext from a byte array;
*              approximate inverse of pack_ciphertext
*
* Arguments:   - polyvec *b: pointer to the output vector of polynomials b
*              - poly *v: pointer to the output polynomial v
*              - const uint8_t *c: pointer to the input serialized ciphertext
**************************************************/
static void unpack_ciphertext(ml_kem_params *params, polyvec *b, poly *v, const uint8_t *c)
{
  polyvec_decompress(params, b, c);
  poly_decompress(params, v, c+params->poly_vec_compressed_bytes);
}

/*************************************************
* Name:        rej_uniform
*
* Description: Run rejection sampling on uniform random bytes to generate
*              uniform random integers mod q
*
* Arguments:   - int16_t *r: pointer to output buffer
*              - unsigned int len: requested number of 16-bit integers (uniform mod q)
*              - const uint8_t *buf: pointer to input buffer (assumed to be uniformly random bytes)
*              - unsigned int buflen: length of input buffer in bytes
*
* Returns number of sampled 16-bit integers (at most len)
**************************************************/
static unsigned int rej_uniform(int16_t *r,
                                unsigned int len,
                                const uint8_t *buf,
                                unsigned int buflen)
{
  unsigned int ctr, pos;
  uint16_t val0, val1;

  ctr = pos = 0;
  while(ctr < len && pos + 3 <= buflen) {
    val0 = ((buf[pos+0] >> 0) | ((uint16_t)buf[pos+1] << 8)) & 0xFFF;
    val1 = ((buf[pos+1] >> 4) | ((uint16_t)buf[pos+2] << 4)) & 0xFFF;
    pos += 3;

    if(val0 < KYBER_Q)
      r[ctr++] = val0;
    if(ctr < len && val1 < KYBER_Q)
      r[ctr++] = val1;
  }

  return ctr;
}

#define gen_a(PARAMS,A,B)  gen_matrix(PARAMS,A,B,0)
#define gen_at(PARAMS,A,B) gen_matrix(PARAMS,A,B,1)

/*************************************************
* Name:        gen_matrix
*
* Description: Deterministically generate matrix A (or the transpose of A)
*              from a seed. Entries of the matrix are polynomials that look
*              uniformly random. Performs rejection sampling on output of
*              a XOF
*
* Arguments:   - polyvec *a: pointer to ouptput matrix A
*              - const uint8_t *seed: pointer to input seed
*              - int transposed: boolean deciding whether A or A^T is generated
**************************************************/
#define GEN_MATRIX_NBLOCKS ((12*KYBER_N/8*(1 << 12)/KYBER_Q + XOF_BLOCKBYTES)/XOF_BLOCKBYTES)
// Not static for benchmarking
void gen_matrix(ml_kem_params *params, polyvec *a, const uint8_t seed[KYBER_SYMBYTES], int transposed)
{
  unsigned int ctr, i, j, k;
  unsigned int buflen, off;
  uint8_t buf[GEN_MATRIX_NBLOCKS*XOF_BLOCKBYTES+2];
  KECCAK1600_CTX ctx;

  for(i=0;i<params->k;i++) {
    for(j=0;j<params->k;j++) {
      if(transposed)
        xof_absorb(&ctx, seed, i, j);
      else
        xof_absorb(&ctx, seed, j, i);

      xof_squeezeblocks(buf, GEN_MATRIX_NBLOCKS, &ctx);
      buflen = GEN_MATRIX_NBLOCKS*XOF_BLOCKBYTES;
      ctr = rej_uniform(a[i].vec[j].coeffs, KYBER_N, buf, buflen);

      while(ctr < KYBER_N) {
        off = buflen % 3;
        for(k = 0; k < off; k++)
          buf[k] = buf[buflen - off + k];
        xof_squeezeblocks(buf + off, 1, &ctx);
        buflen = off + XOF_BLOCKBYTES;
        ctr += rej_uniform(a[i].vec[j].coeffs + ctr, KYBER_N - ctr, buf, buflen);
      }
    }
  }
  
  // FIPS 203. Section 3.3 Destruction of intermediate values.
  OPENSSL_cleanse(buf, sizeof(buf));
}

/*************************************************
* Name:        indcpa_keypair_derand
*
* Description: Generates public and private key for the CPA-secure
*              public-key encryption scheme underlying Kyber
*
* Arguments:   - uint8_t *pk: pointer to output public key
*                             (of length KYBER_INDCPA_PUBLICKEYBYTES bytes)
*              - uint8_t *sk: pointer to output private key
*                             (of length KYBER_INDCPA_SECRETKEYBYTES bytes)
*              - const uint8_t *coins: pointer to input randomness
*                             (of length KYBER_SYMBYTES bytes)
**************************************************/
void indcpa_keypair_derand(ml_kem_params *params,
                           uint8_t *pk,
                           uint8_t *sk,
                           const uint8_t coins[KYBER_SYMBYTES])
{
  unsigned int i;
  uint8_t buf[2*KYBER_SYMBYTES];
  const uint8_t *publicseed = buf;
  const uint8_t *noiseseed = buf+KYBER_SYMBYTES;
  uint8_t nonce = 0;
  polyvec a[KYBER_K_MAX], e, pkpv, skpv;

  uint8_t coins_with_domain_separator[KYBER_SYMBYTES + 1];
  memcpy(coins_with_domain_separator, coins, KYBER_SYMBYTES);
  coins_with_domain_separator[KYBER_SYMBYTES] = params->k;

  hash_g(buf, coins_with_domain_separator, KYBER_SYMBYTES + 1);

  gen_a(params, a, publicseed);

  for(i=0;i<params->k;i++)
    poly_getnoise_eta1(params, &skpv.vec[i], noiseseed, nonce++);
  for(i=0;i<params->k;i++)
    poly_getnoise_eta1(params, &e.vec[i], noiseseed, nonce++);

  polyvec_ntt(params, &skpv);
  polyvec_ntt(params, &e);

  // matrix-vector multiplication
  for(i=0;i<params->k;i++) {
    polyvec_basemul_acc_montgomery(params, &pkpv.vec[i], &a[i], &skpv);
    poly_tomont(&pkpv.vec[i]);
  }

  polyvec_add(params, &pkpv, &pkpv, &e);
  polyvec_reduce(params, &pkpv);

  pack_sk(params, sk, &skpv);
  pack_pk(params, pk, &pkpv, publicseed);

  // FIPS 203. Section 3.3 Destruction of intermediate values.
  OPENSSL_cleanse(buf, sizeof(buf));
  OPENSSL_cleanse(coins_with_domain_separator, sizeof(coins_with_domain_separator));
  OPENSSL_cleanse(a, sizeof(a));
  OPENSSL_cleanse(&e, sizeof(e));
  OPENSSL_cleanse(&pkpv, sizeof(pkpv));
  OPENSSL_cleanse(&skpv, sizeof(skpv));
}


/*************************************************
* Name:        indcpa_enc
*
* Description: Encryption function of the CPA-secure
*              public-key encryption scheme underlying Kyber.
*
* Arguments:   - uint8_t *c: pointer to output ciphertext
*                            (of length KYBER_INDCPA_BYTES bytes)
*              - const uint8_t *m: pointer to input message
*                                  (of length KYBER_INDCPA_MSGBYTES bytes)
*              - const uint8_t *pk: pointer to input public key
*                                   (of length KYBER_INDCPA_PUBLICKEYBYTES)
*              - const uint8_t *coins: pointer to input random coins used as seed
*                                      (of length KYBER_SYMBYTES) to deterministically
*                                      generate all randomness
**************************************************/
void indcpa_enc(ml_kem_params *params,
                uint8_t *c,
                const uint8_t *m,
                const uint8_t *pk,
                const uint8_t coins[KYBER_SYMBYTES])
{
  unsigned int i;
  uint8_t seed[KYBER_SYMBYTES];
  uint8_t nonce = 0;
  polyvec sp, pkpv, ep, at[KYBER_K_MAX], b;
  poly v, k, epp;

  unpack_pk(params, &pkpv, seed, pk);
  poly_frommsg(&k, m);
  gen_at(params, at, seed);

  for(i=0;i<params->k;i++)
    poly_getnoise_eta1(params, sp.vec+i, coins, nonce++);
  for(i=0;i<params->k;i++)
    poly_getnoise_eta2(ep.vec+i, coins, nonce++);
  poly_getnoise_eta2(&epp, coins, nonce++);

  polyvec_ntt(params, &sp);

  // matrix-vector multiplication
  for(i=0;i<params->k;i++)
    polyvec_basemul_acc_montgomery(params, &b.vec[i], &at[i], &sp);

  polyvec_basemul_acc_montgomery(params, &v, &pkpv, &sp);

  polyvec_invntt_tomont(params, &b);
  poly_invntt_tomont(&v);

  polyvec_add(params, &b, &b, &ep);
  poly_add(&v, &v, &epp);
  poly_add(&v, &v, &k);
  polyvec_reduce(params, &b);
  poly_reduce(&v);

  pack_ciphertext(params, c, &b, &v);

  // FIPS 203. Section 3.3 Destruction of intermediate values.
  OPENSSL_cleanse(seed, sizeof(seed));
  OPENSSL_cleanse(&sp, sizeof(sp));
  OPENSSL_cleanse(&pkpv, sizeof(pkpv));
  OPENSSL_cleanse(&ep, sizeof(ep));
  OPENSSL_cleanse(at, sizeof(at));
  OPENSSL_cleanse(&b, sizeof(b));
  OPENSSL_cleanse(&v, sizeof(v));
  OPENSSL_cleanse(&k, sizeof(k));
  OPENSSL_cleanse(&epp, sizeof(epp));
}

/*************************************************
* Name:        indcpa_dec
*
* Description: Decryption function of the CPA-secure
*              public-key encryption scheme underlying Kyber.
*
* Arguments:   - uint8_t *m: pointer to output decrypted message
*                            (of length KYBER_INDCPA_MSGBYTES)
*              - const uint8_t *c: pointer to input ciphertext
*                                  (of length KYBER_INDCPA_BYTES)
*              - const uint8_t *sk: pointer to input secret key
*                                   (of length KYBER_INDCPA_SECRETKEYBYTES)
**************************************************/
void indcpa_dec(ml_kem_params *params,
                uint8_t *m,
                const uint8_t *c,
                const uint8_t *sk)
{
  polyvec b, skpv;
  poly v, mp;

  // work-around for gcc-12 which complains that skpv may be used uninitialized.
  OPENSSL_memset(&skpv, 0, sizeof(polyvec));

  unpack_ciphertext(params, &b, &v, c);
  unpack_sk(params, &skpv, sk);

  polyvec_ntt(params, &b);
  polyvec_basemul_acc_montgomery(params, &mp, &skpv, &b);
  poly_invntt_tomont(&mp);

  poly_sub(&mp, &v, &mp);
  poly_reduce(&mp);

  poly_tomsg(m, &mp);


  // FIPS 203. Section 3.3 Destruction of intermediate values.
  OPENSSL_cleanse(&b, sizeof(b));
  OPENSSL_cleanse(&skpv, sizeof(skpv));
  OPENSSL_cleanse(&v, sizeof(v));
  OPENSSL_cleanse(&mp, sizeof(mp));
}
