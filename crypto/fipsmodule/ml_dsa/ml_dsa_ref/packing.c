#include "params.h"
#include "packing.h"
#include "polyvec.h"
#include "poly.h"
#include "../../sha/internal.h"

/*************************************************
* Name:        ml_dsa_pack_pk_from_sk
*
* Description: Takes a private key and constructs the corresponding public key.
*              The hash of the contructed public key is then compared with
*              the value of tr unpacked from the provided private key.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t pk: pointer to output byte array
*              - const uint8_t sk: pointer to byte array containing bit-packed sk
*
* Returns 0 (when SHAKE256 hash of constructed pk matches tr)
**************************************************/
int ml_dsa_pack_pk_from_sk(ml_dsa_params *params,
                           uint8_t *pk,
                           const uint8_t *sk)
{
  uint8_t rho[ML_DSA_SEEDBYTES];
  uint8_t tr[ML_DSA_TRBYTES];
  uint8_t tr_validate[ML_DSA_TRBYTES];
  uint8_t key[ML_DSA_SEEDBYTES];
  polyvecl mat[ML_DSA_K_MAX];
  polyvecl s1;
  polyveck s2, t1, t0;

  //unpack sk
  ml_dsa_unpack_sk(params, rho, tr, key, &t0, &s1, &s2, sk);

  // generate matrix A
  ml_dsa_polyvec_matrix_expand(params, mat, rho);

  // convert s1 into ntt representation
  ml_dsa_polyvecl_ntt(params, &s1);

  // construct  t1 = A * s1
  ml_dsa_polyvec_matrix_pointwise_montgomery(params, &t1, mat, &s1);

  // reduce t1 modulo field
  ml_dsa_polyveck_reduce(params, &t1);

  // take t1 out of ntt representation
  ml_dsa_polyveck_invntt_tomont(params, &t1);

  // construct t1 = A * s1 + s2
  ml_dsa_polyveck_add(params, &t1, &t1, &s2);

  // cxtract t1 and write public key
  ml_dsa_polyveck_caddq(params, &t1);
  ml_dsa_polyveck_power2round(params, &t1, &t0, &t1);
  ml_dsa_pack_pk(params, pk, rho, &t1);

  // we hash pk to reproduce tr, check it with unpacked value to verify
  SHAKE256(pk, params->public_key_bytes, tr_validate, ML_DSA_TRBYTES);
  return OPENSSL_memcmp(tr_validate, tr, ML_DSA_TRBYTES);
}

/*************************************************
* Name:        ml_dsa_pack_pk
*
* Description: FIPS 204: Algorithm 22 pkEncode.
*              Bit-pack public key pk = (rho, t1).
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t pk[]: pointer to output byte array
*              - const uint8_t rho[]: byte array containing rho
*              - const polyveck *t1: pointer to vector t1
**************************************************/
void ml_dsa_pack_pk(ml_dsa_params *params,
                    uint8_t *pk,
                    const uint8_t rho[ML_DSA_SEEDBYTES],
                    const polyveck *t1)
{
  unsigned int i;

  for(i = 0; i < ML_DSA_SEEDBYTES; ++i) {
    pk[i] = rho[i];
  }
  pk += ML_DSA_SEEDBYTES;

  for(i = 0; i < params->k; ++i) {
    ml_dsa_polyt1_pack(pk + i * ML_DSA_POLYT1_PACKEDBYTES, &t1->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_unpack_pk
*
* Description: FIPS 204: Algorithm 23 pkDecode.
*              Unpack public key pk = (rho, t1).
*
* Arguments:   - ml_dsa_params: parameter struct
*              - const uint8_t rho[]: output byte array for rho
*              - const polyveck *t1: pointer to output vector t1
*              - uint8_t pk[]: pointer to byte array containing bit-packed pk
**************************************************/
void ml_dsa_unpack_pk(ml_dsa_params *params,
                     uint8_t rho[ML_DSA_SEEDBYTES],
                     polyveck *t1,
                     const uint8_t *pk)
{
  unsigned int i;

  for(i = 0; i < ML_DSA_SEEDBYTES; ++i) {
    rho[i] = pk[i];
  }
  pk += ML_DSA_SEEDBYTES;

  for(i = 0; i < params->k; ++i) {
    ml_dsa_polyt1_unpack(&t1->vec[i], pk + i * ML_DSA_POLYT1_PACKEDBYTES);
  }
}

/*************************************************
* Name:        ml_dsa_pack_sk
*
* Description: FIPS 204: Algorithm 24 skEncode.
*              Bit-pack secret key sk = (rho, tr, key, t0, s1, s2).
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t sk[]: pointer to output byte array
*              - const uint8_t rho[]: byte array containing rho
*              - const uint8_t tr[]: byte array containing tr
*              - const uint8_t key[]: byte array containing key
*              - const polyveck *t0: pointer to vector t0
*              - const polyvecl *s1: pointer to vector s1
*              - const polyveck *s2: pointer to vector s2
**************************************************/
void ml_dsa_pack_sk(ml_dsa_params *params,
                    uint8_t *sk,
                    const uint8_t rho[ML_DSA_SEEDBYTES],
                    const uint8_t tr[ML_DSA_TRBYTES],
                    const uint8_t key[ML_DSA_SEEDBYTES],
                    const polyveck *t0,
                    const polyvecl *s1,
                    const polyveck *s2)
{
  unsigned int i;

  for(i = 0; i < ML_DSA_SEEDBYTES; ++i) {
    sk[i] = rho[i];
  }
  sk += ML_DSA_SEEDBYTES;

  for(i = 0; i < ML_DSA_SEEDBYTES; ++i) {
    sk[i] = key[i];
  }
  sk += ML_DSA_SEEDBYTES;

  for(i = 0; i < ML_DSA_TRBYTES; ++i) {
    sk[i] = tr[i];
  }
  sk += ML_DSA_TRBYTES;

  for(i = 0; i < params->l; ++i) {
    ml_dsa_polyeta_pack(params, sk + i * params->poly_eta_packed_bytes, &s1->vec[i]);
  }
  sk +=  params->l * params->poly_eta_packed_bytes;

  for(i = 0; i <  params->k; ++i) {
    ml_dsa_polyeta_pack(params,sk + i * params->poly_eta_packed_bytes, &s2->vec[i]);
  }
  sk +=  params->k * params->poly_eta_packed_bytes;

  for(i = 0; i < params->k; ++i) {
    ml_dsa_polyt0_pack(sk + i * ML_DSA_POLYT0_PACKEDBYTES, &t0->vec[i]);
  }
}

/*************************************************
* Name:        ml_dsa_unpack_sk
*
* Description: FIPS 204: Algorithm 25 skDecode.
*              Unpack secret key sk = (rho, tr, key, t0, s1, s2).
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t rho[]: output byte array for rho
*              - uint8_t tr[]: output byte array for tr
*              - uint8_t key[]: output byte array for key
*              - polyveck *t0: pointer to output vector t0
*              - polyvecl *s1: pointer to output vector s1
*              - polyveck *s2: pointer to output vector s2
*              - uint8_t sk[]: pointer to byte array containing bit-packed sk
**************************************************/
void ml_dsa_unpack_sk(ml_dsa_params *params,
                      uint8_t rho[ML_DSA_SEEDBYTES],
                      uint8_t tr[ML_DSA_TRBYTES],
                      uint8_t key[ML_DSA_SEEDBYTES],
                      polyveck *t0,
                      polyvecl *s1,
                      polyveck *s2,
                      const uint8_t *sk)
{
  unsigned int i;

  for(i = 0; i < ML_DSA_SEEDBYTES; ++i) {
    rho[i] = sk[i];
  }
  sk += ML_DSA_SEEDBYTES;

  for(i = 0; i < ML_DSA_SEEDBYTES; ++i) {
    key[i] = sk[i];
  }
  sk += ML_DSA_SEEDBYTES;

  for(i = 0; i < ML_DSA_TRBYTES; ++i) {
    tr[i] = sk[i];
  }
  sk += ML_DSA_TRBYTES;

  for(i=0; i < params->l; ++i) {
    ml_dsa_polyeta_unpack(params, &s1->vec[i], sk + i * params->poly_eta_packed_bytes);
  }
  sk += params->l * params->poly_eta_packed_bytes;

  for(i=0; i < params->k; ++i) {
    ml_dsa_polyeta_unpack(params, &s2->vec[i], sk + i * params->poly_eta_packed_bytes);
  }
  sk += params->k * params->poly_eta_packed_bytes;

  for(i=0; i < params->k; ++i) {
    ml_dsa_polyt0_unpack(&t0->vec[i], sk + i * ML_DSA_POLYT0_PACKEDBYTES);
  }
}

/*************************************************
* Name:        ml_dsa_pack_sig
*
* Description: FIPS 204: Algorithm 26 sigEncode.
*              Bit-pack signature sig = (c, z, h).
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t sig[]: pointer to output byte array
*              - const uint8_t *c: pointer to challenge hash length SEEDBYTES
*              - const polyvecl *z: pointer to vector z
*              - const polyveck *h: pointer to hint vector h
**************************************************/
void ml_dsa_pack_sig(ml_dsa_params *params,
                     uint8_t *sig,
                     const uint8_t *c,
                     const polyvecl *z,
                     const polyveck *h)
{
  unsigned int i, j, k;

  for(i=0; i < params->c_tilde_bytes; ++i) {
    sig[i] = c[i];
  }
  sig += params->c_tilde_bytes;

  for(i = 0; i < params->l; ++i) {
    ml_dsa_polyz_pack(params, sig + i * params->poly_z_packed_bytes, &z->vec[i]);
  }
  sig += params->l * params->poly_z_packed_bytes;

  /* Encode h */
  for(i = 0; i < params->omega + params->k; ++i) {
    sig[i] = 0;
  }

  k = 0;
  for(i = 0; i < params->k; ++i) {
    for(j = 0; j < ML_DSA_N; ++j) {
      if(h->vec[i].coeffs[j] != 0) {
        sig[k++] = j;
      }
    }

    sig[params->omega + i] = k;
  }
}

/*************************************************
* Name:        ml_dsa_unpack_sig
*
* Description: FIPS 204: Algorithm 27 sigDecode.
*              Unpack signature sig = (c, z, h).
*
* Arguments:   - ml_dsa_params: parameter struct
*              - uint8_t *c: pointer to output challenge hash
*              - polyvecl *z: pointer to output vector z
*              - polyveck *h: pointer to output hint vector h
*              - const uint8_t sig[]: pointer to byte array containing
*                bit-packed signature
*
* Returns 1 in case of malformed signature; otherwise 0.
**************************************************/
int ml_dsa_unpack_sig(ml_dsa_params *params,
                      uint8_t *c,
                      polyvecl *z,
                      polyveck *h,
                      const uint8_t *sig)
{
  unsigned int i, j, k;

  for(i = 0; i < params->c_tilde_bytes; ++i) {
    c[i] = sig[i];
  }
  sig += params->c_tilde_bytes;

  for(i = 0; i < params->l; ++i) {
    ml_dsa_polyz_unpack(params, &z->vec[i], sig + i * params->poly_z_packed_bytes);
  }
  sig += params->l * params->poly_z_packed_bytes;

  /* Decode h */
  k = 0;
  for(i = 0; i < params->k; ++i) {
    for(j = 0; j < ML_DSA_N; ++j) {
      h->vec[i].coeffs[j] = 0;
    }

    if(sig[params->omega + i] < k || sig[params->omega + i] > params->omega) {
      return 1;
    }

    for(j = k; j < sig[params->omega + i]; ++j) {
      /* Coefficients are ordered for strong unforgeability */
      if(j > k && sig[j] <= sig[j-1]) {
        return 1;
      }
      h->vec[i].coeffs[sig[j]] = 1;
    }

    k = sig[params->omega + i];
  }

  /* Extra indices are zero for strong unforgeability */
  for(j = k; j < params->omega; ++j) {
    if(sig[j]) {
      return 1;
    }
  }
  return 0;
}
