#ifndef PARAMS_H
#define PARAMS_H

// The only defined parameters are those that don't depend
// on the parameter set. All other parameters are specified
// in ml_dsa_params structure that is unique for each parameter
// set (ML-DSA 44/65/87).
#define SEEDBYTES 32
#define CRHBYTES 64
#define TRBYTES 64
#define RNDBYTES 32
#define N 256
#define Q 8380417
#define D 13
#define ROOT_OF_UNITY 1753
#define POLYT1_PACKEDBYTES  320
#define POLYT0_PACKEDBYTES  416

// Structure for ML-DSA parameters that depend on the parameter set.
typedef struct {
  uint8_t k;
  uint8_t l;
  size_t eta;
  size_t tau;
  size_t beta;
  size_t gamma1;
  int32_t gamma2;
  size_t omega;
  size_t c_tilde_bytes;
  size_t poly_vech_packed_bytes;
  size_t poly_z_packed_bytes;
  size_t poly_w1_packed_bytes;
  size_t poly_eta_packed_bytes;
  size_t public_key_bytes;
  size_t secret_key_bytes;
  size_t bytes;
} ml_dsa_params;

// We define max values for some parameters because they are used
// for static allocation.
#define DILITHIUM_K_MAX (8)
#define DILITHIUM_L_MAX (7)
#define DILITHIUM_C_TILDE_BYTES_MAX (64)
#define DILITHIUM_POLYW1_PACKEDBYTES_MAX (192)
#define DILITHIUM_POLY_UNIFORM_ETA_NBLOCKS_MAX ((227 + SHAKE256_RATE - 1)/SHAKE256_RATE)
#define DILITHIUM_POLYZ_PACKEDBYTES_MAX (576)

void ml_dsa_44_params_init(ml_dsa_params *params);
void ml_dsa_65_params_init(ml_dsa_params *params);
void ml_dsa_87_params_init(ml_dsa_params *params);

#endif
