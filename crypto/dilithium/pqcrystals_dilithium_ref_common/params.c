#include <openssl/base.h>
#include <assert.h>

#include "params.h"

static void ml_dsa_params_init(ml_dsa_params *params, size_t k) {
  assert((k == 2) || (k == 3) || (k == 5));

  if (k == 2) {
    // Parameters for ML-DSA-44 from Table 1. FIPS-204: ML-DSA Parameter Sets.
    // https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf Section 4
    params->k = 4;
    params->l = 4;
    params->tau = 39;
    params->beta = 78;
    params->omega = 80;
    params->c_tilde_bytes = 32;
    params->gamma1 = (1 << 17);
    params->gamma2 = (ML_DSA_Q-1)/88;
    params->eta = 2;
    params->poly_z_packed_bytes = 576;
    params->poly_w1_packed_bytes = 192;
    params->poly_eta_packed_bytes = 96;
    params->poly_vech_packed_bytes = (params->omega + params->k);

    // Sizes for ML-DSA-44 keys and signatures from Table 2. FIPS-204.
    params->public_key_bytes = (ML_DSA_SEEDBYTES + params->k * ML_DSA_POLYT1_PACKEDBYTES);
    params->secret_key_bytes = (2 * ML_DSA_SEEDBYTES + ML_DSA_TRBYTES +
                                params->l * params->poly_eta_packed_bytes +
                                params->k * params->poly_eta_packed_bytes +
                                params->k * ML_DSA_POLYT0_PACKEDBYTES);
    params->bytes = (params->c_tilde_bytes +
                     params->l *  params->poly_z_packed_bytes +
                     params->poly_vech_packed_bytes);
  }
  else if (k == 3) {
    // Parameters for ML-DSA-65 from Table 1. FIPS-204: ML-DSA Parameter Sets.
    // https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf Section 4
    params->k = 6;
    params->l = 5;
    params->tau = 49;
    params->beta = 196;
    params->omega = 55;
    params->c_tilde_bytes = 48;
    params->gamma1 = (1 << 19);
    params->gamma2 = (ML_DSA_Q-1)/32;
    params->eta = 4;
    params->poly_z_packed_bytes = 640;
    params->poly_w1_packed_bytes = 128;
    params->poly_eta_packed_bytes = 128;
    params->poly_vech_packed_bytes = (params->omega + params->k);

    // Sizes for ML-DSA-65 keys and signatures from Table 2. FIPS-204.
    params->public_key_bytes = (ML_DSA_SEEDBYTES + params->k * ML_DSA_POLYT1_PACKEDBYTES);
    params->secret_key_bytes = (2 * ML_DSA_SEEDBYTES + ML_DSA_TRBYTES +
                                params->l * params->poly_eta_packed_bytes +
                                params->k * params->poly_eta_packed_bytes +
                                params->k * ML_DSA_POLYT0_PACKEDBYTES);
    params->bytes = (params->c_tilde_bytes +
                     params->l *  params->poly_z_packed_bytes +
                     params->poly_vech_packed_bytes);
  }
  else {
    // Parameters for ML-DSA-87 from Table 1. FIPS-204: ML-DSA Parameter Sets.
    // https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf Section 4
    params->k = 8;
    params->l = 7;
    params->tau = 60;
    params->beta = 120;
    params->omega = 75;
    params->c_tilde_bytes = 64;
    params->gamma1 = (1 << 19);
    params->gamma2 = (ML_DSA_Q-1)/32;
    params->eta = 2;
    params->poly_z_packed_bytes = 640;
    params->poly_w1_packed_bytes = 128;
    params->poly_eta_packed_bytes = 96;
    params->poly_vech_packed_bytes = (params->omega + params->k);

    // Sizes for ML-DSA-87 keys and signatures from Table 2. FIPS-204.
    params->public_key_bytes = (ML_DSA_SEEDBYTES + params->k * ML_DSA_POLYT1_PACKEDBYTES);
    params->secret_key_bytes = (2 * ML_DSA_SEEDBYTES + ML_DSA_TRBYTES +
                                params->l * params->poly_eta_packed_bytes +
                                params->k * params->poly_eta_packed_bytes +
                                params->k * ML_DSA_POLYT0_PACKEDBYTES);
    params->bytes = (params->c_tilde_bytes +
                     params->l *  params->poly_z_packed_bytes +
                     params->poly_vech_packed_bytes);
  }
}

void ml_dsa_44_params_init(ml_dsa_params *params) {
  ml_dsa_params_init(params, 2);
}
void ml_dsa_65_params_init(ml_dsa_params *params) {
  ml_dsa_params_init(params, 3);
}
void ml_dsa_87_params_init(ml_dsa_params *params) {
  ml_dsa_params_init(params, 5);
}
