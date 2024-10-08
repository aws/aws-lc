#include <openssl/base.h>
#include <assert.h>

#include "params.h"

static void ml_dsa_params_init(ml_dsa_params *params, size_t k) {
  assert((k == 2) || (k == 3) || (k == 5));
  size_t K;
  size_t L;
  size_t tau;
  size_t beta;
  size_t omega;
  size_t c_tilde_bytes;

  if (k == 2) {
    K = 4;
    L = 4;
    tau = 39;
    beta = 78;
    omega = 80;
    c_tilde_bytes = 32;
  }
  else if (k == 3) {
    K = 6;
    L = 5;
    tau = 49;
    beta = 196;
    omega = 55;
    c_tilde_bytes = 48;
  }
  else { //k == 5
    K = 8;
    L = 7;
    tau = 60;
    beta = 120;
    omega = 75;
    c_tilde_bytes = 64;
  }

  size_t eta = (k == 3) ? 4 : 2;
  size_t gamma1 = (k == 2) ? (1 << 17) : (1 << 19);
  int32_t gamma2 = (k == 2) ? ((Q-1)/88) : ((Q-1)/32);
  size_t poly_vech_packed_bytes = (omega + K);
  size_t poly_z_packed_bytes = (k == 2) ? 576 : 640;
  size_t poly_w1_packed_bytes = (k == 2) ? 192 : 128;
  size_t poly_eta_packed_bytes = (k == 3) ? 128 : 96;
  size_t public_key_bytes = (SEEDBYTES + K * POLYT1_PACKEDBYTES);
  size_t secret_key_bytes = (2 * SEEDBYTES + TRBYTES + L * poly_eta_packed_bytes + K * poly_eta_packed_bytes + K * POLYT0_PACKEDBYTES);
  size_t bytes = (c_tilde_bytes + L * poly_z_packed_bytes + poly_vech_packed_bytes);

  params->k = K;
  params->l = L;
  params->eta = eta;
  params->tau = tau;
  params->beta = beta;
  params->gamma1 = gamma1;
  params->gamma2 = gamma2;
  params->omega = omega;
  params->c_tilde_bytes = c_tilde_bytes;
  params->poly_vech_packed_bytes = poly_vech_packed_bytes;
  params->poly_z_packed_bytes = poly_z_packed_bytes;
  params->poly_w1_packed_bytes = poly_w1_packed_bytes;
  params->poly_eta_packed_bytes = poly_eta_packed_bytes;
  params->public_key_bytes = public_key_bytes;
  params->secret_key_bytes = secret_key_bytes;
  params->bytes = bytes;
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

