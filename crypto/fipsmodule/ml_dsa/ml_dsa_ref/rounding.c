#include <stdint.h>
#include "params.h"
#include "rounding.h"

/*************************************************
* Name:        ml_dsa_power2round
*
* Description: FIPS 204: Algorithm 35.
*              For finite field element a, compute a0, a1 such that
*              a mod^+ Q = a1*2^D + a0 with -2^{D-1} < a0 <= 2^{D-1}.
*              Assumes a to be standard representative.
*
* Arguments:   - int32_t a: input element
*              - int32_t *a0: pointer to output element a0
*
* Returns a1.
**************************************************/
int32_t ml_dsa_power2round(int32_t *a0, int32_t a)  {
  int32_t a1;

  a1 = (a + (1 << (ML_DSA_D-1)) - 1) >> ML_DSA_D;
  *a0 = a - (a1 << ML_DSA_D);
  return a1;
}

/*************************************************
* Name:        ml_dsa_decompose
*
* Description: FIPS 204: Algorithm 36.
*              For finite field element a, compute high and low bits a0, a1 such
*              that a mod^+ Q = a1*ALPHA + a0 with -ALPHA/2 < a0 <= ALPHA/2 except
*              if a1 = (Q-1)/ALPHA where we set a1 = 0 and
*              -ALPHA/2 <= a0 = a mod^+ Q - Q < 0. Assumes a to be standard
*              representative.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - int32_t a: input element
*              - int32_t *a0: pointer to output element a0
*
* Returns a1.
**************************************************/
int32_t ml_dsa_decompose(ml_dsa_params *params, int32_t *a0, int32_t a) {
  assert((params->gamma2 == (ML_DSA_Q-1)/32) || (params->gamma2 == (ML_DSA_Q-1)/88));

  int32_t a1;

  a1 = (a + 127) >> 7;
  if (params->gamma2 == (ML_DSA_Q-1)/32) {
    a1  = (a1*1025 + (1 << 21)) >> 22;
    a1 &= 15;
  } else if (params->gamma2 == (ML_DSA_Q-1)/88) {
    a1  = (a1*11275 + (1 << 23)) >> 24;
    // a1 = 43 < a1 ? 0 : a1;
    a1 = constant_time_select_int(constant_time_msb_w(43 - a1), 0, a1);
  }

  *a0 = a - a1*2*params->gamma2;
  // a0 = (Q-1)/2 < a0 ? a0 - Q : a0;
  *a0 = constant_time_select_int(constant_time_msb_w((ML_DSA_Q-1)/2 - *a0),
                                                     *a0 - ML_DSA_Q, *a0);
  return a1;
}

/*************************************************
* Name:        ml_dsa_make_hint
*
* Description: FIPS 204: Algorithm 39 MakeHint.
*              Compute hint bit indicating whether the low bits of the
*              input element overflow into the high bits.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - int32_t a0: low bits of input element
*              - int32_t a1: high bits of input element
*
* Returns 1 if overflow.
**************************************************/
unsigned int ml_dsa_make_hint(ml_dsa_params *params, int32_t a0, int32_t a1) {
  if(a0 > (params->gamma2) || a0 < -(params->gamma2) ||
    (a0 == -(params->gamma2) && a1 != 0)) {
    return 1;
  }
  return 0;
}

/*************************************************
* Name:        ml_dsa_use_hint
*
* Description: FIPS 204: Algorithm 40 UseHint.
*              Correct high bits according to hint.
*
* Arguments:   - ml_dsa_params: parameter struct
*              - int32_t a: input element
*              - unsigned int hint: hint bit
*
* Returns corrected high bits.
**************************************************/
int32_t ml_dsa_use_hint(ml_dsa_params *params, int32_t a, unsigned int hint) {
  int32_t a0, a1;

  assert((params->gamma2 == (ML_DSA_Q-1)/32) || (params->gamma2 == (ML_DSA_Q-1)/88));

  a1 = ml_dsa_decompose(params, &a0, a);
  if(hint == 0) {
    return a1;
  }

  if (params->gamma2 == (ML_DSA_Q-1)/32) {
    if(a0 > 0) {
      return (a1 + 1) & 15;
    }
    else {
      return (a1 - 1) & 15;
    }
  }
  else  {
    if(a0 > 0) {
      return (a1 == 43) ?  0 : a1 + 1;
    }
    else {
      return (a1 ==  0) ? 43 : a1 - 1;
    }
  }
}
