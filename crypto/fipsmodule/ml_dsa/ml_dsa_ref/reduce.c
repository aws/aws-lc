#include <stdint.h>
#include "params.h"
#include "reduce.h"

/*************************************************
* Name:        ml_dsa_fqmul
*
* Description: Multiplication followed by Montgomery reduction
*              For finite field element a with -2^{31}Q <= a <= Q*2^31,
*              compute r \equiv a*2^{-32} (mod Q) such that -Q < r < Q.
*
* Arguments:   - int32_t a: first factor
*              - int32_t b: second factor
*
* Returns r.
**************************************************/
int64_t ml_dsa_fqmul(int32_t a, int32_t b) {
  int64_t s;
  int32_t t;

  s = (int64_t)a*b;
  t = (int64_t)(int32_t)s * ML_DSA_QINV;
  t = (s - (int64_t)t * ML_DSA_Q) >> 32;
  return t;
}

/*************************************************
* Name:        ml_dsa_reduce32
*
* Description: For finite field element a with a <= 2^{31} - 2^{22} - 1,
*              compute r \equiv a (mod Q) such that -6283009 <= r <= 6283008.
*
* Arguments:   - int32_t: finite field element a
*
* Returns r.
**************************************************/
int32_t ml_dsa_reduce32(int32_t a) {
  int32_t t;

  t = (a + (1 << 22)) >> 23;
  t = a - t * ML_DSA_Q;
  return t;
}

/*************************************************
* Name:        ml_dsa_caddq
*
* Description: Add Q if input coefficient is negative.
*
* Arguments:   - int32_t: finite field element a
*
* Returns r.
**************************************************/
int32_t ml_dsa_caddq(int32_t a) {
  // a = a < 0 ? a + Q : a;
  a = constant_time_select_int(constant_time_msb_w(a), a + ML_DSA_Q, a);
  return a;
}

/*************************************************
* Name:        ml_dsa_freeze
*
* Description: For finite field element a, compute standard
*              representative r = a mod^+ Q.
*
* Arguments:   - int32_t: finite field element a
*
* Returns r.
**************************************************/
int32_t ml_dsa_freeze(int32_t a) {
  a = ml_dsa_reduce32(a);
  a = ml_dsa_caddq(a);
  return a;
}
