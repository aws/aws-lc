#ifndef ML_DSA_REDUCE_H
#define ML_DSA_REDUCE_H

#include <stdint.h>
#include "params.h"

#define ML_DSA_QINV 58728449 // q^(-1) mod 2^32

int64_t ml_dsa_fqmul(int32_t a, int32_t b);

int32_t ml_dsa_reduce32(int32_t a);

int32_t ml_dsa_caddq(int32_t a);

int32_t ml_dsa_freeze(int32_t a);

#endif
