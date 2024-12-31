#ifndef ML_DSA_ROUNDING_H
#define ML_DSA_ROUNDING_H

#include <stdint.h>
#include "params.h"

int32_t ml_dsa_power2round(int32_t *a0, int32_t a);

int32_t ml_dsa_decompose(ml_dsa_params *params, int32_t *a0, int32_t a);

unsigned int ml_dsa_make_hint(ml_dsa_params *params, int32_t a0, int32_t a1);

int32_t ml_dsa_use_hint(ml_dsa_params *params, int32_t a, unsigned int hint);

#endif
