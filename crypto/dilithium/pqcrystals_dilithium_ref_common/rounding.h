#ifndef ROUNDING_H
#define ROUNDING_H

#include <stdint.h>
#include "params.h"

int32_t power2round(int32_t *a0, int32_t a);

int32_t decompose(ml_dsa_params *params, int32_t *a0, int32_t a);

unsigned int make_hint(ml_dsa_params *params, int32_t a0, int32_t a1);

int32_t use_hint(ml_dsa_params *params, int32_t a, unsigned int hint);

#endif
