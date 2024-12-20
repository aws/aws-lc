#ifndef ML_DSA_NTT_H
#define ML_DSA_NTT_H

#include <stdint.h>
#include "params.h"

void ntt(int32_t a[N]);

void invntt_tomont(int32_t a[N]);

#endif
