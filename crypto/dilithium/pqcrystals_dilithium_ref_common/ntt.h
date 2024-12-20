#ifndef ML_DSA_NTT_H
#define ML_DSA_NTT_H

#include <stdint.h>
#include "params.h"

void ml_dsa_ntt(int32_t a[ML_DSA_N]);

void invntt_tomont(int32_t a[ML_DSA_N]);

#endif
