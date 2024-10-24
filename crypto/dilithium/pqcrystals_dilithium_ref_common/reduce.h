#ifndef REDUCE_H
#define REDUCE_H

#include <stdint.h>
#include "params.h"

#define MONT -4186625 // 2^32 % Q
#define QINV 58728449 // q^(-1) mod 2^32

int64_t fqmul(int32_t a, int32_t b);

int32_t reduce32(int32_t a);

int32_t caddq(int32_t a);

int32_t freeze(int32_t a);

#endif
