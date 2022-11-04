/*
------------------------------------------------------------------------------------
 Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0 OR ISC
------------------------------------------------------------------------------------
*/

/*
The functions in this file were compiled into ARMv8 assembly code
in order to experiment with the generated instructions and use them in beeu.S.
*/

#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif
#include <inttypes.h>

typedef double *__attribute__((aligned(64))) aligned_double;


uint64_t bn_add_words(uint64_t *restrict a, const uint64_t *restrict b) {
  uint64_t c, l, t;

  c = 0;
//  while (n & ~3) {
    t = a[0];
    t += c;
    c = (t < c);
    l = t + b[0];
    c += (l < t);
    a[0] = l;
    t = a[1];
    t += c;
    c = (t < c);
    l = t + b[1];
    c += (l < t);
    a[1] = l;
    t = a[2];
    t += c;
    c = (t < c);
    l = t + b[2];
    c += (l < t);
    a[2] = l;
    t = a[3];
    t += c;
    c = (t < c);
    l = t + b[3];
    c += (l < t);
    a[3] = l;
//    a += 4;
//  }
//  while (n) {
    t = a[4];
    t += c;
    c = (t < c);
    l = t + 0;
    c += (l < t);
    a[4] = l;
//  }
  return (uint64_t)c;
}

void bn_shift1_words(uint64_t *restrict a)
{
    a[0] = (a[0] >> 1) | (a[1] << 63);
    a[1] = (a[1] >> 1) | (a[2] << 63);
    a[2] = (a[2] >> 1) | (a[3] << 63);
    a[3] = (a[3] >> 1) | (a[4] << 63);
    a[4] >>= 1;
}

void bn_shift(uint64_t *restrict a, uint8_t count)
{
    if (count < 64)
    {
        a[0] = (a[0] >> count) | (a[1] << (64-count));
        a[1] = (a[1] >> count) | (a[2] << (64-count));
        a[2] = (a[2] >> count) | (a[3] << (64-count));
        a[3] >>= count;
    }
}
