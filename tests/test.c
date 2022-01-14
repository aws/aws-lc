/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

// ***************************************************************************
// Do some rudimentary unit testing of s2n-bignum functions against
// simple and straightforward generic C reference code. This is a
// useful complement to the formal proofs, handy for catching basic
// problems quickly and for providing an extra layer of assurance
// against disparities between the formal model and the real world.
// ***************************************************************************

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <time.h>
#include <alloca.h>

// Prototypes for the assembler implementations

#include "../include/s2n-bignum.h"

// Some big static buffers (need them big enough for largest test)

#define BUFFERSIZE 65536

static uint64_t b0[BUFFERSIZE];
static uint64_t b1[BUFFERSIZE];
static uint64_t b2[BUFFERSIZE];
static uint64_t b3[BUFFERSIZE];
static uint64_t b4[BUFFERSIZE];
static uint64_t b5[BUFFERSIZE];
static uint64_t b6[BUFFERSIZE];
static uint64_t b7[BUFFERSIZE];
static uint64_t b8[BUFFERSIZE];
static uint64_t b9[BUFFERSIZE];
static uint64_t b10[BUFFERSIZE];
static uint64_t b11[BUFFERSIZE];
static uint64_t b12[BUFFERSIZE];

// What to test, default number of tests, verbosity of output

#define VERBOSE 1
#define TESTS 100
#define MAXSIZE 35

// The actual number of tests, from input parameter or default to TESTS

static int tests = TESTS;

#define WHAT TEST_ALL_APPLICABLE

enum {
       TEST_ALL,
       TEST_ALL_APPLICABLE,
       TEST_KNOWN_VALUES,
       TEST_BIGNUM_ADD,
       TEST_BIGNUM_ADD_P256,
       TEST_BIGNUM_ADD_P256K1,
       TEST_BIGNUM_ADD_P384,
       TEST_BIGNUM_ADD_P521,
       TEST_BIGNUM_AMONTIFIER,
       TEST_BIGNUM_AMONTMUL,
       TEST_BIGNUM_AMONTREDC,
       TEST_BIGNUM_AMONTSQR,
       TEST_BIGNUM_BITFIELD,
       TEST_BIGNUM_BITSIZE,
       TEST_BIGNUM_BIGENDIAN_4,
       TEST_BIGNUM_BIGENDIAN_6,
       TEST_BIGNUM_CDIV,
       TEST_BIGNUM_CDIV_EXACT,
       TEST_BIGNUM_CLD,
       TEST_BIGNUM_CLZ,
       TEST_BIGNUM_CMADD,
       TEST_BIGNUM_CMNEGADD,
       TEST_BIGNUM_CMOD,
       TEST_BIGNUM_CMUL,
       TEST_BIGNUM_CMUL_P256,
       TEST_BIGNUM_CMUL_P256_ALT,
       TEST_BIGNUM_CMUL_P256K1,
       TEST_BIGNUM_CMUL_P256K1_ALT,
       TEST_BIGNUM_CMUL_P384,
       TEST_BIGNUM_CMUL_P521,
       TEST_BIGNUM_COPRIME,
       TEST_BIGNUM_COPY,
       TEST_BIGNUM_CTD,
       TEST_BIGNUM_CTZ,
       TEST_BIGNUM_DEAMONT_P256,
       TEST_BIGNUM_DEAMONT_P256_ALT,
       TEST_BIGNUM_DEAMONT_P256K1,
       TEST_BIGNUM_DEAMONT_P384,
       TEST_BIGNUM_DEAMONT_P521,
       TEST_BIGNUM_DEMONT,
       TEST_BIGNUM_DEMONT_P256,
       TEST_BIGNUM_DEMONT_P256_ALT,
       TEST_BIGNUM_DEMONT_P256K1,
       TEST_BIGNUM_DEMONT_P384,
       TEST_BIGNUM_DEMONT_P521,
       TEST_BIGNUM_DIGIT,
       TEST_BIGNUM_DIGITSIZE,
       TEST_BIGNUM_DIVMOD10,
       TEST_BIGNUM_DOUBLE_P256,
       TEST_BIGNUM_DOUBLE_P256K1,
       TEST_BIGNUM_DOUBLE_P384,
       TEST_BIGNUM_DOUBLE_P521,
       TEST_BIGNUM_EMONTREDC,
       TEST_BIGNUM_EMONTREDC_8N,
       TEST_BIGNUM_EQ,
       TEST_BIGNUM_EVEN,
       TEST_BIGNUM_FROMBEBYTES_4,
       TEST_BIGNUM_FROMBEBYTES_6,
       TEST_BIGNUM_FROMLEBYTES_4,
       TEST_BIGNUM_FROMLEBYTES_6,
       TEST_BIGNUM_GE,
       TEST_BIGNUM_GT,
       TEST_BIGNUM_HALF_P256,
       TEST_BIGNUM_HALF_P256K1,
       TEST_BIGNUM_HALF_P384,
       TEST_BIGNUM_HALF_P521,
       TEST_BIGNUM_ISZERO,
       TEST_BIGNUM_KMUL_16_32,
       TEST_BIGNUM_KMUL_32_64,
       TEST_BIGNUM_KSQR_16_32,
       TEST_BIGNUM_KSQR_32_64,
       TEST_BIGNUM_LE,
       TEST_BIGNUM_LITTLEENDIAN_4,
       TEST_BIGNUM_LITTLEENDIAN_6,
       TEST_BIGNUM_LT,
       TEST_BIGNUM_MADD,
       TEST_BIGNUM_MOD_N256,
       TEST_BIGNUM_MOD_N256_ALT,
       TEST_BIGNUM_MOD_N256_4,
       TEST_BIGNUM_MOD_N256K1_4,
       TEST_BIGNUM_MOD_N384,
       TEST_BIGNUM_MOD_N384_6,
       TEST_BIGNUM_MOD_N521_9,
       TEST_BIGNUM_MOD_P256_ALT,
       TEST_BIGNUM_MOD_P256,
       TEST_BIGNUM_MOD_P256_4,
       TEST_BIGNUM_MOD_P256K1_4,
       TEST_BIGNUM_MOD_P384,
       TEST_BIGNUM_MOD_P384_6,
       TEST_BIGNUM_MOD_P521_9,
       TEST_BIGNUM_MODADD,
       TEST_BIGNUM_MODDOUBLE,
       TEST_BIGNUM_MODIFIER,
       TEST_BIGNUM_MODINV,
       TEST_BIGNUM_MODOPTNEG,
       TEST_BIGNUM_MODSUB,
       TEST_BIGNUM_MONTIFIER,
       TEST_BIGNUM_MONTMUL,
       TEST_BIGNUM_MONTMUL_P256,
       TEST_BIGNUM_MONTMUL_P256_ALT,
       TEST_BIGNUM_MONTMUL_P256K1,
       TEST_BIGNUM_MONTMUL_P256K1_ALT,
       TEST_BIGNUM_MONTMUL_P384,
       TEST_BIGNUM_MONTMUL_P521,
       TEST_BIGNUM_MONTREDC,
       TEST_BIGNUM_MONTSQR,
       TEST_BIGNUM_MONTSQR_P256,
       TEST_BIGNUM_MONTSQR_P256_ALT,
       TEST_BIGNUM_MONTSQR_P256K1,
       TEST_BIGNUM_MONTSQR_P256K1_ALT,
       TEST_BIGNUM_MONTSQR_P384,
       TEST_BIGNUM_MONTSQR_P521,
       TEST_BIGNUM_MUL,
       TEST_BIGNUM_MUL_4_8,
       TEST_BIGNUM_MUL_4_8_ALT,
       TEST_BIGNUM_MUL_6_12,
       TEST_BIGNUM_MUL_8_16,
       TEST_BIGNUM_MUL_P256K1,
       TEST_BIGNUM_MUL_P256K1_ALT,
       TEST_BIGNUM_MUL_P521,
       TEST_BIGNUM_MULADD10,
       TEST_BIGNUM_MUX,
       TEST_BIGNUM_MUX_4,
       TEST_BIGNUM_MUX_6,
       TEST_BIGNUM_MUX16,
       TEST_BIGNUM_NEG_P256,
       TEST_BIGNUM_NEG_P256K1,
       TEST_BIGNUM_NEG_P384,
       TEST_BIGNUM_NEG_P521,
       TEST_BIGNUM_NEGMODINV,
       TEST_BIGNUM_NONZERO,
       TEST_BIGNUM_NONZERO_4,
       TEST_BIGNUM_NONZERO_6,
       TEST_BIGNUM_NORMALIZE,
       TEST_BIGNUM_ODD,
       TEST_BIGNUM_OF_WORD,
       TEST_BIGNUM_OPTADD,
       TEST_BIGNUM_OPTNEG,
       TEST_BIGNUM_OPTNEG_P256,
       TEST_BIGNUM_OPTNEG_P256K1,
       TEST_BIGNUM_OPTNEG_P384,
       TEST_BIGNUM_OPTNEG_P521,
       TEST_BIGNUM_OPTSUB,
       TEST_BIGNUM_OPTSUBADD,
       TEST_BIGNUM_POW2,
       TEST_BIGNUM_SHL_SMALL,
       TEST_BIGNUM_SHR_SMALL,
       TEST_BIGNUM_SQR,
       TEST_BIGNUM_SQR_4_8,
       TEST_BIGNUM_SQR_4_8_ALT,
       TEST_BIGNUM_SQR_6_12,
       TEST_BIGNUM_SQR_8_16,
       TEST_BIGNUM_SQR_P256K1,
       TEST_BIGNUM_SQR_P256K1_ALT,
       TEST_BIGNUM_SQR_P521,
       TEST_BIGNUM_SUB,
       TEST_BIGNUM_SUB_P256,
       TEST_BIGNUM_SUB_P256K1,
       TEST_BIGNUM_SUB_P384,
       TEST_BIGNUM_SUB_P521,
       TEST_BIGNUM_TOBEBYTES_4,
       TEST_BIGNUM_TOBEBYTES_6,
       TEST_BIGNUM_TOLEBYTES_4,
       TEST_BIGNUM_TOLEBYTES_6,
       TEST_BIGNUM_TOMONT_P256,
       TEST_BIGNUM_TOMONT_P256_ALT,
       TEST_BIGNUM_TOMONT_P256K1,
       TEST_BIGNUM_TOMONT_P256K1_ALT,
       TEST_BIGNUM_TOMONT_P384,
       TEST_BIGNUM_TOMONT_P521,
       TEST_BIGNUM_TRIPLE_P256,
       TEST_BIGNUM_TRIPLE_P256_ALT,
       TEST_BIGNUM_TRIPLE_P256K1,
       TEST_BIGNUM_TRIPLE_P256K1_ALT,
       TEST_BIGNUM_TRIPLE_P384,
       TEST_BIGNUM_TRIPLE_P521,
       TEST_WORD_BYTEREVERSE,
       TEST_WORD_CLZ,
       TEST_WORD_CTZ,
       TEST_WORD_MAX,
       TEST_WORD_MIN,
       TEST_WORD_NEGMODINV,
       TEST_WORD_RECIP
};

// ***************************************************************************
// Random number generation
// ***************************************************************************

// Source of random 64-bit numbers with bit density
// 0 = all zeros, 32 = "average", 64 = all ones
// Then a generic one with the density itself randomized

uint64_t random64d(int density)
{ int i;
  uint64_t r = 0, b = 0;
  for (i = 0; i < 64; i++)
   { b = ((rand() & 0x3F) < density);
     r = (r + r) + b;
   }
  return r;
}

uint64_t random64(void)
{ int d = ((unsigned) rand() & 0xFFFF) % 65;
  return random64d(d);
}

// Fill size-k bignum array with random digits, again with density option

void random_bignumd(uint64_t k,uint64_t *a,int density)
{ uint64_t i;
  for (i = 0; i < k; ++i) a[i] = random64d(density);
}

void random_bignum(uint64_t k,uint64_t *a)
{ int d = ((unsigned) rand() & 0xFFFF) % 65;
  random_bignumd(k,a,d);
}

void random_sparse_bignum(uint64_t k,uint64_t *a)
{ uint64_t i;
  int d = ((unsigned) rand() & 0xFFFF) % 65;
  for (i = 0; i < k; ++i)
   { if (((unsigned) rand() & 0xFFFF) % 100 <= 1)
       a[i] = random64d(d);
     else a[i] = 0;
   }
}

// ****************************************************************************
// Constants relevant to the P-256, P-384 and P-521 functions
// ****************************************************************************

uint64_t p_256[4] =
 { UINT64_C(0xffffffffffffffff),
   UINT64_C(0x00000000ffffffff),
   UINT64_C(0x0000000000000000),
   UINT64_C(0xffffffff00000001)
 };

uint64_t n_256[4] =
 { UINT64_C(0xf3b9cac2fc632551),
   UINT64_C(0xbce6faada7179e84),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffff00000000)
 };

uint64_t i_256[4] =
 { UINT64_C(0x0000000000000001),
   UINT64_C(0x0000000100000000),
   UINT64_C(0x0000000000000000),
   UINT64_C(0xffffffff00000002)
 };


uint64_t p_256k1[4] =
 { UINT64_C(0xfffffffefffffc2f),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff) ,
   UINT64_C(0xffffffffffffffff)
 };

uint64_t n_256k1[4] =
 { UINT64_C(0xbfd25e8cd0364141),
   UINT64_C(0xbaaedce6af48a03b),
   UINT64_C(0xfffffffffffffffe),
   UINT64_C(0xffffffffffffffff)
 };

uint64_t i_256k1[4] =
 { UINT64_C(0xd838091dd2253531),
   UINT64_C(0xbcb223fedc24a059),
   UINT64_C(0x9c46c2c295f2b761),
   UINT64_C(0xc9bd190515538399)
 };

uint64_t p_384[6] =
 { UINT64_C(0x00000000ffffffff),
   UINT64_C(0xffffffff00000000),
   UINT64_C(0xfffffffffffffffe),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff)
 };

uint64_t n_384[6] =
 { UINT64_C(0xecec196accc52973),
   UINT64_C(0x581a0db248b0a77a),
   UINT64_C(0xc7634d81f4372ddf),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff)
 };

uint64_t i_384[6] =
 { UINT64_C(0x0000000100000001),
   UINT64_C(0x0000000000000001),
   UINT64_C(0xfffffffbfffffffe),
   UINT64_C(0xfffffffcfffffffa),
   UINT64_C(0x0000000c00000002),
   UINT64_C(0x0000001400000014)
 };

uint64_t p_521[9] =
 { UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0x00000000000001ff)
 };

uint64_t i_521[9] =
 { UINT64_C(0x0000000000000001),
   UINT64_C(0x0000000000000000),
   UINT64_C(0x0000000000000000),
   UINT64_C(0x0000000000000000),
   UINT64_C(0x0000000000000000),
   UINT64_C(0x0000000000000000),
   UINT64_C(0x0000000000000000),
   UINT64_C(0x0000000000000000),
   UINT64_C(0x0000000000000200)
 };

uint64_t n_521[9] =
 { UINT64_C(0xbb6fb71e91386409),
   UINT64_C(0x3bb5c9b8899c47ae),
   UINT64_C(0x7fcc0148f709a5d0),
   UINT64_C(0x51868783bf2f966b),
   UINT64_C(0xfffffffffffffffa),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0x00000000000001ff)
 };

// ****************************************************************************
// Reference implementations, basic and stupid ones in C
// ****************************************************************************

// Some functions to do carry chains and high multiplies in C

#define hi32(x) ((x) >> 32)
#define lo32(x) ((x) & UINT64_C(0xFFFFFFFF))

uint64_t carryout2(uint64_t x,uint64_t y)
{ uint64_t z = x + y;
  return (uint64_t) ((z < x));
}

uint64_t carryout3(uint64_t x,uint64_t y,uint64_t c)
{ uint64_t w = x + y;
  return (uint64_t) (carryout2(x,y) || carryout2(w,c));
}

uint64_t borrowout2(uint64_t x,uint64_t y)
{ return (uint64_t) ((x < y));
}

uint64_t borrowout3(uint64_t x,uint64_t y,uint64_t b)
{ return (uint64_t) (b ? (x <= y) : (x < y));
}

uint64_t multop(uint64_t x,uint64_t y)
{
  uint64_t x1 = hi32(x);
  uint64_t x0 = lo32(x);
  uint64_t y1 = hi32(y);
  uint64_t y0 = lo32(y);

  uint64_t z0 = x0 * y0;
  uint64_t z1 = x0 * y1;
  uint64_t w1 = x1 * y0 + hi32(z0) + lo32(z1);
  uint64_t z2 = x1 * y1 + hi32(z1) + hi32(w1);
  return z2;
}

// Get a digit from a bignum using default of zero
// This is useful for "simple and naive" reference implementations

uint64_t digit(uint64_t k,uint64_t *a,uint64_t i)
{ if (i < k) return a[i];
  else return 0;
}

// Similarly, get fields indexed by bits

uint64_t bitword(uint64_t k,uint64_t *x,uint64_t b)
{ uint64_t bhi = b >> 6, blo = b & UINT64_C(63);
  if (blo == 0) return digit(k,x,bhi);
  return (digit(k,x,bhi)>>blo) + (digit(k,x,bhi+1) << (64 - blo));
}

uint64_t bitfield(uint64_t k,uint64_t *x,uint64_t b,uint64_t l)
{ uint64_t w = bitword(k,x,b);
  if (l >= 64) return w;
  else return bitword(k,x,b) & ((UINT64_C(1) << l) - UINT64_C(1));
}

// Other trivia on 64-bit unsigned words

uint64_t max(uint64_t x,uint64_t y)
{ if (x < y) return y; else return x;
}

uint64_t min(uint64_t x,uint64_t y)
{ if (x < y) return x; else return y;
}

#define swap(x,y) { uint64_t tmp = x; x = y; y = tmp; }

uint64_t reference_wordbytereverse(uint64_t n)
{ uint64_t n2 = ((n & UINT64_C(0xFF00FF00FF00FF00)) >> 8) |
                ((n & UINT64_C(0x00FF00FF00FF00FF)) << 8);
  uint64_t n4 = ((n2 & UINT64_C(0xFFFF0000FFFF0000)) >> 16) |
                ((n2 & UINT64_C(0x0000FFFF0000FFFF)) << 16);
  uint64_t n8 = ((n4 & UINT64_C(0xFFFFFFFF00000000)) >> 32) |
                ((n4 & UINT64_C(0x00000000FFFFFFFF)) << 32);
  return n8;
}

uint64_t reference_wordclz(uint64_t n)
{ uint64_t m, i;
  m = n;
  for (i = 0; i < 64; ++i)
   { if (m & UINT64_C(0x8000000000000000)) return i;
     m = m << 1;
   }
  return 64;
}

uint64_t reference_wordctz(uint64_t n)
{ uint64_t m, i;
  m = n;
  for (i = 0; i < 64; ++i)
   { if (m & UINT64_C(0x1)) return i;
     m = m >> 1;
   }
  return 64;
}

void reference_copy(uint64_t k,uint64_t *z,uint64_t n, uint64_t *x)
{ uint64_t i;
  for (i = 0; i < k; ++i) z[i] = digit(n,x,i);
}

void reference_of_word(uint64_t k,uint64_t *z,uint64_t n)
{ uint64_t i;
  if (k != 0)
   { z[0] = n;
     for (i = 1; i < k; ++i) z[i] = 0;
   }
}

void reference_pow2(uint64_t k,uint64_t *z,uint64_t n)
{ uint64_t i;
  for (i = 0; i < k; ++i) z[i] = 0;
  if (n < 64*k) z[n>>6] = UINT64_C(1)<<(n&UINT64_C(63));
}

uint64_t reference_iszero(uint64_t k,uint64_t *x)
{ uint64_t i;
  for (i = 0; i < k; ++i)
     if (x[i] != 0) return 0;
  return 1;
}

int reference_compare(uint64_t k1,uint64_t *a1,
                      uint64_t k2,uint64_t *a2)
{ uint64_t k = (k1 < k2) ? k2 : k1;
  uint64_t i;
  if (k == 0) return 0;
  for (i = 1; i <= k; ++i)
   { uint64_t d1 = digit(k1,a1,k - i);
     uint64_t d2 = digit(k2,a2,k - i);
     if (d1 != d2)
      { if (d1 < d2) return -1; else return 1;
      }
   }
  return 0;
}

uint64_t reference_le(uint64_t k,uint64_t *a1,uint64_t p,uint64_t *a2)
{ return reference_compare(k,a1,p,a2) <= 0;
}

uint64_t reference_eq_samelen(uint64_t k,uint64_t *a1,uint64_t *a2)
{ return reference_compare(k,a1,k,a2) == 0;
}

uint64_t reference_lt_samelen(uint64_t k,uint64_t *a1,uint64_t *a2)
{ return reference_compare(k,a1,k,a2) < 0;
}

uint64_t reference_le_samelen(uint64_t k,uint64_t *a1,uint64_t *a2)
{ return reference_compare(k,a1,k,a2) <= 0;
}

uint64_t reference_gt_samelen(uint64_t k,uint64_t *a1,uint64_t *a2)
{ return reference_compare(k,a1,k,a2) > 0;
}

uint64_t reference_ge_samelen(uint64_t k,uint64_t *a1,uint64_t *a2)
{ return reference_compare(k,a1,k,a2) >= 0;
}

uint64_t reference_adc
  (uint64_t k,uint64_t *z,
   uint64_t m,uint64_t *x,uint64_t n,uint64_t *y,uint64_t cin)
{ uint64_t c = cin;
  uint64_t i;
  for (i = 0; i < k; ++i)
   { uint64_t a = digit(m,x,i);
     uint64_t b = digit(n,y,i);
     uint64_t r = a + b + c;
     z[i] = r;
     c = carryout3(a,b,c);
   }
  return c;
}

uint64_t reference_sbb
  (uint64_t k,uint64_t *z,
   uint64_t m,uint64_t *x,uint64_t n,uint64_t *y,uint64_t cin)
{ uint64_t c = cin;
  uint64_t i;
  for (i = 0; i < k; ++i)
   { uint64_t a = digit(m,x,i);
     uint64_t b = digit(n,y,i);
     uint64_t r = a - (b + c);
     z[i] = r;
     c = borrowout3(a,b,c);
   }
  return c;
}

uint64_t reference_add_samelen
  (uint64_t k,uint64_t *z,uint64_t *x,uint64_t *y)
{ return reference_adc(k,z,k,x,k,y,0);
}

uint64_t reference_sub_samelen
  (uint64_t k,uint64_t *z,uint64_t *x,uint64_t *y)
{ return reference_sbb(k,z,k,x,k,y,0);
}

uint64_t reference_optsub
 (uint64_t k, uint64_t *z, uint64_t *x, uint64_t p, uint64_t *y)
{ if (p != 0) return reference_sbb(k,z,k,x,k,y,0);
  else { bignum_copy(k,z,k,x); return 0; }
}

uint64_t reference_ctz(uint64_t k,uint64_t *x)
{ uint64_t i;
  for (i = 0; i < 64 * k; ++i)
    if (x[i>>6] & (UINT64_C(1)<<(i&63))) return i;
  return 64*k;
}

uint64_t reference_clz(uint64_t k,uint64_t *x)
{ uint64_t i;
  for (i = 0; i < 64 * k; ++i)
    if (x[(64*k-i-1)>>6] & (UINT64_C(1)<<((64*k-i-1)&63))) return i;
  return 64*k;
}

uint64_t reference_shr_samelen(uint64_t k,uint64_t *z,uint64_t *x,uint64_t cin)
{ uint64_t c, t, i;

  c = (cin != 0);

  for (i = 1; i <= k; ++i)
   { t = x[k - i] & UINT64_C(1);
     z[k - i] = (x[k - i] >> 1) + (c << 63);
     c = t;
   }
  return c;
}

// z = a * x as a k-digit number where x is a n-digit number

void reference_cmul(uint64_t k,uint64_t *z,uint64_t a,uint64_t n,uint64_t *x)
{ uint64_t c, xi, hi, lo, i;

  c = 0;
  for (i = 0; i < k; ++i)
   { xi = (i < n ? x[i] : (uint64_t) 0);
     hi = multop(a,xi), lo = a * xi;
     z[i] = lo + c;
     c = hi + carryout2(lo,c);
   }
}

void reference_cmadd(uint64_t k,uint64_t *z,uint64_t a,uint64_t n,uint64_t *x)
{ uint64_t *temp = malloc(k * sizeof(uint64_t));
  reference_cmul(k,temp,a,n,x);
  (void) reference_adc(k,z,k,z,k,temp,0);
  free(temp);
}

void reference_cmnegadd
  (uint64_t k,uint64_t *z,uint64_t a,uint64_t n,uint64_t *x)
{ uint64_t *temp = malloc(k * sizeof(uint64_t));
  reference_cmul(k,temp,a,n,x);
  (void) reference_sbb(k,z,k,z,k,temp,0);
  free(temp);
}

void reference_shiftleft(uint64_t k,uint64_t *x,uint64_t i)
{ uint64_t j;
  if (k == 0) return;
  for (j = k; j > 0; --j)
     x[j-1] = (j-1 < i) ? 0 : x[j-1 - i];
}

void reference_madd(uint64_t k,uint64_t *z,
                    uint64_t m,uint64_t *x,
                    uint64_t n,uint64_t *y)
{ uint64_t i, km;

  km = (k < m) ? k : m;

  for (i = 0; i < km; ++i)
     reference_cmadd(k-i,z+i,x[i],n,y);
}

void reference_mul(uint64_t k,uint64_t *z,
                    uint64_t m,uint64_t *x,
                    uint64_t n,uint64_t *y)
{ uint64_t i;
  for (i = 0; i < k; ++i) z[i] = 0;
  reference_madd(k,z,m,x,n,y);
}

void reference_divmod(uint64_t k,uint64_t *q,uint64_t *r,
                      uint64_t *x,uint64_t *y)
{ uint64_t i;
  uint64_t *a;
  uint64_t b, c;
  uint64_t bit, word;

  for (i = 0; i < k; ++i) q[i] = r[i] = 0;
  if (k == 0) return;

  a = alloca(8 * (k + 1));      // Accumulator for r with extra space to double
  for (i = 0; i <= k; ++i) a[i] = 0;

  word = k;
  do
   { --word;
     bit = 64;
     do
      { --bit;
        b = (x[word] >> bit) & 1;
        reference_adc(k+1,a,k+1,a,k+1,a,b);
        c = (reference_compare(k+1,a,k,y) >= 0);
        if (c) reference_sbb(k+1,a,k+1,a,k,y,0);
        reference_adc(k,q,k,q,k,q,c);
      }
     while (bit != 0);
   }
  while (word != 0);

  for (i = 0; i < k; ++i) r[i] = a[i];
}

void reference_mod(uint64_t k,uint64_t *r,
                   uint64_t *x,uint64_t *y)
{ uint64_t *q = alloca(2 * k * sizeof(uint64_t));
  reference_divmod(k,q,r,x,y);
}

void reference_gcd(uint64_t k,uint64_t *z,uint64_t *x,uint64_t *y)
{
  uint64_t *xx = alloca(8 * k);
  uint64_t *yy = alloca(8 * k);
  reference_copy(k,xx,k,x);
  reference_copy(k,yy,k,y);

  for (;;)
   {
     if (reference_iszero(k,xx))
      { reference_copy(k,z,k,yy);
        return;
      }
     else if (reference_iszero(k,yy))
      { reference_copy(k,z,k,xx);
        return;
      }

     if (reference_lt_samelen(k,xx,yy))
      { reference_mod(k,z,yy,xx);
        reference_copy(k,yy,k,z);
      }
     else
      { reference_mod(k,z,xx,yy);
        reference_copy(k,xx,k,z);
      }
   }
}

uint64_t reference_odd(uint64_t k,uint64_t *x)
{ return (k != 0) && (x[0] & UINT64_C(1));
}

uint64_t reference_even(uint64_t k,uint64_t *x)
{ return !reference_odd(k,x);
}

void reference_oddgcd(uint64_t k,uint64_t *z,uint64_t *x,uint64_t *y)
{ uint64_t b, i;
  uint64_t *m = alloca(8 * k);
  uint64_t *n = alloca(8 * k);

  if (k == 0) return;

  reference_copy(k,m,k,x);
  reference_copy(k,n,k,y);

  for (i = 0; i < 128 * k; ++i)
   {
     b = reference_even(k,n) ||
         (reference_odd(k,m) && reference_lt_samelen(k,m,n));
     if (b) {uint64_t *t = m; m = n; n = t; } // swap pointers not contents

     b = reference_odd(k,m);
     if (b) reference_sub_samelen(k,m,m,n);

     reference_shr_samelen(k,m,m,0);
   }

  bignum_copy(k,z,k,n);
}

uint64_t reference_coprime(uint64_t k,uint64_t *x,uint64_t *y)
{ uint64_t *z = alloca(k * sizeof(uint64_t));
  uint64_t *w = alloca(k * sizeof(uint64_t));
  if (reference_even(k,x) && reference_even(k,y)) return 0;
  reference_oddgcd(k,z,x,y);
  reference_of_word(k,w,1);
  return reference_eq_samelen(k,w,z);
}

void reference_dmontmul(int k,uint64_t *z,uint64_t *x,uint64_t *y,
                       uint64_t *m,uint64_t *i,uint64_t *t)
{ uint64_t p;
  reference_mul(2 * k + 1,t,k,x,k,y);  // t = x * y
  reference_mul(k,z,k,t,k,i);      // z = ((t MOD R) * m') MOD R
  reference_madd(2 * k + 1,t,k,m,k,z);
  p = reference_le(k,m,k+1,t+k);
  reference_optsub(k,z,t+k,p,m);
}

void reference_modpowtwo(uint64_t k,uint64_t *z,uint64_t n, uint64_t *m)
{ uint64_t i, p, c;
  reference_of_word(k,z,0);
  for (i = 0; i <= n; ++i)
   { c = (i == 0) ? 1 : 0;
     c = reference_adc(k,z,k,z,k,z,c);
     p = reference_le_samelen(k,m,z);
     reference_optsub(k,z,z,(c|p),m);
   }
}

uint64_t reference_wordnegmodinv(uint64_t a)
{ uint64_t x = (a - (a<<2))^2;
  uint64_t e = a * x + 1;
  x = e * x + x; e = e * e;
  x = e * x + x; e = e * e;
  x = e * x + x; e = e * e;
  x = e * x + x;
  return x;
}

void reference_negmodinv(uint64_t k,uint64_t *x,uint64_t *a)
{ uint64_t *y = alloca(k * sizeof(uint64_t));
  uint64_t i, b, b2;

  if (k == 0) return;

  x[0] = reference_wordnegmodinv(a[0]);
  for (i = 1; i < k; ++i) x[i] = 0;
  b = 1;

  while (b < k)
   { b2 = 2 * b; if (b2 > k) b2 = k;            // b2 = min(2 * b,k)

     y[0] = 1; for (i = 1; i < b2; ++i) y[i] = 0; // y = 1
     reference_madd(b2,y,b2,a,b,x);               // y = a * x + 1 (length b2)
     reference_madd(b2-b,x+b,b,x,b2-b,y+b);     // x' = x + x * y = x * (1 + y)

     b = b2;
   }
}

void reference_bigendian(uint64_t k,uint64_t *z,uint64_t *x)
{ uint64_t i;

  for (i = 0; i < k; ++i)
   { z[k-(i+1)] =
     (((uint64_t) (((uint8_t *) x)[8*i])) << 56) +
     (((uint64_t) (((uint8_t *) x)[8*i+1])) << 48) +
     (((uint64_t) (((uint8_t *) x)[8*i+2])) << 40) +
     (((uint64_t) (((uint8_t *) x)[8*i+3])) << 32) +
     (((uint64_t) (((uint8_t *) x)[8*i+4])) << 24) +
     (((uint64_t) (((uint8_t *) x)[8*i+5])) << 16) +
     (((uint64_t) (((uint8_t *) x)[8*i+6])) << 8) +
     (((uint64_t) (((uint8_t *) x)[8*i+7])) << 0);
   }
}

void reference_littleendian(uint64_t k,uint64_t *z,uint64_t *x)
{ uint64_t i;

  for (i = 0; i < k; ++i)
   { z[i] =
     (((uint64_t) (((uint8_t *) x)[8*i+7])) << 56) +
     (((uint64_t) (((uint8_t *) x)[8*i+6])) << 48) +
     (((uint64_t) (((uint8_t *) x)[8*i+5])) << 40) +
     (((uint64_t) (((uint8_t *) x)[8*i+4])) << 32) +
     (((uint64_t) (((uint8_t *) x)[8*i+3])) << 24) +
     (((uint64_t) (((uint8_t *) x)[8*i+2])) << 16) +
     (((uint64_t) (((uint8_t *) x)[8*i+1])) << 8) +
     (((uint64_t) (((uint8_t *) x)[8*i])) << 0);
   }
}

// ****************************************************************************
// Testing functions
// ****************************************************************************

int test_bignum_add(void)
{ uint64_t t, j, k0, k1, k2;
  printf("Testing bignum_add with %d cases\n",tests);
  uint64_t c, c1, c2;
  for (t = 0; t < tests; ++t)
   { k0 = (unsigned) rand() % MAXSIZE;
     k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k0,b0);
     random_bignum(k1,b1);
     random_bignum(k2,b2);
     for (j = 0; j < k2; ++j) b3[j] = b2[j];
     c1 = bignum_add(k2,b2,k0,b0,k1,b1);
     c2 = reference_adc(k2,b3,k0,b0,k1,b1,0);
     c = reference_compare(k2,b2,k2,b3);
     if ((c != 0) || (c1 != c2))
      { printf("### Disparity: [sizes %4"PRIu64" := %4"PRIu64" + %4"PRIu64"] "
               "...0x%016"PRIx64" + ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k0,k1,b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k0 == 0 || k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" := %4"PRIu64" + %4"PRIu64"]\n",k2,k0,k1);
        else printf("OK: [sizes %4"PRIu64" := %4"PRIu64" + %4"PRIu64"] ...0x%016"PRIx64" + ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k2,k0,k1,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_add_p256(void)
{ uint64_t i, k;
  printf("Testing bignum_add_p256 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_256);
     bignum_add_p256(b2,b0,b1);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_256);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_256[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_256[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_add_p256k1(void)
{ uint64_t i, k;
  printf("Testing bignum_add_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256k1);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_256k1);
     bignum_add_p256k1(b2,b0,b1);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_256k1);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_add_p384(void)
{ uint64_t i, k;
  printf("Testing bignum_add_p384 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_384);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_384);
     bignum_add_p384(b2,b0,b1);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_384);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_384[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_384[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_add_p521(void)
{ uint64_t i, k;
  printf("Testing bignum_add_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_521);
     bignum_add_p521(b2,b0,b1);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_521);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_521[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_521[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_amontifier(void)
{ uint64_t i, k, c;
  printf("Testing bignum_amontifier with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0); b0[0] |= 1;

     bignum_amontifier(k,b1,b0,b7); // b1 = test fun
     reference_mod(k,b2,b1,b0);        // b2 = Fully reduced modulo for comparison

     reference_modpowtwo(k,b3,128*k,b0); /// Naive regerence

     c = reference_compare(k,b2,k,b3);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
           "bignum_amontifier(...0x%016"PRIx64") = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
            k,b0[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_amontifier(...0x%016"PRIx64") =..0x%016"PRIx64"\n",
                    k,b0[0],b1[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_amontmul(void)
{ uint64_t t, k;
  printf("Testing bignum_amontmul with %d cases\n",tests);
  int c = 0;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0); b0[0] |= 1; // b0 = m
     random_bignum(k,b1);             // b1 = x
     random_bignum(k,b2);             // b2 = y
     reference_mul(2 * k,b3,k,b1,k,b2);  // b3 = z = x * y
     reference_negmodinv(k,b4,b0);    // b4 = m' = negmodinv(m)
     bignum_amontmul(k,b6,b1,b2,b0);        // b6 = output of function

     reference_mod(k,b5,b6,b0);                // b5 = full modulus for comparison
     reference_copy(k,b7,k,b1); reference_mod(k,b1,b7,b0);
     reference_copy(k,b7,k,b2); reference_mod(k,b2,b7,b0);
     reference_dmontmul(k,b3,b1,b2,b0,b4,b8);   // b3 = "reference" Montgomery

     c = reference_compare(k,b3,k,b5);
     if (c != 0)
      { printf("### Disparity (Montgomery mul): [size %4"PRIu64"]\n",k);
        printf("### Output is ...0x%016"PRIx64"\n",b5[0]);
        printf("### Reference ...0x%016"PRIx64"\n",b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_amontmul(...0x%016"PRIx64",...0x%016"PRIx64") wrt ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k,b1[0],b2[0],b0[0],b6[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_amontredc(void)
{ uint64_t t, k, n, p, r;
  printf("Testing bignum_amontredc with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     n = (unsigned) rand() % MAXSIZE;
     p = (unsigned) rand() % MAXSIZE;

     random_bignum(k,b0); b0[0] |= 1;  // b0 = m
     random_bignum(n,b1);              // b1 = x

     bignum_amontredc(k,b4,n,b1,b0,p); // b4 = test function

     r = max(p+k,n);

     reference_pow2(r,b2,64*p);            // b2 = 2^{64p}
     reference_mul(r,b3,r,b2,k,b4);        // b3 = 2^{64p} * z
     reference_copy(r,b2,min(n,p+k),b1);   // b2 = x' (truncated x)
     reference_copy(r,b5,k,b0);            // b5 = m
     reference_mod(r,b6,b2,b5);            // b6 = x mod m
     reference_mod(r,b7,b3,b5);            // b7 = (2^{64p} * z) mod m
     c = ((k != 0) && reference_compare(r,b6,r,b7));
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "...%016"PRIx64" / 2^%"PRIu64" mod ...%016"PRIx64" = ...%016"PRIx64"\n",
               n,k,b1[0],64*p,b0[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] "
               "...%016"PRIx64" / 2^%"PRIu64" mod ...%016"PRIx64" = ...%016"PRIx64"\n",
               n,k,b1[0],64*p,b0[0],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_amontsqr(void)
{ uint64_t t, k;
  printf("Testing bignum_amontsqr with %d cases\n",tests);
  int c = 0;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0); b0[0] |= 1; // b0 = m
     random_bignum(k,b1);             // b1 = x
     reference_copy(k,b2,k,b1);          // b2 = y = x in squaring case
     reference_mul(2 * k,b3,k,b1,k,b2);  // b3 = z = x * y
     reference_negmodinv(k,b4,b0);    // b4 = m' = negmodinv(m)
     bignum_amontsqr(k,b6,b1,b0);        // b6 = output of function

     reference_mod(k,b5,b6,b0);                // b5 = full modulus for comparison
     reference_copy(k,b7,k,b1); reference_mod(k,b1,b7,b0);
     reference_copy(k,b7,k,b2); reference_mod(k,b2,b7,b0);
     reference_dmontmul(k,b3,b1,b2,b0,b4,b8);   // b3 = "reference" Montgomery

     c = reference_compare(k,b3,k,b5);
     if (c != 0)
      { printf("### Disparity (Montgomery sqr): [size %4"PRIu64"]\n",k);
        printf("### Output is ...0x%016"PRIx64"\n",b5[0]);
        printf("### Reference ...0x%016"PRIx64"\n",b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_amontsqr(...0x%016"PRIx64") wrt ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k,b1[0],b0[0],b6[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_bigendian_4(void)
{ uint64_t t;
  printf("Testing bignum_bigendian_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_bigendian(4,b3,b0);
     bignum_bigendian_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_bigendian_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_bigendian_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_bigendian_6(void)
{ uint64_t t;
  printf("Testing bignum_bigendian_6 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     reference_bigendian(6,b3,b0);
     bignum_bigendian_6(b4,b0);
     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_bigendian_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_bigendian_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_bitfield(void)
{ uint64_t t, k, n, l;
  printf("Testing bignum_bitfield with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     n = random64();
     l = random64() % UINT64_C(68);
     if (rand() & 3) n %= (64 * k + 1);
     if ((k > 0) && (rand() & 3) == 0) n = 64 * (k - 1) + (rand() % 130);
     c1 = bignum_bitfield(k,b0,n,l);
     c2 = bitfield(k,b0,n,l);
     if (c1 != c2)
      { printf(
          "### Disparity: [size %4"PRIu64"] bignum_bitfield(...0x%016"PRIx64",%"PRIu64",%"PRIu64") = 0x%016"PRIx64" not 0x%016"PRIx64"\n",
          k,b0[0],n,l,c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_bitfield(...0x%016"PRIx64",%"PRIu64",%"PRIu64") = 0x%016"PRIx64"\n",
                    k,b0[0],n,l,c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_bitsize(void)
{ uint64_t t, k;
  printf("Testing bignum_bitsize with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     if (rand() & 1) random_sparse_bignum(k,b0); else random_bignum(k,b0);
     c1 = bignum_bitsize(k,b0);
     c2 = 64 * k - reference_clz(k,b0);
     if (c1 != c2)
      { printf(
          "### Disparity: [size %4"PRIu64"] bignum_bitsize(0x%016"PRIx64"...) = %"PRIu64" not %"PRIu64"\n",
          k,b0[k-1],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_bitsize(0x%016"PRIx64"...) = %"PRIu64"\n",
                    k,b0[k-1],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cdiv(void)
{ uint64_t t, j1, j2, k1, k2, k, m, r, s;
  printf("Testing bignum_cdiv with %d cases\n",tests);
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     m = random64(); if (m == 0) m = (rand() & 31) + 1;
     random_bignum(k1,b1);
     k = max(k1,k2);
     bignum_copy(k,b3,k1,b1);
     bignum_of_word(k,b4,m);
     reference_divmod(k,b5,b6,b3,b4);
     reference_copy(k2,b3,k,b5);
     s = (k == 0) ? 0 : b6[0];
     r = bignum_cdiv(k2,b4,k1,b1,m);
     j1 = (k1 == 0) ? 0 : k1-1;
     j2 = (k2 == 0) ? 0 : k2-1;
     if (reference_compare(k2,b3,k2,b4) != 0)
      { printf("### Disparity in quotient: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" div %"PRIu64" = "
               "0x%016"PRIx64"...%016"PRIx64" rem %"PRIu64" not 0x%016"PRIx64"...%016"PRIx64" rem %"PRIu64"\n",
               k2,b1[j1],b1[0],m,b4[j2],b4[0],r,b3[j2],b3[0],s);
        return 1;
      }
     if (r != s)
      { printf("### Disparity in modulus: [sizes %4"PRIu64" := %4"PRIu64" / 1] "
               "0x%016"PRIx64"...%016"PRIx64" mod %"PRIu64" = "
               "%"PRIu64" not %"PRIu64"\n",
               k2,k1,b1[j1],b1[0],m,r,s);
        return 1;
     }
     else if (VERBOSE)
      { if (k2 == 0) printf("OK: [sizes %4"PRIu64" := %4"PRIu64" / 1]\n",k2,k1);
        else printf("OK: [sizes %4"PRIu64" := %4"PRIu64" / 1]  0x%016"PRIx64"...0x%016"PRIx64" / 0x%016"PRIx64" = "
                    "0x%016"PRIx64"...0x%016"PRIx64" rem %"PRIu64"\n",
                    k2,k1,b1[j1],b1[0],m,b4[j2],b4[0],r);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cdiv_exact(void)
{ uint64_t t, j1, j2, k1, k2, k, m;
  printf("Testing bignum_cdiv_exact with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     m = random64(); if (m == 0) m = (rand() & 31) + 1;
     random_bignum(k2,b2);
     if (k1 >= 2)
      { random_bignum(k1-1,b3);
        reference_cmul(k1,b1,m,k1-1,b3);
      }
     else if (k1 == 1)
      { b1[0] = random64();
        b1[0] -= b1[0] % m;
      }
     bignum_cdiv_exact(k2,b2,k1,b1,m);
     k = max(k1,k2);
     bignum_copy(k,b3,k1,b1);
     bignum_of_word(k,b4,m);
     reference_divmod(k,b5,b6,b3,b4);
     reference_copy(k2,b3,k,b5);
     c = reference_compare(k2,b2,k2,b3);
     j1 = (k1 == 0) ? 0 : k1-1;
     j2 = (k2 == 0) ? 0 : k2-1;
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" := %4"PRIu64" / 1] "
               "0x%016"PRIx64"...0x%016"PRIx64" / 0x%016"PRIx64" = 0x%016"PRIx64"....0x%016"PRIx64" not 0x%016"PRIx64"...0x%016"PRIx64"\n",
               k2,k1,b1[j1],b1[0],m,b2[j2],b2[0],b3[j2],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k2 == 0) printf("OK: [sizes %4"PRIu64" := %4"PRIu64" / 1]\n",k2,k1);
        else printf("OK: [sizes %4"PRIu64" := %4"PRIu64" / 1]  0x%016"PRIx64"...0x%016"PRIx64" / 0x%016"PRIx64" =  0x%016"PRIx64"...0x%016"PRIx64"\n",
                    k2,k1,b1[j1],b1[0],m,b2[j2],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cld(void)
{ uint64_t t, k;
  printf("Testing bignum_cld with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     if (rand() & 1) random_sparse_bignum(k,b0); else random_bignum(k,b0);
     c1 = bignum_cld(k,b0);
     c2 = reference_clz(k,b0) >> 6;
     if (c1 != c2)
      { printf(
          "### Disparity: [size %4"PRIu64"] bignum_cld(0x%016"PRIx64"...) = %"PRIu64" not %"PRIu64"\n",
          k,b0[k-1],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_cld(0x%016"PRIx64"...) = %"PRIu64"\n",
                    k,b0[k-1],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_clz(void)
{ uint64_t t, k;
  printf("Testing bignum_clz with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     if (rand() & 1) random_sparse_bignum(k,b0); else random_bignum(k,b0);
     c1 = bignum_clz(k,b0);
     c2 = reference_clz(k,b0);
     if (c1 != c2)
      { printf(
          "### Disparity: [size %4"PRIu64"] bignum_clz(0x%016"PRIx64"...) = %"PRIu64" not %"PRIu64"\n",
          k,b0[k-1],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_clz(0x%016"PRIx64"...) = %"PRIu64"\n",
                    k,b0[k-1],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmadd(void)
{ uint64_t t, k1, k2, a;
  printf("Testing bignum_cmadd with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     a = random64();
     random_bignum(k1,b1);
     random_bignum(k2,b2);
     reference_copy(k2,b3,k2,b2);
     bignum_cmadd(k2,b2,a,k1,b1);
     reference_cmadd(k2,b3,a,k1,b1);
     c = reference_compare(k2,b2,k2,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" := 1 * %4"PRIu64"] "
               "0x%016"PRIx64" * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k1,a,b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k2 == 0) printf("OK: [sizes %4"PRIu64" := 1 * %4"PRIu64"]\n",k2,k1);
        else printf("OK: [sizes %4"PRIu64" := 1 * %4"PRIu64"] 0x%016"PRIx64" * ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k2,k1,a,b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmnegadd(void)
{ uint64_t t, k1, k2, a;
  printf("Testing bignum_cmnegadd with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     a = random64();
     random_bignum(k1,b1);
     random_bignum(k2,b2);
     bignum_copy(k2,b3,k2,b2);
     bignum_cmnegadd(k2,b2,a,k1,b1);
     reference_cmnegadd(k2,b3,a,k1,b1);
     c = reference_compare(k2,b2,k2,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" := 1 * %4"PRIu64"] "
               "0x%016"PRIx64" * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k1,a,b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k2 == 0) printf("OK: [sizes %4"PRIu64" := 1 * %4"PRIu64"]\n",k2,k1);
        else printf("OK: [sizes %4"PRIu64" := 1 * %4"PRIu64"] 0x%016"PRIx64" * ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k2,k1,a,b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmod(void)
{ uint64_t t, k, r, j, m;
  printf("Testing bignum_cmod with %d cases\n",tests);
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     m = random64();
     if (m == 0) m += (1ull<<(rand() % 64));
     r = bignum_cmod(k,b0,m);
     bignum_copy(k+2,b1,k,b0);
     bignum_of_word(k+2,b2,m);
     reference_divmod(k+2,b4,b3,b1,b2); // b3 = x mod m

     j = (k == 0) ? 0 : k-1;
     if (r != b3[0])
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod %"PRIu64" = %"PRIu64" not %"PRIu64"\n",
               k,b0[j],b0[0],m,r,b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod %"PRIu64" = %"PRIu64"\n",
               k,b0[j],b0[0],m,r);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmul(void)
{ uint64_t t, j, k1, k2, a;
  printf("Testing bignum_cmul with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     a = random64();
     random_bignum(k1,b1);
     random_bignum(k2,b2);
     for (j = 0; j < k2; ++j) b3[j] = b2[j] + 1;
     bignum_cmul(k2,b2,a,k1,b1);
     reference_cmul(k2,b3,a,k1,b1);
     c = reference_compare(k2,b2,k2,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" := 1 * %4"PRIu64"] "
               "0x%016"PRIx64" * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k1,a,b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k2 == 0) printf("OK: [sizes %4"PRIu64" := 1 * %4"PRIu64"]\n",k2,k1);
        else printf("OK: [sizes %4"PRIu64" := 1 * %4"PRIu64"] 0x%016"PRIx64" * ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k2,k1,a,b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmul_p256(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p256 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256);
     m = random64();
     bignum_cmul_p256(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_256);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_256[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_256[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmul_p256_alt(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p256_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256);
     m = random64();
     bignum_cmul_p256_alt(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_256);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_256[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_256[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmul_p256k1(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256k1);
     m = random64();
     bignum_cmul_p256k1(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_256k1);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmul_p256k1_alt(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p256k1_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256k1);
     m = random64();
     bignum_cmul_p256k1_alt(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_256k1);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmul_p384(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p384 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_384);
     m = random64();
     bignum_cmul_p384(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_384);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_384[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_384[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmul_p521(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     m = random64();
     bignum_cmul_p521(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_521);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_521[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_521[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_coprime(void)
{ uint64_t i, k0, k1, kmin, kmax, c1, c2;
  printf("Testing bignum_coprime with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { k0 = (unsigned) rand() % MAXSIZE;
     k1 = (unsigned) rand() % MAXSIZE;
     kmin = (k0 < k1) ? k0 : k1;
     kmax = (k0 < k1) ? k1 : k0;
     if (rand() & 1)
      { random_bignum(k0,b0);
        random_bignum(k1,b1);
      }
     else
      { random_bignum(k0/2,b2);
        random_bignum(k1/2,b3);
        random_bignum(kmin/2,b4);
        reference_mul(k0,b0,k0/2,b2,kmin/2,b4);
        reference_mul(k1,b1,k1/2,b3,kmin/2,b4);
      }
     reference_copy(kmax,b4,k0,b0);
     reference_copy(kmax,b5,k1,b1);
     c1 = bignum_coprime(k0,b0,k1,b1,b7);
     c2 = reference_coprime(kmax,b4,b5);
     if (c1 != c2)
      { printf("### Disparity: [sizes %4"PRIu64", %4"PRIu64"] "
               "coprime(...0x%016"PRIx64", ...0x%016"PRIx64") = %4"PRIu64" not %4"PRIu64"\n",
               k0,k1,b0[0],b1[0],c1,c2);
        return 1;

      }
     else if (VERBOSE)
      { if (kmax == 0) printf("OK: [sizes %4"PRIu64", %4"PRIu64"]\n",k0, k1);
        else printf
         ("OK: [size %4"PRIu64", %4"PRIu64"] coprime(...0x%016"PRIx64" , ...0x%016"PRIx64") = %4"PRIu64"\n",
            k0,k1,b0[0],b1[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_copy(void)
{ uint64_t t, k1, k2, d;
  printf("Testing bignum_copy with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k1,b0);
     random_bignum(k2,b1);
     b0[k1] = d = random64();
     bignum_copy(k1,b0,k2,b1);
     c = (k2 <= k1) ? reference_compare(k1,b0,k2,b1)
                    : reference_compare(k1,b0,k1,b1);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" := %4"PRIu64"] "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k1,k2,b0[0],b1[0]);
        return 1;
      }
     else if (b0[k1] != d)
      { printf("### Disparity: [sizes %4"PRIu64" := %4"PRIu64"]: writes off end\n",k1,k2);
        return 1;
      }
     else if (VERBOSE)
      { if (k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" := %4"PRIu64"]\n",k1,k2);
        else printf("OK: [sizes %4"PRIu64" := %4"PRIu64"] "
                    "....0x%016"PRIx64" = ...0x%016"PRIx64"\n",
               k1,k2,b0[0],b1[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_ctd(void)
{ uint64_t t, k;
  printf("Testing bignum_ctd with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     if (rand() & 1) random_sparse_bignum(k,b0); else random_bignum(k,b0);
     c1 = bignum_ctd(k,b0);
     c2 = reference_ctz(k,b0) >> 6;
     if (c1 != c2)
      { printf(
          "### Disparity: [size %4"PRIu64"] bignum_ctd(...0x%016"PRIx64") = %"PRIu64" not %"PRIu64"\n",
          k,b0[0],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_ctd(...0x%016"PRIx64") = %"PRIu64"\n",
                    k,b0[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_ctz(void)
{ uint64_t t, k;
  printf("Testing bignum_ctz with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     if (rand() & 1) random_sparse_bignum(k,b0); else random_bignum(k,b0);
     c1 = bignum_ctz(k,b0);
     c2 = reference_ctz(k,b0);
     if (c1 != c2)
      { printf(
          "### Disparity: [size %4"PRIu64"] bignum_ctz(...0x%016"PRIx64") = %"PRIu64" not %"PRIu64"\n",
          k,b0[0],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_ctz(...0x%016"PRIx64") = %"PRIu64"\n",
                    k,b0[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_deamont_p256(void)
{ uint64_t t;
  printf("Testing bignum_deamont_p256 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     bignum_deamont_p256(b4,b0);
     reference_of_word(4,b1,UINT64_C(1));
     reference_dmontmul(4,b3,b0,b1,p_256,i_256,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_deamont_p256_alt(void)
{ uint64_t t;
  printf("Testing bignum_deamont_p256_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     bignum_deamont_p256_alt(b4,b0);
     reference_of_word(4,b1,UINT64_C(1));
     reference_dmontmul(4,b3,b0,b1,p_256,i_256,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_deamont_p256k1(void)
{ uint64_t t;
  printf("Testing bignum_deamont_p256k1 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     bignum_deamont_p256k1(b4,b0);
     reference_of_word(4,b1,UINT64_C(1));
     reference_dmontmul(4,b3,b0,b1,p_256k1,i_256k1,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_deamont_p384(void)
{ uint64_t t;
  printf("Testing bignum_deamont_p384 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     bignum_deamont_p384(b4,b0);
     reference_of_word(6,b1,UINT64_C(1));
     reference_dmontmul(6,b3,b0,b1,p_384,i_384,b5);

     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-384 * ...0x%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-384 * ...0x%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_deamont_p521(void)
{ uint64_t t;
  printf("Testing bignum_deamont_p521 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b0);
     bignum_deamont_p521(b4,b0);
     reference_of_word(9,b1,UINT64_C(1));
     reference_dmontmul(9,b3,b0,b1,p_521,i_521,b5);

     c = reference_compare(9,b3,9,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-576 * ...0x%016"PRIx64" mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[0],b4[8],b4[0],b3[8],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-576 * ...0x%016"PRIx64" mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[0],b4[8],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_demont(void)
{ uint64_t t, k;
  printf("Testing bignum_demont with %d cases\n",tests);
  int c = 0;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0); b0[0] |= 1; // b0 = m
     random_bignum(k,b1);             // b1 = raw x
     reference_copy(k,b2,k,b1);          // b2 = y = x in redc case
     reference_copy(2 * k,b3,k,b1);      // b3 = x as well, just reduction here
     reference_negmodinv(k,b4,b0);    // b4 = m' = negmodinv(m)
     bignum_demont(k,b5,b1,b0);        // b5 = output of function
     reference_copy(k,b7,k,b1);
     reference_of_word(k,b2,UINT64_C(1));

     reference_dmontmul(k,b3,b1,b2,b0,b4,b8);   // b3 = "reference" Montgomery

     c = reference_compare(k,b3,k,b5);
     if (c != 0)
      { printf("### Disparity (Montgomery redc): [size %4"PRIu64"]\n",k);
        printf("### Output is ...0x%016"PRIx64"\n",b5[0]);
        printf("### Reference ...0x%016"PRIx64"\n",b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_demont(...0x%016"PRIx64") wrt ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k,b1[0],b0[0],b5[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_demont_p256(void)
{ uint64_t t;
  printf("Testing bignum_demont_p256 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256);
     bignum_demont_p256(b4,b0);
     reference_of_word(4,b1,UINT64_C(1));
     reference_dmontmul(4,b3,b0,b1,p_256,i_256,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_demont_p256_alt(void)
{ uint64_t t;
  printf("Testing bignum_demont_p256_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256);
     bignum_demont_p256_alt(b4,b0);
     reference_of_word(4,b1,UINT64_C(1));
     reference_dmontmul(4,b3,b0,b1,p_256,i_256,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_demont_p256k1(void)
{ uint64_t t;
  printf("Testing bignum_demont_p256k1 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256k1);
     bignum_demont_p256k1(b4,b0);
     reference_of_word(4,b1,UINT64_C(1));
     reference_dmontmul(4,b3,b0,b1,p_256k1,i_256k1,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_demont_p384(void)
{ uint64_t t;
  printf("Testing bignum_demont_p384 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b2);
     reference_mod(6,b0,b2,p_384);
     bignum_demont_p384(b4,b0);
     reference_of_word(6,b1,UINT64_C(1));
     reference_dmontmul(6,b3,b0,b1,p_384,i_384,b5);

     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-384 * ...0x%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-384 * ...0x%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_demont_p521(void)
{ uint64_t t;
  printf("Testing bignum_demont_p521 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b2);
     reference_mod(9,b0,b2,p_521);
     bignum_demont_p521(b4,b0);
     reference_of_word(9,b1,UINT64_C(1));
     reference_dmontmul(9,b3,b0,b1,p_521,i_521,b5);

     c = reference_compare(9,b3,9,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-576 * ...0x%016"PRIx64" mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[8],b4[0],b3[8],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-576 * ...0x%016"PRIx64" mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[8],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_digit(void)
{ uint64_t t, k, n;
  printf("Testing bignum_digit with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     n = random64();
     if (rand() & 3) n %= (k + 1);
     c1 = bignum_digit(k,b0,n);
     c2 = digit(k,b0,n);
     if (c1 != c2)
      { printf(
          "### Disparity: [size %4"PRIu64"] bignum_digit(...0x%016"PRIx64",%"PRIu64") = 0x%016"PRIx64" not 0x%016"PRIx64"\n",
          k,b0[0],n,c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_digit(...0x%016"PRIx64",%"PRIu64") = 0x%016"PRIx64"\n",
                    k,b0[0],n,c1);
      }
   }
  printf("All OK\n");
  return 0;
}


int test_bignum_digitsize(void)
{ uint64_t t, k;
  printf("Testing bignum_digitsize with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     if (rand() & 1) random_sparse_bignum(k,b0); else random_bignum(k,b0);
     c1 = bignum_digitsize(k,b0);
     c2 = ((64 * k + 63) - reference_clz(k,b0)) / 64;
     if (c1 != c2)
      { printf(
          "### Disparity: [size %4"PRIu64"] bignum_digitsize(0x%016"PRIx64"...) = %"PRIu64" not %"PRIu64"\n",
          k,b0[k-1],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_digitsize(0x%016"PRIx64"...) = %"PRIu64"\n",
                    k,b0[k-1],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_divmod10(void)
{ uint64_t t, k, r, d, j, s;
  printf("Testing bignum_divmod10 with %d cases\n",tests);
  d = 10;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b4,k,b0);
     reference_of_word(k,b1,d);
     reference_divmod(k,b3,b2,b0,b1);
     r = bignum_divmod10(k,b4);
     s = (k == 0) ? 0 : b2[0];
     j = (k == 0) ? 0 : k - 1;
    if (reference_compare(k,b3,k,b4) != 0)
      { printf("### Disparity in quotient: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" div %"PRIu64" = "
               "0x%016"PRIx64"...%016"PRIx64" rem %"PRIu64" not 0x%016"PRIx64"...%016"PRIx64" rem %"PRIu64"\n",
               k,b0[j],b0[0],d,b4[j],b4[0],r,b3[j],b3[0],s);
        return 1;
      }
     else if (r != s)
      { printf("### Disparity in modulus: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod %"PRIu64" = "
               "%"PRIu64" not %"PRIu64"\n",
               k,b0[j],b0[0],d,r,b2[0]);
        return 1;
     }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" div %"PRIu64" = "
               "0x%016"PRIx64"...%016"PRIx64", remainder %"PRIu64"\n",
               k,b0[j],b0[0],d,b4[j],b4[0],r);
      }
   }

  printf("All OK\n");
  return 0;
}

int test_bignum_double_p256(void)
{ uint64_t i, k;
  printf("Testing bignum_double_p256 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256);
     bignum_double_p256(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_256);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_256[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_double_p256k1(void)
{ uint64_t i, k;
  printf("Testing bignum_double_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256k1);
     bignum_double_p256k1(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_256k1);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_double_p384(void)
{ uint64_t i, k;
  printf("Testing bignum_double_p384 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_384);
     bignum_double_p384(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_384);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_384[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_384[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_double_p521(void)
{ uint64_t i, k;
  printf("Testing bignum_double_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     bignum_double_p521(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_521);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_521[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_521[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_emontredc(void)
{ uint64_t t, k, w, tc;
  printf("Testing bignum_emontredc with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;

     random_bignum(k,b0); b0[0] |= 1;   // b0 = m
     w = word_negmodinv(b0[0]);         // w = negated modular inverse
     random_bignum(2*k,b4);             // b4 = initial z

     reference_copy(2*k+1,b1,2*k,b4);      // b1 = longer copy of z_0
     reference_copy(2*k+1,b2,2*k,b4);      // b2 = also longer copy of z_0

     tc = bignum_emontredc(k,b4,b0,w);

     reference_madd(2*k+1,b1,k,b4,k,b0);   // b1 = q * m + z_0

     c = ((b1[2*k] == tc) &&
          reference_eq_samelen(k,b4+k,b1+k) &&
          reference_iszero(k,b1));

     if (!c)
      { printf("### Disparity reducing modulo: [size %4"PRIu64" -> %4"PRIu64"] "
               "...%016"PRIx64" / 2^%"PRIu64" mod ...%016"PRIx64" = ...%016"PRIx64"\n",
               2*k,k,b2[0],64*k,b0[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] "
               "...%016"PRIx64" / 2^%"PRIu64" mod ...%016"PRIx64" = ...%016"PRIx64"\n",
               2*k,k,b2[0],64*k,b0[0],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_emontredc_8n(void)
{ uint64_t t, k, w, tc;
  printf("Testing bignum_emontredc_8n with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     k = (k>>3)<<3;
     if (k == 0) k = 8;

     random_bignum(k,b0); b0[0] |= 1;   // b0 = m
     w = word_negmodinv(b0[0]);         // w = negated modular inverse
     random_bignum(2*k,b4);             // b4 = initial z

     reference_copy(2*k+1,b1,2*k,b4);      // b1 = longer copy of z_0
     reference_copy(2*k+1,b2,2*k,b4);      // b2 = also longer copy of z_0

     tc = bignum_emontredc_8n(k,b4,b0,w);

     reference_madd(2*k+1,b1,k,b4,k,b0);   // b1 = q * m + z_0

     c = ((b1[2*k] == tc) &&
          reference_eq_samelen(k,b4+k,b1+k) &&
          reference_iszero(k,b1));

     if (!c)
      { printf("### Disparity reducing modulo: [size %4"PRIu64" -> %4"PRIu64"] "
               "...%016"PRIx64" / 2^%"PRIu64" mod ...%016"PRIx64" = ...%016"PRIx64"\n",
               2*k,k,b2[0],64*k,b0[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] "
               "...%016"PRIx64" / 2^%"PRIu64" mod ...%016"PRIx64" = ...%016"PRIx64"\n",
               2*k,k,b2[0],64*k,b0[0],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}


int test_bignum_eq(void)
{ uint64_t t, k1, k2;
  printf("Testing bignum_eq with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k1,b0);
     random_bignum(k2,b1);
     if (rand() % 16 == 0) reference_copy(k1,b0,k2,b1);
     if (rand() % 16 == 0) reference_copy(k2,b1,k1,b0);
     if ((rand() % 16 == 0) && (k1 != 0)) ++b0[rand() % k1];
     if ((rand() % 16 == 0) && (k1 != 0)) --b0[rand() % k1];
     if ((rand() % 16 == 0) && (k2 != 0)) ++b1[rand() % k2];
     if ((rand() % 16 == 0) && (k2 != 0)) --b1[rand() % k2];
     c1 = bignum_eq(k1,b0,k2,b1);
     c2 = (reference_compare(k1,b0,k2,b1) == 0);
     if (c1 != c2)
      { printf("### Disparity: [sizes %4"PRIu64" == %4"PRIu64"] ...0x%016"PRIx64" == ...0x%016"PRIx64" <=> %"PRIx64" not %"PRIx64"\n",
               k1,k2,b0[0],b1[0],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" == %4"PRIu64" ]\n",k1,k2);
        else printf("OK: [sizes %4"PRIu64" == %4"PRIu64"] ...0x%016"PRIx64" == ...0x%016"PRIx64" <=> %"PRIx64"\n",
                    k1,k2,b0[0],b1[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_even(void)
{ uint64_t t, k;
  printf("Testing bignum_even with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     c1 = bignum_even(k,b0);
     c2 = !((k != 0) && (b0[0] & 1));
     if (c1 != c2)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_even(...0x%016"PRIx64") = %"PRIx64" not %"PRIx64"\n",
               k,b0[0],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK:[size %4"PRIu64"] "
               "bignum_even(...0x%016"PRIx64") = %"PRIx64"\n",
               k,b0[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_frombebytes_4(void)
{ uint64_t t;
  printf("Testing bignum_frombebytes_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_bigendian(4,b3,b0);
     bignum_frombebytes_4(b4,(uint8_t *)b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_frombebytes_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_frombebytes_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_frombebytes_6(void)
{ uint64_t t;
  printf("Testing bignum_frombebytes_6 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     reference_bigendian(6,b3,b0);
     bignum_frombebytes_6(b4,(uint8_t *)b0);
     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_frombebytes_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_frombebytes_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_fromlebytes_4(void)
{ uint64_t t;
  printf("Testing bignum_fromlebytes_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_littleendian(4,b3,b0);
     bignum_fromlebytes_4(b4,(uint8_t *)b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_fromlebytes_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_fromlebytes_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_fromlebytes_6(void)
{ uint64_t t;
  printf("Testing bignum_fromlebytes_6 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     reference_littleendian(6,b3,b0);
     bignum_fromlebytes_6(b4,(uint8_t *)b0);
     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_fromlebytes_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_fromlebytes_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_ge(void)
{ uint64_t t, k1, k2;
  printf("Testing bignum_ge with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k1,b0);
     random_bignum(k2,b1);
     if (rand() % 16 == 0) reference_copy(k1,b0,k2,b1);
     if (rand() % 16 == 0) reference_copy(k2,b1,k1,b0);
     if ((rand() % 16 == 0) && (k1 != 0)) ++b0[rand() % k1];
     if ((rand() % 16 == 0) && (k1 != 0)) --b0[rand() % k1];
     if ((rand() % 16 == 0) && (k2 != 0)) ++b1[rand() % k2];
     if ((rand() % 16 == 0) && (k2 != 0)) --b1[rand() % k2];
     c1 = bignum_ge(k1,b0,k2,b1);
     c2 = (reference_compare(k1,b0,k2,b1) >= 0);
     if (c1 != c2)
      { printf("### Disparity: [sizes %4"PRIu64" >= %4"PRIu64"] ...0x%016"PRIx64" >= ...0x%016"PRIx64" <=> %"PRIx64" not %"PRIx64"\n",
               k1,k2,b0[0],b1[0],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" >= %4"PRIu64" ]\n",k1,k2);
        else printf("OK: [sizes %4"PRIu64" >= %4"PRIu64"] ...0x%016"PRIx64" >= ...0x%016"PRIx64" <=> %"PRIx64"\n",
                    k1,k2,b0[0],b1[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_gt(void)
{ uint64_t t, k1, k2;
  printf("Testing bignum_gt with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k1,b0);
     random_bignum(k2,b1);
     if (rand() % 16 == 0) reference_copy(k1,b0,k2,b1);
     if (rand() % 16 == 0) reference_copy(k2,b1,k1,b0);
     if ((rand() % 16 == 0) && (k1 != 0)) ++b0[rand() % k1];
     if ((rand() % 16 == 0) && (k1 != 0)) --b0[rand() % k1];
     if ((rand() % 16 == 0) && (k2 != 0)) ++b1[rand() % k2];
     if ((rand() % 16 == 0) && (k2 != 0)) --b1[rand() % k2];
     c1 = bignum_gt(k1,b0,k2,b1);
     c2 = (reference_compare(k1,b0,k2,b1) > 0);
     if (c1 != c2)
      { printf("### Disparity: [sizes %4"PRIu64" > %4"PRIu64"] ...0x%016"PRIx64" > ...0x%016"PRIx64" <=> %"PRIx64" not %"PRIx64"\n",
               k1,k2,b0[0],b1[0],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" > %4"PRIu64" ]\n",k1,k2);
        else printf("OK: [sizes %4"PRIu64" > %4"PRIu64"] ...0x%016"PRIx64" > ...0x%016"PRIx64" <=> %"PRIx64"\n",
                    k1,k2,b0[0],b1[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_half_p256(void)
{ uint64_t i, k;
  printf("Testing bignum_half_p256 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256);

     bignum_half_p256(b2,b0);

     reference_adc(k+1,b4,k,b2,k,b2,0);
     reference_copy(k+1,b5,k,p_256);
     reference_mod(k+1,b6,b4,b5);
     reference_copy(k,b3,k+1,b6);

     c = reference_compare(k,b3,k,b0);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256[0],b3[0],b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_256[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_half_p256k1(void)
{ uint64_t i, k;
  printf("Testing bignum_half_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256k1);

     bignum_half_p256k1(b2,b0);

     reference_adc(k+1,b4,k,b2,k,b2,0);
     reference_copy(k+1,b5,k,p_256k1);
     reference_mod(k+1,b6,b4,b5);
     reference_copy(k,b3,k+1,b6);

     c = reference_compare(k,b3,k,b0);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256k1[0],b3[0],b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_256k1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_half_p384(void)
{ uint64_t i, k;
  printf("Testing bignum_half_p384 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_384);

     bignum_half_p384(b2,b0);
     reference_adc(k+1,b4,k,b2,k,b2,0);
     reference_copy(k+1,b5,k,p_384);;
     reference_mod(k+1,b6,b4,b5);
     reference_copy(k,b3,k+1,b6);

     c = reference_compare(k,b3,k,b0);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_384[0],b3[0],b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_384[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_half_p521(void)
{ uint64_t i, k;
  printf("Testing bignum_half_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);

     bignum_half_p521(b2,b0);
     reference_adc(k+1,b4,k,b2,k,b2,0);
     reference_copy(k+1,b5,k,p_521);;
     reference_mod(k+1,b6,b4,b5);
     reference_copy(k,b3,k+1,b6);

     c = reference_compare(k,b3,k,b0);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_521[0],b3[0],b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_521[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_iszero(void)
{ uint64_t t, k;
  printf("Testing bignum_iszero with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_sparse_bignum(k,b0);
     c1 = bignum_iszero(k,b0);
     c2 = reference_iszero(k,b0);
     if (c1 != c2)
      { printf("### Disparity: [size %4"PRIu64"] ...0x%016"PRIx64" = 0\n",
               k,b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] ...0x%016"PRIx64" = 0 <=> %"PRIx64"\n",
                    k,b0[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_kmul_specific
  (uint64_t p,uint64_t m,uint64_t n, char *name,
   void (*f)(uint64_t *,uint64_t *,uint64_t *,uint64_t *))
{ uint64_t i, j;
  printf("Testing %s with %d cases\n",name,tests);
  int c;
  for (i = 0; i < tests; ++i)
   { random_bignum(m,b0);
     random_bignum(n,b1);
     random_bignum(p,b2);
     for (j = 0; j < p; ++j) b3[j] = b2[j] + 1;
     (*f)(b2,b0,b1,b5);
     reference_mul(p,b3,m,b0,n,b1);
     c = reference_compare(p,b2,p,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               m,n,p,b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (p == 0) printf("OK: [size %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"]\n",m,n,p);
        else printf("OK: [size %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" =..0x%016"PRIx64"\n",
                    m,n,p,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_kmul_16_32(void)
{ return test_bignum_kmul_specific(32,16,16,"bignum_kmul_16_32",bignum_kmul_16_32);
}

int test_bignum_kmul_32_64(void)
{ return test_bignum_kmul_specific(64,32,32,"bignum_kmul_32_64",bignum_kmul_32_64);
}

int test_bignum_ksqr_specific
  (uint64_t p,uint64_t n, char *name,
   void (*f)(uint64_t *,uint64_t *,uint64_t *))
{ uint64_t i, j;
  printf("Testing %s with %d cases\n",name,tests);
  int c;
  for (i = 0; i < tests; ++i)
   { random_bignum(n,b0);
     random_bignum(p,b2);
     for (j = 0; j < p; ++j) b3[j] = b2[j] + 1;
     (*f)(b2,b0,b5);
     reference_mul(p,b3,n,b0,n,b0);
     c = reference_compare(p,b2,p,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"] "
               "...0x%016"PRIx64"^2  = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               n,n,p,b0[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (p == 0) printf("OK: [size %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"]\n",n,n,p);
        else printf("OK: [size %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"] "
                    "...0x%016"PRIx64"^2 =..0x%016"PRIx64"\n",
                    n,n,p,b0[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_ksqr_16_32(void)
{ return test_bignum_ksqr_specific(32,16,"bignum_ksqr_16_32",bignum_ksqr_16_32);
}

int test_bignum_ksqr_32_64(void)
{ return test_bignum_ksqr_specific(64,32,"bignum_ksqr_32_64",bignum_ksqr_32_64);
}

int test_bignum_le(void)
{ uint64_t t, k1, k2;
  printf("Testing bignum_le with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k1,b0);
     random_bignum(k2,b1);
     if (rand() % 16 == 0) reference_copy(k1,b0,k2,b1);
     if (rand() % 16 == 0) reference_copy(k2,b1,k1,b0);
     if ((rand() % 16 == 0) && (k1 != 0)) ++b0[rand() % k1];
     if ((rand() % 16 == 0) && (k1 != 0)) --b0[rand() % k1];
     if ((rand() % 16 == 0) && (k2 != 0)) ++b1[rand() % k2];
     if ((rand() % 16 == 0) && (k2 != 0)) --b1[rand() % k2];
     c1 = bignum_le(k1,b0,k2,b1);
     c2 = (reference_compare(k1,b0,k2,b1) <= 0);
     if (c1 != c2)
      { printf("### Disparity: [sizes %4"PRIu64" <= %4"PRIu64"] ...0x%016"PRIx64" <= ...0x%016"PRIx64" <=> %"PRIx64" not %"PRIx64"\n",
               k1,k2,b0[0],b1[0],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" <= %4"PRIu64" ]\n",k1,k2);
        else printf("OK: [sizes %4"PRIu64" <= %4"PRIu64"] ...0x%016"PRIx64" <= ...0x%016"PRIx64" <=> %"PRIx64"\n",
                    k1,k2,b0[0],b1[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_littleendian_4(void)
{ uint64_t t;
  printf("Testing bignum_littleendian_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_littleendian(4,b3,b0);
     bignum_littleendian_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_littleendian_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_littleendian_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_littleendian_6(void)
{ uint64_t t;
  printf("Testing bignum_littleendian_6 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     reference_littleendian(6,b3,b0);
     bignum_littleendian_6(b4,b0);
     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_littleendian_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_littleendian_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_lt(void)
{ uint64_t t, k1, k2;
  printf("Testing bignum_lt with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k1,b0);
     random_bignum(k2,b1);
     if (rand() % 16 == 0) reference_copy(k1,b0,k2,b1);
     if (rand() % 16 == 0) reference_copy(k2,b1,k1,b0);
     if ((rand() % 16 == 0) && (k1 != 0)) ++b0[rand() % k1];
     if ((rand() % 16 == 0) && (k1 != 0)) --b0[rand() % k1];
     if ((rand() % 16 == 0) && (k2 != 0)) ++b1[rand() % k2];
     if ((rand() % 16 == 0) && (k2 != 0)) --b1[rand() % k2];
     c1 = bignum_lt(k1,b0,k2,b1);
     c2 = (reference_compare(k1,b0,k2,b1) < 0);
     if (c1 != c2)
      { printf("### Disparity: [sizes %4"PRIu64" < %4"PRIu64"] ...0x%016"PRIx64" < ...0x%016"PRIx64" <=> %"PRIx64" not %"PRIx64"\n",
               k1,k2,b0[0],b1[0],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" < %4"PRIu64" ]\n",k1,k2);
        else printf("OK: [sizes %4"PRIu64" < %4"PRIu64"] ...0x%016"PRIx64" < ...0x%016"PRIx64" <=> %"PRIx64"\n",
                    k1,k2,b0[0],b1[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_madd(void)
{ uint64_t t, j, k0, k1, k2;
  printf("Testing bignum_madd with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k0 = (unsigned) rand() % MAXSIZE;
     k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k0,b0);
     random_bignum(k1,b1);
     random_bignum(k2,b2);
     for (j = 0; j < k2; ++j) b3[j] = b2[j];

     bignum_madd(k2,b2,k0,b0,k1,b1);
     reference_madd(k2,b3,k0,b0,k1,b1);
     c = reference_compare(k2,b2,k2,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" + %4"PRIu64" * %4"PRIu64"] "
               "... + ...0x%016"PRIx64" * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k0,k1,b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k0 == 0 || k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" + %4"PRIu64" * %4"PRIu64"]\n",k2,k0,k1);
        else printf("OK: [sizes %4"PRIu64" + %4"PRIu64" * %4"PRIu64"] ... + ...0x%016"PRIx64" * ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k2,k0,k1,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_n256(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_n256 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,4,n_256);
     reference_mod(k,b3,b0,b1);
     bignum_mod_n256(b4,k,b0);
     c = reference_compare(k,(k < 4) ? b0 : b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_n256_alt(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_n256_alt with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,4,n_256);
     reference_mod(k,b3,b0,b1);
     bignum_mod_n256_alt(b4,k,b0);
     c = reference_compare(k,(k < 4) ? b0 : b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_n256_4(void)
{ uint64_t t;
  printf("Testing bignum_mod_n256_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     if ((rand() & 0xF) == 0) b0[3] |= UINT64_C(0xFFFFFFF000000000);
     else if ((rand() & 0xF) == 0)
      { b0[3] = n_256[3];
        b0[2] = n_256[2];
        b0[1] = n_256[1];
        b0[0] = (n_256[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(4,b3,b0,n_256);
     bignum_mod_n256_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_n256k1_4(void)
{ uint64_t t;
  printf("Testing bignum_mod_n256k1_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     if ((rand() & 0xF) == 0) b0[3] |= UINT64_C(0xFFFFFFF000000000);
     else if ((rand() & 0xF) == 0)
      { b0[3] = n_256k1[3];
        b0[2] = n_256k1[2];
        b0[1] = n_256k1[1];
        b0[0] = (n_256k1[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(4,b3,b0,n_256k1);
     bignum_mod_n256k1_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_n384(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_n384 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,6,n_384);
     reference_mod(k,b3,b0,b1);
     bignum_mod_n384(b4,k,b0);
     c = reference_compare(k,(k < 6) ? b0 : b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_384 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(6),b0[k-1],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_384 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(6),b0[k-1],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_n384_6(void)
{ uint64_t t;
  printf("Testing bignum_mod_n384_6 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     if ((rand() & 0xF) == 0) b0[5] |= UINT64_C(0xFFFFFFFFFFFFFFFF);
     else if ((rand() & 0xF) == 0)
      { b0[5] = n_384[5];
        b0[4] = n_384[4];
        b0[3] = n_384[3];
        b0[2] = n_384[2];
        b0[1] = n_384[1];
        b0[0] = (n_384[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(6,b3,b0,n_384);
     bignum_mod_n384_6(b4,b0);
     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_384 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_384 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_n521_9(void)
{ uint64_t t;
  printf("Testing bignum_mod_n521_9 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b0);
     if ((rand() & 0xF) == 0) b0[8] |= UINT64_C(0xFFFFFFFFFFFFFFFF);
     else if ((rand() & 0xF) == 0)
      { b0[8] = n_521[8];
        b0[7] = n_521[7];
        b0[6] = n_521[6];
        b0[5] = n_521[5];
        b0[4] = n_521[4];
        b0[3] = n_521[3];
        b0[2] = n_521[2];
        b0[1] = n_521[1];
        b0[0] = (n_521[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(9,b3,b0,n_521);
     bignum_mod_n521_9(b4,b0);
     c = reference_compare(9,b3,9,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_521 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[8],b0[0],b4[8],b4[0],b3[8],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_521 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[8],b0[0],b4[8],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_p256(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_p256 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,4,p_256);
     reference_mod(k,b3,b0,b1);
     bignum_mod_p256(b4,k,b0);
     c = reference_compare(k,(k < 4) ? b0 : b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_p256_alt(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_p256_alt with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,4,p_256);
     reference_mod(k,b3,b0,b1);
     bignum_mod_p256_alt(b4,k,b0);
     c = reference_compare(k,(k < 4) ? b0 : b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_p256_4(void)
{ uint64_t t;
  printf("Testing bignum_mod_p256_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     if ((rand() & 0xF) == 0) b0[3] |= UINT64_C(0xFFFFFFF000000000);
     else if ((rand() & 0xF) == 0)
      { b0[3] = p_256[3];
        b0[2] = p_256[2];
        b0[1] = p_256[1];
        b0[0] = (p_256[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(4,b3,b0,p_256);
     bignum_mod_p256_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_p256k1_4(void)
{ uint64_t t;
  printf("Testing bignum_mod_p256k1_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     if ((rand() & 0xF) == 0) b0[3] |= UINT64_C(0xFFFFFFF000000000);
     else if ((rand() & 0xF) == 0)
      { b0[3] = p_256k1[3];
        b0[2] = p_256k1[2];
        b0[1] = p_256k1[1];
        b0[0] = (p_256k1[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(4,b3,b0,p_256k1);
     bignum_mod_p256k1_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_p384(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_p384 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,6,p_384);
     reference_mod(k,b3,b0,b1);
     bignum_mod_p384(b4,k,b0);
     c = reference_compare(k,(k < 6) ? b0 : b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(6),b0[k-1],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(6),b0[k-1],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_p384_6(void)
{ uint64_t t;
  printf("Testing bignum_mod_p384_6 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     if ((rand() & 0xF) == 0) b0[5] |= UINT64_C(0xFFFFFFFFFFFFFFFF);
     else if ((rand() & 0xF) == 0)
      { b0[5] = p_384[5];
        b0[4] = p_384[4];
        b0[3] = p_384[3];
        b0[2] = p_384[2];
        b0[1] = p_384[1];
        b0[0] = (p_384[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(6,b3,b0,p_384);
     bignum_mod_p384_6(b4,b0);
     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_p521_9(void)
{ uint64_t t;
  printf("Testing bignum_mod_p521_9 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b0);
     if ((rand() & 0xF) == 0) b0[8] |= UINT64_C(0xFFFFFFFFFFFFFFFF);
     else if ((rand() & 0xF) == 0)
      { b0[8] = p_521[8];
        b0[7] = p_521[7];
        b0[6] = p_521[6];
        b0[5] = p_521[5];
        b0[4] = p_521[4];
        b0[3] = p_521[3];
        b0[2] = p_521[2];
        b0[1] = p_521[1];
        b0[0] = (p_521[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(9,b3,b0,p_521);
     bignum_mod_p521_9(b4,b0);
     c = reference_compare(9,b3,9,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[8],b0[0],b4[8],b4[0],b3[8],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[8],b0[0],b4[8],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_modadd(void)
{ uint64_t i, k;
  printf("Testing bignum_modadd with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b2);
     random_bignum(k,b3); reference_divmod(k,b4,b0,b3,b2);
     random_bignum(k,b3); reference_divmod(k,b4,b1,b3,b2);

     reference_adc(k+1,b4,k,b0,k,b1,0);
     reference_copy(k+1,b5,k,b2);
     reference_divmod(k+1,b6,b7,b4,b5);
     reference_copy(k,b3,k+1,b7);

     bignum_modadd(k,b4,b0,b1,b2);
     c = reference_compare(k,b3,k,b4);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
         "(...0x%016"PRIx64" + ...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
         "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
        k,b0[0],b1[0],b2[0],b4[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        printf("OK: [size %4"PRIu64"] "
         "(...0x%016"PRIx64" + ...0x%016"PRIx64") mod ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
        k,b0[0],b1[0],b2[0],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_moddouble(void)
{ uint64_t i, k;
  printf("Testing bignum_moddouble with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b2);
     random_bignum(k,b3); reference_divmod(k,b4,b0,b3,b2);

     reference_adc(k+1,b4,k,b0,k,b0,0);
     reference_copy(k+1,b5,k,b2);
     reference_divmod(k+1,b6,b7,b4,b5);
     reference_copy(k,b3,k+1,b7);

     bignum_moddouble(k,b4,b0,b2);
     c = reference_compare(k,b3,k,b4);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
         "(2 * ...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
         "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
        k,b0[0],b2[0],b4[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        printf("OK: [size %4"PRIu64"] "
         "(2 * ...0x%016"PRIx64") mod ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
        k,b0[0],b2[0],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_modifier(void)
{ uint64_t i, k, c;
  printf("Testing bignum_modifier with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0); b0[0] |= 1;

     bignum_modifier(k,b2,b0,b7); // b2 = test fun
     reference_modpowtwo(k,b3,64*k,b0); // Naive regerence

     c = reference_compare(k,b2,k,b3);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
           "bignum_modifier(...0x%016"PRIx64") = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
            k,b0[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_modifier(...0x%016"PRIx64") =..0x%016"PRIx64"\n",
                    k,b0[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_modinv(void)
{ uint64_t i, k;
  int c;
  printf("Testing bignum_modinv with %d cases\n",tests);

  for (i = 0; i < tests; ++i)
   { k = (unsigned) rand() % MAXSIZE + 1; // Size 0 cannot make sense
     random_bignum(k,b0), b0[0] |= 1;     // Modulus b, which has to be odd

     do random_bignum(k,b1);
     while (!reference_coprime(k,b1,b0));

     // Make sure to check the degnerate a = 1 and b = 1 cases occasionally
     if ((rand() & 0xFF) < 3) reference_of_word(k,b0,UINT64_C(1));
     if ((rand() & 0xFF) < 3) reference_of_word(k,b1,UINT64_C(1));

     bignum_modinv(k,b2,b1,b0,b7);        // s with a * s == 1 (mod b)
     reference_mul(2 * k,b4,k,b1,k,b2);    // b4 = a * s
     reference_copy(2 * k,b5,k,b0);        // b5 = b (double-length)
     reference_mod(2 * k,b3,b4,b5);        // b3 = (a * s) mod b
     reference_modpowtwo(k,b4,0,b0);       // b4 = 1 mod b = 2^k mod b

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf
         ("OK: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_modoptneg(void)
{ uint64_t i, k, p;
  printf("Testing bignum_modoptneg with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b1);
     random_bignum(k,b4);
     reference_mod(k,b0,b4,b1);
     p = (rand() & 1) ? 0 :
         (rand() & 1) ? 1 :
         (rand() & 1) ? 2 : random64();
     bignum_modoptneg(k,b2,p,b0,b1);
     if ((p == 0) || reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,b1,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_modsub(void)
{ uint64_t i, k;
  printf("Testing bignum_modsub with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b2);
     random_bignum(k,b3); reference_divmod(k,b4,b0,b3,b2);
     random_bignum(k,b3); reference_divmod(k,b4,b1,b3,b2);

     reference_adc(k+1,b4,k,b0,k,b2,0);
     reference_sbb(k+1,b4,k+1,b4,k,b1,0);
     reference_copy(k+1,b5,k,b2);
     reference_divmod(k+1,b6,b7,b4,b5);
     reference_copy(k,b3,k+1,b7);

     bignum_modsub(k,b4,b0,b1,b2);
     c = reference_compare(k,b3,k,b4);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
         "(...0x%016"PRIx64" - ...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
         "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
        k,b0[0],b1[0],b2[0],b4[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        printf("OK: [size %4"PRIu64"] "
         "(...0x%016"PRIx64" - ...0x%016"PRIx64") mod ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
        k,b0[0],b1[0],b2[0],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montifier(void)
{ uint64_t i, k, c;
  printf("Testing bignum_montifier with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0); b0[0] |= 1;

     bignum_montifier(k,b2,b0,b7); // b2 = test fun
     reference_modpowtwo(k,b3,128*k,b0); // Naive regerence

     c = reference_compare(k,b2,k,b3);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
           "bignum_montifier(...0x%016"PRIx64") = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
            k,b0[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_montifier(...0x%016"PRIx64") =..0x%016"PRIx64"\n",
                    k,b0[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montmul(void)
{ uint64_t t, k;
  printf("Testing bignum_montmul with %d cases\n",tests);
  int c = 0;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0); b0[0] |= 1; // b0 = m
     random_bignum(k,b1);             // b1 = x
     random_bignum(k,b2);             // b2 = y
     reference_mul(2 * k,b3,k,b1,k,b2);  // b3 = z = x * y
     reference_negmodinv(k,b4,b0);    // b4 = m' = negmodinv(m)

     reference_copy(3 * k,b7,k,b0);                           // b7 = m
     reference_of_word(k,b8,0); reference_copy(2*k,b8+k,k,b1);   // b8 = R * x
     reference_of_word(k,b9,0); reference_copy(2*k,b9+k,k,b2);   // b9 = R * x
     reference_of_word(k,b10,0); reference_copy(2*k,b10+k,2*k,b3);   // b10 = R * z

     reference_divmod(3*k,b11,b12,b8,b7);
     reference_copy(k,b1,k,b12);                          // b1 = (R * x) MOD m
     reference_divmod(3*k,b11,b12,b9,b7);
     reference_copy(k,b2,k,b12);                          // b2 = (R * y) MOD m
     reference_divmod(3*k,b11,b12,b10,b7);
     reference_copy(k,b3,k,b12);                          // b3 = (R * z) MOD m
     bignum_montmul(k,b5,b1,b2,b0);           // b5 = function

     c = reference_compare(k,b3,k,b5);
     if (c != 0)
      { printf("### Disparity (Montgomery mul): [size %4"PRIu64"]\n",k);
        printf("### Output is ...0x%016"PRIx64"\n",b5[0]);
        printf("### Reference ...0x%016"PRIx64"\n",b3[0]);
        return 1;
      }
     else
      { printf("OK: [size %4"PRIu64"] bignum_montmul(...0x%016"PRIx64",...0x%016"PRIx64") wrt ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k,b1[0],b2[0],b0[0],b5[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montmul_p256(void)
{ uint64_t t;
  printf("Testing bignum_montmul_p256 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256);
     random_bignum(4,b2);
     reference_mod(4,b1,b2,p_256);
     bignum_montmul_p256(b4,b0,b1);
     reference_dmontmul(4,b3,b0,b1,p_256,i_256,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montmul_p256_alt(void)
{ uint64_t t;
  printf("Testing bignum_montmul_p256_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256);
     random_bignum(4,b2);
     reference_mod(4,b1,b2,p_256);
     bignum_montmul_p256_alt(b4,b0,b1);
     reference_dmontmul(4,b3,b0,b1,p_256,i_256,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montmul_p256k1(void)
{ uint64_t t;
  printf("Testing bignum_montmul_p256k1 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256k1);
     random_bignum(4,b2);
     reference_mod(4,b1,b2,p_256k1);
     bignum_montmul_p256k1(b4,b0,b1);
     reference_dmontmul(4,b3,b0,b1,p_256k1,i_256k1,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montmul_p256k1_alt(void)
{ uint64_t t;
  printf("Testing bignum_montmul_p256k1_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256k1);
     random_bignum(4,b2);
     reference_mod(4,b1,b2,p_256k1);
     bignum_montmul_p256k1_alt(b4,b0,b1);
     reference_dmontmul(4,b3,b0,b1,p_256k1,i_256k1,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montmul_p384(void)
{ uint64_t t;
  printf("Testing bignum_montmul_p384 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b2);
     reference_mod(6,b0,b2,p_384);
     random_bignum(6,b2);
     reference_mod(6,b1,b2,p_384);
     bignum_montmul_p384(b4,b0,b1);
     reference_dmontmul(6,b3,b0,b1,p_384,i_384,b5);

     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-384 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b1[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-384 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b1[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montmul_p521(void)
{ uint64_t t;
  printf("Testing bignum_montmul_p521 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b2);
     reference_mod(9,b0,b2,p_521);
     random_bignum(9,b2);
     reference_mod(9,b1,b2,p_521);
     bignum_montmul_p521(b4,b0,b1);
     reference_dmontmul(9,b3,b0,b1,p_521,i_521,b5);

     c = reference_compare(9,b3,9,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-576 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[0],b1[0],b4[8],b4[0],b3[8],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-576 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[0],b1[0],b4[8],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montredc(void)
{ uint64_t t, k, n, p, r, q;
  printf("Testing bignum_montredc with %d cases\n",tests);

  int c, d;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     n = (unsigned) rand() % MAXSIZE;
     p = (unsigned) rand() % MAXSIZE;

     q = max(p+k,n) + 1;

     random_bignum(k,b0); b0[0] |= 1;  // b0 = m
     random_bignum(n,b1);              // b1 = x

     // To test strict Montgomery reduction make x <= 2^{64p} * n.
     // Actually this never hits the x = 2^{64p} * n case

     reference_copy(q,b3,k,b0);            // b3 = m
     reference_pow2(q,b4,64*p);            // b4 = 2^{64p}
     reference_mul(q,b2,q,b3,q,b4);        // b2 = 2^{64p} * m
     reference_copy(q,b3,n,b1);            // b3 = x
     reference_mod(q,b4,b3,b2);            // b4 = x mod (2^{64p} * m)
     reference_copy(n,b1,q,b4);

     bignum_montredc(k,b4,n,b1,b0,p); // b4 = test function

     r = max(p+k,n);

     reference_pow2(r,b2,64*p);            // b2 = 2^{64p}
     reference_mul(r,b3,r,b2,k,b4);        // b3 = 2^{64p} * z
     reference_copy(r,b2,min(n,p+k),b1);   // b2 = x' (truncated x)
     reference_copy(r,b5,k,b0);            // b5 = m
     reference_mod(r,b6,b2,b5);            // b6 = x mod m
     reference_mod(r,b7,b3,b5);            // b7 = (2^{64p} * z) mod m
     c = ((k != 0) && reference_compare(r,b6,r,b7));
     d = (k == 0) || reference_lt_samelen(k,b4,b0);
     if (c != 0)
      { printf("### Disparity even reducing modulo: [size %4"PRIu64" -> %4"PRIu64"] "
               "...%016"PRIx64" / 2^%"PRIu64" mod ...%016"PRIx64" = ...%016"PRIx64"\n",
               n,k,b1[0],64*p,b0[0],b4[0]);
        return 1;
      }
     if (d != 1)
      { printf("### Disparity with modular reduction: [size %4"PRIu64" -> %4"PRIu64"] "
               "...%016"PRIx64" / 2^%"PRIu64" mod ...%016"PRIx64" = ...%016"PRIx64"\n",
               n,k,b1[0],64*p,b0[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] "
               "...%016"PRIx64" / 2^%"PRIu64" mod ...%016"PRIx64" = ...%016"PRIx64"\n",
               n,k,b1[0],64*p,b0[0],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montsqr(void)
{ uint64_t t, k;
  printf("Testing bignum_montsqr with %d cases\n",tests);
  int c = 0;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0); b0[0] |= 1; // b0 = m
     random_bignum(k,b2);             // b2 = raw x
     reference_mod(k,b1,b2,b0);          // b1 = x with < m
     reference_copy(k,b2,k,b1);          // b2 = y = x in squaring case
     reference_mul(2 * k,b3,k,b1,k,b2);  // b3 = z = x * y
     reference_negmodinv(k,b4,b0);    // b4 = m' = negmodinv(m)
     bignum_montsqr(k,b5,b1,b0);        // b5 = output of function
     reference_copy(k,b7,k,b1);
     reference_copy(k,b7,k,b2);
     reference_dmontmul(k,b3,b1,b2,b0,b4,b8);   // b3 = "reference" Montgomery

     c = reference_compare(k,b3,k,b5);
     if (c != 0)
      { printf("### Disparity (Montgomery sqr): [size %4"PRIu64"]\n",k);
        printf("### Output is ...0x%016"PRIx64"\n",b5[0]);
        printf("### Reference ...0x%016"PRIx64"\n",b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] bignum_montsqr(...0x%016"PRIx64") wrt ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k,b1[0],b0[0],b5[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montsqr_p256(void)
{ uint64_t t;
  printf("Testing bignum_montsqr_p256 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256);
     bignum_montsqr_p256(b4,b0);
     reference_dmontmul(4,b3,b0,b0,p_256,i_256,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montsqr_p256_alt(void)
{ uint64_t t;
  printf("Testing bignum_montsqr_p256_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256);
     bignum_montsqr_p256_alt(b4,b0);
     reference_dmontmul(4,b3,b0,b0,p_256,i_256,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montsqr_p256k1(void)
{ uint64_t t;
  printf("Testing bignum_montsqr_p256k1 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256k1);
     bignum_montsqr_p256k1(b4,b0);
     reference_dmontmul(4,b3,b0,b0,p_256k1,i_256k1,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montsqr_p256k1_alt(void)
{ uint64_t t;
  printf("Testing bignum_montsqr_p256k1_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256k1);
     bignum_montsqr_p256k1_alt(b4,b0);
     reference_dmontmul(4,b3,b0,b0,p_256k1,i_256k1,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montsqr_p384(void)
{ uint64_t t;
  printf("Testing bignum_montsqr_p384 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b2);
     reference_mod(6,b0,b2,p_384);
     bignum_montsqr_p384(b4,b0);
     reference_dmontmul(6,b3,b0,b0,p_384,i_384,b5);

     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-384 * ...0x%016"PRIx64"^2 mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-384 * ...0x%016"PRIx64"^2 mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montsqr_p521(void)
{ uint64_t t;
  printf("Testing bignum_montsqr_p521 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b2);
     reference_mod(9,b0,b2,p_521);
     bignum_montsqr_p521(b4,b0);
     reference_dmontmul(9,b3,b0,b0,p_521,i_521,b5);

     c = reference_compare(9,b3,9,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-576 * ...0x%016"PRIx64"^2 mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[0],b4[8],b4[0],b3[8],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-576 * ...0x%016"PRIx64"^2 mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[0],b4[8],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mul(void)
{ uint64_t t, j, k0, k1, k2;
  printf("Testing bignum_mul with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k0 = (unsigned) rand() % MAXSIZE;
     k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k0,b0);
     random_bignum(k1,b1);
     random_bignum(k2,b2);
     for (j = 0; j < k2; ++j) b3[j] = b2[j];
     bignum_mul(k2,b2,k0,b0,k1,b1);
     reference_mul(k2,b3,k0,b0,k1,b1);
     c = reference_compare(k2,b2,k2,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" := %4"PRIu64" * %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k0,k1,b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k0 == 0 || k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" := %4"PRIu64" * %4"PRIu64"]\n",k2,k0,k1);
        else printf("OK: [sizes %4"PRIu64" := %4"PRIu64" * %4"PRIu64"] ...0x%016"PRIx64" * ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k2,k0,k1,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mul_specific
  (uint64_t p,uint64_t m,uint64_t n, char *name,
   void (*f)(uint64_t *,uint64_t *,uint64_t *))
{ uint64_t i, j;
  printf("Testing %s with %d cases\n",name,tests);
  int c;
  for (i = 0; i < tests; ++i)
   { random_bignum(m,b0);
     random_bignum(n,b1);
     random_bignum(p,b2);
     for (j = 0; j < p; ++j) b3[j] = b2[j] + 1;
     (*f)(b2,b0,b1);
     reference_mul(p,b3,m,b0,n,b1);
     c = reference_compare(p,b2,p,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               m,n,p,b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (p == 0) printf("OK: [size %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"]\n",m,n,p);
        else printf("OK: [size %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" =..0x%016"PRIx64"\n",
                    m,n,p,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mul_4_8(void)
{ return test_bignum_mul_specific(8,4,4,"bignum_mul_4_8",bignum_mul_4_8);
}

int test_bignum_mul_4_8_alt(void)
{ return test_bignum_mul_specific(8,4,4,"bignum_mul_4_8_alt",bignum_mul_4_8_alt);
}

int test_bignum_mul_6_12(void)
{ return test_bignum_mul_specific(12,6,6,"bignum_mul_6_12",bignum_mul_6_12);
}

int test_bignum_mul_8_16(void)
{ return test_bignum_mul_specific(16,8,8,"bignum_mul_8_16",bignum_mul_8_16);
}

int test_bignum_mul_p256k1(void)
{ uint64_t i, k;
  printf("Testing bignum_mul_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     random_bignum(k,b1);
     bignum_mul_p256k1(b2,b0,b1);
     reference_mul(2*k,b4,k,b0,k,b1);
     reference_copy(2*k,b3,k,p_256k1);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);
     c = reference_compare(k,b3,k,b2);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mul_p256k1_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_mul_p256k1_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     random_bignum(k,b1);
     bignum_mul_p256k1_alt(b2,b0,b1);
     reference_mul(2*k,b4,k,b0,k,b1);
     reference_copy(2*k,b3,k,p_256k1);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);
     c = reference_compare(k,b3,k,b2);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mul_p521(void)
{ uint64_t i, k;
  printf("Testing bignum_mul_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_521);
     bignum_mul_p521(b2,b0,b1);
     reference_mul(2*k,b4,k,b0,k,b1);
     reference_copy(2*k,b3,k,p_521);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);
     c = reference_compare(k,b3,k,b2);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_521[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_521[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_muladd10(void)
{ uint64_t t, k, r, d, j, s;
  printf("Testing bignum_muladd10 with %d cases\n",tests);
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     d = random64();
     bignum_copy(k,b4,k,b0);
     bignum_of_word(k+1,b3,d);
     reference_cmadd(k+1,b3,10,k,b0);
     r = bignum_muladd10(k,b4,d);
     j = (k == 0) ? 0 : k - 1;
     s = b3[k];
     if (reference_compare(k,b3,k,b4) != 0)
      { printf("### Disparity in product: [size %4"PRIu64"] "
               "10 * 0x%016"PRIx64"...%016"PRIx64" + %"PRIu64" = "
               "0x%016"PRIx64"...%016"PRIx64" carry %"PRIu64" not 0x%016"PRIx64"...%016"PRIx64" carry %"PRIu64"\n",
               k,b0[j],b0[0],d,b4[j],b4[0],r,b3[j],b3[0],s);
        return 1;
      }
     else if (r != s)
      { printf("### Disparity in carry: [size %4"PRIu64"] "
               "10 * 0x%016"PRIx64"...%016"PRIx64" + %"PRIu64" = "
               "%"PRIu64" not %"PRIu64"\n",
               k,b0[j],b0[0],d,r,b2[0]);
        return 1;
     }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 10 * 0x%016"PRIx64"...%016"PRIx64" + %"PRIu64" = "
               "0x%016"PRIx64"...%016"PRIx64", carry %"PRIu64"\n",
               k,b0[j],b0[0],d,b4[j],b4[0],r);
      }
   }

  printf("All OK\n");
  return 0;
}

int test_bignum_mux(void)
{ uint64_t i, n;
  printf("Testing bignum_mux with %d cases\n",tests);
  int b, c;
  for (i = 0; i < tests; ++i)
   { n = (unsigned) rand() % MAXSIZE;
     random_bignum(n,b0);
     random_bignum(n,b1);
     b = rand() & 1;
     bignum_mux(b,n,b2,b0,b1);
     c = (b ? reference_compare(n,b2,n,b0)
            : reference_compare(n,b2,n,b1));

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "if %d then ...0x%016"PRIx64" else ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               n,b,b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (n == 0) printf("OK: [size %4"PRIu64"]\n",n);
        else printf("OK: [size %4"PRIu64"] if %d then ...0x%016"PRIx64" else ...0x%016"PRIx64" =..0x%016"PRIx64"\n",
                    n,b,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

// Test size-4 multiplexing function

int test_bignum_mux_4(void)
{ uint64_t i, n;
  printf("Testing bignum_mux_4 with %d cases\n",tests);
  int b, c;
  for (i = 0; i < tests; ++i)
   { n = 4;
     random_bignum(n,b0);
     random_bignum(n,b1);
     b = rand() & 1;
     bignum_mux_4(b,b2,b0,b1);
     c = (b ? reference_compare(n,b2,n,b0)
            : reference_compare(n,b2,n,b1));

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "if %d then ...0x%016"PRIx64" else ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               n,b,b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (n == 0) printf("OK: [size %4"PRIu64"]\n",n);
        else printf("OK: [size %4"PRIu64"] if %d then ...0x%016"PRIx64" else ...0x%016"PRIx64" =..0x%016"PRIx64"\n",
                    n,b,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

// Test size-6 multiplexing function

int test_bignum_mux_6(void)
{ uint64_t i, n;
  printf("Testing bignum_mux_6 with %d cases\n",tests);
  int b, c;
  for (i = 0; i < tests; ++i)
   { n = 6;
     random_bignum(n,b0);
     random_bignum(n,b1);
     b = rand() & 1;
     bignum_mux_6(b,b2,b0,b1);
     c = (b ? reference_compare(n,b2,n,b0)
            : reference_compare(n,b2,n,b1));

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "if %d then ...0x%016"PRIx64" else ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               n,b,b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (n == 0) printf("OK: [size %4"PRIu64"]\n",n);
        else printf("OK: [size %4"PRIu64"] if %d then ...0x%016"PRIx64" else ...0x%016"PRIx64" =..0x%016"PRIx64"\n",
                    n,b,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mux16(void)
{ uint64_t i, k, t;
  printf("Testing bignum_mux16 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     uint64_t *bs = malloc(16 * k * sizeof(uint64_t));
     for (i = 0; i < 16; ++i)
       random_bignum(k,bs+k*i);
     i = rand() & 15;
     reference_copy(k,b1,k,bs+k*i);
     bignum_mux16(k,b2,bs,i);

     c = reference_compare(k,b2,k,b1);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "element [%4"PRIu64"] = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,i,b2[0],b1[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] element [%4"PRIu64"] = .0x%016"PRIx64"\n",
                    k,i,b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_neg_p256(void)
{ uint64_t i, k;
  printf("Testing bignum_neg_p256 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256);
     if ((rand() & 0x1F) == 0) reference_of_word(k,b0,0);

     bignum_neg_p256(b2,b0);
     if (reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_256,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "- ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_256[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_neg_p256k1(void)
{ uint64_t i, k;
  printf("Testing bignum_neg_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256k1);
     if ((rand() & 0x1F) == 0) reference_of_word(k,b0,0);

     bignum_neg_p256k1(b2,b0);
     if (reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_256k1,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "- ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_neg_p384(void)
{ uint64_t i, k;
  printf("Testing bignum_neg_p384 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_384);
     if ((rand() & 0x1F) == 0) reference_of_word(k,b0,0);

     bignum_neg_p384(b2,b0);
     if (reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_384,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "- ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_384[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_384[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_neg_p521(void)
{ uint64_t i, k;
  printf("Testing bignum_neg_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     if ((rand() & 0x1F) == 0) reference_of_word(k,b0,0);

     bignum_neg_p521(b2,b0);
     if (reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_521,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "- ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_521[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_521[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_negmodinv(void)
{ uint64_t t, i, k;
  printf("Testing bignum_negmodinv  with %d cases\n",tests);
  int c = 0;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0); b0[0] |= 1;
     bignum_negmodinv(k,b1,b0);
     b2[0] = 1; for (i = 1; i < k; ++i) b2[i] = 0;
     reference_madd(k,b2,k,b1,k,b0);
     c = 0; for (i = 0; i < k; ++i) if (b2[i] != 0) c = 1;
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" + 1 = ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],b2[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" + 1 = ...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_nonzero(void)
{ uint64_t t, k;
  printf("Testing bignum_nonzero with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_sparse_bignum(k,b0);
     c1 = bignum_nonzero(k,b0);
     c2 = !reference_iszero(k,b0);
     if (c1 != c2)
      { printf("### Disparity: [size %4"PRIu64"] ...0x%016"PRIx64" = 0\n",
               k,b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] ...0x%016"PRIx64" = 0 <=> %"PRIx64"\n",
                    k,b0[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_nonzero_4(void)
{ uint64_t t, k;
  printf("Testing bignum_nonzero_4 with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = 4;
     if (rand() & 1) random_sparse_bignum(k,b0);
     else random_bignum(k,b0);
     c1 = bignum_nonzero_4(b0);
     c2 = !reference_iszero(k,b0);
     if (c1 != c2)
      { printf("### Disparity: [size %4"PRIu64"] 0x%016"PRIx64"...0x%016"PRIx64" = 0\n",
               k,b0[3],b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...0x%016"PRIx64" = 0 <=> %"PRIx64"\n",
                    k,b0[3],b0[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_nonzero_6(void)
{ uint64_t t, k;
  printf("Testing bignum_nonzero_6 with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = 6;
     if (rand() & 1) random_sparse_bignum(k,b0);
     else random_bignum(k,b0);
     c1 = bignum_nonzero_6(b0);
     c2 = !reference_iszero(k,b0);
     if (c1 != c2)
      { printf("### Disparity: [size %4"PRIu64"] 0x%016"PRIx64"...0x%016"PRIx64" = 0\n",
               k,b0[5],b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...0x%016"PRIx64" = 0 <=> %"PRIx64"\n",
                    k,b0[5],b0[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_normalize(void)
{ uint64_t t, k, r;
  printf("Testing bignum_normalize with %d cases\n",tests);
  int c = 0;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,k,b0);
     r = bignum_normalize(k,b1);
     reference_pow2(k,b2,reference_clz(k,b0));
     reference_mul(k,b3,k,b0,k,b2);
     c = reference_compare(k,b1,k,b3);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"]",k);
        if (k == 0) printf("\n");
        else printf (" normalize(0x%016"PRIx64"...0x%016"PRIx64") = 0x%016"PRIx64"...0x%016"PRIx64""
                     " not 0x%016"PRIx64"...0x%016"PRIx64"\n",
                     b0[k-1],b0[0],b1[k-1],b1[0],b3[k-1],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"]",k);
        if (k == 0) printf("\n");
        else printf (" normalize(0x%016"PRIx64"...0x%016"PRIx64") = 0x%016"PRIx64"...0x%016"PRIx64" "
                     "(%"PRIu64" places)\n",
                     b0[k-1],b0[0],b1[k-1],b1[0],r);
      }
     if (r != reference_clz(k,b0))
      { printf("### Disparity: [size %4"PRIu64"]: %"PRIu64" not %"PRIu64" return value\n",
               k,r,reference_clz(k,b0));
        return 1;
      }

   }
  printf("All OK\n");
  return 0;
}

int test_bignum_odd(void)
{ uint64_t t, k;
  printf("Testing bignum_odd with %d cases\n",tests);
  uint64_t c1, c2;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     c1 = bignum_odd(k,b0);
     c2 = (k != 0) && (b0[0] & 1);
     if (c1 != c2)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_odd(...0x%016"PRIx64") = %"PRIx64" not %"PRIx64"\n",
               k,b0[0],c1,c2);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK:[size %4"PRIu64"] "
               "bignum_odd(...0x%016"PRIx64") = %"PRIx64"\n",
               k,b0[0],c1);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_of_word(void)
{ uint64_t t, i, k, n;
  printf("Testing bignum_of_word with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     n = random64();
     bignum_of_word(k,b0,n);
     c = 0;
     if ((k > 0) && (b0[0] != n)) c = 1;
     for (i = 1; i < k; ++i) if (b0[i] != 0) c = 1;
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_of_word(0x%016"PRIx64") = ....0x%016"PRIx64"\n",
               k,n,b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK:[size %4"PRIu64"] "
               "bignum_of_word(0x%016"PRIx64") = ....0x%016"PRIx64"\n",
               k,n,b0[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_optadd(void)
{ uint64_t t, i, k;
  printf("Testing bignum_optadd with %d cases\n",tests);
  uint64_t c, c1, c2;
  uint64_t p;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     random_bignum(k,b1);
     random_bignum(k,b2);
     random_bignum(k,b3);
     p = rand() & 1;

     for (i = 0; i < k; ++i) b3[i] = b0[i];
     c1 = 0; if (p) c1 = reference_adc(k,b3,k,b3,k,b1,0);

     c2 = bignum_optadd(k,b2,b0,p,b1);

     c = reference_compare(k,b2,k,b3);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" + %"PRIx64" * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p,b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (c1 != c2)
      {
        printf("### Disparity: [size %4"PRIu64"]: ...0x%016"PRIx64" + %"PRIx64" * ...0x%016"PRIx64" carry %"PRIu64" not %"PRIu64"\n",
               k,b0[0],p,b1[0],c2,c1);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] ...0x%016"PRIx64" + %"PRIx64" * ...0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p,b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_optneg(void)
{ uint64_t t, k;
  printf("Testing bignum_optneg with %d cases\n",tests);
  uint64_t c, c1, c2;
  uint64_t p;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b1);
     random_bignum(k,b2);
     random_bignum(k,b3);
     p = random64();
     if (rand() & 1) p = 0;
     if ((rand() & 31) == 0) reference_of_word(k,b1,0);

     c1 = 0;
     if (p != 0) c1 = reference_sbb(k,b3,0,NULL,k,b1,0);
     else reference_copy(k,b3,k,b1);

     c2 = bignum_optneg(k,b2,p,b1);

     c = reference_compare(k,b2,k,b3);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "(%s) ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (c1 != c2)
      {
        printf("### Disparity: [size %4"PRIu64"]: (%s) ...0x%016"PRIx64" carry %"PRIu64" not %"PRIu64"\n",
               k,(p ? "-" : "+"),b1[0],c2,c1);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] (%s) ...0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,(p ? "-" : "+"),b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_optneg_p256(void)
{ uint64_t i, k, p;
  printf("Testing bignum_optneg_p256 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256);
     p = (rand() & 1) ? 0 :
         (rand() & 1) ? 1 :
         (rand() & 1) ? 2 : random64();
     bignum_optneg_p256(b2,p,b0);
     if ((p == 0) || reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_256,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_256[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_256[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_optneg_p256k1(void)
{ uint64_t i, k, p;
  printf("Testing bignum_optneg_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256k1);
     p = (rand() & 1) ? 0 :
         (rand() & 1) ? 1 :
         (rand() & 1) ? 2 : random64();
     bignum_optneg_p256k1(b2,p,b0);
     if ((p == 0) || reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_256k1,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_optneg_p384(void)
{ uint64_t i, k, p;
  printf("Testing bignum_optneg_p384 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_384);
     p = (rand() & 1) ? 0 :
         (rand() & 1) ? 1 :
         (rand() & 1) ? 2 : random64();
     bignum_optneg_p384(b2,p,b0);
     if (!p || reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_384,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_384[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_384[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_optneg_p521(void)
{ uint64_t i, k, p;
  printf("Testing bignum_optneg_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     p = (rand() & 1) ? 0 :
         (rand() & 1) ? 1 :
         (rand() & 1) ? 2 : random64();
     bignum_optneg_p521(b2,p,b0);
     if (!p || reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_521,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_521[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_521[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_optsub(void)
{ uint64_t t, i, k;
  printf("Testing bignum_optsub with %d cases\n",tests);
  uint64_t c, c1, c2;
  uint64_t p;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     random_bignum(k,b1);
     random_bignum(k,b2);
     random_bignum(k,b3);
     p = rand() & 1;

     for (i = 0; i < k; ++i) b3[i] = b0[i];
     c1 = 0; if (p) c1 = reference_sbb(k,b3,k,b3,k,b1,0);

     c2 = bignum_optsub(k,b2,b0,p,b1);

     c = reference_compare(k,b2,k,b3);

    if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" - %"PRIx64" * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p,b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (c1 != c2)
      {
        printf("### Disparity: [size %4"PRIu64"]: ...0x%016"PRIx64" - %"PRIx64" * ...0x%016"PRIx64" carry %"PRIu64" not %"PRIu64"\n",
               k,b0[0],p,b1[0],c2,c1);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] ...0x%016"PRIx64" - %"PRIx64" * ...0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p,b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_optsubadd(void)
{ uint64_t t, i, k;
  printf("Testing bignum_optsubadd with %d cases\n",tests);
  uint64_t c, c1, c2;
  uint64_t p;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     random_bignum(k,b1);
     random_bignum(k,b2);
     random_bignum(k,b3);
     p = random64();

     for (i = 0; i < k; ++i) b3[i] = b0[i];
     c1 = 0;
     if (p & (UINT64_C(1)<<63)) c1 = reference_sbb(k,b3,k,b3,k,b1,0);
     else if (p != 0) c1 = reference_adc(k,b3,k,b3,k,b1,0);

     c2 = bignum_optsubadd(k,b2,b0,p,b1);

     c = reference_compare(k,b2,k,b3);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" + sgn(%"PRIx64") * ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p,b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (c1 != c2)
      {
        printf("### Disparity: [size %4"PRIu64"]: ...0x%016"PRIx64" + sgn(%"PRIx64") * ...0x%016"PRIx64" carry %"PRIu64" not %"PRIu64"\n",
               k,b0[0],p,b1[0],c2,c1);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] ...0x%016"PRIx64" + sgn(%"PRIx64") * ...0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p,b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_pow2(void)
{ uint64_t t, i, k, n;
  printf("Testing bignum_pow2 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     n = random64() % (1000 * k + 1);
     if (rand() & 1) n %= (65 * k + 1);
     for (i = 0; i < k; ++i) b0[i] = 42;
     bignum_pow2(k,b0,n);
     for (i = 0; i < k; ++i) b1[i] = 0;
     if (n < 64*k) b1[n>>6] = UINT64_C(1)<<(n&UINT64_C(63));
     c = reference_compare(k,b0,k,b1);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_pow2(0x%016"PRIx64") = ....0x%016"PRIx64" not ....0x%016"PRIx64"\n",
               k,n,b0[0],b1[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size    0] bignum_pow2(0x%016"PRIx64")\n",n);
        else printf("OK: [size %4"PRIu64"] "
               "bignum_pow2(0x%016"PRIx64") = ....0x%016"PRIx64"\n",
               k,n,b0[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_shl_small(void)
{ uint64_t t, j, k1, k2, a, r;
  printf("Testing bignum_shl_small with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     a = random64();
     if (rand() & 31) a &= UINT64_C(63);
     random_bignum(k1,b1);
     random_bignum(k2,b2);
     for (j = 0; j < k2; ++j) b3[j] = b2[j] + 1;
     r = bignum_shl_small(k2,b2,k1,b1,a); b2[k2] = r;
     reference_cmul(k2+1,b3,(UINT64_C(1)<<(a&UINT64_C(63))),(k2 < k1 ? k2 : k1),b1);
     c = reference_compare(k2+1,b2,k2+1,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" := %4"PRIu64"] "
               "...0x%016"PRIx64" << %2"PRIu64", = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k1,b1[0],a,b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k2 == 0) printf("OK: [sizes %4"PRIu64" := %4"PRIu64"]\n",k2,k1);
        else printf("OK: [sizes %4"PRIu64" := %4"PRIu64"] ...0x%016"PRIx64" << %2"PRIu64" = ...0x%016"PRIx64"\n",
                    k2,k1,b1[0],a,b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_shr_small(void)
{ uint64_t t, j, k1, k2, a, r;
  printf("Testing bignum_shr_small with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     a = random64();
     if (rand() & 31) a &= UINT64_C(63);
     random_bignum(k1,b1);
     random_bignum(k2,b2);
     for (j = 0; j < k2+1; ++j) b3[j] = b2[j] + 1;

     r = bignum_shr_small(k2,b2+1,k1,b1,a);
     b2[0] = ((a&UINT64_C(63)) == 0) ? 0 : (r<<(64 - (a&UINT64_C(63))));

     reference_copy(k2+1,b3+1,k1,b1); b3[0] = 0;
     c = 0; for (j = 0; j < (a & UINT64_C(63)); ++j) c = reference_shr_samelen(k2+2,b3,b3,c);

     c = reference_compare(k2+1,b2,k2+1,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" := %4"PRIu64"] "
               "...0x%016"PRIx64" >> %2"PRIu64", = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k1,b1[0],a,b2[1],b3[1]);
        return 1;
      }
     else if (VERBOSE)
      { if (k2 == 0) printf("OK: [sizes %4"PRIu64" := %4"PRIu64"]\n",k2,k1);
        else printf("OK: [sizes %4"PRIu64" := %4"PRIu64"] ...0x%016"PRIx64" >> %2"PRIu64" = ...0x%016"PRIx64"\n",
                    k2,k1,b1[0],a,b2[1]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sqr(void)
{ uint64_t t, j, k0, k2;
  printf("Testing bignum_sqr with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k0 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k0,b0);
     random_bignum(k2,b2);
     for (j = 0; j < k2; ++j) b3[j] = b2[j];
     bignum_sqr(k2,b2,k0,b0);
     reference_mul(k2,b3,k0,b0,k0,b0);
     c = reference_compare(k2,b2,k2,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" := %4"PRIu64"^2] "
               "...0x%016"PRIx64" ^ 2 = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k0,b0[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k0 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" := %4"PRIu64"^2]\n",k2,k0);
        else printf("OK: [sizes %4"PRIu64" := %4"PRIu64"^2] ...0x%016"PRIx64" ^ 2 = ...0x%016"PRIx64"\n",
                    k2,k0,b0[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}


int test_bignum_sqr_specific
  (uint64_t p,uint64_t n, char *name,
   void (*f)(uint64_t *,uint64_t *))
{ uint64_t i, j;
  printf("Testing %s with %d cases\n",name,tests);
  int c;
  for (i = 0; i < tests; ++i)
   { random_bignum(n,b0);
     random_bignum(p,b2);
     for (j = 0; j < p; ++j) b3[j] = b2[j] + 1;
     (*f)(b2,b0);
     reference_mul(p,b3,n,b0,n,b0);
     c = reference_compare(p,b2,p,b3);
     if (c != 0)
      { printf("### Disparity: [sizes %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"] "
               "...0x%016"PRIx64"^2  = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               n,n,p,b0[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (p == 0) printf("OK: [size %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"]\n",n,n,p);
        else printf("OK: [size %4"PRIu64" x %4"PRIu64" -> %4"PRIu64"] "
                    "...0x%016"PRIx64"^2 =..0x%016"PRIx64"\n",
                    n,n,p,b0[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sqr_4_8(void)
{ return test_bignum_sqr_specific(8,4,"bignum_sqr_4_8",bignum_sqr_4_8);
}

int test_bignum_sqr_4_8_alt(void)
{ return test_bignum_sqr_specific(8,4,"bignum_sqr_4_8_alt",bignum_sqr_4_8_alt);
}

int test_bignum_sqr_6_12(void)
{ return test_bignum_sqr_specific(12,6,"bignum_sqr_6_12",bignum_sqr_6_12);
}

int test_bignum_sqr_8_16(void)
{ return test_bignum_sqr_specific(16,8,"bignum_sqr_8_16",bignum_sqr_8_16);
}

int test_bignum_sqr_p256k1(void)
{ uint64_t i, k;
  printf("Testing bignum_sqr_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_sqr_p256k1(b2,b0);
     reference_mul(2*k,b4,k,b0,k,b0);
     reference_copy(2*k,b3,k,p_256k1);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sqr_p256k1_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_sqr_p256k1_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_sqr_p256k1_alt(b2,b0);
     reference_mul(2*k,b4,k,b0,k,b0);
     reference_copy(2*k,b3,k,p_256k1);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sqr_p521(void)
{ uint64_t i, k;
  printf("Testing bignum_sqr_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     bignum_sqr_p521(b2,b0);
     reference_mul(2*k,b4,k,b0,k,b0);
     reference_copy(2*k,b3,k,p_521);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_521[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_521[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sub(void)
{ uint64_t t, j, k0, k1, k2;
  printf("Testing bignum_sub with %d cases\n",tests);
  uint64_t c, c1, c2;
  for (t = 0; t < tests; ++t)
   { k0 = (unsigned) rand() % MAXSIZE;
     k1 = (unsigned) rand() % MAXSIZE;
     k2 = (unsigned) rand() % MAXSIZE;
     random_bignum(k0,b0);
     random_bignum(k1,b1);
     random_bignum(k2,b2);
     for (j = 0; j < k2; ++j) b3[j] = b2[j];
     c1 = bignum_sub(k2,b2,k0,b0,k1,b1);
     c2 = reference_sbb(k2,b3,k0,b0,k1,b1,0);
     c = reference_compare(k2,b2,k2,b3);
     if ((c != 0) || (c1 != c2))
      { printf("### Disparity: [sizes %4"PRIu64" := %4"PRIu64" - %4"PRIu64"] "
               "...0x%016"PRIx64" - ...0x%016"PRIx64" = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k2,k0,k1,b0[0],b1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k0 == 0 || k1 == 0 || k2 == 0) printf("OK: [sizes %4"PRIu64" := %4"PRIu64" - %4"PRIu64"]\n",k2,k0,k1);
        else printf("OK: [sizes %4"PRIu64" := %4"PRIu64" - %4"PRIu64"] ...0x%016"PRIx64" - ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
                    k2,k0,k1,b0[0],b1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}


int test_bignum_sub_p256(void)
{ uint64_t i, k;
  printf("Testing bignum_sub_p256 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_256);
     bignum_sub_p256(b2,b0,b1);
     reference_copy(k+1,b3,k,p_256);
     reference_copy(k+1,b4,k,b0);
     reference_copy(k+1,b5,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_sub_samelen(k+1,b4,b4,b5);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_256[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_256[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sub_p256k1(void)
{ uint64_t i, k;
  printf("Testing bignum_sub_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_256k1);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_256k1);
     bignum_sub_p256k1(b2,b0,b1);
     reference_copy(k+1,b3,k,p_256k1);
     reference_copy(k+1,b4,k,b0);
     reference_copy(k+1,b5,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_sub_samelen(k+1,b4,b4,b5);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sub_p384(void)
{ uint64_t i, k;
  printf("Testing bignum_sub_p384 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_384);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_384);
     bignum_sub_p384(b2,b0,b1);
     reference_copy(k+1,b3,k,p_384);
     reference_copy(k+1,b4,k,b0);
     reference_copy(k+1,b5,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_sub_samelen(k+1,b4,b4,b5);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_384[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_384[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sub_p521(void)
{ uint64_t i, k;
  printf("Testing bignum_sub_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_521);
     bignum_sub_p521(b2,b0,b1);
     reference_copy(k+1,b3,k,p_521);
     reference_copy(k+1,b4,k,b0);
     reference_copy(k+1,b5,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_sub_samelen(k+1,b4,b4,b5);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_521[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_521[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tobebytes_4(void)
{ uint64_t t;
  printf("Testing bignum_tobebytes_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_bigendian(4,b3,b0);
     bignum_tobebytes_4((uint8_t *)b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_tobebytes_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_tobebytes_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tobebytes_6(void)
{ uint64_t t;
  printf("Testing bignum_tobebytes_6 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     reference_bigendian(6,b3,b0);
     bignum_tobebytes_6((uint8_t *)b4,b0);
     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_tobebytes_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_tobebytes_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tolebytes_4(void)
{ uint64_t t;
  printf("Testing bignum_tolebytes_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_littleendian(4,b3,b0);
     bignum_tolebytes_4((uint8_t *)b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_tolebytes_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_tolebytes_4(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tolebytes_6(void)
{ uint64_t t;
  printf("Testing bignum_tolebytes_6 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     reference_littleendian(6,b3,b0);
     bignum_tolebytes_6((uint8_t *)b4,b0);
     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_tolebytes_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_tolebytes_6(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[5],b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tomont_p256(void)
{ uint64_t t;
  printf("Testing bignum_tomont_p256 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_modpowtwo(4,b1,256,p_256);
     reference_mul(8,b2,4,b1,4,b0);
     reference_copy(8,b1,4,p_256);
     reference_mod(8,b3,b2,b1);
     bignum_tomont_p256(b4,b0);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tomont_p256_alt(void)
{ uint64_t t;
  printf("Testing bignum_tomont_p256_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_modpowtwo(4,b1,256,p_256);
     reference_mul(8,b2,4,b1,4,b0);
     reference_copy(8,b1,4,p_256);
     reference_mod(8,b3,b2,b1);
     bignum_tomont_p256_alt(b4,b0);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tomont_p256k1(void)
{ uint64_t t;
  printf("Testing bignum_tomont_p256k1 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_modpowtwo(4,b1,256,p_256k1);
     reference_mul(8,b2,4,b1,4,b0);
     reference_copy(8,b1,4,p_256k1);
     reference_mod(8,b3,b2,b1);
     bignum_tomont_p256k1(b4,b0);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tomont_p256k1_alt(void)
{ uint64_t t;
  printf("Testing bignum_tomont_p256k1_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_modpowtwo(4,b1,256,p_256k1);
     reference_mul(8,b2,4,b1,4,b0);
     reference_copy(8,b1,4,p_256k1);
     reference_mod(8,b3,b2,b1);
     bignum_tomont_p256k1_alt(b4,b0);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_256k1 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tomont_p384(void)
{ uint64_t t;
  printf("Testing bignum_tomont_p384 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     reference_modpowtwo(6,b1,384,p_384);
     reference_mul(12,b2,6,b1,6,b0);
     reference_copy(12,b1,6,p_384);
     reference_mod(12,b3,b2,b1);
     bignum_tomont_p384(b4,b0);

     c = reference_compare(6,b3,6,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^384 * ...0x%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[5],b4[0],b3[5],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^384 * ...0x%016"PRIx64" mod p_384 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(6),b0[0],b4[5],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_tomont_p521(void)
{ uint64_t t;
  printf("Testing bignum_tomont_p521 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b0);
     reference_modpowtwo(9,b1,576,p_521);
     reference_mul(18,b2,9,b1,9,b0);
     reference_copy(18,b1,9,p_521);
     reference_mod(18,b3,b2,b1);
     bignum_tomont_p521(b4,b0);

     c = reference_compare(9,b3,9,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^576 * ...0x%016"PRIx64" mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[0],b4[8],b4[0],b3[8],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^576 * ...0x%016"PRIx64" mod p_521 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[0],b4[8],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_triple_p256(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_p256 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_triple_p256(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_256);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_256[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_triple_p256_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_p256_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_triple_p256_alt(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_256);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_256[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_triple_p256k1(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_p256k1 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_triple_p256k1(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_256k1);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_triple_p256k1_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_p256k1_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_triple_p256k1_alt(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_256k1);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_256k1[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_256k1[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_triple_p384(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_p384 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;
     random_bignum(k,b0);
     bignum_triple_p384(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_384);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_384[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_384[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_triple_p521(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_p521 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     bignum_triple_p521(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_521);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_521[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_521[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_word_bytereverse(void)
{ uint64_t i, a, x, y;
  printf("Testing word_bytereverse with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { a = random64();
     x = word_bytereverse(a);
     y = reference_wordbytereverse(a);
     if (x != y)
      { printf("### Disparity: word_bytereverse(0x%016"PRIx64") = 0x%016"PRIx64" not 0x%016"PRIx64"\n",a,x,y);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: word_bytereverse(0x%016"PRIx64") = 0x%016"PRIx64"\n",a,x);
      }
    }
  printf("All OK\n");
  return 0;
}

int test_word_clz(void)
{ uint64_t i, a, x, y;
  printf("Testing word_clz with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { a = random64();
     x = word_clz(a);
     y = reference_wordclz(a);
     if (x != y)
      { printf("### Disparity: word_clz(0x%016"PRIx64") = %"PRIu64" not %"PRIu64"\n",a,x,y);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: word_clz(0x%016"PRIx64") = %"PRIu64"\n",a,x);
      }
    }
  printf("All OK\n");
  return 0;
}

int test_word_ctz(void)
{ uint64_t i, a, x, y;
  printf("Testing word_ctz with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { a = random64();
     x = word_ctz(a);
     y = reference_wordctz(a);
     if (x != y)
      { printf("### Disparity: word_ctz(0x%016"PRIx64") = %"PRIu64" not %"PRIu64"\n",a,x,y);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: word_ctz(0x%016"PRIx64") = %"PRIu64"\n",a,x);
      }
    }
  printf("All OK\n");
  return 0;
}

int test_word_max(void)
{ uint64_t i, a, b, x, y;
  printf("Testing word_max with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { a = random64();
     b = random64();
     if (rand() & 1) a = b + (rand() & 7);
     if (rand() & 1) b = a + (rand() & 7);

     x = word_max(a,b);
     y = (a < b) ? b : a;;
     if (x != y)
      { printf("### Disparity: word_max(0x%016"PRIx64",0x%016"PRIx64") = 0x%016"PRIx64" not 0x%016"PRIx64"\n",a,b,x,y);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: word_max(0x%016"PRIx64",0x%016"PRIx64") = 0x%016"PRIx64"\n",a,b,x);
      }
    }
  printf("All OK\n");
  return 0;
}

int test_word_min(void)
{ uint64_t i, a, b, x, y;
  printf("Testing word_min with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { a = random64();
     b = random64();
     if (rand() & 1) a = b + (rand() & 7);
     if (rand() & 1) b = a + (rand() & 7);

     x = word_min(a,b);
     y = (a < b) ? a : b;;
     if (x != y)
      { printf("### Disparity: word_min(0x%016"PRIx64",0x%016"PRIx64") = 0x%016"PRIx64" not 0x%016"PRIx64"\n",a,b,x,y);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: word_min(0x%016"PRIx64",0x%016"PRIx64") = 0x%016"PRIx64"\n",a,b,x);
      }
    }
  printf("All OK\n");
  return 0;
}

int test_word_negmodinv(void)
{ uint64_t i, a, x;
  printf("Testing word_negmodinv with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { a = 2 * random64() + 1;
     x = word_negmodinv(a);
     if (a * x + 1 != 0)
      { printf("### Disparity: a * word_negmodinv a + 1 = 0x%016"PRIx64" * 0x%016"PRIx64" + 1 = %"PRIu64"\n",a,x,a*x+1);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: a * word_negmodinv a + 1 = 0x%016"PRIx64" * 0x%016"PRIx64" + 1 = %"PRIu64"\n",a,x,a*x+1);
      }
    }
  printf("All OK\n");
  return 0;
}

int test_word_recip(void)
{ uint64_t i, a, x;
  printf("Testing word_recip with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { a = random64() | (UINT64_C(1)<<63);
     x = word_recip(a);

     b0[2] = UINT64_C(1), b0[1] = b0[0] = UINT64_C(0);
     bignum_of_word(3,b1,a);
     reference_divmod(3,b3,b2,b0,b1);
     if (a == (UINT64_C(1)<<63)) b3[1] = UINT64_C(1), b3[0] = ~UINT64_C(0);

     if (!((b3[0] == x) && b3[1] == UINT64_C(1)))
      { printf("### Disparity: word_recip(%"PRIu64") = %"PRIu64" not %"PRIu64"\n",
               a,x,b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: word_recip(%"PRIu64") = %"PRIu64"\n",a,b3[0]);
      }
    }
  printf("All OK\n");
  return 0;
}

#define ASSIGN6(x,n0,n1,n2,n3,n4,n5) x[0] = UINT64_C(n0), x[1] = UINT64_C(n1), x[2] = UINT64_C(n2), x[3] = UINT64_C(n3), x[4] = UINT64_C(n4), x[5] = UINT64_C(n5)

#define ASSIGN1(x,n) x[0] = UINT64_C(n)

#define CHECK6(x,n0,n1,n2,n3,n4,n5) \
  if ((x[0] != UINT64_C(n0)) || (x[1] != UINT64_C(n1)) || (x[2] != UINT64_C(n2)) || (x[3] != UINT64_C(n3)) || (x[4] != UINT64_C(n4)) || (x[5] != UINT64_C(n5))) \
  { printf("Failed known value test\n"); ++failures; } else { ++successes; }

#define CHECK1(x,n) \
  if (x[0] != UINT64_C(n)) \
  { printf("Failed known value test\n"); ++failures; } else { ++successes; }

int test_known_values(void)
{ int failures = 0, successes = 0;
  printf("Testing known value cases\n");

#include "known_value_tests_p384.h"

  if (failures != 0)
    { printf ("Failed %d known value tests, passed %d\n",failures,successes);
      return failures;
    }
  else
    { printf("Successfully passed %d known value tests\n",successes);
      return 0;
    }
}

#define dotest(f) (f()==0) ? ++successes : ++failures;

int test_all(void)
{ int failures = 0, successes = 0;

  dotest(test_bignum_add);
  dotest(test_bignum_add_p256);
  dotest(test_bignum_add_p256k1);
  dotest(test_bignum_add_p384);
  dotest(test_bignum_add_p521);
  dotest(test_bignum_amontifier);
  dotest(test_bignum_amontmul);
  dotest(test_bignum_amontredc);
  dotest(test_bignum_amontsqr);
  dotest(test_bignum_bigendian_4);
  dotest(test_bignum_bigendian_6);
  dotest(test_bignum_bitfield);
  dotest(test_bignum_bitsize);
  dotest(test_bignum_cdiv);
  dotest(test_bignum_cdiv_exact);
  dotest(test_bignum_cld);
  dotest(test_bignum_clz);
  dotest(test_bignum_cmadd);
  dotest(test_bignum_cmnegadd);
  dotest(test_bignum_cmod);
  dotest(test_bignum_cmul);
  dotest(test_bignum_cmul_p256);
  dotest(test_bignum_cmul_p256_alt);
  dotest(test_bignum_cmul_p256k1);
  dotest(test_bignum_cmul_p256k1_alt);
  dotest(test_bignum_cmul_p384);
  dotest(test_bignum_cmul_p521);
  dotest(test_bignum_coprime);
  dotest(test_bignum_copy);
  dotest(test_bignum_ctd);
  dotest(test_bignum_ctz);
  dotest(test_bignum_deamont_p256);
  dotest(test_bignum_deamont_p256_alt);
  dotest(test_bignum_deamont_p256k1);
  dotest(test_bignum_deamont_p384);
  dotest(test_bignum_deamont_p521);
  dotest(test_bignum_demont);
  dotest(test_bignum_demont_p256);
  dotest(test_bignum_demont_p256_alt);
  dotest(test_bignum_demont_p256k1);
  dotest(test_bignum_demont_p384);
  dotest(test_bignum_demont_p521);
  dotest(test_bignum_digit);
  dotest(test_bignum_digitsize);
  dotest(test_bignum_divmod10);
  dotest(test_bignum_double_p256);
  dotest(test_bignum_double_p256k1);
  dotest(test_bignum_double_p384);
  dotest(test_bignum_double_p521);
  dotest(test_bignum_emontredc);
  dotest(test_bignum_emontredc_8n);
  dotest(test_bignum_eq);
  dotest(test_bignum_even);
  dotest(test_bignum_frombebytes_4);
  dotest(test_bignum_frombebytes_6);
  dotest(test_bignum_fromlebytes_4);
  dotest(test_bignum_fromlebytes_6);
  dotest(test_bignum_ge);
  dotest(test_bignum_gt);
  dotest(test_bignum_half_p256);
  dotest(test_bignum_half_p256k1);
  dotest(test_bignum_half_p384);
  dotest(test_bignum_half_p521);
  dotest(test_bignum_iszero);
  dotest(test_bignum_kmul_16_32);
  dotest(test_bignum_kmul_32_64);
  dotest(test_bignum_ksqr_16_32);
  dotest(test_bignum_ksqr_32_64);
  dotest(test_bignum_le);
  dotest(test_bignum_littleendian_4);
  dotest(test_bignum_littleendian_6);
  dotest(test_bignum_lt);
  dotest(test_bignum_madd);
  dotest(test_bignum_mod_n256);
  dotest(test_bignum_mod_n256_alt);
  dotest(test_bignum_mod_n256_4);
  dotest(test_bignum_mod_n256k1_4);
  dotest(test_bignum_mod_n384);
  dotest(test_bignum_mod_n384_6);
  dotest(test_bignum_mod_n521_9);
  dotest(test_bignum_mod_p256);
  dotest(test_bignum_mod_p256_alt);
  dotest(test_bignum_mod_p256_4);
  dotest(test_bignum_mod_p256k1_4);
  dotest(test_bignum_mod_p384);
  dotest(test_bignum_mod_p384_6);
  dotest(test_bignum_mod_p521_9);
  dotest(test_bignum_modadd);
  dotest(test_bignum_moddouble);
  dotest(test_bignum_modifier);
  dotest(test_bignum_modinv);
  dotest(test_bignum_modoptneg);
  dotest(test_bignum_modsub);
  dotest(test_bignum_montifier);
  dotest(test_bignum_montmul);
  dotest(test_bignum_montmul_p256);
  dotest(test_bignum_montmul_p256_alt);
  dotest(test_bignum_montmul_p256k1);
  dotest(test_bignum_montmul_p256k1_alt);
  dotest(test_bignum_montmul_p384);
  dotest(test_bignum_montmul_p521);
  dotest(test_bignum_montredc);
  dotest(test_bignum_montsqr);
  dotest(test_bignum_montsqr_p256);
  dotest(test_bignum_montsqr_p256_alt);
  dotest(test_bignum_montsqr_p256k1);
  dotest(test_bignum_montsqr_p256k1_alt);
  dotest(test_bignum_montsqr_p384);
  dotest(test_bignum_montsqr_p521);
  dotest(test_bignum_mul);
  dotest(test_bignum_mul_4_8);
  dotest(test_bignum_mul_4_8_alt);
  dotest(test_bignum_mul_6_12);
  dotest(test_bignum_mul_8_16);
  dotest(test_bignum_mul_p256k1);
  dotest(test_bignum_mul_p256k1_alt);
  dotest(test_bignum_mul_p521);
  dotest(test_bignum_muladd10);
  dotest(test_bignum_mux);
  dotest(test_bignum_mux_4);
  dotest(test_bignum_mux_6);
  dotest(test_bignum_mux16);
  dotest(test_bignum_neg_p256);
  dotest(test_bignum_neg_p256k1);
  dotest(test_bignum_neg_p384);
  dotest(test_bignum_neg_p521);
  dotest(test_bignum_negmodinv);
  dotest(test_bignum_nonzero);
  dotest(test_bignum_nonzero_4);
  dotest(test_bignum_nonzero_6);
  dotest(test_bignum_normalize);
  dotest(test_bignum_odd);
  dotest(test_bignum_of_word);
  dotest(test_bignum_optadd);
  dotest(test_bignum_optneg);
  dotest(test_bignum_optneg_p256);
  dotest(test_bignum_optneg_p256k1);
  dotest(test_bignum_optneg_p384);
  dotest(test_bignum_optneg_p521);
  dotest(test_bignum_optsub);
  dotest(test_bignum_optsubadd);
  dotest(test_bignum_pow2);
  dotest(test_bignum_shl_small);
  dotest(test_bignum_shr_small);
  dotest(test_bignum_sqr);
  dotest(test_bignum_sqr_4_8);
  dotest(test_bignum_sqr_4_8_alt);
  dotest(test_bignum_sqr_6_12);
  dotest(test_bignum_sqr_8_16);
  dotest(test_bignum_sqr_p256k1);
  dotest(test_bignum_sqr_p256k1_alt);
  dotest(test_bignum_sqr_p521);
  dotest(test_bignum_sub);
  dotest(test_bignum_sub_p256);
  dotest(test_bignum_sub_p256k1);
  dotest(test_bignum_sub_p384);
  dotest(test_bignum_sub_p521);
  dotest(test_bignum_tobebytes_4);
  dotest(test_bignum_tobebytes_6);
  dotest(test_bignum_tolebytes_4);
  dotest(test_bignum_tolebytes_6);
  dotest(test_bignum_tomont_p256);
  dotest(test_bignum_tomont_p256_alt);
  dotest(test_bignum_tomont_p256k1);
  dotest(test_bignum_tomont_p256k1_alt);
  dotest(test_bignum_tomont_p384);
  dotest(test_bignum_tomont_p521);
  dotest(test_bignum_triple_p256);
  dotest(test_bignum_triple_p256_alt);
  dotest(test_bignum_triple_p256k1);
  dotest(test_bignum_triple_p256k1_alt);
  dotest(test_bignum_triple_p384);
  dotest(test_bignum_triple_p521);
  dotest(test_word_bytereverse);
  dotest(test_word_clz);
  dotest(test_word_ctz);
  dotest(test_word_max);
  dotest(test_word_min);
  dotest(test_word_negmodinv);
  dotest(test_word_recip);

  failures += test_known_values();

  if (failures != 0)
   { printf("All tests run, **** %d failures out of %d ****\n",
            failures,failures+successes);
     return 1;
   }
  else if (tests == 0)
   { printf("Zero tests run, *** no testing\n");
     return 1;
   }
  else
   { printf("All %d tests run, all passed\n",successes);
     return 0;
   }
}

// This skips functions where the x86 form uses instructions
// mulx, adcx or adoc (from BMI2 and ADX extensions). This is not
// relevant on ARM. The TEST_ALL_APPLICABLE tries to select
// this based on the architecture and CPUID, otherwise you
// just get "illegal instruction". Generally your machine
// has to be fairly old not to support these instructions.

int test_allnonbmi()
{ int failures = 0, successes = 0;

  dotest(test_bignum_add);
  dotest(test_bignum_add_p256);
  dotest(test_bignum_add_p256k1);
  dotest(test_bignum_add_p384);
  dotest(test_bignum_add_p521);
  dotest(test_bignum_amontifier);
  dotest(test_bignum_amontmul);
  dotest(test_bignum_amontredc);
  dotest(test_bignum_amontsqr);
  dotest(test_bignum_bigendian_4);
  dotest(test_bignum_bigendian_6);
  dotest(test_bignum_bitfield);
  dotest(test_bignum_bitsize);
  dotest(test_bignum_cdiv);
  dotest(test_bignum_cdiv_exact);
  dotest(test_bignum_cld);
  dotest(test_bignum_clz);
  dotest(test_bignum_cmadd);
  dotest(test_bignum_cmnegadd);
  dotest(test_bignum_cmod);
  dotest(test_bignum_cmul);
  dotest(test_bignum_cmul_p256_alt);
  dotest(test_bignum_cmul_p256k1_alt);
  dotest(test_bignum_coprime);
  dotest(test_bignum_copy);
  dotest(test_bignum_ctd);
  dotest(test_bignum_ctz);
  dotest(test_bignum_deamont_p256_alt);
  dotest(test_bignum_deamont_p256k1);
  dotest(test_bignum_deamont_p521);
  dotest(test_bignum_demont);
  dotest(test_bignum_demont_p256_alt);
  dotest(test_bignum_demont_p256k1);
  dotest(test_bignum_demont_p521);
  dotest(test_bignum_digit);
  dotest(test_bignum_digitsize);
  dotest(test_bignum_divmod10);
  dotest(test_bignum_double_p256);
  dotest(test_bignum_double_p256k1);
  dotest(test_bignum_double_p384);
  dotest(test_bignum_double_p521);
  dotest(test_bignum_emontredc);
  dotest(test_bignum_eq);
  dotest(test_bignum_even);
  dotest(test_bignum_frombebytes_4);
  dotest(test_bignum_frombebytes_6);
  dotest(test_bignum_fromlebytes_4);
  dotest(test_bignum_fromlebytes_6);
  dotest(test_bignum_ge);
  dotest(test_bignum_gt);
  dotest(test_bignum_half_p256);
  dotest(test_bignum_half_p256k1);
  dotest(test_bignum_half_p384);
  dotest(test_bignum_half_p521);
  dotest(test_bignum_iszero);
  dotest(test_bignum_le);
  dotest(test_bignum_littleendian_4);
  dotest(test_bignum_littleendian_6);
  dotest(test_bignum_lt);
  dotest(test_bignum_madd);
  dotest(test_bignum_mod_n256_alt);
  dotest(test_bignum_mod_n256_4);
  dotest(test_bignum_mod_n256k1_4);
  dotest(test_bignum_mod_n384_6);
  dotest(test_bignum_mod_p256_alt);
  dotest(test_bignum_mod_p256_4);
  dotest(test_bignum_mod_p256k1_4);
  dotest(test_bignum_mod_p384_6);
  dotest(test_bignum_mod_p521_9);
  dotest(test_bignum_modadd);
  dotest(test_bignum_moddouble);
  dotest(test_bignum_modifier);
  dotest(test_bignum_modinv);
  dotest(test_bignum_modoptneg);
  dotest(test_bignum_modsub);
  dotest(test_bignum_montifier);
  dotest(test_bignum_montmul);
  dotest(test_bignum_montmul_p256_alt);
  dotest(test_bignum_montmul_p256k1_alt);
  dotest(test_bignum_montredc);
  dotest(test_bignum_montsqr);
  dotest(test_bignum_montsqr_p256_alt);
  dotest(test_bignum_montsqr_p256k1_alt);
  dotest(test_bignum_mul);
  dotest(test_bignum_mul_4_8_alt);
  dotest(test_bignum_mul_p256k1_alt);
  dotest(test_bignum_muladd10);
  dotest(test_bignum_mux);
  dotest(test_bignum_mux_4);
  dotest(test_bignum_mux_6);
  dotest(test_bignum_mux16);
  dotest(test_bignum_neg_p256);
  dotest(test_bignum_neg_p256k1);
  dotest(test_bignum_neg_p384);
  dotest(test_bignum_neg_p521);
  dotest(test_bignum_negmodinv);
  dotest(test_bignum_nonzero);
  dotest(test_bignum_nonzero_4);
  dotest(test_bignum_nonzero_6);
  dotest(test_bignum_normalize);
  dotest(test_bignum_odd);
  dotest(test_bignum_of_word);
  dotest(test_bignum_optadd);
  dotest(test_bignum_optneg);
  dotest(test_bignum_optneg_p256);
  dotest(test_bignum_optneg_p256k1);
  dotest(test_bignum_optneg_p384);
  dotest(test_bignum_optneg_p521);
  dotest(test_bignum_optsub);
  dotest(test_bignum_optsubadd);
  dotest(test_bignum_pow2);
  dotest(test_bignum_shl_small);
  dotest(test_bignum_shr_small);
  dotest(test_bignum_sqr);
  dotest(test_bignum_sqr_4_8_alt);
  dotest(test_bignum_sqr_p256k1_alt);
  dotest(test_bignum_sub);
  dotest(test_bignum_sub_p256);
  dotest(test_bignum_sub_p256k1);
  dotest(test_bignum_sub_p384);
  dotest(test_bignum_sub_p521);
  dotest(test_bignum_tobebytes_4);
  dotest(test_bignum_tobebytes_6);
  dotest(test_bignum_tolebytes_4);
  dotest(test_bignum_tolebytes_6);
  dotest(test_bignum_tomont_p256_alt);
  dotest(test_bignum_tomont_p256k1_alt);
  dotest(test_bignum_tomont_p521);
  dotest(test_bignum_triple_p256_alt);
  dotest(test_bignum_triple_p256k1_alt);
  dotest(test_word_bytereverse);
  dotest(test_word_clz);
  dotest(test_word_ctz);
  dotest(test_word_max);
  dotest(test_word_min);
  dotest(test_word_negmodinv);
  dotest(test_word_recip);

  if (failures != 0)
   { printf("*** Partial tests (%d) run and **** %d failures ***\n",
            successes+failures,failures);
     return 1;
   }
  else if (tests == 0)
   { printf("*** Zero tests run, *** no testing\n");
     return 1;
   }
  else
   { printf("*** Partial tests (%d) run; no failures but some skipped\n",
            successes);
     printf("*** x86 BMI and ADX instructions needed for other functions\n");
     return 0;
   }
}

// ****************************************************************************
// Main dispatching to appropriate test code
// ****************************************************************************

// On x86 machines, restrict the set of tested functions appropriately
// if the machine does not seem to support the BMI2 and ADX extensions.

#ifdef __x86_64__

int cpuid_extendedfeatures(void)
{ int a = 7, b = 0, c = 0, d = 0;
  asm ("cpuid\n\t"
    : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
    : "0" (a), "2" (c));
  return b;
}

int all_applicable(void)
{ int c = cpuid_extendedfeatures();
  return (c & (1ul<<8)) && (c & (1ul<<19));
}

#else

int all_applicable(void)
{ return 1;
}

#endif

// If there is a single command line argument then interpret it
// as the number of tests, which otherwise defaults to TESTS
// Zero is interpreted as the default TESTS but for *all* tests
// including known value tests.

int main(int argc, char *argv[])
{ if (argc == 2)
    tests = atoi(argv[1]);
  else
    tests = TESTS;

  if (tests == 0)
   { tests = TESTS;
     return test_all();
   }

   switch(WHAT)
   { case TEST_ALL:                       return test_all();

     case TEST_ALL_APPLICABLE:            if (all_applicable())
                                            return test_all();
                                          else
                                            return test_allnonbmi();

     case TEST_KNOWN_VALUES:              return test_known_values();

     case TEST_BIGNUM_ADD:                return test_bignum_add();
     case TEST_BIGNUM_ADD_P256:           return test_bignum_add_p256();
     case TEST_BIGNUM_ADD_P256K1:         return test_bignum_add_p256k1();
     case TEST_BIGNUM_ADD_P384:           return test_bignum_add_p384();
     case TEST_BIGNUM_ADD_P521:           return test_bignum_add_p521();
     case TEST_BIGNUM_AMONTIFIER:         return test_bignum_amontifier();
     case TEST_BIGNUM_AMONTMUL:           return test_bignum_amontmul();
     case TEST_BIGNUM_AMONTREDC:          return test_bignum_amontredc();
     case TEST_BIGNUM_AMONTSQR:           return test_bignum_amontsqr();
     case TEST_BIGNUM_BIGENDIAN_4:        return test_bignum_bigendian_4();
     case TEST_BIGNUM_BIGENDIAN_6:        return test_bignum_bigendian_6();
     case TEST_BIGNUM_BITFIELD:           return test_bignum_bitfield();
     case TEST_BIGNUM_BITSIZE:            return test_bignum_bitsize();
     case TEST_BIGNUM_CDIV:               return test_bignum_cdiv();
     case TEST_BIGNUM_CDIV_EXACT:         return test_bignum_cdiv_exact();
     case TEST_BIGNUM_CLD:                return test_bignum_cld();
     case TEST_BIGNUM_CLZ:                return test_bignum_clz();
     case TEST_BIGNUM_CMADD:              return test_bignum_cmadd();
     case TEST_BIGNUM_CMNEGADD:           return test_bignum_cmnegadd();
     case TEST_BIGNUM_CMOD:               return test_bignum_cmod();
     case TEST_BIGNUM_CMUL:               return test_bignum_cmul();
     case TEST_BIGNUM_CMUL_P256:          return test_bignum_cmul_p256();
     case TEST_BIGNUM_CMUL_P256_ALT:      return test_bignum_cmul_p256_alt();
     case TEST_BIGNUM_CMUL_P256K1:        return test_bignum_cmul_p256k1();
     case TEST_BIGNUM_CMUL_P256K1_ALT:    return test_bignum_cmul_p256k1_alt();
     case TEST_BIGNUM_CMUL_P384:          return test_bignum_cmul_p384();
     case TEST_BIGNUM_CMUL_P521:          return test_bignum_cmul_p521();
     case TEST_BIGNUM_COPRIME:            return test_bignum_coprime();
     case TEST_BIGNUM_COPY:               return test_bignum_copy();
     case TEST_BIGNUM_CTD:                return test_bignum_ctd();
     case TEST_BIGNUM_CTZ:                return test_bignum_ctz();
     case TEST_BIGNUM_DEAMONT_P256:       return test_bignum_deamont_p256();
     case TEST_BIGNUM_DEAMONT_P256_ALT:   return test_bignum_deamont_p256_alt();
     case TEST_BIGNUM_DEAMONT_P256K1:     return test_bignum_deamont_p256k1();
     case TEST_BIGNUM_DEAMONT_P384:       return test_bignum_deamont_p384();
     case TEST_BIGNUM_DEAMONT_P521:       return test_bignum_deamont_p521();
     case TEST_BIGNUM_DEMONT:             return test_bignum_demont();
     case TEST_BIGNUM_DEMONT_P256:        return test_bignum_demont_p256();
     case TEST_BIGNUM_DEMONT_P256_ALT:    return test_bignum_demont_p256_alt();
     case TEST_BIGNUM_DEMONT_P256K1:      return test_bignum_demont_p256k1();
     case TEST_BIGNUM_DEMONT_P384:        return test_bignum_demont_p384();
     case TEST_BIGNUM_DEMONT_P521:        return test_bignum_demont_p521();
     case TEST_BIGNUM_DIGIT:              return test_bignum_digit();
     case TEST_BIGNUM_DIGITSIZE:          return test_bignum_digitsize();
     case TEST_BIGNUM_DIVMOD10 :          return test_bignum_divmod10();
     case TEST_BIGNUM_DOUBLE_P256:        return test_bignum_double_p256();
     case TEST_BIGNUM_DOUBLE_P256K1:      return test_bignum_double_p256k1();
     case TEST_BIGNUM_DOUBLE_P384:        return test_bignum_double_p384();
     case TEST_BIGNUM_DOUBLE_P521:        return test_bignum_double_p521();
     case TEST_BIGNUM_EMONTREDC:          return test_bignum_emontredc();
     case TEST_BIGNUM_EMONTREDC_8N:       return test_bignum_emontredc_8n();
     case TEST_BIGNUM_EQ:                 return test_bignum_eq();
     case TEST_BIGNUM_EVEN:               return test_bignum_even();
     case TEST_BIGNUM_FROMBEBYTES_4:      return test_bignum_frombebytes_4();
     case TEST_BIGNUM_FROMBEBYTES_6:      return test_bignum_frombebytes_6();
     case TEST_BIGNUM_FROMLEBYTES_4:      return test_bignum_fromlebytes_4();
     case TEST_BIGNUM_FROMLEBYTES_6:      return test_bignum_fromlebytes_6();
     case TEST_BIGNUM_GE:                 return test_bignum_ge();
     case TEST_BIGNUM_GT:                 return test_bignum_gt();
     case TEST_BIGNUM_HALF_P256:          return test_bignum_half_p256();
     case TEST_BIGNUM_HALF_P256K1:        return test_bignum_half_p256k1();
     case TEST_BIGNUM_HALF_P384:          return test_bignum_half_p384();
     case TEST_BIGNUM_HALF_P521:          return test_bignum_half_p521();
     case TEST_BIGNUM_ISZERO:             return test_bignum_iszero();
     case TEST_BIGNUM_KMUL_16_32:         return test_bignum_kmul_16_32();
     case TEST_BIGNUM_KMUL_32_64:         return test_bignum_kmul_32_64();
     case TEST_BIGNUM_KSQR_16_32:         return test_bignum_ksqr_16_32();
     case TEST_BIGNUM_KSQR_32_64:         return test_bignum_ksqr_32_64();
     case TEST_BIGNUM_LE:                 return test_bignum_le();
     case TEST_BIGNUM_LITTLEENDIAN_4:     return test_bignum_littleendian_4();
     case TEST_BIGNUM_LITTLEENDIAN_6:     return test_bignum_littleendian_6();
     case TEST_BIGNUM_LT:                 return test_bignum_lt();
     case TEST_BIGNUM_MADD:               return test_bignum_madd();
     case TEST_BIGNUM_MOD_N256:           return test_bignum_mod_n256();
     case TEST_BIGNUM_MOD_N256_ALT:       return test_bignum_mod_n256_alt();
     case TEST_BIGNUM_MOD_N256_4:         return test_bignum_mod_n256_4();
     case TEST_BIGNUM_MOD_N256K1_4:       return test_bignum_mod_n256k1_4();
     case TEST_BIGNUM_MOD_N384:           return test_bignum_mod_n384();
     case TEST_BIGNUM_MOD_N384_6:         return test_bignum_mod_n384_6();
     case TEST_BIGNUM_MOD_N521_9:         return test_bignum_mod_n521_9();
     case TEST_BIGNUM_MOD_P256:           return test_bignum_mod_p256();
     case TEST_BIGNUM_MOD_P256_ALT:       return test_bignum_mod_p256_alt();
     case TEST_BIGNUM_MOD_P256_4:         return test_bignum_mod_p256_4();
     case TEST_BIGNUM_MOD_P256K1_4:       return test_bignum_mod_p256k1_4();
     case TEST_BIGNUM_MOD_P384:           return test_bignum_mod_p384();
     case TEST_BIGNUM_MOD_P384_6:         return test_bignum_mod_p384_6();
     case TEST_BIGNUM_MOD_P521_9:         return test_bignum_mod_p521_9();
     case TEST_BIGNUM_MODADD:             return test_bignum_modadd();
     case TEST_BIGNUM_MODDOUBLE:          return test_bignum_moddouble();
     case TEST_BIGNUM_MODIFIER:           return test_bignum_modifier();
     case TEST_BIGNUM_MODINV:             return test_bignum_modinv();
     case TEST_BIGNUM_MODOPTNEG:          return test_bignum_modoptneg();
     case TEST_BIGNUM_MODSUB:             return test_bignum_modsub();
     case TEST_BIGNUM_MONTIFIER:          return test_bignum_montifier();
     case TEST_BIGNUM_MONTMUL:            return test_bignum_montmul();
     case TEST_BIGNUM_MONTMUL_P256:       return test_bignum_montmul_p256();
     case TEST_BIGNUM_MONTMUL_P256_ALT:   return test_bignum_montmul_p256_alt();
     case TEST_BIGNUM_MONTMUL_P256K1:     return test_bignum_montmul_p256k1();
     case TEST_BIGNUM_MONTMUL_P256K1_ALT: return test_bignum_montmul_p256k1_alt();
     case TEST_BIGNUM_MONTMUL_P384:       return test_bignum_montmul_p384();
     case TEST_BIGNUM_MONTMUL_P521:       return test_bignum_montmul_p521();
     case TEST_BIGNUM_MONTREDC:           return test_bignum_montredc();
     case TEST_BIGNUM_MONTSQR:            return test_bignum_montsqr();
     case TEST_BIGNUM_MONTSQR_P256:       return test_bignum_montsqr_p256();
     case TEST_BIGNUM_MONTSQR_P256_ALT:   return test_bignum_montsqr_p256_alt();
     case TEST_BIGNUM_MONTSQR_P256K1:     return test_bignum_montsqr_p256k1();
     case TEST_BIGNUM_MONTSQR_P256K1_ALT: return test_bignum_montsqr_p256k1_alt();
     case TEST_BIGNUM_MONTSQR_P384:       return test_bignum_montsqr_p384();
     case TEST_BIGNUM_MONTSQR_P521:       return test_bignum_montsqr_p521();
     case TEST_BIGNUM_MUL:                return test_bignum_mul();
     case TEST_BIGNUM_MUL_4_8:            return test_bignum_mul_4_8();
     case TEST_BIGNUM_MUL_4_8_ALT:        return test_bignum_mul_4_8_alt();
     case TEST_BIGNUM_MUL_6_12:           return test_bignum_mul_6_12();
     case TEST_BIGNUM_MUL_8_16:           return test_bignum_mul_8_16();
     case TEST_BIGNUM_MUL_P256K1:         return test_bignum_mul_p256k1();
     case TEST_BIGNUM_MUL_P256K1_ALT:     return test_bignum_mul_p256k1_alt();
     case TEST_BIGNUM_MUL_P521:           return test_bignum_mul_p521();
     case TEST_BIGNUM_MULADD10:           return test_bignum_muladd10();
     case TEST_BIGNUM_MUX:                return test_bignum_mux();
     case TEST_BIGNUM_MUX_4:              return test_bignum_mux_4();
     case TEST_BIGNUM_MUX_6:              return test_bignum_mux_6();
     case TEST_BIGNUM_MUX16:              return test_bignum_mux16();
     case TEST_BIGNUM_NEG_P256:           return test_bignum_neg_p256();
     case TEST_BIGNUM_NEG_P256K1:         return test_bignum_neg_p256k1();
     case TEST_BIGNUM_NEG_P384:           return test_bignum_neg_p384();
     case TEST_BIGNUM_NEG_P521:           return test_bignum_neg_p521();
     case TEST_BIGNUM_NEGMODINV:          return test_bignum_negmodinv();
     case TEST_BIGNUM_NONZERO:            return test_bignum_nonzero();
     case TEST_BIGNUM_NONZERO_4:           return test_bignum_nonzero_4();
     case TEST_BIGNUM_NONZERO_6:          return test_bignum_nonzero_6();
     case TEST_BIGNUM_NORMALIZE:          return test_bignum_normalize();
     case TEST_BIGNUM_ODD:                return test_bignum_odd();
     case TEST_BIGNUM_OF_WORD:            return test_bignum_of_word();
     case TEST_BIGNUM_OPTADD:             return test_bignum_optadd();
     case TEST_BIGNUM_OPTNEG:             return test_bignum_optneg();
     case TEST_BIGNUM_OPTNEG_P256:        return test_bignum_optneg_p256();
     case TEST_BIGNUM_OPTNEG_P256K1:      return test_bignum_optneg_p256k1();
     case TEST_BIGNUM_OPTNEG_P384:        return test_bignum_optneg_p384();
     case TEST_BIGNUM_OPTNEG_P521:        return test_bignum_optneg_p521();
     case TEST_BIGNUM_OPTSUB:             return test_bignum_optsub();
     case TEST_BIGNUM_OPTSUBADD:          return test_bignum_optsubadd();
     case TEST_BIGNUM_POW2:               return test_bignum_pow2();
     case TEST_BIGNUM_SHL_SMALL:          return test_bignum_shl_small();
     case TEST_BIGNUM_SHR_SMALL:          return test_bignum_shr_small();
     case TEST_BIGNUM_SQR:                return test_bignum_sqr();
     case TEST_BIGNUM_SQR_4_8:            return test_bignum_sqr_4_8();
     case TEST_BIGNUM_SQR_4_8_ALT:        return test_bignum_sqr_4_8_alt();
     case TEST_BIGNUM_SQR_6_12:           return test_bignum_sqr_6_12();
     case TEST_BIGNUM_SQR_8_16:           return test_bignum_sqr_8_16();
     case TEST_BIGNUM_SQR_P256K1:         return test_bignum_sqr_p256k1();
     case TEST_BIGNUM_SQR_P256K1_ALT:     return test_bignum_sqr_p256k1_alt();
     case TEST_BIGNUM_SQR_P521:           return test_bignum_sqr_p521();
     case TEST_BIGNUM_SUB:                return test_bignum_sub();
     case TEST_BIGNUM_SUB_P256:           return test_bignum_sub_p256();
     case TEST_BIGNUM_SUB_P256K1:         return test_bignum_sub_p256k1();
     case TEST_BIGNUM_SUB_P384:           return test_bignum_sub_p384();
     case TEST_BIGNUM_SUB_P521:           return test_bignum_sub_p521();
     case TEST_BIGNUM_TOBEBYTES_4:        return test_bignum_tobebytes_4();
     case TEST_BIGNUM_TOBEBYTES_6:        return test_bignum_tobebytes_6();
     case TEST_BIGNUM_TOLEBYTES_4:        return test_bignum_tolebytes_4();
     case TEST_BIGNUM_TOLEBYTES_6:        return test_bignum_tolebytes_6();
     case TEST_BIGNUM_TOMONT_P256:        return test_bignum_tomont_p256();
     case TEST_BIGNUM_TOMONT_P256_ALT:    return test_bignum_tomont_p256_alt();
     case TEST_BIGNUM_TOMONT_P256K1:      return test_bignum_tomont_p256k1();
     case TEST_BIGNUM_TOMONT_P256K1_ALT:  return test_bignum_tomont_p256k1_alt();
     case TEST_BIGNUM_TOMONT_P384:        return test_bignum_tomont_p384();
     case TEST_BIGNUM_TOMONT_P521:        return test_bignum_tomont_p521();
     case TEST_BIGNUM_TRIPLE_P256:        return test_bignum_triple_p256();
     case TEST_BIGNUM_TRIPLE_P256_ALT:    return test_bignum_triple_p256_alt();
     case TEST_BIGNUM_TRIPLE_P256K1:      return test_bignum_triple_p256k1();
     case TEST_BIGNUM_TRIPLE_P256K1_ALT:  return test_bignum_triple_p256k1_alt();
     case TEST_BIGNUM_TRIPLE_P384:        return test_bignum_triple_p384();
     case TEST_BIGNUM_TRIPLE_P521:        return test_bignum_triple_p521();
     case TEST_WORD_BYTEREVERSE:          return test_word_bytereverse();
     case TEST_WORD_CLZ:                  return test_word_clz();
     case TEST_WORD_CTZ:                  return test_word_ctz();
     case TEST_WORD_MAX:                  return test_word_max();
     case TEST_WORD_MIN:                  return test_word_min();
     case TEST_WORD_NEGMODINV:            return test_word_negmodinv();
     case TEST_WORD_RECIP:                return test_word_recip();

     default:
        printf("### Unknown function to test: %d\n",WHAT);
        return 1;

   }
}
