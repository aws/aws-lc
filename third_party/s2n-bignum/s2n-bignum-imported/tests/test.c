// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ***************************************************************************
// Do some rudimentary unit testing of s2n-bignum functions against
// simple and straightforward generic C reference code. This is a
// useful complement to the formal proofs, handy for catching basic
// problems quickly and for providing an extra layer of assurance
// against disparities between the formal model and the real world.
// ***************************************************************************

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <math.h>
#include <time.h>
#include <alloca.h>
#include <string.h>

// Prototypes for the assembler implementations

#include "../include/s2n-bignum.h"

// Functions for detecting architectures and instruction sets

#include "arch.h"

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

static uint8_t bb1[BUFFERSIZE];
static uint8_t bb2[BUFFERSIZE];
static uint8_t bb3[BUFFERSIZE];
static uint8_t bb4[BUFFERSIZE];

// What to test, default number of tests, verbosity of output

#define VERBOSE 1
#define TESTS 100
#define MAXSIZE 35

// The actual number of tests, from input parameter or default to TESTS

static int tests = TESTS;

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

// (-3 * 2^256) mod p_256 (Montgomery form of a coefficient)

uint64_t a_256[4] =
 { UINT64_C(0xfffffffffffffffc),
   UINT64_C(0x00000003ffffffff),
   UINT64_C(0x0000000000000000),
   UINT64_C(0xfffffffc00000004)
 };

// Standard generator for P-256 curve

static uint64_t gen_p256[8] =
 { UINT64_C(0xf4a13945d898c296), UINT64_C(0x77037d812deb33a0),
   UINT64_C(0xf8bce6e563a440f2), UINT64_C(0x6b17d1f2e12c4247),
   UINT64_C(0xcbb6406837bf51f5), UINT64_C(0x2bce33576b315ece),
   UINT64_C(0x8ee7eb4a7c0f9e16), UINT64_C(0x4fe342e2fe1a7f9b)
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

// (-3 * 2^384) mod p_384 (Montgomery form of a coefficient)

uint64_t a_384[6] =
 { UINT64_C(0x00000003fffffffc),
   UINT64_C(0xfffffffc00000000),
   UINT64_C(0xfffffffffffffffb),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff)
 };

// Standard generator for P-384 curve

static uint64_t gen_p384[12] =
 { UINT64_C(0x3a545e3872760ab7),  UINT64_C(0x5502f25dbf55296c),
   UINT64_C(0x59f741e082542a38), UINT64_C(0x6e1d3b628ba79b98),
   UINT64_C(0x8eb1c71ef320ad74), UINT64_C(0xaa87ca22be8b0537),
   UINT64_C(0x7a431d7c90ea0e5f), UINT64_C(0x0a60b1ce1d7e819d),
   UINT64_C(0xe9da3113b5f0b8c0), UINT64_C(0xf8f41dbd289a147c),
   UINT64_C(0x5d9e98bf9292dc29), UINT64_C(0x3617de4a96262c6f)
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

// (-3) mod p_521 - non-Montgomery form

uint64_t aa_521[9] =
 { UINT64_C(0xfffffffffffffffc),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0x00000000000001ff)
 };

// (-3 * 2^576) mod p_521 - Montgomery form of -3

uint64_t a_521[9] =
 { UINT64_C(0xfe7fffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0x00000000000001ff)
 };

// Standard generator for P-521 curve

static uint64_t gen_p521[18] =
 { UINT64_C(0xf97e7e31c2e5bd66), UINT64_C(0x3348b3c1856a429b),
   UINT64_C(0xfe1dc127a2ffa8de), UINT64_C(0xa14b5e77efe75928),
   UINT64_C(0xf828af606b4d3dba), UINT64_C(0x9c648139053fb521),
   UINT64_C(0x9e3ecb662395b442), UINT64_C(0x858e06b70404e9cd),
   UINT64_C(0x00000000000000c6), UINT64_C(0x88be94769fd16650),
   UINT64_C(0x353c7086a272c240), UINT64_C(0xc550b9013fad0761),
   UINT64_C(0x97ee72995ef42640), UINT64_C(0x17afbd17273e662c),
   UINT64_C(0x98f54449579b4468), UINT64_C(0x5c8a5fb42c7d1bd9),
   UINT64_C(0x39296a789a3bc004), UINT64_C(0x0000000000000118)
 };

uint64_t p_25519[4] =
 { UINT64_C(0xffffffffffffffed),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0xffffffffffffffff),
   UINT64_C(0x7fffffffffffffff)
 };

// Square root of -1 modulo p_25519

uint64_t j_25519[4] =
 { UINT64_C(0xc4ee1b274a0ea0b0),
   UINT64_C(0x2f431806ad2fe478),
   UINT64_C(0x2b4d00993dfbd7a7),
   UINT64_C(0x2b8324804fc1df0b)
 };

// Basepoint order for curve25519/edwards25519

uint64_t n_25519[4] =
{
  UINT64_C(0x5812631a5cf5d3ed),
  UINT64_C(0x14def9dea2f79cd6),
  UINT64_C(0x0000000000000000),
  UINT64_C(0x1000000000000000)
};

// Full group order for curve25519/edwards25519 = 8 * n_25519

uint64_t m_25519[4] =
{
  UINT64_C(0xc09318d2e7ae9f68),
  UINT64_C(0xa6f7cef517bce6b2),
  UINT64_C(0x0000000000000000),
  UINT64_C(0x8000000000000000)
};

// d_25519 = d constant for edwards25519

uint64_t d_25519[4] =
 { UINT64_C(0x75eb4dca135978a3),
   UINT64_C(0x00700a4d4141d8ab),
   UINT64_C(0x8cc740797779e898),
   UINT64_C(0x52036cee2b6ffe73)
 };

// k_25519 = 2 * d for edwards25519

uint64_t k_25519[4] =
 { UINT64_C(0xebd69b9426b2f159),
   UINT64_C(0x00e0149a8283b156),
   UINT64_C(0x198e80f2eef3d130),
   UINT64_C(0x2406d9dc56dffce7)
 };

// Full basepoint for edwards25519

uint64_t g_edwards25519[8] =
{
  UINT64_C(0xc9562d608f25d51a),
  UINT64_C(0x692cc7609525a7b2),
  UINT64_C(0xc0a4e231fdd6dc5c),
  UINT64_C(0x216936d3cd6e53fe),
  UINT64_C(0x6666666666666658),
  UINT64_C(0x6666666666666666),
  UINT64_C(0x6666666666666666),
  UINT64_C(0x6666666666666666)
};

// Parameters for sm2

uint64_t p_sm2[4] =
 { UINT64_C(0xFFFFFFFFFFFFFFFF),
   UINT64_C(0xFFFFFFFF00000000),
   UINT64_C(0xFFFFFFFFFFFFFFFF),
   UINT64_C(0xFFFFFFFEFFFFFFFF)
};

uint64_t n_sm2[4] =
 { UINT64_C(0x53BBF40939D54123),
   UINT64_C(0x7203DF6B21C6052B),
   UINT64_C(0xFFFFFFFFFFFFFFFF),
   UINT64_C(0xFFFFFFFEFFFFFFFF)
};

uint64_t i_sm2[4] =
 { UINT64_C(0x0000000000000001),
   UINT64_C(0xFFFFFFFF00000001),
   UINT64_C(0xFFFFFFFE00000000),
   UINT64_C(0xFFFFFFFC00000001)
 };

// (-3 * 2^256) mod p_sm2 (Montgomery form of a coefficient)

uint64_t a_sm2[4] =
 { UINT64_C(0xFFFFFFFFFFFFFFFC),
   UINT64_C(0xFFFFFFFC00000003),
   UINT64_C(0xFFFFFFFFFFFFFFFF),
   UINT64_C(0xFFFFFFFBFFFFFFFF)
 };

// Standard generator for SM2 curve

static uint64_t gen_sm2[8] =
 { UINT64_C(0x715a4589334c74c7), UINT64_C(0x8fe30bbff2660be1),
   UINT64_C(0x5f9904466a39c994), UINT64_C(0x32c4ae2c1f198119),
   UINT64_C(0x02df32e52139f0a0), UINT64_C(0xd0a9877cc62a4740),
   UINT64_C(0x59bdcee36b692153), UINT64_C(0xbc3736a2f4f6779c)
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

uint64_t reference_wordpopcount(uint64_t n)
{ uint64_t m = 0;
  uint64_t i;
  for (i = 0; i < 64; ++i)
     if ((UINT64_C(0x1) << i) & n) ++m;
  return m;
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
  else { reference_copy(k,z,k,x); return 0; }
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

  reference_copy(k,z,k,n);
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

void reference_fromlebytes(uint64_t k,uint64_t *z,uint64_t n,uint8_t *x)
{ uint64_t i, acc;

  acc = 0; i = n;
  while (i != 0)
   { --i;
     acc = (acc<<8) + (uint64_t) x[i];
     if (i % 8 == 0) z[i/8] = acc, acc = 0;
   }
}

void reference_tolebytes(uint64_t k,uint8_t *z,uint64_t n,uint64_t *x)
{ uint64_t i;

  for (i = 0; i < k; ++i)
    z[i] = x[i/8] >> (8*(i%8));
}

int64_t reference_divstep(int64_t m[2][2],int n,int64_t din,int64_t fin,int64_t gin)
{ int64_t d, f, g, t;
  int64_t u = 1, v = 0, r = 0, s = 1;
  int i;

  if (n > 61)
   { printf("reference_divstep: parameter too big\n");
     exit(1);
   }

  fin &= 0x1FFFFFFFFFFFFFFF;
  gin &= 0x1FFFFFFFFFFFFFFF;
  d = din; f = fin; g = gin;

  for (i = 0; i < n; ++i)
    if ((d > 0) && (g & 1))
       d = 2 - d, t = g, g = (g - f) >> 1, f = t,
                  t = r, r = (r - u), u = t << 1,
                  t = s, s = (s - v), v = t << 1;
     else if (g & 1)
       d = 2 + d, g = (g + f) >> 1,
                  r = (r + u), u = u << 1,
                  s = (s + v), v = v << 1;
     else d = 2 + d, g = g >> 1, u = u << 1, v = v << 1;

  m[0][0] = u;
  m[0][1] = v;
  m[1][0] = r;
  m[1][1] = s;
  return d;
}

// Reference for computation of Legendre symbol (x/m)
// where m is assumed to be an odd prime.

int64_t reference_legendre(uint64_t k,uint64_t *x,uint64_t *m)
{ uint64_t *w = alloca(8 * k);
  uint64_t *a = alloca(8 * k);
  uint64_t *s = alloca(8 * k);
  uint64_t *t = alloca(8 * k);
  uint64_t i, b;
  int64_t z, p;

  bignum_montifier(k,w,m,t);
  bignum_montmul(k,a,w,x,m);
  bignum_demont(k,s,w,m);

  for (i = 64 * k - 1; i >= 1; --i)
   { bignum_montsqr(k,t,s,m);
     bignum_montmul(k,s,a,t,m);
     b = bignum_bitfield(k,m,i,1);
     bignum_mux(b,k,s,s,t);
   }

  bignum_demont(k,t,s,m);
  z = bignum_iszero(k,t);
  t[0] ^= UINT64_C(1);
  p = bignum_iszero(k,t);

  if (z) return 0;
  else if (p) return 1;
  else return -1;
}

int64_t reference_sqrt_p25519(uint64_t z[4],uint64_t x[4])
{
  uint64_t i, c;
  uint64_t a[4], sq[4], s[4];
  int64_t p, d;

  // First the candidate square root s = a^{252-2}

  bignum_mod_p25519_4(a,x);
  bignum_of_word(4,s,1);
  for (i = 1; i <= 251; ++i)
   { bignum_sqr_p25519_alt(s,s);
     bignum_mul_p25519_alt(s,s,a);
   }
  bignum_sqr_p25519_alt(s,s);

  // If s^2 = a then that's a square root, otherwise multiply by j_25519

  bignum_sqr_p25519_alt(sq,s);
  c = bignum_eq(4,sq,4,a);
  bignum_mul_p25519_alt(sq,s,j_25519);
  bignum_mux(c,4,s,s,sq);

  // For definiteness, choose "positive" (LSB=0) square root

  c = s[0] & 1;
  bignum_optneg_p25519(z,c,s);

  // Now determine if even that is right, for return value

  bignum_sqr_p25519_alt(sq,z);
  p = bignum_eq(4,sq,4,a);
  d = bignum_iszero(4,sq);

  return ((1 - d) * (2 * p - 1));
}

int64_t reference_invsqrt_p25519(uint64_t z[4],uint64_t x[4])
{
  uint64_t i, c;
  uint64_t a[4], sq[4], s[4], t[4], w[4];
  int64_t p, d;

  // First the candidate inverse square root s = a^{252-3}

  bignum_mod_p25519_4(a,x);
  bignum_of_word(4,s,1);
  for (i = 1; i <= 250; ++i)
   { bignum_sqr_p25519_alt(s,s);
     bignum_mul_p25519_alt(s,s,a);
   }
  bignum_sqr_p25519_alt(s,s);
  bignum_sqr_p25519_alt(s,s);
  bignum_mul_p25519_alt(s,s,a);

  // Alternative candidate t = s * sqrt(-1)

  bignum_mul_p25519_alt(t,s,j_25519);

  // Multiplex according to whether in fact a * s^2 = 1

  bignum_sqr_p25519_alt(sq,s);
  bignum_mul_p25519_alt(sq,a,sq);
  reference_of_word(4,w,1);
  c = bignum_eq(4,sq,4,w);
  bignum_mux(c,4,s,s,t);

  // For definiteness, choose "positive" (LSB=0) inverse square root

  c = s[0] & 1;
  bignum_optneg_p25519(z,c,s);

  // Now determine if even that is right, for return value

  bignum_sqr_p25519_alt(sq,z);
  bignum_mul_p25519_alt(sq,a,sq);
  p = bignum_eq(4,sq,4,w);
  d = bignum_iszero(4,sq);

  return ((1 - d) * (2 * p - 1));
}

// ****************************************************************************
// References for point operations (sometimes using generic bignum_xxx)
// ****************************************************************************

void reference_p25519xzdouble(uint64_t res[8],uint64_t point[8])
{ uint64_t *x = point, *z = point+4;
  uint64_t s[4], d[4], p[4];
  bignum_add_p25519(s,x,z);
  bignum_sqr_p25519_alt(s,s);
  bignum_sub_p25519(d,x,z);
  bignum_sqr_p25519_alt(d,d);
  bignum_mul_p25519_alt(res,s,d);
  bignum_sub_p25519(p,s,d);
  bignum_cmul_p25519_alt(s,121666,p);
  bignum_add_p25519(d,d,s);
  bignum_mul_p25519_alt(res+4,p,d);
}

void reference_p25519xzdiffadd(uint64_t res[8],uint64_t x[4],uint64_t n[8],uint64_t m[8])
{ uint64_t *xm = m, *zm = m+4, *xn = n, *zn = n+4;
  uint64_t sm[4], sn[4], dm[4], dn[4], p[4], q[4], s[4], d[4];
  bignum_add_p25519(sm,xm,zm);
  bignum_add_p25519(sn,xn,zn);
  bignum_sub_p25519(dm,xm,zm);
  bignum_sub_p25519(dn,xn,zn);
  bignum_mul_p25519_alt(p,dm,sn);
  bignum_mul_p25519_alt(q,sm,dn);
  bignum_add_p25519(s,p,q);
  bignum_sqr_p25519_alt(res,s);
  bignum_sub_p25519(d,p,q);
  bignum_sqr_p25519_alt(d,d);
  bignum_mul_p25519_alt(res+4,x,d);
}

void reference_curve25519ladderstep
  (uint64_t rr[16],uint64_t point[4],uint64_t pp[16],uint64_t b)
{ if (b != 0)
   { reference_p25519xzdiffadd(rr,point,pp,pp+8);
     reference_p25519xzdouble(rr+8,pp+8);
   }
  else
   { reference_p25519xzdiffadd(rr+8,point,pp,pp+8);
     reference_p25519xzdouble(rr,pp);
   }
}

void reference_curve25519pxscalarmul
  (uint64_t res[8],uint64_t scalar[4],uint64_t point[4])
{ uint64_t pp[16];
  uint64_t *pn = pp, *pn1 = pp+8;
  uint64_t i, bf;
  uint64_t triv, lsb;

  bignum_of_word(4,pn,1); bignum_of_word(4,pn+4,0);
  bignum_copy(4,pn1,4,point); bignum_of_word(4,pn1+4,1);

  i = 256;
  do
   { --i;
     bf = (scalar[i>>6] >> (i & 0x3F)) & 1ull;
     reference_curve25519ladderstep(pp,point,pp,bf);
   }
  while (i != 0);

  // Handle the special case of point = (0,0) at the end
  // which the ladder won't do correctly by default.
  // (0,0)^odd = (0,1) and (0,0)^even = (1,0)

  triv = bignum_iszero(4,point);
  lsb = scalar[0] & 1;

  bignum_copy(8,res,8,pn);

  bignum_of_word(8,pn,0);
  if (lsb) pn[4] = 1; else pn[0] = 1;
  bignum_mux(triv,8,res,pn,res);

}

void reference_curve25519x25519
  (uint64_t res[4],uint64_t scalar[4],uint64_t point[4])
{ uint64_t mscalar[4], mpoint[4], pres[8], zinv[4], tmpspace[12];
  uint64_t *prez = pres+4;

  bignum_copy(4,mscalar,4,scalar);
  mscalar[3] &= UINT64_C(0x7fffffffffffffff);
  mscalar[3] |= UINT64_C(0x4000000000000000);
  mscalar[0] &= UINT64_C(0xfffffffffffffff8);

  bignum_copy(4,mpoint,4,point);
  mpoint[3] &= UINT64_C(0x7fffffffffffffff);
  if (!bignum_lt(4,mpoint,4,p_25519))
     bignum_sub(4,mpoint,4,mpoint,4,p_25519);

  reference_curve25519pxscalarmul(pres,mscalar,mpoint);

  bignum_modinv(4,zinv,prez,p_25519,tmpspace);

  bignum_mul_p25519_alt(res,pres,zinv);
  if (bignum_iszero(4,prez)) bignum_of_word(4,res,0);
}

// Doubling formulas from projective inputs (not using the W/T input field)
// and either generating projective or extended projective results.

void reference_edwards25519pdouble(uint64_t p3[12],uint64_t p1[12])
{ uint64_t *x1 = p1, *y1 = p1 + 4, *z1 = p1 + 2*4;
  uint64_t *x3 = p3, *y3 = p3 + 4, *z3 = p3 + 2*4;
  uint64_t t0[4], t1[4], t2[4], t3[4], t4[4], t5[4],
           t6[4], t7[4], t8[4], t9[4];
  bignum_sqr_p25519_alt(t0,x1);
  bignum_sqr_p25519_alt(t1,y1);
  bignum_sqr_p25519_alt(t2,z1);
  bignum_add_p25519(t3,t2,t2);
  bignum_add_p25519(t4,x1,y1);
  bignum_sqr_p25519_alt(t5,t4);
  bignum_add_p25519(t6,t0,t1);
  bignum_sub_p25519(t7,t6,t5);
  bignum_sub_p25519(t8,t0,t1);
  bignum_add_p25519(t9,t3,t8);
  bignum_mul_p25519_alt(x3,t7,t9);
  bignum_mul_p25519_alt(y3,t8,t6);
  bignum_mul_p25519_alt(z3,t9,t8);
}

void reference_edwards25519epdouble(uint64_t p3[16],uint64_t p1[12])
{ uint64_t *x1 = p1, *y1 = p1 + 4, *z1 = p1 + 2*4;
  uint64_t *x3 = p3, *y3 = p3 + 4, *z3 = p3 + 2*4, *w3 = p3 + 3*4;
  uint64_t t0[4], t1[4], t2[4], t3[4], t4[4], t5[4],
           t6[4], t7[4], t8[4], t9[4];
  bignum_sqr_p25519_alt(t0,x1);
  bignum_sqr_p25519_alt(t1,y1);
  bignum_sqr_p25519_alt(t2,z1);
  bignum_add_p25519(t3,t2,t2);
  bignum_add_p25519(t4,x1,y1);
  bignum_sqr_p25519_alt(t5,t4);
  bignum_add_p25519(t6,t0,t1);
  bignum_sub_p25519(t7,t6,t5);
  bignum_sub_p25519(t8,t0,t1);
  bignum_add_p25519(t9,t3,t8);
  bignum_mul_p25519_alt(x3,t7,t9);
  bignum_mul_p25519_alt(y3,t8,t6);
  bignum_mul_p25519_alt(z3,t9,t8);
  bignum_mul_p25519_alt(w3,t7,t6);
}

void reference_edwards25519epadd(uint64_t p3[16],uint64_t p1[16],uint64_t p2[16])
{ uint64_t *x1 = p1, *y1 = p1 + 4, *z1 = p1 + 2*4, *w1 = p1 + 3*4;
  uint64_t *x2 = p2, *y2 = p2 + 4, *z2 = p2 + 2*4, *w2 = p2 + 3*4;
  uint64_t *x3 = p3, *y3 = p3 + 4, *z3 = p3 + 2*4, *w3 = p3 + 3*4;
  uint64_t t0[4], t1[4], a[4], t2[4], t3[4], b[4], t4[4], c[4], t5[4],
           d[4], e[4], f[4], g[4], h[4];
  bignum_sub_p25519(t0,y1,x1);
  bignum_sub_p25519(t1,y2,x2);
  bignum_mul_p25519_alt(a,t0,t1);
  bignum_add_p25519(t2,y1,x1);
  bignum_add_p25519(t3,y2,x2);
  bignum_mul_p25519_alt(b,t2,t3);
  bignum_mul_p25519_alt(t4,k_25519,w2);
  bignum_mul_p25519_alt(c,w1,t4);
  bignum_add_p25519(t5,z2,z2);
  bignum_mul_p25519_alt(d,z1,t5);
  bignum_sub_p25519(e,b,a);
  bignum_sub_p25519(f,d,c);
  bignum_add_p25519(g,d,c);
  bignum_add_p25519(h,b,a);
  bignum_mul_p25519_alt(x3,e,f);
  bignum_mul_p25519_alt(y3,g,h);
  bignum_mul_p25519_alt(z3,f,g);
  bignum_mul_p25519_alt(w3,e,h);
}

void reference_edwards25519pepadd(uint64_t p3[16],uint64_t p1[16],uint64_t p2[12])
{ uint64_t *x1 = p1, *y1 = p1 + 4, *z1 = p1 + 2*4, *w1 = p1 + 3*4;
  uint64_t *ymx2 = p2, *xpy2 = p2 + 4, *kxy = p2 + 2*4;
  uint64_t *x3 = p3, *y3 = p3 + 4, *z3 = p3 + 2*4, *w3 = p3 + 3*4;
  uint64_t t0[4], t1[4], t2[4], t3[4], t4[4],
           t5[4], t6[4], t7[4], t8[4], t9[4];
  bignum_sub_p25519(t0,y1,x1);
  bignum_mul_p25519_alt(t1,t0,ymx2);
  bignum_add_p25519(t2,y1,x1);
  bignum_mul_p25519_alt(t3,t2,xpy2);
  bignum_mul_p25519_alt(t4,w1,kxy);
  bignum_double_p25519(t5,z1);
  bignum_sub_p25519(t6,t3,t1);
  bignum_sub_p25519(t7,t5,t4);
  bignum_add_p25519(t8,t5,t4);
  bignum_add_p25519(t9,t3,t1);
  bignum_mul_p25519_alt(x3,t6,t7);
  bignum_mul_p25519_alt(y3,t8,t9);
  bignum_mul_p25519_alt(z3,t7,t8);
  bignum_mul_p25519_alt(w3,t6,t9);
}

void reference_edwards25519scalarmul
 (uint64_t res[8],uint64_t scalar[4],uint64_t point[static 8])
{ uint64_t ep[16], acc[16], zinv[4], tmpspace[12], bf;
  int i;

  // ep = extended-projective initial point

  bignum_copy(8,ep,8,point);
  bignum_of_word(4,ep+8,UINT64_C(1));
  bignum_mul_p25519_alt(ep+12,point,point+4);

  // acc = extended-projective (0,1)

  bignum_of_word(4,acc,UINT64_C(0));
  bignum_of_word(4,acc+4,UINT64_C(1));
  bignum_of_word(4,acc+8,UINT64_C(1));
  bignum_of_word(4,acc+12,UINT64_C(0));

  i = 256;
  do
   { --i;
     reference_edwards25519epdouble(acc,acc);
     bf = (scalar[i>>6] >> (i & 0x3F)) & 1ull;
     if (bf) reference_edwards25519epadd(acc,acc,ep);
   }
  while (i != 0);

  bignum_modinv(4,zinv,acc+8,p_25519,tmpspace);

  bignum_mul_p25519_alt(res,acc,zinv);
  bignum_mul_p25519_alt(res+4,acc+4,zinv);
}

void reference_edwards25519scalarmulbase(uint64_t res[8],uint64_t scalar[4])
{ reference_edwards25519scalarmul(res,scalar,g_edwards25519);
}

// res = scalar * point + bscalar * basepoint

void reference_edwards25519scalarmuldouble
 (uint64_t res[8],uint64_t scalar[4],uint64_t point[8],uint64_t bscalar[4])
{ uint64_t res1[16], res2[16], res3[16], zinv[4], tmpspace[12];

  // res1 = scalar * point

  reference_edwards25519scalarmul(res1,scalar,point);
  bignum_of_word(4,res1+8,UINT64_C(1));
  bignum_mul_p25519_alt(res1+12,res1,res1+4);

  // res2 = bscalar * basepoint

  reference_edwards25519scalarmul(res2,bscalar,g_edwards25519);
  bignum_of_word(4,res2+8,UINT64_C(1));
  bignum_mul_p25519_alt(res2+12,res2,res2+4);

  // Add them, so res3 = scalar * point + bscalar * basepoint

  reference_edwards25519epadd(res3,res1,res2);

  // Map out of the projective representation into res

  bignum_modinv(4,zinv,res3+8,p_25519,tmpspace);
  bignum_mul_p25519_alt(res,res3,zinv);
  bignum_mul_p25519_alt(res+4,res3+4,zinv);
}

void reference_edwards25519encode(uint8_t z[32], uint64_t p[8])
{ uint64_t q[4];
  q[0] = p[4];
  q[1] = p[5];
  q[2] = p[6];
  q[3] = (p[7] & 0x7FFFFFFFFFFFFFFF) | (p[0]<<63);
  reference_tolebytes(32,z,4,q);
}

uint64_t reference_edwards25519decode(uint64_t z[8],uint8_t c[32])
{ uint64_t y[4], s[4], t[4], u[4], v[4], w[4];
  uint64_t sgnbit, zerox, flip;
  int64_t j;

  // This tracks the invalidity of the input.
  // It is set if any of three different conditions holds:
  //
  //   * y >= p_25519 (initial y coordinate not reduced)
  //   * (y^2 - 1) * (1 + d * y^2) is a nonzero quadratic nonresidue
  //   * x = 0 (equivalently y^2 = 1) and negative sign is requested

  uint64_t badun;

  // Let y be the lowest 255 bits of input and sgnbit the desired parity
  // If y >= p_25519 then already flag the input as invalid

  reference_fromlebytes(4,y,32,c);
  sgnbit = y[3] >> 63;
  y[3] &= 0x7FFFFFFFFFFFFFFF;
  badun = reference_ge_samelen(4,y,p_25519);

  // u = y^2 - 1
  // v = 1 + d * y^2
  // w = u * v

  bignum_sqr_p25519_alt(v,y);
  bignum_of_word(4,t,1);
  bignum_sub_p25519(u,v,t);
  bignum_mul_p25519_alt(v,d_25519,v);
  bignum_add_p25519(v,v,t);
  bignum_mul_p25519_alt(w,u,v);

  // s = sqrt(u / v) with j the Jacobi symbol for (u * v,p_25519)
  // If j indicates no square root (not even zero), flag as invalid.

  j = bignum_invsqrt_p25519_alt(s,w);
  badun |= (j < 0);
  bignum_mul_p25519_alt(s,u,s);

  // zerox = (x = 0)
  // flip = (x_0 <=> sgnbit)

  zerox = bignum_iszero(4,s);
  flip = ((s[0] & 1) != sgnbit);
  badun |= (flip && zerox);

  // Return sign-adjusted square root

  bignum_optneg_p25519(z,(flip && !zerox),s);
  bignum_copy(4,z+4,4,y);
  return badun;
}

void reference_montjdouble
  (uint64_t k,uint64_t *p3,uint64_t *p1,uint64_t *a,uint64_t *m)
{ uint64_t *xx = alloca(8 * k);
  uint64_t *yy  = alloca(8 * k);
  uint64_t *yyyy = alloca(8 * k);
  uint64_t *zz  = alloca(8 * k);
  uint64_t *s  = alloca(8 * k);
  uint64_t *mm  = alloca(8 * k);
  uint64_t *t0  = alloca(8 * k);
  uint64_t *t1  = alloca(8 * k);
  uint64_t *t2  = alloca(8 * k);
  uint64_t *t3 = alloca(8 * k);
  uint64_t *t4  = alloca(8 * k);
  uint64_t *t5  = alloca(8 * k);
  uint64_t *t6  = alloca(8 * k);
  uint64_t *t7  = alloca(8 * k);
  uint64_t *t8 = alloca(8 * k);
  uint64_t *t9 = alloca(8 * k);
  uint64_t *t10 = alloca(8 * k);
  uint64_t *t11 = alloca(8 * k);
  uint64_t *t12 = alloca(8 * k);
  uint64_t *t13 = alloca(8 * k);
  uint64_t *t14 = alloca(8 * k);
  uint64_t *x1 = p1, *y1 = p1 + k, *z1 = p1 + 2*k;
  uint64_t *x3 = p3, *y3 = p3 + k, *z3 = p3 + 2*k;
  bignum_montsqr(k,xx,x1,m);
  bignum_montsqr(k,yy,y1,m);
  bignum_montsqr(k,yyyy,yy,m);
  bignum_montsqr(k,zz,z1,m);
  bignum_modadd(k,t0,x1,yy,m);
  bignum_montsqr(k,t1,t0,m);
  bignum_modsub(k,t2,t1,xx,m);
  bignum_modsub(k,t3,t2,yyyy,m);
  bignum_moddouble(k,s,t3,m);
  bignum_montsqr(k,t4,zz,m);
  bignum_montmul(k,t5,a,t4,m);
  bignum_moddouble(k,t6,xx,m);
    bignum_modadd(k,t6,t6,xx,m);
  bignum_modadd(k,mm,t6,t5,m);
  bignum_montsqr(k,t7,mm,m);
  bignum_moddouble(k,t8,s,m);
  bignum_modsub(k,x3,t7,t8,m);
  bignum_modsub(k,t9,s,x3,m);
  bignum_moddouble(k,t10,yyyy,m);
    bignum_moddouble(k,t10,t10,m); bignum_moddouble(k,t10,t10,m);
  bignum_montmul(k,t11,mm,t9,m);
  bignum_modadd(k,t12,y1,z1,m);
  bignum_modsub(k,y3,t11,t10,m);
  bignum_montsqr(k,t13,t12,m);
  bignum_modsub(k,t14,t13,yy,m);
  bignum_modsub(k,z3,t14,zz,m);
}

void reference_jdouble
  (uint64_t k,uint64_t *p3,uint64_t *p1,uint64_t *a,uint64_t *m)
{ uint64_t *i = alloca(8 * k);
  uint64_t *t = alloca(8 * k);
  uint64_t *p1m = alloca(8 * 3 * k);
  uint64_t *am = alloca(8 * k);
  uint64_t *p3m = alloca(8 * 3 * k);

  bignum_montifier(k,i,m,t);
  bignum_montmul(k,p1m,i,p1,m);
  bignum_montmul(k,p1m+k,i,p1+k,m);
  bignum_montmul(k,p1m+2*k,i,p1+2*k,m);
  bignum_montmul(k,am,i,a,m);
  reference_montjdouble(k,p3m,p1m,am,m);
  bignum_montredc(k,p3,k,p3m,m,k);
  bignum_montredc(k,p3+k,k,p3m+k,m,k);
  bignum_montredc(k,p3+2*k,k,p3m+2*k,m,k);
}

void reference_montjmixadd
  (uint64_t k,uint64_t *p3,uint64_t *p1,uint64_t *p2,uint64_t *m)
{ uint64_t *z12 = alloca(8 * k);
  uint64_t *y2z1  = alloca(8 * k);
  uint64_t *s = alloca(8 * k);
  uint64_t *u  = alloca(8 * k);
  uint64_t *v  = alloca(8 * k);
  uint64_t *w  = alloca(8 * k);
  uint64_t *v2  = alloca(8 * k);
  uint64_t *w2  = alloca(8 * k);
  uint64_t *v3  = alloca(8 * k);
  uint64_t *rv2 = alloca(8 * k);
  uint64_t *t0  = alloca(8 * k);
  uint64_t *t1  = alloca(8 * k);
  uint64_t *t2  = alloca(8 * k);
  uint64_t *t3  = alloca(8 * k);
  uint64_t *t4 = alloca(8 * k);
  uint64_t *x1 = p1, *y1 = p1 + k, *z1 = p1 + 2*k;
  uint64_t *x2 = p2, *y2 = p2 + k;
  uint64_t *x3 = p3, *y3 = p3 + k, *z3 = p3 + 2*k;

  if (bignum_iszero(k,z1))
   { bignum_copy(k,x3,k,x2);
     bignum_copy(k,y3,k,y2);
     bignum_montifier(k,t1,m,t2);
     bignum_montredc(k,z3,k,t1,m,k);
   }
  else
   { bignum_montsqr(k,z12,z1,m);
     bignum_montmul(k,y2z1,y2,z1,m);
     bignum_montmul(k,s,x2,z12,m);
     bignum_montmul(k,u,y2z1,z12,m);
     bignum_modsub(k,v,s,x1,m);
     bignum_modsub(k,w,u,y1,m);
     bignum_montsqr(k,v2,v,m);
     bignum_montsqr(k,w2,w,m);
     bignum_montmul(k,v3,v,v2,m);
     bignum_montmul(k,rv2,x1,v2,m);
     bignum_modsub(k,t0,w2,v3,m);
     bignum_modsub(k,t1,t0,rv2,m);
     bignum_modsub(k,x3,t1,rv2,m);
     bignum_modsub(k,t2,rv2,x3,m);
     bignum_montmul(k,t3,v3,y1,m);
     bignum_montmul(k,t4,w,t2,m);
     bignum_modsub(k,y3,t4,t3,m);
     bignum_montmul(k,t1,z1,v,m);
     bignum_copy(k,z3,k,t1);
   }
}

void reference_jmixadd
  (uint64_t k,uint64_t *p3,uint64_t *p1,uint64_t *p2,uint64_t *m)
{ uint64_t *i = alloca(8 * k);
  uint64_t *t = alloca(8 * k);
  uint64_t *p1m = alloca(8 * 3 * k);
  uint64_t *p2m = alloca(8 * 2 * k);
  uint64_t *p3m = alloca(8 * 3 * k);

  bignum_montifier(k,i,m,t);
  bignum_montmul(k,p1m,i,p1,m);
  bignum_montmul(k,p1m+k,i,p1+k,m);
  bignum_montmul(k,p1m+2*k,i,p1+2*k,m);
  bignum_montmul(k,p2m,i,p2,m);
  bignum_montmul(k,p2m+k,i,p2+k,m);
  reference_montjmixadd(k,p3m,p1m,p2m,m);
  bignum_montredc(k,p3,k,p3m,m,k);
  bignum_montredc(k,p3+k,k,p3m+k,m,k);
  bignum_montredc(k,p3+2*k,k,p3m+2*k,m,k);
}

void reference_montjadd
  (uint64_t k,uint64_t *p3,uint64_t *p1,uint64_t *p2,uint64_t *m)
{ uint64_t *z22 = alloca(8 * k);
  uint64_t *z12 = alloca(8 * k);
  uint64_t *y1z2 = alloca(8 * k);
  uint64_t *y2z1 = alloca(8 * k);
  uint64_t *r = alloca(8 * k);
  uint64_t *s = alloca(8 * k);
  uint64_t *t = alloca(8 * k);
  uint64_t *u = alloca(8 * k);
  uint64_t *v = alloca(8 * k);
  uint64_t *w = alloca(8 * k);
  uint64_t *v2 = alloca(8 * k);
  uint64_t *w2 = alloca(8 * k);
  uint64_t *v3 = alloca(8 * k);
  uint64_t *rv2 = alloca(8 * k);
  uint64_t *t0 = alloca(8 * k);
  uint64_t *t1 = alloca(8 * k);
  uint64_t *t2 = alloca(8 * k);
  uint64_t *t3 = alloca(8 * k);
  uint64_t *t4 = alloca(8 * k);
  uint64_t *t5 = alloca(8 * k);
  uint64_t *x1 = p1, *y1 = p1 + k, *z1 = p1 + 2*k;
  uint64_t *x2 = p2, *y2 = p2 + k, *z2 = p2 + 2*k;
  uint64_t *x3 = p3, *y3 = p3 + k, *z3 = p3 + 2*k;

  if (bignum_iszero(k,z1) && !bignum_iszero(k,z2))
     bignum_copy(3*k,p3,3*k,p2);
  else if (bignum_iszero(k,z2) && !bignum_iszero(k,z1))
     bignum_copy(3*k,p3,3*k,p1);
  else
   { bignum_montsqr(k,z22,z2,m);
     bignum_montsqr(k,z12,z1,m);
     bignum_montmul(k,y1z2,y1,z2,m);
     bignum_montmul(k,y2z1,y2,z1,m);
     bignum_montmul(k,r,x1,z22,m);
     bignum_montmul(k,s,x2,z12,m);
     bignum_montmul(k,t,y1z2,z22,m);
     bignum_montmul(k,u,y2z1,z12,m);
     bignum_modsub(k,v,s,r,m);
     bignum_modsub(k,w,u,t,m);
     bignum_montsqr(k,v2,v,m);
     bignum_montsqr(k,w2,w,m);
     bignum_montmul(k,v3,v,v2,m);
     bignum_montmul(k,rv2,r,v2,m);
     bignum_modsub(k,t0,w2,v3,m);
     bignum_modsub(k,t1,t0,rv2,m);
     bignum_modsub(k,x3,t1,rv2,m);
     bignum_modsub(k,t2,rv2,x3,m);
     bignum_montmul(k,t3,v3,t,m);
     bignum_montmul(k,t4,w,t2,m);
     bignum_modsub(k,y3,t4,t3,m);
     bignum_montmul(k,t5,z1,z2,m);
     bignum_montmul(k,z3,t5,v,m);
   }
}

void reference_jadd
  (uint64_t k,uint64_t *p3,uint64_t *p1,uint64_t *p2,uint64_t *m)
{ uint64_t *i = alloca(8 * k);
  uint64_t *t = alloca(8 * k);
  uint64_t *p1m = alloca(8 * 3 * k);
  uint64_t *p2m = alloca(8 * 3 * k);
  uint64_t *p3m = alloca(8 * 3 * k);

  bignum_montifier(k,i,m,t);
  bignum_montmul(k,p1m,i,p1,m);
  bignum_montmul(k,p1m+k,i,p1+k,m);
  bignum_montmul(k,p1m+2*k,i,p1+2*k,m);
  bignum_montmul(k,p2m,i,p2,m);
  bignum_montmul(k,p2m+k,i,p2+k,m);
  bignum_montmul(k,p2m+2*k,i,p2+2*k,m);
  reference_montjadd(k,p3m,p1m,p2m,m);
  bignum_montredc(k,p3,k,p3m,m,k);
  bignum_montredc(k,p3+k,k,p3m+k,m,k);
  bignum_montredc(k,p3+2*k,k,p3m+2*k,m,k);
}

// Reference version of modular exponentiation (for odd modulus).
// For the sake of efficiency, this does use generic s2n-bignum primitives
// but is otherwise quite naive and simple, and it is not constant-time.

void reference_modexp(uint64_t k,uint64_t *res,
                      uint64_t *a,uint64_t *p,uint64_t *m)
{ uint64_t j;
  uint64_t *x = alloca(8 * k), *y = alloca(8 * k), *z = alloca(8 * k);

  // Let x = Mont(a) and initialize z = Mont(1)

  bignum_montifier(k,z,m,y);
  bignum_montmul(k,x,z,a,m);
  bignum_demont(k,z,z,m);

  // Main loop with invariant z = Mont(a^(p >> 2^j))

  j = 64 * k;
  while (j != 0)
   { --j;
     bignum_montsqr(k,y,z,m);
     if (bignum_bitfield(k,p,j,1)) bignum_montmul(k,z,x,y,m);
     else bignum_copy(k,z,k,y);
   }

  // Convert back from Montgomery representation

  bignum_demont(k,res,z,m);
}

// Generic conversion from affine (x,y) to Montgomery-Jacobian (x',y',1')
// where priming indicates Montgomery domain, x' = (2^64k * x) mod p etc.

void reference_to_montjacobian
  (uint64_t k,uint64_t *jacpoint,uint64_t *affpoint,uint64_t *p)
{
  uint64_t *monty = alloca(8 * k);
  uint64_t *tmp = alloca(3 * 8 * k);

  bignum_montifier(k,monty,p,tmp);

  bignum_montmul(k,jacpoint,monty,affpoint,p);
  bignum_montmul(k,jacpoint+k,monty,affpoint+k,p);
  bignum_montredc(k,jacpoint+2*k,k,monty,p,k);
}

// Generic conversion from Montgomery-Jacobian (x',y',z') to (x/z^2,y/z^3)
// where priming indicates Montgomery domain, x' = (2^64k * x) mod p etc.

void reference_to_affine
  (uint64_t k,uint64_t *affpoint,uint64_t *jacpoint,uint64_t *p)
{
  uint64_t *z2 = alloca(8 * k);
  uint64_t *z3 = alloca(8 * k);
  uint64_t *tmp = alloca(3 * 8 * k);

  // Let z2 = 1/z^2 and z3 = 1/z^3, all without Montgomery form

  bignum_montsqr(k,z2,jacpoint+2*k,p);
  bignum_montmul(k,z3,jacpoint+2*k,z2,p);
  bignum_montredc(k,z2,k,z3,p,k);
  bignum_modinv(k,z3,z2,p,tmp);
  bignum_montmul(k,z2,jacpoint+2*k,z3,p);

  // Convert back from Jacobian (X,Y,Z) |-> (X/Z^2, Y/Z^3)

  bignum_montmul(k,affpoint,jacpoint,z2,p);
  bignum_montmul(k,affpoint+k,jacpoint+k,z3,p);
}

// Generic conversion from Montgomery-Jacobian to Montgomery affine form.

void reference_to_montaffine
  (uint64_t k,uint64_t *maffpoint,uint64_t *jacpoint,uint64_t *p)
{
  uint64_t *affpoint = alloca(2 * 8 * k);

  uint64_t *monty = alloca(8 * k);
  uint64_t *tmp = alloca(3 * 8 * k);

  bignum_montifier(k,monty,p,tmp);

  reference_to_affine(k,affpoint,jacpoint,p);
  bignum_montmul(k,maffpoint,monty,affpoint,p);
  bignum_montmul(k,maffpoint+k,monty,affpoint+k,p);
}

// Generic Weierstrass scalar multiplication for 64k-bit scalar and point
// with all points (input and output) in Montgomery-Jacobian form
//
// p is the field characteristic
// n is the group order
// a is the *MONTGOMERY FORM* coefficient of x (which is often -3 mod p)

void reference_montjscalarmul
  (uint64_t k,uint64_t *res,uint64_t *scalar,uint64_t *point,
   uint64_t *p,uint64_t *n,uint64_t *a)
{ uint64_t *rscalar = alloca(8 * k);
  uint64_t *acc = alloca(3 * 8 * k);

  uint64_t i, bf;

  // Reduce scalar modulo n, to avoid worries over P + P in addition

  reference_mod(k,rscalar,scalar,n);

  // Set up starting accumulator of 0 (only z component matters in fact)

  bignum_of_word(3*k,acc,0);

  // Main loop

  i = 64 * k;
  do
   { --i;
     reference_montjdouble(k,acc,acc,a,p);
     bf = (rscalar[i>>6] >> (i & 0x3F)) & 1ull;
     if (bf) reference_montjadd(k,acc,acc,point,p);
   }
  while (i != 0);

  // Copy back to output, still in Montgomery-Jacobian form

  reference_copy(3*k,res,3*k,acc);
}

// Same again without Montgomery form

void reference_jscalarmul
  (uint64_t k,uint64_t *res,uint64_t *scalar,uint64_t *point,
   uint64_t *p,uint64_t *n,uint64_t *a)
{ uint64_t *i = alloca(8 * k);
  uint64_t *t = alloca(8 * k);
  uint64_t *mpoint = alloca(8 * 3 * k);
  uint64_t *ma = alloca(8 * k);
  uint64_t *mres = alloca(8 * 3 * k);

  bignum_montifier(k,i,p,t);
  bignum_montmul(k,ma,i,a,p);
  bignum_montmul(k,mpoint,i,point,p);
  bignum_montmul(k,mpoint+k,i,point+k,p);
  bignum_montmul(k,mpoint+2*k,i,point+2*k,p);

  reference_montjscalarmul(k,mres,scalar,mpoint,p,n,ma);

  bignum_montredc(k,res,k,mres,p,k);
  bignum_montredc(k,res+k,k,mres+k,p,k);
  bignum_montredc(k,res+2*k,k,mres+2*k,p,k);
}

// Generic Weierstrass scalar multiplication for 64k-bit scalar and point
//
// p is the field characteristic
// n is the group order
// a is the *MONTGOMERY FORM* coefficient of x (which is often -3 mod p)

void reference_scalarmul
  (uint64_t k,uint64_t *res,uint64_t *scalar,uint64_t *point,
   uint64_t *p,uint64_t *n,uint64_t *a)
{ uint64_t *rscalar = alloca(8 * k);
  uint64_t *mpoint = alloca(3 * 8 * k);
  uint64_t *acc = alloca(3 * 8 * k);

  uint64_t i, bf;

  // Reduce scalar modulo n, to avoid worries over P + P in addition

  reference_mod(k,rscalar,scalar,n);

  // Convert input point to Montgomery-Jacobian (don't actually need z coord)

  reference_to_montjacobian(k,mpoint,point,p);

  // Set up starting accumulator of 0 (only z component matters in fact)

  bignum_of_word(3*k,acc,0);

  // Main loop

  i = 64 * k;
  do
   { --i;
     reference_montjdouble(k,acc,acc,a,p);
     bf = (rscalar[i>>6] >> (i & 0x3F)) & 1ull;
     if (bf) reference_montjmixadd(k,acc,acc,mpoint,p);
   }
  while (i != 0);

  // Convert back to affine form

  reference_to_affine(k,res,acc,p);
}

// Generic precomputed table construction for Weierstrass curve points
//
// p is the field characteristic
// n is the group order
// a is the *MONTGOMERY FORM* coefficient of x (which is often -3 mod p)
//
// b is the number of bits per table block
// point is the input point (affine form, no Montgomery)
// res is the pointer for the output table of Montgomery-affine points
//
// The table has TAB(i,j) = 2^{b i} j * P with 1 <= j <= 2^{b-1} and
// i having sufficient range to cover any 64k-bit scalar. The indexing
// of the output is captured in the following macro TAB

#define TAB(tab,k,bsize,i,j) (tab+2*k*((1<<(bsize-1))*i+j-1))

void reference_multable
  (uint64_t k,uint64_t *res,uint64_t b,uint64_t *point,
   uint64_t *p,uint64_t *a)
{ uint64_t *mpoint = alloca(3 * 8 * k);
  uint64_t *acc = alloca(3 * 8 * k);

  uint64_t i, j;

  // Convert input point to Montgomery-Jacobian form as mpoint = (x',y',1')

  reference_to_montjacobian(k,mpoint,point,p);

  // Iterate i over blocks

  for (i = 0; b*i <= 64*k; ++i)
   {
      reference_to_montaffine(k,TAB(res,k,b,i,1),mpoint,p);
      reference_montjdouble(k,acc,mpoint,a,p);
      reference_to_montaffine(k,TAB(res,k,b,i,2),acc,p);

     for (j = 3; j <= (1<<(b-1)); ++j)
      { reference_montjadd(k,acc,acc,mpoint,p);
        reference_to_montaffine(k,TAB(res,k,b,i,j),acc,p);
      }

     reference_montjdouble(k,mpoint,acc,a,p);
   }
}

// Generic Weierstrass scalar multiplication for 64k-bit scalar and point
// where the table of multiples with block size b has been precomputed
//
// p is the field characteristic
// n is the group order
// a is the *MONTGOMERY FORM* coefficient of x (which is often -3 mod p)

void reference_scalarmultab
  (uint64_t k,uint64_t *res,uint64_t *scalar,uint64_t b,uint64_t *tab,
   uint64_t *p,uint64_t *n,uint64_t *a)
{ uint64_t *rscalar = alloca(8 * k);
  uint64_t *acc = alloca(3 * 8 * k);
  uint64_t *tabent = alloca(2 * 8 * k);

  uint64_t i, bf, cf, j;

  // Reduce scalar modulo n, to avoid worries over P + P in addition

  reference_mod(k,rscalar,scalar,n);

  // Initialize accumulator and "carry-in" to zero

  bignum_of_word(3*k,acc,0);
  cf = 0;

  // Main loop

  for (i = 0; b*i <= 64*k; ++i)
   { bf = bignum_bitfield(k,rscalar,b*i,b) + cf;
     cf = (bf > (1<<(b-1)));
     j = cf ? (1<<b) - bf : bf;

     if (j == 0) bignum_of_word(2*k,tabent,0);
     else bignum_copy(2*k,tabent,2*k,TAB(tab,k,b,i,j));

     bignum_modoptneg(k,tabent+k,cf,tabent+k,p);

     if (j != 0) reference_montjmixadd(k,acc,acc,tabent,p);

   }

  // Convert back to affine form

  reference_to_affine(k,res,acc,p);
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

int test_bignum_add_p25519(void)
{ uint64_t i, k;
  printf("Testing bignum_add_p25519 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_25519);
     bignum_add_p25519(b2,b0,b1);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_25519);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_25519[0],b2[0]);
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

int test_bignum_add_sm2(void)
{ uint64_t i, k;
  printf("Testing bignum_add_sm2 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_sm2);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_sm2);
     bignum_add_sm2(b2,b0,b1);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b1);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_sm2);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_sm2[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" + ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_sm2[0],b2[0]);
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

int test_bignum_cmul_p25519(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p25519 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     m = random64();
     bignum_cmul_p25519(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_25519);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_25519[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmul_p25519_alt(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p25519_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     m = random64();
     bignum_cmul_p25519_alt(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_25519);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_25519[0],b2[0]);
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

int test_bignum_cmul_p384_alt(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p384_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_384);
     m = random64();
     bignum_cmul_p384_alt(b2,m,b0);
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

int test_bignum_cmul_p521_alt(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_p521_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     m = random64();
     bignum_cmul_p521_alt(b2,m,b0);
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

int test_bignum_cmul_sm2(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_sm2 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_sm2);
     m = random64();
     bignum_cmul_sm2(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_sm2);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_sm2[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_sm2[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_cmul_sm2_alt(void)
{ uint64_t i, k, m;
  printf("Testing bignum_cmul_sm2_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_sm2);
     m = random64();
     bignum_cmul_sm2_alt(b2,m,b0);
     reference_mul(k+1,b1,1,&m,k,b0);
     reference_copy(k+1,b3,k,p_sm2);
     reference_mod(k+1,b4,b1,b3);
     reference_copy(k,b3,k+1,b4);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64" *  ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,m,b0[0],p_sm2[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,m,b0[0],p_sm2[0],b2[0]);
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

int test_bignum_copy_row_from_table_specific(const char *name, uint64_t fixed_width,
    int width_multiple_of_8,
    void (*f)(uint64_t*, const uint64_t*, uint64_t, uint64_t, uint64_t))
{ uint64_t i, t;
  // The height, width, height*width of table
  uint64_t h, w, n;
  printf("Testing %s with %d cases\n", name, tests);
  int c;

  for (t = 0; t < tests; ++t)
   { // Use BUFFERSIZE instead of MAXSIZE because MAXSIZE is too small
     if (fixed_width) w = fixed_width;
     else {
       w = (uint64_t) rand() % (uint64_t)sqrt((double)BUFFERSIZE);
       if (width_multiple_of_8) w = w & ~7ull;
     }

     h = (uint64_t) rand() % (uint64_t)sqrt((double)BUFFERSIZE);
     if (h == 0) ++h;
     n = h * w;
     uint64_t *table = malloc(n * sizeof(uint64_t));
     for (i = 0; i < h; ++i)
       random_bignum(w,&table[w * i]);

     i = rand() % h;
     reference_copy(w,b1,w,&table[w * i]);
     f(b2, table, h, w, i);

     c = reference_compare(w,b2,w,b1);
     free(table);

     if (c != 0)
      { printf("### Disparity: [height %5"PRIu64", width %5"PRIu64"] "
               "table [%5"PRIu64"*%5"PRIu64"] = ....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               h, w, i, w, b2[0], b1[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [height %5"PRIu64", width %5"PRIu64"]", h, w);
        if (n == 0) printf("\n");
        else printf(" element [%5"PRIu64"*%5"PRIu64"] = .0x%016"PRIx64"\n",
                    i, w, b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_copy_row_from_table(void)
{
  return test_bignum_copy_row_from_table_specific("bignum_copy_row_from_table",
      0, 0, bignum_copy_row_from_table);
}

int test_bignum_copy_row_from_table_8n(void)
{
#ifdef __x86_64__
  return 1;
#else
  return test_bignum_copy_row_from_table_specific(
      "bignum_copy_row_from_table_8n", 0, 1,
      bignum_copy_row_from_table_8n);
#endif
}

#ifdef __x86_64__
int test_bignum_copy_row_from_table_16(void)
{ return 1;
}
#else
void _bignum_copy_row_from_table_16_wrapper(uint64_t *z, const uint64_t *table,
                                                 uint64_t height,
                                                 uint64_t width,
                                                 uint64_t index) {
  assert(width == 16);
  bignum_copy_row_from_table_16(z, table, height, index);
}

int test_bignum_copy_row_from_table_16(void)
{ return test_bignum_copy_row_from_table_specific(
      "bignum_copy_row_from_table_16", 16, 0,
      _bignum_copy_row_from_table_16_wrapper);
}
#endif

#ifdef __x86_64__
int test_bignum_copy_row_from_table_32(void)
{ return 1;
}
#else
void _bignum_copy_row_from_table_32_wrapper(uint64_t *z, const uint64_t *table,
                                                 uint64_t height,
                                                 uint64_t width,
                                                 uint64_t index) {
  assert(width == 32);
  bignum_copy_row_from_table_32(z, table, height, index);
}

int test_bignum_copy_row_from_table_32(void)
{ return test_bignum_copy_row_from_table_specific(
      "bignum_copy_row_from_table_32", 32, 0,
      _bignum_copy_row_from_table_32_wrapper);
}
#endif

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

int test_bignum_deamont_p384_alt(void)
{ uint64_t t;
  printf("Testing bignum_deamont_p384_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     bignum_deamont_p384_alt(b4,b0);
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

int test_bignum_deamont_sm2(void)
{ uint64_t t;
  printf("Testing bignum_deamont_sm2 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     bignum_deamont_sm2(b4,b0);
     reference_of_word(4,b1,UINT64_C(1));
     reference_dmontmul(4,b3,b0,b1,p_sm2,i_sm2,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
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

int test_bignum_demont_p384_alt(void)
{ uint64_t t;
  printf("Testing bignum_demont_p384_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b2);
     reference_mod(6,b0,b2,p_384);
     bignum_demont_p384_alt(b4,b0);
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

int test_bignum_demont_sm2(void)
{ uint64_t t;
  printf("Testing bignum_demont_sm2 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_sm2);
     bignum_demont_sm2(b4,b0);
     reference_of_word(4,b1,UINT64_C(1));
     reference_dmontmul(4,b3,b0,b1,p_sm2,i_sm2,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
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

int test_bignum_double_p25519(void)
{ uint64_t i, k;
  printf("Testing bignum_double_p25519 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     bignum_double_p25519(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_25519);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_25519[0],b2[0]);
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

int test_bignum_double_sm2(void)
{ uint64_t i, k;
  printf("Testing bignum_double_sm2 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_sm2);
     bignum_double_sm2(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_sm2);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_sm2[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_sm2[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_emontredc_specific(const char *name, int is_8n, int ge_16,
                                   uint64_t (*f)(uint64_t, uint64_t *,
                                                 const uint64_t *, uint64_t)) {
  uint64_t t, k, w, tc;
  printf("Testing %s with %d cases\n", name, tests);

  int c;
  for (t = 0; t < tests; ++t) {
    k = (unsigned)rand() % MAXSIZE;
    if (is_8n) {
      k = (k >> 3) << 3;
      if (k == 0)
        k = 8;
      if (ge_16 && k < 16)
        k = 16;
    }

    random_bignum(k, b0);
    b0[0] |= 1;                // b0 = m
    w = word_negmodinv(b0[0]); // w = negated modular inverse
    random_bignum(2 * k, b4);  // b4 = initial z

    reference_copy(2 * k + 1, b1, 2 * k, b4); // b1 = longer copy of z_0
    reference_copy(2 * k + 1, b2, 2 * k, b4); // b2 = also longer copy of z_0

    tc = f(k, b4, b0, w);

    reference_madd(2 * k + 1, b1, k, b4, k, b0); // b1 = q * m + z_0

    c = ((b1[2 * k] == tc) && reference_eq_samelen(k, b4 + k, b1 + k) &&
         reference_iszero(k, b1));

    if (!c) {
      printf("### Disparity reducing modulo: [size %4" PRIu64 " -> %4" PRIu64
             "] "
             "...%016" PRIx64 " / 2^%" PRIu64 " mod ...%016" PRIx64
             " = ...%016" PRIx64 "\n",
             2 * k, k, b2[0], 64 * k, b0[0], b4[k]);
      return 1;
    } else if (VERBOSE) {
      printf("OK: [size %4" PRIu64 " -> %4" PRIu64 "] "
             "...%016" PRIx64 " / 2^%" PRIu64 " mod ...%016" PRIx64
             " = ...%016" PRIx64 "\n",
             2 * k, k, b2[0], 64 * k, b0[0], b4[0]);
    }
  }
  printf("All OK\n");
  return 0;
}

int test_bignum_emontredc(void)
{ return test_bignum_emontredc_specific("bignum_emontredc", 0, 0,
                                        bignum_emontredc);
}

int test_bignum_emontredc_8n(void)
{ return test_bignum_emontredc_specific("bignum_emontredc_8n", 1, 0,
                                        bignum_emontredc_8n);
}

#ifndef __x86_64__
uint64_t bignum_emontredc_8n_cdiff_wrapper (uint64_t k, uint64_t *z,
                                            const uint64_t *m, uint64_t w) {
  // b12 is a buffer that is not used by bignum_emontredc_specific.
  return bignum_emontredc_8n_cdiff(k, z, m, w, b12);
}
#endif

int test_bignum_emontredc_8n_cdiff(void)
{
#ifdef __x86_64__
  // Do not call the neon function to avoid a linking failure error.
  return 1;
#else
  return test_bignum_emontredc_specific("bignum_emontredc_8n_cdiff", 1, 1,
                                        bignum_emontredc_8n_cdiff_wrapper);
#endif
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

int test_bignum_fromlebytes_p521(void)
{ uint64_t t;
  printf("Testing bignum_fromlebytes_p521 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b0);
     reference_fromlebytes(9,b3,66,(uint8_t *)b0);
     bignum_fromlebytes_p521(b4,(uint8_t *)b0);
     c = reference_compare(9,b3,9,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_fromlebytes_p521(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[8],b0[0],b4[8],b4[0],b3[8],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_fromlebytes_p521(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[8],b0[0],b4[8],b4[0]);
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

int test_bignum_half_sm2(void)
{ uint64_t i, k;
  printf("Testing bignum_half_sm2 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_sm2);

     bignum_half_sm2(b2,b0);

     reference_adc(k+1,b4,k,b2,k,b2,0);
     reference_copy(k+1,b5,k,p_sm2);
     reference_mod(k+1,b6,b4,b5);
     reference_copy(k,b3,k+1,b6);

     c = reference_compare(k,b3,k,b0);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_sm2[0],b3[0],b0[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "2 * (...0x%016"PRIx64" / 2) mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_sm2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_inv_p25519(void)
{ uint64_t i, k;
  int c, d;
  printf("Testing bignum_inv_p25519 with %d cases\n",tests);

  for (i = 0; i < tests; ++i)
   { k = 4;
     bignum_copy(k,b0,k,p_25519);

     do random_bignum(k,b1);
     while (!reference_coprime(k,b1,b0));

     // Make sure to check the degenerate a = 1 cases occasionally
     if ((rand() & 0xFFF) < 1) reference_of_word(k,b1,UINT64_C(1));

     // Another pathological case worth re-checking
     // It makes some intermediate results > p_25519
     // for the current algorithm

     if ((rand() & 0xFFFF) < 1)
      { b1[3] = 0xfddfffffffffffff;
        b1[2] = 0xffffffffffffffff;
        b1[1] = 0xfffffffbffffffff;
        b1[0] = 0xffffefffffffffff;
      }

     bignum_inv_p25519(b2,b1);             // s with a * s == 1 (mod b)
     reference_mul(2 * k,b4,k,b1,k,b2);    // b4 = a * s
     reference_copy(2 * k,b5,k,b0);        // b5 = b (double-length)
     reference_mod(2 * k,b3,b4,b5);        // b3 = (a * s) mod b
     reference_modpowtwo(k,b4,0,b0);       // b4 = 1 mod b = 2^k mod b

     c = reference_compare(k,b3,k,b4);
     d = reference_le(k,p_25519,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0],b4[0]);
        return 1;
      }
     else if (d != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "congruent but not reduced modulo, top word 0x%016"PRIx64"\n",
               k,b2[3]);
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

int test_bignum_inv_p256(void)
{ uint64_t i, k;
  int c, d;
  printf("Testing bignum_inv_p256 with %d cases\n",tests);

  for (i = 0; i < tests; ++i)
   { k = 4;
     bignum_copy(k,b0,k,p_256);

     do random_bignum(k,b1);
     while (!reference_coprime(k,b1,b0));

     // Make sure to check the degenerate a = 1 cases occasionally
     if ((rand() & 0xFFF) < 1) reference_of_word(k,b1,UINT64_C(1));

     bignum_inv_p256(b2,b1);             // s with a * s == 1 (mod b)

     reference_mul(2 * k,b4,k,b1,k,b2);    // b4 = a * s
     reference_copy(2 * k,b5,k,b0);        // b5 = b (double-length)
     reference_mod(2 * k,b3,b4,b5);        // b3 = (a * s) mod b
     reference_modpowtwo(k,b4,0,b0);       // b4 = 1 mod b = 2^k mod b

     c = reference_compare(k,b3,k,b4);
     d = reference_le(k,p_256,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0],b4[0]);
        return 1;
      }
     else if (d != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "congruent but not reduced modulo, top word 0x%016"PRIx64"\n",
               k,b2[3]);
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

int test_bignum_inv_p384(void)
{ uint64_t i, k;
  int c, d;
  printf("Testing bignum_inv_p384 with %d cases\n",tests);

  for (i = 0; i < tests; ++i)
   { k = 6;
     bignum_copy(k,b0,k,p_384);

     do random_bignum(k,b1);
     while (!reference_coprime(k,b1,b0));

     // Make sure to check the degenerate a = 1 cases occasionally
     if ((rand() & 0xFFF) < 1) reference_of_word(k,b1,UINT64_C(1));

     bignum_inv_p384(b2,b1);             // s with a * s == 1 (mod b)

     reference_mul(2 * k,b4,k,b1,k,b2);    // b4 = a * s
     reference_copy(2 * k,b5,k,b0);        // b5 = b (double-length)
     reference_mod(2 * k,b3,b4,b5);        // b3 = (a * s) mod b
     reference_modpowtwo(k,b4,0,b0);       // b4 = 1 mod b = 2^k mod b

     c = reference_compare(k,b3,k,b4);
     d = reference_le(k,p_384,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0],b4[0]);
        return 1;
      }
     else if (d != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "congruent but not reduced modulo, top word 0x%016"PRIx64"\n",
               k,b2[3]);
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

int test_bignum_inv_p521(void)
{ uint64_t i, k;
  int c, d;
  printf("Testing bignum_inv_p521 with %d cases\n",tests);

  for (i = 0; i < tests; ++i)
   { k = 9;
     bignum_copy(k,b0,k,p_521);

     do random_bignum(k,b1);
     while (!reference_coprime(k,b1,b0));

     // Make sure to check the degenerate a = 1 cases occasionally
     if ((rand() & 0xFFF) < 1) reference_of_word(k,b1,UINT64_C(1));

     bignum_inv_p521(b2,b1);               // s with a * s == 1 (mod b)

     reference_mul(2 * k,b4,k,b1,k,b2);    // b4 = a * s
     reference_copy(2 * k,b5,k,b0);        // b5 = b (double-length)
     reference_mod(2 * k,b3,b4,b5);        // b3 = (a * s) mod b
     reference_modpowtwo(k,b4,0,b0);       // b4 = 1 mod b = 2^k mod b

     c = reference_compare(k,b3,k,b4);
     d = reference_le(k,p_521,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0],b4[0]);
        return 1;
      }
     else if (d != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "congruent but not reduced modulo, top word 0x%016"PRIx64"\n",
               k,b2[3]);
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

int test_bignum_inv_sm2(void)
{ uint64_t i, k;
  int c, d;
  printf("Testing bignum_inv_sm2 with %d cases\n",tests);

  for (i = 0; i < tests; ++i)
   { k = 4;
     bignum_copy(k,b0,k,p_sm2);

     do random_bignum(k,b1);
     while (!reference_coprime(k,b1,b0));

     // Make sure to check the degenerate a = 1 cases occasionally
     if ((rand() & 0xFFF) < 1) reference_of_word(k,b1,UINT64_C(1));

     bignum_inv_sm2(b2,b1);                // s with a * s == 1 (mod b)

     reference_mul(2 * k,b4,k,b1,k,b2);    // b4 = a * s
     reference_copy(2 * k,b5,k,b0);        // b5 = b (double-length)
     reference_mod(2 * k,b3,b4,b5);        // b3 = (a * s) mod b
     reference_modpowtwo(k,b4,0,b0);       // b4 = 1 mod b = 2^k mod b

     c = reference_compare(k,b3,k,b4);
     d = reference_le(k,p_sm2,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0],b4[0]);
        return 1;
      }
     else if (d != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "congruent but not reduced modulo, top word 0x%016"PRIx64"\n",
               k,b2[3]);
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

int test_bignum_invsqrt_p25519(void)
{ uint64_t i, k;
  printf("Testing bignum_invsqrt_p25519 with %d cases\n",tests);
  uint64_t c, d;
  uint64_t  l, r;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     l = reference_legendre(k,b0,p_25519);
     r = bignum_invsqrt_p25519(b2,b0);

     reference_mul(2*k,b4,k,b2,k,b2);
     reference_copy(2*k,b3,k,p_25519);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b4,2*k,b5);       // b4 = b2^2

     reference_mul(2*k,b5,k,b4,k,b0);
     reference_mod(2*k,b4,b5,b3);
     reference_copy(k,b3,2*k,b4);       // b3 = b0 * b2^2

     reference_of_word(k,b4,1);         // b4 = 1

     c = reference_compare(k,b3,k,b4);
     d = reference_iszero(k,b3);

     if (l != r)
      { printf("### Disparity: [size %4"PRIu64"] "
               "legendre(...0x%016"PRIx64" / ....0x%016"PRIx64") = "
               "%"PRIi64" not %"PRIi64"\n",
               k,b0[0],p_25519[0],r,l);
        return 1;
      }
     else if ((l == 0) != d)
      { printf("### Disparity: [size %4"PRIu64"] "
               "Legendre symbol (%"PRIi64") versus result zeroness "
               "on ...0x%016"PRIx64"\n",
               k,l,b0[0]);
        return 1;
      }
     else if ((l == 1) && (c != 0))
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b2[0],p_25519[0],b3[0],b4[0]);
        return 1;
      }
     else if (b2[0] & 1)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" is odd (wrong choice of square root)\n",
               k,b2[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64" (%s)\n",
                    k,b0[2],b2[0],p_25519[0],b3[0],
                    ((l == -1) ? "nonresidue" :
                     (l == 1) ? "residue" :
                     (l == 0) ? "trivial" : "invalid"));
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_invsqrt_p25519_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_invsqrt_p25519_alt with %d cases\n",tests);
  uint64_t c, d;
  uint64_t  l, r;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     l = reference_legendre(k,b0,p_25519);
     r = bignum_invsqrt_p25519_alt(b2,b0);

     reference_mul(2*k,b4,k,b2,k,b2);
     reference_copy(2*k,b3,k,p_25519);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b4,2*k,b5);       // b4 = b2^2

     reference_mul(2*k,b5,k,b4,k,b0);
     reference_mod(2*k,b4,b5,b3);
     reference_copy(k,b3,2*k,b4);       // b3 = b0 * b2^2

     reference_of_word(k,b4,1);         // b4 = 1

     c = reference_compare(k,b3,k,b4);
     d = reference_iszero(k,b3);

     if (l != r)
      { printf("### Disparity: [size %4"PRIu64"] "
               "legendre(...0x%016"PRIx64" / ....0x%016"PRIx64") = "
               "%"PRIi64" not %"PRIi64"\n",
               k,b0[0],p_25519[0],r,l);
        return 1;
      }
     else if ((l == 0) != d)
      { printf("### Disparity: [size %4"PRIu64"] "
               "Legendre symbol (%"PRIi64") versus result zeroness "
               "on ...0x%016"PRIx64"\n",
               k,l,b0[0]);
        return 1;
      }
     else if ((l == 1) && (c != 0))
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b2[0],p_25519[0],b3[0],b4[0]);
        return 1;
      }
     else if (b2[0] & 1)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" is odd (wrong choice of square root)\n",
               k,b2[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64" (%s)\n",
                    k,b0[2],b2[0],p_25519[0],b3[0],
                    ((l == -1) ? "nonresidue" :
                     (l == 1) ? "residue" :
                     (l == 0) ? "trivial" : "invalid"));
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
   void (*f)(uint64_t *,const uint64_t *, const uint64_t *,uint64_t *))
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
   void (*f)(uint64_t *,const uint64_t *,uint64_t *))
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

int test_bignum_madd_n25519(void)
{ uint64_t t, k;
  printf("Testing bignum_madd_n25519 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = 4;
     random_bignum(8,b0);
     random_bignum(4,b1);
     random_bignum(4,b2);
     random_bignum(4,b3);
     bignum_madd_n25519(b0,b1,b2,b3);
     bignum_copy(9,b4,4,b3);
     reference_madd(9,b4,4,b1,4,b2);
     reference_copy(9,b5,4,n_25519);
     reference_mod(9,b6,b4,b5);
     reference_copy(4,b4,9,b6);
     c = reference_compare(4,b0,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "(...0x%016"PRIx64" * ...%016"PRIx64" + ...%016"PRIx64") mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b1[0],b2[0],b3[0],b0[3],b0[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] "
               "(...0x%016"PRIx64" * ...%016"PRIx64" + ...%016"PRIx64") mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b1[0],b2[0],b3[0],b0[3],b0[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_madd_n25519_alt(void)
{ uint64_t t, k;
  printf("Testing bignum_madd_n25519_alt with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = 4;
     random_bignum(8,b0);
     random_bignum(4,b1);
     random_bignum(4,b2);
     random_bignum(4,b3);
     bignum_madd_n25519_alt(b0,b1,b2,b3);
     bignum_copy(9,b4,4,b3);
     reference_madd(9,b4,4,b1,4,b2);
     reference_copy(9,b5,4,n_25519);
     reference_mod(9,b6,b4,b5);
     reference_copy(4,b4,9,b6);
     c = reference_compare(4,b0,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "(...0x%016"PRIx64" * ...%016"PRIx64" + ...%016"PRIx64") mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b1[0],b2[0],b3[0],b0[3],b0[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] "
               "(...0x%016"PRIx64" * ...%016"PRIx64" + ...%016"PRIx64") mod n_256 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b1[0],b2[0],b3[0],b0[3],b0[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_m25519_4(void)
{ uint64_t t;
  printf("Testing bignum_mod_m25519_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     if ((rand() & 0xF) == 0) b0[3] |= UINT64_C(0xFFFFFFF000000000);
     else if ((rand() & 0xF) == 0)
      { b0[3] = m_25519[3];
        b0[2] = m_25519[2];
        b0[1] = m_25519[1];
        b0[0] = (m_25519[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(4,b3,b0,m_25519);
     bignum_mod_m25519_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod m_25519 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod m_25519 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_n25519(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_n25519 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,4,n_25519);
     reference_mod(k,b3,b0,b1);
     bignum_mod_n25519(b4,k,b0);
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

int test_bignum_mod_n25519_4(void)
{ uint64_t t;
  printf("Testing bignum_mod_n25519_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     if ((rand() & 0xF) == 0) b0[3] |= UINT64_C(0xFFFFFFF000000000);
     else if ((rand() & 0xF) == 0)
      { b0[3] = n_25519[3];
        b0[2] = n_25519[2];
        b0[1] = n_25519[1];
        b0[0] = (n_25519[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(4,b3,b0,n_25519);
     bignum_mod_n25519_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_25519 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_25519 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
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

int test_bignum_mod_n384_alt(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_n384_alt with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,6,n_384);
     reference_mod(k,b3,b0,b1);
     bignum_mod_n384_alt(b4,k,b0);
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

int test_bignum_mod_n521_9_alt(void)
{ uint64_t t;
  printf("Testing bignum_mod_n521_9_alt with %d cases\n",tests);
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
     bignum_mod_n521_9_alt(b4,b0);
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

int test_bignum_mod_nsm2(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_nsm2 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,4,n_sm2);
     reference_mod(k,b3,b0,b1);
     bignum_mod_nsm2(b4,k,b0);
     c = reference_compare(k,(k < 4) ? b0 : b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_nsm2_alt(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_nsm2_alt with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,4,n_sm2);
     reference_mod(k,b3,b0,b1);
     bignum_mod_nsm2_alt(b4,k,b0);
     c = reference_compare(k,(k < 4) ? b0 : b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_nsm2_4(void)
{ uint64_t t;
  printf("Testing bignum_mod_nsm2_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     if ((rand() & 0xF) == 0) b0[3] |= UINT64_C(0xFFFFFFF000000000);
     else if ((rand() & 0xF) == 0)
      { b0[3] = n_sm2[3];
        b0[2] = n_sm2[2];
        b0[1] = n_sm2[1];
        b0[0] = (n_sm2[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(4,b3,b0,n_sm2);
     bignum_mod_nsm2_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod n_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod n_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_p25519_4(void)
{ uint64_t t;
  printf("Testing bignum_mod_p25519_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     if ((rand() & 0xF) == 0)
      { b0[3] = p_25519[3];
        b0[2] = p_25519[2];
        b0[1] = p_25519[1];
        b0[0] = (p_25519[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(4,b3,b0,p_25519);
     bignum_mod_p25519_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_25519 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_25519 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
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

int test_bignum_mod_p384_alt(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_p384_alt with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,6,p_384);
     reference_mod(k,b3,b0,b1);
     bignum_mod_p384_alt(b4,k,b0);
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

int test_bignum_mod_sm2(void)
{ uint64_t t, k;
  printf("Testing bignum_mod_sm2 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);
     reference_copy(k,b1,4,p_sm2);
     reference_mod(k,b3,b0,b1);
     bignum_mod_sm2(b4,k,b0);
     c = reference_compare(k,(k < 4) ? b0 : b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64" -> %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64" -> %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,UINT64_C(4),b0[k-1],b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mod_sm2_4(void)
{ uint64_t t;
  printf("Testing bignum_mod_sm2_4 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     if ((rand() & 0xF) == 0) b0[3] |= UINT64_C(0xFFFFFFF000000000);
     else if ((rand() & 0xF) == 0)
      { b0[3] = p_sm2[3];
        b0[2] = p_sm2[2];
        b0[1] = p_sm2[1];
        b0[0] = (p_sm2[0] - UINT64_C(3)) + (rand() & UINT64_C(7));
      }

     reference_mod(4,b3,b0,p_sm2);
     bignum_mod_sm2_4(b4,b0);
     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] 0x%016"PRIx64"...%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[3],b0[0],b4[3],b4[0]);
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

int test_bignum_modexp(void)
{ uint64_t i, k;
  printf("Testing bignum_modexp with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = (unsigned) rand() % MAXSIZE;
     random_bignum(k,b0);       // a
     random_bignum(k,b1);       // p
     random_bignum(k,b2);       // m
     b2[0] |= 1;                // ...which is always odd

     bignum_modexp(k,b3,b0,b1,b2,b5);
     reference_modexp(k,b4,b0,b1,b2);
     c = reference_compare(k,b4,k,b3);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" ^ ...0x%016"PRIx64" mod ...0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "...0x%016"PRIx64" ^ ...0x%016"PRIx64" mod ...0x%016"PRIx64" = ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],b2[0],b3[0]);
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

     // Make sure to check the degenerate a = 1 and b = 1 cases occasionally
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

int test_bignum_montinv_p256(void)
{ uint64_t i, k;
  int c, d;
  printf("Testing bignum_montinv_p256 with %d cases\n",tests);

  for (i = 0; i < tests; ++i)
   { k = 4;
     bignum_copy(k,b0,k,p_256);

     do random_bignum(k,b1);
     while (!reference_coprime(k,b1,b0));

     // Make sure to check the degenerate a = 1 cases occasionally
     if ((rand() & 0xFFF) < 1) reference_of_word(k,b1,UINT64_C(1));

     bignum_montinv_p256(b2,b1);           // s with a * s == 2^512 (mod b)

     reference_mul(2 * k,b4,k,b1,k,b2);    // b4 = a * s
     reference_copy(2 * k,b5,k,b0);        // b5 = b (double-length)
     reference_mod(2 * k,b3,b4,b5);        // b3 = (a * s) mod b
     reference_modpowtwo(k,b4,512,b0);     // b4 = 2^512 mod b

     c = reference_compare(k,b3,k,b4);
     d = reference_le(k,p_256,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0],b4[0]);
        return 1;
      }
     else if (d != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "congruent but not reduced modulo, top word 0x%016"PRIx64"\n",
               k,b2[3]);
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

int test_bignum_montinv_p384(void)
{ uint64_t i, k;
  int c, d;
  printf("Testing bignum_montinv_p384 with %d cases\n",tests);

  for (i = 0; i < tests; ++i)
   { k = 6;
     bignum_copy(k,b0,k,p_384);

     do random_bignum(k,b1);
     while (!reference_coprime(k,b1,b0));

     // Make sure to check the degenerate a = 1 cases occasionally
     if ((rand() & 0xFFF) < 1) reference_of_word(k,b1,UINT64_C(1));

     bignum_montinv_p384(b2,b1);           // s with a * s == 2^768 (mod b)

     reference_mul(2 * k,b4,k,b1,k,b2);    // b4 = a * s
     reference_copy(2 * k,b5,k,b0);        // b5 = b (double-length)
     reference_mod(2 * k,b3,b4,b5);        // b3 = (a * s) mod b
     reference_modpowtwo(k,b4,768,b0);     // b4 = 2^768 mod b

     c = reference_compare(k,b3,k,b4);
     d = reference_le(k,p_384,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0],b4[0]);
        return 1;
      }
     else if (d != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "congruent but not reduced modulo, top word 0x%016"PRIx64"\n",
               k,b2[3]);
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

int test_bignum_montinv_sm2(void)
{ uint64_t i, k;
  int c, d;
  printf("Testing bignum_montinv_sm2 with %d cases\n",tests);

  for (i = 0; i < tests; ++i)
   { k = 4;
     bignum_copy(k,b0,k,p_sm2);

     do random_bignum(k,b1);
     while (!reference_coprime(k,b1,b0));

     // Make sure to check the degenerate a = 1 cases occasionally
     if ((rand() & 0xFFF) < 1) reference_of_word(k,b1,UINT64_C(1));

     bignum_montinv_sm2(b2,b1);           // s with a * s == 2^512 (mod b)

     reference_mul(2 * k,b4,k,b1,k,b2);    // b4 = a * s
     reference_copy(2 * k,b5,k,b0);        // b5 = b (double-length)
     reference_mod(2 * k,b3,b4,b5);        // b3 = (a * s) mod b
     reference_modpowtwo(k,b4,512,b0);     // b4 = 2^512 mod b

     c = reference_compare(k,b3,k,b4);
     d = reference_le(k,p_sm2,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * modinv(...0x%016"PRIx64") mod ...0x%016"PRIx64" = "
               "....0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b1[0],b1[0],b0[0],b3[0],b4[0]);
        return 1;
      }
     else if (d != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "congruent but not reduced modulo, top word 0x%016"PRIx64"\n",
               k,b2[3]);
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

int test_bignum_montmul_p256_specific(
    const char *name, void (*f)(uint64_t *, const uint64_t *, const uint64_t *))
{ uint64_t t;
  printf("Testing %s with %d cases\n",name,tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256);
     random_bignum(4,b2);
     reference_mod(4,b1,b2,p_256);
     f(b4,b0,b1);
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

int test_bignum_montmul_p256(void)
{ return test_bignum_montmul_p256_specific("bignum_montmul_p256",
      bignum_montmul_p256);
}

int test_bignum_montmul_p256_alt(void)
{ return test_bignum_montmul_p256_specific("bignum_montmul_p256_alt",
      bignum_montmul_p256_alt);
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

int test_bignum_montmul_p384_specific(const char *name,
    void (*f)(uint64_t *z, const uint64_t *x, const uint64_t *y))
{ uint64_t t;
  printf("Testing %s with %d cases\n",name,tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b2);
     reference_mod(6,b0,b2,p_384);
     random_bignum(6,b2);
     reference_mod(6,b1,b2,p_384);
     f(b4,b0,b1);
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

int test_bignum_montmul_p384(void) {
  return test_bignum_montmul_p384_specific("bignum_montmul_p384",
                                           bignum_montmul_p384);
}

int test_bignum_montmul_p384_alt(void) {
  return test_bignum_montmul_p384_specific("bignum_montmul_p384_alt",
                                           bignum_montmul_p384_alt);
}

int test_bignum_montmul_p521_specific(const char *name,
                                      void (*f)(uint64_t *z, const uint64_t *x,
                                                const uint64_t *y)) {
  uint64_t t;
  printf("Testing %s with %d cases\n",name,tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b2);
     reference_mod(9,b0,b2,p_521);
     random_bignum(9,b2);
     reference_mod(9,b1,b2,p_521);
     f(b4,b0,b1);
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

int test_bignum_montmul_p521(void)
{ return test_bignum_montmul_p521_specific("bignum_montmul_p521",
                                           bignum_montmul_p521);
}

int test_bignum_montmul_p521_alt(void)
{ return test_bignum_montmul_p521_specific("bignum_montmul_p521_alt",
                                           bignum_montmul_p521_alt);
}

int test_bignum_montmul_sm2(void)
{ uint64_t t;
  printf("Testing bignum_montmul_sm2 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_sm2);
     random_bignum(4,b2);
     reference_mod(4,b1,b2,p_sm2);
     bignum_montmul_sm2(b4,b0,b1);
     reference_dmontmul(4,b3,b0,b1,p_sm2,i_sm2,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montmul_sm2_alt(void)
{ uint64_t t;
  printf("Testing bignum_montmul_sm2_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_sm2);
     random_bignum(4,b2);
     reference_mod(4,b1,b2,p_sm2);
     bignum_montmul_sm2_alt(b4,b0,b1);
     reference_dmontmul(4,b3,b0,b1,p_sm2,i_sm2,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64" * ...%016"PRIx64"  mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b1[0],b4[3],b4[0]);
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

int test_bignum_montsqr_p256_specific(const char *name,
    void (*f)(uint64_t *z, const uint64_t *x))
{ uint64_t t;
  printf("Testing %s with %d cases\n",name,tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_256);
     f(b4,b0);
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

int test_bignum_montsqr_p256(void)
{ return test_bignum_montsqr_p256_specific("bignum_montsqr_p256",
      bignum_montsqr_p256);
}

int test_bignum_montsqr_p256_alt(void)
{ return test_bignum_montsqr_p256_specific("bignum_montsqr_p256_alt",
      bignum_montsqr_p256_alt);
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

int test_bignum_montsqr_p384_specific(const char *name,
    void (*f)(uint64_t *z, const uint64_t *x))
{ uint64_t t;
  printf("Testing %s with %d cases\n",name,tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b2);
     reference_mod(6,b0,b2,p_384);
     f(b4,b0);
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

int test_bignum_montsqr_p384(void) {
  return test_bignum_montsqr_p384_specific("bignum_montsqr_p384",
                                           bignum_montsqr_p384);
}

int test_bignum_montsqr_p384_alt(void) {
  return test_bignum_montsqr_p384_specific("bignum_montsqr_p384_alt",
                                           bignum_montsqr_p384_alt);
}

int test_bignum_montsqr_p521_specific(const char *name,
                                      void (*f)(uint64_t *z, const uint64_t *x)) {
  uint64_t t;
  printf("Testing %s with %d cases\n",name,tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b2);
     reference_mod(9,b0,b2,p_521);
     f(b4,b0);
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

int test_bignum_montsqr_p521(void)
{ return test_bignum_montsqr_p521_specific("bignum_montsqr_p521",
                                           bignum_montsqr_p521);
}

int test_bignum_montsqr_p521_alt(void)
{ return test_bignum_montsqr_p521_specific("bignum_montsqr_p521_alt",
                                           bignum_montsqr_p521_alt);
}

int test_bignum_montsqr_sm2(void)
{ uint64_t t;
  printf("Testing bignum_montsqr_sm2 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_sm2);
     bignum_montsqr_sm2(b4,b0);
     reference_dmontmul(4,b3,b0,b0,p_sm2,i_sm2,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_montsqr_sm2_alt(void)
{ uint64_t t;
  printf("Testing bignum_montsqr_sm2_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b2);
     reference_mod(4,b0,b2,p_sm2);
     bignum_montsqr_sm2_alt(b4,b0);
     reference_dmontmul(4,b3,b0,b0,p_sm2,i_sm2,b5);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^-256 * ...0x%016"PRIx64"^2 mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
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
   void (*f)(uint64_t *,const uint64_t *,const uint64_t *))
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

int test_bignum_mul_6_12_alt(void)
{ return test_bignum_mul_specific(12,6,6,"bignum_mul_6_12_alt",bignum_mul_6_12_alt);
}

int test_bignum_mul_8_16(void)
{ return test_bignum_mul_specific(16,8,8,"bignum_mul_8_16",bignum_mul_8_16);
}

int test_bignum_mul_8_16_alt(void)
{ return test_bignum_mul_specific(16,8,8,"bignum_mul_8_16_alt",bignum_mul_8_16_alt);
}

int test_bignum_mul_p25519(void) {
  uint64_t i, k;
  printf("Testing bignum_mul_p25519 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     random_bignum(k,b1);
     bignum_mul_p25519(b2,b0,b1);
     reference_mul(2*k,b4,k,b0,k,b1);
     reference_copy(2*k,b3,k,p_25519);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);
     c = reference_compare(k,b3,k,b2);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_25519[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_mul_p25519_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_mul_p25519_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     random_bignum(k,b1);
     bignum_mul_p25519_alt(b2,b0,b1);
     reference_mul(2*k,b4,k,b0,k,b1);
     reference_copy(2*k,b3,k,p_25519);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);
     c = reference_compare(k,b3,k,b2);

     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],b1[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_25519[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
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

int test_bignum_mul_p521_specific(const char *name,
                                  void (*f)(uint64_t *z, const uint64_t *x,
                                            const uint64_t *y))
{ uint64_t i, k;
  printf("Testing %s with %d cases\n",name,tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_521);
     f(b2,b0,b1);
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

int test_bignum_mul_p521(void)
{ return test_bignum_mul_p521_specific("bignum_mul_p521", bignum_mul_p521);
}

int test_bignum_mul_p521_alt(void)
{ return test_bignum_mul_p521_specific("bignum_mul_p521_alt", bignum_mul_p521_alt);
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
     free(bs);

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

int test_bignum_neg_p25519(void)
{ uint64_t i, k;
  printf("Testing bignum_neg_p25519 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     if ((rand() & 0x1F) == 0) reference_of_word(k,b0,0);

     bignum_neg_p25519(b2,b0);
     if (reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_25519,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "- ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_25519[0],b2[0]);
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

int test_bignum_neg_sm2(void)
{ uint64_t i, k;
  printf("Testing bignum_neg_sm2 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_sm2);
     if ((rand() & 0x1F) == 0) reference_of_word(k,b0,0);

     bignum_neg_sm2(b2,b0);
     if (reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_sm2,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "- ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_sm2[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,b0[0],p_sm2[0],b2[0]);
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

int test_bignum_optneg_p25519(void)
{ uint64_t i, k, p;
  printf("Testing bignum_optneg_p25519 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     p = (rand() & 1) ? 0 :
         (rand() & 1) ? 1 :
         (rand() & 1) ? 2 : random64();
     bignum_optneg_p25519(b2,p,b0);
     if ((p == 0) || reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_25519,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_25519[0],b2[0]);
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

int test_bignum_optneg_sm2(void)
{ uint64_t i, k, p;
  printf("Testing bignum_optneg_sm2 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_sm2);
     p = (rand() & 1) ? 0 :
         (rand() & 1) ? 1 :
         (rand() & 1) ? 2 : random64();
     bignum_optneg_sm2(b2,p,b0);
     if ((p == 0) || reference_iszero(k,b0)) reference_copy(k,b3,k,b0);
     else reference_sub_samelen(k,b3,p_sm2,b0);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_sm2[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
               "%s...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64"\n",
               k,(p ? "-" : "+"),b0[0],p_sm2[0],b2[0]);
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
   void (*f)(uint64_t *, const uint64_t *))
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

int test_bignum_sqr_6_12_alt(void)
{ return test_bignum_sqr_specific(12,6,"bignum_sqr_6_12_alt",bignum_sqr_6_12_alt);
}

int test_bignum_sqr_8_16(void)
{ return test_bignum_sqr_specific(16,8,"bignum_sqr_8_16",bignum_sqr_8_16);
}

int test_bignum_sqr_8_16_alt(void)
{ return test_bignum_sqr_specific(16,8,"bignum_sqr_8_16_alt",bignum_sqr_8_16_alt);
}

int test_bignum_sqr_p25519(void)
{ uint64_t i, k;
  printf("Testing bignum_sqr_p25519 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_sqr_p25519(b2,b0);
     reference_mul(2*k,b4,k,b0,k,b0);
     reference_copy(2*k,b3,k,p_25519);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_25519[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sqr_p25519_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_sqr_p25519_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_sqr_p25519_alt(b2,b0);
     reference_mul(2*k,b4,k,b0,k,b0);
     reference_copy(2*k,b3,k,p_25519);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_25519[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
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

int test_bignum_sqr_p521_specific(const char *name, void (*f)(uint64_t*, const uint64_t*))
{ uint64_t i, k;
  printf("Testing %s with %d cases\n",name,tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     f(b2,b0);
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

int test_bignum_sqr_p521(void)
{ return test_bignum_sqr_p521_specific("bignum_sqr_p521", bignum_sqr_p521) ;
}

int test_bignum_sqr_p521_alt(void)
{ return test_bignum_sqr_p521_specific("bignum_sqr_p521_alt", bignum_sqr_p521_alt);
}

int test_bignum_sqrt_p25519(void)
{ uint64_t i, k;
  printf("Testing bignum_sqrt_p25519 with %d cases\n",tests);
  uint64_t c;
  uint64_t  l, r;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     l = reference_legendre(k,b0,p_25519);
     r = bignum_sqrt_p25519(b2,b0);
     reference_mul(2*k,b4,k,b2,k,b2);
     reference_copy(2*k,b3,k,p_25519);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);

     c = reference_compare(k,b3,k,b0);
     if (l != r)
      { printf("### Disparity: [size %4"PRIu64"] "
               "legendre(...0x%016"PRIx64" / ....0x%016"PRIx64") = "
               "%"PRIi64" not %"PRIi64"\n",
               k,b0[0],p_25519[0],r,l);
        return 1;
      }
     else if ((l != -1) && (c != 0))
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b2[0],p_25519[0],b3[0],b0[0]);
        return 1;
      }
     else if (b2[0] & 1)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" is odd (wrong choice of square root)\n",
               k,b2[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64" (%s)\n",
                    k,b2[0],p_25519[0],b0[0],
                    ((l == -1) ? "nonresidue" :
                     (l == 1) ? "residue" :
                     (l == 0) ? "trivial" : "invalid"));
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_sqrt_p25519_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_sqrt_p25519_alt with %d cases\n",tests);
  uint64_t c;
  uint64_t  l, r;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     l = reference_legendre(k,b0,p_25519);
     r = bignum_sqrt_p25519_alt(b2,b0);
     reference_mul(2*k,b4,k,b2,k,b2);
     reference_copy(2*k,b3,k,p_25519);
     reference_mod(2*k,b5,b4,b3);
     reference_copy(k,b3,2*k,b5);

     c = reference_compare(k,b3,k,b0);
     if (l != r)
      { printf("### Disparity: [size %4"PRIu64"] "
               "legendre(...0x%016"PRIx64" / ....0x%016"PRIx64") = "
               "%"PRIi64" not %"PRIi64"\n",
               k,b0[0],p_25519[0],r,l);
        return 1;
      }
     else if ((l != -1) && (c != 0))
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b2[0],p_25519[0],b3[0],b0[0]);
        return 1;
      }
     else if (b2[0] & 1)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" is odd (wrong choice of square root)\n",
               k,b2[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" ^ 2 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64" (%s)\n",
                    k,b2[0],p_25519[0],b0[0],
                    ((l == -1) ? "nonresidue" :
                     (l == 1) ? "residue" :
                     (l == 0) ? "trivial" : "invalid"));
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

int test_bignum_sub_p25519(void)
{ uint64_t i, k;
  printf("Testing bignum_sub_p25519 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_25519);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_25519);
     bignum_sub_p25519(b2,b0,b1);
     reference_copy(k+1,b3,k,p_25519);
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
               k,b0[0],b1[0],p_25519[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_25519[0],b2[0]);
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

int test_bignum_sub_sm2(void)
{ uint64_t i, k;
  printf("Testing bignum_sub_sm2 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_sm2);
     random_bignum(k,b2); reference_mod(k,b1,b2,p_sm2);
     bignum_sub_sm2(b2,b0,b1);
     reference_copy(k+1,b3,k,p_sm2);
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
               k,b0[0],b1[0],p_sm2[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" - ...0x%016"PRIx64" mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],b1[0],p_sm2[0],b2[0]);
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

int test_bignum_tolebytes_p521(void)
{ uint64_t t;
  printf("Testing bignum_tolebytes_p521 with %d cases\n",tests);
  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(9,b0);
     reference_tolebytes(66,(uint8_t *)b3,9,b0);
     bignum_tolebytes_p521((uint8_t *)b4,b0);
     c = reference_compare(9,b3,9,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "bignum_tolebytes_p521(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[8],b0[0],b4[8],b4[0],b3[8],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] bignum_tolebytes_p521(0x%016"PRIx64"...%016"PRIx64") = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(9),b0[8],b0[0],b4[8],b4[0]);
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

int test_bignum_tomont_p384_alt(void)
{ uint64_t t;
  printf("Testing bignum_tomont_p384_alt with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(6,b0);
     reference_modpowtwo(6,b1,384,p_384);
     reference_mul(12,b2,6,b1,6,b0);
     reference_copy(12,b1,6,p_384);
     reference_mod(12,b3,b2,b1);
     bignum_tomont_p384_alt(b4,b0);

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

int test_bignum_tomont_sm2(void)
{ uint64_t t;
  printf("Testing bignum_tomont_sm2 with %d cases\n",tests);

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);
     reference_modpowtwo(4,b1,256,p_sm2);
     reference_mul(8,b2,4,b1,4,b0);
     reference_copy(8,b1,4,p_sm2);
     reference_mod(8,b3,b2,b1);
     bignum_tomont_sm2(b4,b0);

     c = reference_compare(4,b3,4,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64" not 0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0],b3[3],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2^256 * ...0x%016"PRIx64" mod p_sm2 = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               UINT64_C(4),b0[0],b4[3],b4[0]);
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

int test_bignum_triple_p384_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_p384_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 6;
     random_bignum(k,b0);
     bignum_triple_p384_alt(b2,b0);
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

int test_bignum_triple_p521_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_p521_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 9;
     random_bignum(k,b2); reference_mod(k,b0,b2,p_521);
     bignum_triple_p521_alt(b2,b0);
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

int test_bignum_triple_sm2(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_sm2 with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_triple_sm2(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_sm2);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_sm2[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_sm2[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_bignum_triple_sm2_alt(void)
{ uint64_t i, k;
  printf("Testing bignum_triple_sm2_alt with %d cases\n",tests);
  uint64_t c;
  for (i = 0; i < tests; ++i)
   { k = 4;
     random_bignum(k,b0);
     bignum_triple_sm2_alt(b2,b0);
     reference_copy(k+1,b3,k,b0);
     reference_copy(k+1,b4,k,b0);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_add_samelen(k+1,b4,b4,b3);
     reference_copy(k+1,b3,k,p_sm2);
     reference_mod(k+1,b5,b4,b3);
     reference_copy(k,b3,k+1,b5);

     c = reference_compare(k,b3,k,b2);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
               "...0x%016"PRIx64" not ...0x%016"PRIx64"\n",
               k,b0[0],p_sm2[0],b2[0],b3[0]);
        return 1;
      }
     else if (VERBOSE)
      { if (k == 0) printf("OK: [size %4"PRIu64"]\n",k);
        else printf("OK: [size %4"PRIu64"] "
                    "...0x%016"PRIx64" * 3 mod ....0x%016"PRIx64" = "
                    "...0x%016"PRIx64"\n",
                    k,b0[0],p_sm2[0],b2[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_ladderstep(void)
{ uint64_t t, k, b;
  printf("Testing curve25519_ladderstep with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+3*k,b0,p_25519);
     b = (rand() & 1) ? rand() : 0;
     curve25519_ladderstep(b3,b1,b2,b);
     reference_curve25519ladderstep(b4,b1,b2,b);

     c = reference_compare(4*k,b3,4*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "step_%d [...0x%016"PRIx64"] (<...0x%016"PRIx64">,<...0x%016"PRIx64">) = "
               "(<...0x%016"PRIx64">,<...0x%016"PRIx64">) not "
               "(<...0x%016"PRIx64">,<...0x%016"PRIx64">)\n",
               k,(b != 0),b1[0],b2[0],b2[4],b3[0],b3[4],b4[0],b4[4]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "step_%d [...0x%016"PRIx64"] (<...0x%016"PRIx64">,<...0x%016"PRIx64">) = "
               "(<...0x%016"PRIx64">,<...0x%016"PRIx64">)\n",
               k,(b != 0),b1[0],b2[0],b2[4],b3[0],b3[4]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_ladderstep_alt(void)
{ uint64_t t, k, b;
  printf("Testing curve25519_ladderstep_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+3*k,b0,p_25519);
     b = (rand() & 1) ? rand() : 0;
     curve25519_ladderstep_alt(b3,b1,b2,b);
     reference_curve25519ladderstep(b4,b1,b2,b);

     c = reference_compare(4*k,b3,4*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "step_%d [...0x%016"PRIx64"] (<...0x%016"PRIx64">,<...0x%016"PRIx64">) = "
               "(<...0x%016"PRIx64">,<...0x%016"PRIx64">) not "
               "(<...0x%016"PRIx64">,<...0x%016"PRIx64">)\n",
               k,(b != 0),b1[0],b2[0],b2[4],b3[0],b3[4],b4[0],b4[4]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "step_%d [...0x%016"PRIx64"] (<...0x%016"PRIx64">,<...0x%016"PRIx64">) = "
               "(<...0x%016"PRIx64">,<...0x%016"PRIx64">)\n",
               k,(b != 0),b1[0],b2[0],b2[4],b3[0],b3[4]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_pxscalarmul(void)
{ uint64_t t, k;
  printf("Testing curve25519_pxscalarmul with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_25519);
     curve25519_pxscalarmul(b3,b1,b2);
     reference_curve25519pxscalarmul(b4,b1,b2);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[4],b4[0],b4[4]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[4]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_pxscalarmul_alt(void)
{ uint64_t t, k;
  printf("Testing curve25519_pxscalarmul_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_25519);
     curve25519_pxscalarmul_alt(b3,b1,b2);
     reference_curve25519pxscalarmul(b4,b1,b2);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[4],b4[0],b4[4]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[4]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519 with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b2);
     random_bignum(k,b1);

     // With non-trivial probability, let X be in the cofactor 8-group

     if ((rand() & 15) == 0)
      { b2[3] = UINT64_C(0x57119fd0dd4e22d8);
        b2[2] = UINT64_C(0x868e1c58c45c4404);
        b2[1] = UINT64_C(0x5bef839c55b1d0b1);
        b2[0] = UINT64_C(0x248c50a3bc959c5f);
      }

     curve25519_x25519(b3,b1,b2);
     reference_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519_alt(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b2);
     random_bignum(k,b1);

     // With non-trivial probability, let X be in the cofactor 8-group

     if ((rand() & 15) == 0)
      { b2[3] = UINT64_C(0x57119fd0dd4e22d8);
        b2[2] = UINT64_C(0x868e1c58c45c4404);
        b2[1] = UINT64_C(0x5bef839c55b1d0b1);
        b2[0] = UINT64_C(0x248c50a3bc959c5f);
      }

     curve25519_x25519_alt(b3,b1,b2);
     reference_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519_byte(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519_byte with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b2);
     random_bignum(k,b1);

     // With non-trivial probability, let X be in the cofactor 8-group

     if ((rand() & 15) == 0)
      { b2[3] = UINT64_C(0x57119fd0dd4e22d8);
        b2[2] = UINT64_C(0x868e1c58c45c4404);
        b2[1] = UINT64_C(0x5bef839c55b1d0b1);
        b2[0] = UINT64_C(0x248c50a3bc959c5f);
      }

     reference_tolebytes(32,bb1,4,b1);
     reference_tolebytes(32,bb2,4,b2);
     curve25519_x25519_byte(bb3,bb1,bb2);
     reference_fromlebytes(4,b3,32,bb3);
     reference_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519_byte_alt(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519_byte_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b2);
     random_bignum(k,b1);

     // With non-trivial probability, let X be in the cofactor 8-group

     if ((rand() & 15) == 0)
      { b2[3] = UINT64_C(0x57119fd0dd4e22d8);
        b2[2] = UINT64_C(0x868e1c58c45c4404);
        b2[1] = UINT64_C(0x5bef839c55b1d0b1);
        b2[0] = UINT64_C(0x248c50a3bc959c5f);
      }

     reference_tolebytes(32,bb1,4,b1);
     reference_tolebytes(32,bb2,4,b2);
     curve25519_x25519_byte_alt(bb3,bb1,bb2);
     reference_fromlebytes(4,b3,32,bb3);
     reference_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519base(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519base with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     reference_of_word(k,b2,UINT64_C(9));

     curve25519_x25519base(b3,b1);
     reference_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519base_alt(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519base_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     reference_of_word(k,b2,UINT64_C(9));

     curve25519_x25519base_alt(b3,b1);
     reference_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519base_byte(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519base_byte with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     reference_of_word(k,b2,UINT64_C(9));

     reference_tolebytes(32,bb1,4,b1);
     curve25519_x25519base_byte(bb3,bb1);
     reference_fromlebytes(4,b3,32,bb3);
     reference_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519base_byte_alt(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519base_byte_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     reference_of_word(k,b2,UINT64_C(9));

     reference_tolebytes(32,bb1,4,b1);
     curve25519_x25519base_byte_alt(bb3,bb1);
     reference_fromlebytes(4,b3,32,bb3);
     reference_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_decode(void)
{ uint64_t t, k;
  printf("Testing edwards25519_decode with %d cases\n",tests);
  k = 4;

  uint64_t b, b_ref;
  int c, d;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);

     b = edwards25519_decode(b1,(uint8_t*)b0);
     b_ref = reference_edwards25519decode(b3,(uint8_t*)b0);

     if (b != b_ref)
      { printf("Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" should be %s but isn't\n",
               k,b0[3],b0[0],
               (b_ref ? "invalid" : "valid"));

        return 1;
      }

     reference_edwards25519encode((uint8_t*)b2,b1);
     c = reference_compare(k,b2,k,b0);
     d = reference_compare(2*k,b3,2*k,b1);

     if ((b == 0) && (c != 0))
      { printf("### Disparity: [size %4"PRIu64"] "
               "encode <...0x%016"PRIx64",...%016"PRIx64"> = "
               "0x%016"PRIx64"...%016"PRIx64", input = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,b1[0],b1[4],b2[3],b2[0],b0[3],b0[0]);
        return 1;
      }

     if ((b == 0) && (d != 0))
      { printf("### Disparity: [size %4"PRIu64"] "
               "decode 0x%016"PRIx64"...%016"PRIx64" = "
              "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
              "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
              k,b0[3],b0[0],b1[0],b1[4],b3[0],b3[4]);
        return 1;
      }

     else if (VERBOSE && (b != 0))
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64
               " is correctly flagged as invalid\n",
               k,b0[3],b0[0]);
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
              "encode <...0x%016"PRIx64",...%016"PRIx64"> = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,b1[0],b1[4],b0[3],b0[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_decode_alt(void)
{ uint64_t t, k;
  printf("Testing edwards25519_decode_alt with %d cases\n",tests);
  k = 4;

  uint64_t b, b_ref;
  int c, d;
  for (t = 0; t < tests; ++t)
   { random_bignum(4,b0);

     b = edwards25519_decode_alt(b1,(uint8_t*)b0);
     b_ref = reference_edwards25519decode(b3,(uint8_t*)b0);

     if (b != b_ref)
      { printf("Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" should be %s but isn't\n",
               k,b0[3],b0[0],
               (b_ref ? "invalid" : "valid"));

        return 1;
      }

     reference_edwards25519encode((uint8_t*)b2,b1);
     c = reference_compare(k,b2,k,b0);
     d = reference_compare(2*k,b3,2*k,b1);

     if ((b == 0) && (c != 0))
      { printf("### Disparity: [size %4"PRIu64"] "
               "encode <...0x%016"PRIx64",...%016"PRIx64"> = "
               "0x%016"PRIx64"...%016"PRIx64", input = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,b1[0],b1[4],b2[3],b2[0],b0[3],b0[0]);
        return 1;
      }

     if ((b == 0) && (d != 0))
      { printf("### Disparity: [size %4"PRIu64"] "
               "decode 0x%016"PRIx64"...%016"PRIx64" = "
              "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
              "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
              k,b0[3],b0[0],b1[0],b1[4],b3[0],b3[4]);
        return 1;
      }

     else if (VERBOSE && (b != 0))
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64
               " is correctly flagged as invalid\n",
               k,b0[3],b0[0]);
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
              "encode <...0x%016"PRIx64",...%016"PRIx64"> = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,b1[0],b1[4],b0[3],b0[0]);
      }
   }
  printf("All OK\n");
  return 0;
}


int test_edwards25519_encode(void)
{ uint64_t t, k;
  printf("Testing edwards25519_encode with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(2*k,b1);
     b1[3] &= UINT64_C(0x7FFFFFFFFFFFFFFF);
     b1[7] &= UINT64_C(0x7FFFFFFFFFFFFFFF);

     edwards25519_encode((uint8_t*)b3,b1);
     reference_edwards25519encode((uint8_t*)b4,b1);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "encode <...0x%016"PRIx64",...%016"PRIx64"> = "
               "0x%016"PRIx64"...%016"PRIx64" not "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,b1[0],b1[4],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
              "encode <...0x%016"PRIx64",...%016"PRIx64"> = "
               "0x%016"PRIx64"...%016"PRIx64"\n",
               k,b1[0],b1[4],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}


int test_edwards25519_epadd(void)
{ uint64_t t, k;
  printf("Testing edwards25519_epadd with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+3*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+3*k,b0,p_25519);
     edwards25519_epadd(b3,b1,b2);
     reference_edwards25519epadd(b4,b1,b2);

     c = reference_compare(4*k,b3,4*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_epadd_alt(void)
{ uint64_t t, k;
  printf("Testing edwards25519_epadd_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+3*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+3*k,b0,p_25519);
     edwards25519_epadd_alt(b3,b1,b2);
     reference_edwards25519epadd(b4,b1,b2);

     c = reference_compare(4*k,b3,4*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_epdouble(void)
{ uint64_t t, k;
  printf("Testing edwards25519_epdouble with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_25519);
     edwards25519_epdouble(b3,b1);
     reference_edwards25519epdouble(b4,b1);

     c = reference_compare(4*k,b3,4*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_epdouble_alt(void)
{ uint64_t t, k;
  printf("Testing edwards25519_epdouble_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_25519);
     edwards25519_epdouble_alt(b3,b1);
     reference_edwards25519epdouble(b4,b1);

     c = reference_compare(4*k,b3,4*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_pdouble(void)
{ uint64_t t, k;
  printf("Testing edwards25519_pdouble with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_25519);
     edwards25519_pdouble(b3,b1);
     reference_edwards25519pdouble(b4,b1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_pdouble_alt(void)
{ uint64_t t, k;
  printf("Testing edwards25519_pdouble_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_25519);
     edwards25519_pdouble_alt(b3,b1);
     reference_edwards25519pdouble(b4,b1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_pepadd(void)
{ uint64_t t, k;
  printf("Testing edwards25519_pepadd with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+3*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_25519);
     edwards25519_pepadd(b3,b1,b2);
     reference_edwards25519pepadd(b4,b1,b2);

     c = reference_compare(4*k,b3,4*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_pepadd_alt(void)
{ uint64_t t, k;
  printf("Testing edwards25519_pepadd_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b1+3*k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_25519);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_25519);
     edwards25519_pepadd_alt(b3,b1,b2);
     reference_edwards25519pepadd(b4,b1,b2);

     c = reference_compare(4*k,b3,4*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_scalarmulbase(void)
{ uint64_t t, k;
  printf("Testing edwards25519_scalarmulbase with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);

     // With non-zero probability exercise values near multiples of
     // the basepoint element order

     if ((rand() & 0xF) == 0)
      { bignum_cmul(4,b1,(rand() & 0xF),4,n_25519);
        if ((rand() & 0x3) == 0) b1[0] += (rand() & 0x3);
      }

     // With non-zero probability exercise close to top
     // word of the basepoint order 2^252

     if ((rand() & 0x3F) == 0)
      { b1[3] = UINT64_C(0x1000000000000000) * rand();
        b1[2] = random64d(6);
        b1[1] = random64();
        b1[0] = random64();
      }

     edwards25519_scalarmulbase(b3,b1);
     reference_edwards25519scalarmulbase(b4,b1);

     c = reference_compare(8,b3,8,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],g_edwards25519[3],g_edwards25519[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],g_edwards25519[3],g_edwards25519[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_scalarmulbase_alt(void)
{ uint64_t t, k;
  printf("Testing edwards25519_scalarmulbase_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);

     // With non-zero probability exercise values near multiples of
     // the basepoint element order

     if ((rand() & 0xF) == 0)
      { bignum_cmul(4,b1,(rand() & 0xF),4,n_25519);
        if ((rand() & 0x3) == 0) b1[0] += (rand() & 0x3);
      }

     // With non-zero probability exercise close to top
     // word of the basepoint order 2^252

     if ((rand() & 0x3F) == 0)
      { b1[3] = UINT64_C(0x1000000000000000) * rand();
        b1[2] = random64d(6);
        b1[1] = random64();
        b1[0] = random64();
      }

     edwards25519_scalarmulbase_alt(b3,b1);
     reference_edwards25519scalarmulbase(b4,b1);

     c = reference_compare(8,b3,8,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],g_edwards25519[3],g_edwards25519[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],g_edwards25519[3],g_edwards25519[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_scalarmuldouble(void)
{ uint64_t t, k;
  printf("Testing edwards25519_scalarmuldouble with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   {
     random_bignum(k,b0);
     random_bignum(k,b3); reference_edwards25519scalarmulbase(b1,b3);
     random_bignum(k,b2);

     edwards25519_scalarmuldouble(b3,b0,b1,b2);
     reference_edwards25519scalarmuldouble(b4,b0,b1,b2);

     c = reference_compare(8,b3,8,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> + "
               "0x%016"PRIx64"...%016"PRIx64" * base = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b0[3],b0[0],b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> + ... * ... = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b0[3],b0[0],b1[3],b1[0],b3[3],b3[0]);
     }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_scalarmuldouble_alt(void)
{ uint64_t t, k;
  printf("Testing edwards25519_scalarmuldouble_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   {
     random_bignum(k,b0);
     random_bignum(k,b3); reference_edwards25519scalarmulbase(b1,b3);
     random_bignum(k,b2);

     edwards25519_scalarmuldouble_alt(b3,b0,b1,b2);
     reference_edwards25519scalarmuldouble(b4,b0,b1,b2);

     c = reference_compare(8,b3,8,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> + "
               "0x%016"PRIx64"...%016"PRIx64" * base = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b0[3],b0[0],b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> + ... * ... = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b0[3],b0[0],b1[3],b1[0],b3[3],b3[0]);
     }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_montjadd(void)
{ uint64_t t, k;
  printf("Testing p256_montjadd with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_256);

     p256_montjadd(b3,b1,b2);
     reference_montjadd(k,b4,b1,b2,p_256);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_montjadd_alt(void)
{ uint64_t t, k;
  printf("Testing p256_montjadd_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_256);

     p256_montjadd_alt(b3,b1,b2);
     reference_montjadd(k,b4,b1,b2,p_256);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_montjdouble(void)
{ uint64_t t, k;
  printf("Testing p256_montjdouble with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256);

     reference_montjdouble(k,b4,b1,a_256,p_256);
     p256_montjdouble(b3,b1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_montjdouble_alt(void)
{ uint64_t t, k;
  printf("Testing p256_montjdouble_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256);

     reference_montjdouble(k,b4,b1,a_256,p_256);
     p256_montjdouble_alt(b3,b1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_montjmixadd(void)
{ uint64_t t, k;
  printf("Testing p256_montjmixadd with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_256);
     p256_montjmixadd(b3,b1,b2);
     reference_montjmixadd(k,b4,b1,b2,p_256);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_montjmixadd_alt(void)
{ uint64_t t, k;
  printf("Testing p256_montjmixadd_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_256);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_256);
     p256_montjmixadd_alt(b3,b1,b2);
     reference_montjmixadd(k,b4,b1,b2,p_256);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_montjscalarmul(void)
{ uint64_t t, k;
  printf("Testing p256_montjscalarmul with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);

     // Select an affine point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.

     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p256,p_256,n_256,a_256);

     // Map (x,y) into Montgomery form (x',y')
     bignum_tomont_p256(b2,b2);
     bignum_tomont_p256(b2+k,b2+k);

     // Pick a nonzero z coordinate and scale things, except if
     // z = 0, in which case randomize x and y as well. This is
     // a representation of the point at infinity (group identity).

     random_bignum(k,b0);
     reference_mod(k,b2+2*k,b0,p_256);
     if (bignum_iszero(k,b2+2*k))
      { random_bignum(k,b2);
        random_bignum(k,b2+k);
      }
     else
      { bignum_montsqr_p256_alt(b0,b2+2*k);
        bignum_montmul_p256_alt(b2,b2,b0);
        bignum_montmul_p256_alt(b0,b0,b2+2*k);
        bignum_montmul_p256_alt(b2+k,b2+k,b0);
      }

     p256_montjscalarmul(b5,b1,b2);
     reference_to_affine(k,b3,b5,p_256);

     reference_montjscalarmul(k,b5,b1,b2,p_256,n_256,a_256);
     reference_to_affine(k,b4,b5,p_256);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k],b4[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_montjscalarmul_alt(void)
{ uint64_t t, k;
  printf("Testing p256_montjscalarmul_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);

     // Select an affine point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.

     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p256,p_256,n_256,a_256);

     // Map (x,y) into Montgomery form (x',y')
     bignum_tomont_p256(b2,b2);
     bignum_tomont_p256(b2+k,b2+k);

     // Pick a nonzero z coordinate and scale things, except if
     // z = 0, in which case randomize x and y as well. This is
     // a representation of the point at infinity (group identity).

     random_bignum(k,b0);
     reference_mod(k,b2+2*k,b0,p_256);
     if (bignum_iszero(k,b2+2*k))
      { random_bignum(k,b2);
        random_bignum(k,b2+k);
      }
     else
      { bignum_montsqr_p256_alt(b0,b2+2*k);
        bignum_montmul_p256_alt(b2,b2,b0);
        bignum_montmul_p256_alt(b0,b0,b2+2*k);
        bignum_montmul_p256_alt(b2+k,b2+k,b0);
      }

     p256_montjscalarmul_alt(b5,b1,b2);
     reference_to_affine(k,b3,b5,p_256);

     reference_montjscalarmul(k,b5,b1,b2,p_256,n_256,a_256);
     reference_to_affine(k,b4,b5,p_256);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k],b4[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_scalarmul(void)
{ uint64_t t, k;
  printf("Testing p256_scalarmul with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     // Select a point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.
     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p256,p_256,n_256,a_256);

     p256_scalarmul(b3,b1,b2);
     reference_scalarmul(k,b4,b1,b2,p_256,n_256,a_256);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[4],b4[0],b4[4]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[4]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_scalarmul_alt(void)
{ uint64_t t, k;
  printf("Testing p256_scalarmul_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     // Select a point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.
     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p256,p_256,n_256,a_256);

     p256_scalarmul_alt(b3,b1,b2);
     reference_scalarmul(k,b4,b1,b2,p_256,n_256,a_256);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[4],b4[0],b4[4]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[4]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_scalarmulbase(void)
{ uint64_t t, k, b;
  printf("Testing p256_scalarmulbase with %d cases\n",tests);
  k = 4;
  int c;
  for (t = 0; t < tests; ++t)
   { b = 2 + (rand() & 0x7);            // Block sizes from 2 to 9
     uint64_t *tab = malloc(8 * (2 * k) * (1<<(b-1)) * (((64 * k) / b) + 1));

     // Generate the random scalar
     random_bignum(k,b1);

     // Select a point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.
     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p256,p_256,n_256,a_256);

     // Now generate the precomputed table
     reference_multable(k,tab,b,b2,p_256,a_256);

     // Now actually call the function using that table

     p256_scalarmulbase(b3,b1,b,tab);
     reference_scalarmul(k,b4,b1,b2,p_256,n_256,a_256);

     // Free the table, which is no longer needed this iteration

     free(tab);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64", block size %4"PRIu64"] "
               "...0x%016"PRIx64" * <...0x%016"PRIx64",-> = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b,b1[0],b2[0],b3[0],b3[4],b4[0],b4[4]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64", block size %4"PRIu64"] "
               "...0x%016"PRIx64", * <...0x%016"PRIx64",-> = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b,b1[0],b2[0],b3[0],b3[4]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p256_scalarmulbase_alt(void)
{ uint64_t t, k, b;
  printf("Testing p256_scalarmulbase_alt with %d cases\n",tests);
  k = 4;
  int c;
  for (t = 0; t < tests; ++t)
   { b = 2 + (rand() & 0x7);            // Block sizes from 2 to 9
     uint64_t *tab = malloc(8 * (2 * k) * (1<<(b-1)) * (((64 * k) / b) + 1));

     // Generate the random scalar
     random_bignum(k,b1);

     // Select a point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.
     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p256,p_256,n_256,a_256);

     // Now generate the precomputed table
     reference_multable(k,tab,b,b2,p_256,a_256);

     // Now actually call the function using that table

     p256_scalarmulbase_alt(b3,b1,b,tab);
     reference_scalarmul(k,b4,b1,b2,p_256,n_256,a_256);

     // Free the table, which is no longer needed this iteration

     free(tab);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64", block size %4"PRIu64"] "
               "...0x%016"PRIx64" * <...0x%016"PRIx64",-> = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b,b1[0],b2[0],b3[0],b3[4],b4[0],b4[4]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64", block size %4"PRIu64"] "
               "...0x%016"PRIx64", * <...0x%016"PRIx64",-> = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b,b1[0],b2[0],b3[0],b3[4]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p384_montjadd(void)
{ uint64_t t, k;
  printf("Testing p384_montjadd with %d cases\n",tests);
  k = 6;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_384);

     p384_montjadd(b3,b1,b2);
     reference_montjadd(k,b4,b1,b2,p_384);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p384_montjadd_alt(void)
{ uint64_t t, k;
  printf("Testing p384_montjadd_alt with %d cases\n",tests);
  k = 6;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_384);

     p384_montjadd_alt(b3,b1,b2);
     reference_montjadd(k,b4,b1,b2,p_384);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p384_montjdouble(void)
{ uint64_t t, k;
  printf("Testing p384_montjdouble with %d cases\n",tests);
  k = 6;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_384);

     reference_montjdouble(k,b4,b1,a_384,p_384);
     p384_montjdouble(b3,b1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p384_montjdouble_alt(void)
{ uint64_t t, k;
  printf("Testing p384_montjdouble_alt with %d cases\n",tests);
  k = 6;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_384);

     reference_montjdouble(k,b4,b1,a_384,p_384);
     p384_montjdouble_alt(b3,b1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p384_montjmixadd(void)
{ uint64_t t, k;
  printf("Testing p384_montjmixadd with %d cases\n",tests);
  k = 6;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_384);
     p384_montjmixadd(b3,b1,b2);
     reference_montjmixadd(k,b4,b1,b2,p_384);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p384_montjmixadd_alt(void)
{ uint64_t t, k;
  printf("Testing p384_montjmixadd_alt with %d cases\n",tests);
  k = 6;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_384);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_384);
     p384_montjmixadd_alt(b3,b1,b2);
     reference_montjmixadd(k,b4,b1,b2,p_384);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p384_montjscalarmul(void)
{ uint64_t t, k;
  printf("Testing p384_montjscalarmul with %d cases\n",tests);
  k = 6;

  int c;
  for (t = 0; t < tests; ++t)
   {
     // With reasonable probability try scalars near the group order
     // and its negation

     random_bignum(k,b1);
     if ((rand() & 31) < 2)
      { bignum_copy(k,b1,k,n_384);
        if (rand() & 1)
          b1[0] += ((rand() & 1) ? random64d(5) : rand() & 63);
        else
          b1[0] -= ((rand() & 1) ? random64d(5) : rand() & 63);
        if (rand() & 1) bignum_sub(k,b1,0,NULL,k,b1);
      }

     // Select an affine point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.

     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p384,p_384,n_384,a_384);

     // Map (x,y) into Montgomery form (x',y')
     bignum_tomont_p384(b2,b2);
     bignum_tomont_p384(b2+k,b2+k);

     // Pick a nonzero z coordinate and scale things, except if
     // z = 0, in which case randomize x and y as well. This is
     // a representation of the point at infinity (group identity).

     random_bignum(k,b0);
     reference_mod(k,b2+2*k,b0,p_384);
     if (bignum_iszero(k,b2+2*k))
      { random_bignum(k,b2);
        random_bignum(k,b2+k);
      }
     else
      { bignum_montsqr_p384_alt(b0,b2+2*k);
        bignum_montmul_p384_alt(b2,b2,b0);
        bignum_montmul_p384_alt(b0,b0,b2+2*k);
        bignum_montmul_p384_alt(b2+k,b2+k,b0);
      }

     p384_montjscalarmul(b5,b1,b2);
     reference_to_affine(k,b3,b5,p_384);

     reference_montjscalarmul(k,b5,b1,b2,p_384,n_384,a_384);
     reference_to_affine(k,b4,b5,p_384);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k],b4[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p384_montjscalarmul_alt(void)
{ uint64_t t, k;
  printf("Testing p384_montjscalarmul_alt with %d cases\n",tests);
  k = 6;

  int c;
  for (t = 0; t < tests; ++t)
   {
     // With reasonable probability try scalars near the group order
     // and its negation

     random_bignum(k,b1);
     if ((rand() & 31) < 2)
      { bignum_copy(k,b1,k,n_384);
        if (rand() & 1)
          b1[0] += ((rand() & 1) ? random64d(5) : rand() & 63);
        else
          b1[0] -= ((rand() & 1) ? random64d(5) : rand() & 63);
        if (rand() & 1) bignum_sub(k,b1,0,NULL,k,b1);
      }

     // Select an affine point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.

     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p384,p_384,n_384,a_384);

     // Map (x,y) into Montgomery form (x',y')
     bignum_tomont_p384(b2,b2);
     bignum_tomont_p384(b2+k,b2+k);

     // Pick a nonzero z coordinate and scale things, except if
     // z = 0, in which case randomize x and y as well. This is
     // a representation of the point at infinity (group identity).

     random_bignum(k,b0);
     reference_mod(k,b2+2*k,b0,p_384);
     if (bignum_iszero(k,b2+2*k))
      { random_bignum(k,b2);
        random_bignum(k,b2+k);
      }
     else
      { bignum_montsqr_p384_alt(b0,b2+2*k);
        bignum_montmul_p384_alt(b2,b2,b0);
        bignum_montmul_p384_alt(b0,b0,b2+2*k);
        bignum_montmul_p384_alt(b2+k,b2+k,b0);
      }

     p384_montjscalarmul_alt(b5,b1,b2);
     reference_to_affine(k,b3,b5,p_384);

     reference_montjscalarmul(k,b5,b1,b2,p_384,n_384,a_384);
     reference_to_affine(k,b4,b5,p_384);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k],b4[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p521_jadd(void)
{ uint64_t t, k;
  printf("Testing p521_jadd with %d cases\n",tests);
  k = 9;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_521);

     p521_jadd(b3,b1,b2);
     reference_jadd(k,b4,b1,b2,p_521);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p521_jadd_alt(void)
{ uint64_t t, k;
  printf("Testing p521_jadd_alt with %d cases\n",tests);
  k = 9;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_521);

     p521_jadd_alt(b3,b1,b2);
     reference_jadd(k,b4,b1,b2,p_521);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p521_jdouble(void)
{ uint64_t t, k;
  printf("Testing p521_jdouble with %d cases\n",tests);
  k = 9;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_521);

     p521_jdouble(b3,b1);
     reference_jdouble(k,b4,b1,aa_521,p_521);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p521_jdouble_alt(void)
{ uint64_t t, k;
  printf("Testing p521_jdouble_alt with %d cases\n",tests);
  k = 9;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_521);

     p521_jdouble_alt(b3,b1);
     reference_jdouble(k,b4,b1,aa_521,p_521);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p521_jmixadd(void)
{ uint64_t t, k;
  printf("Testing p521_jmixadd with %d cases\n",tests);
  k = 9;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_521);
     p521_jmixadd(b3,b1,b2);
     reference_jmixadd(k,b4,b1,b2,p_521);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p521_jmixadd_alt(void)
{ uint64_t t, k;
  printf("Testing p521_jmixadd_alt with %d cases\n",tests);
  k = 9;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_521);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_521);
     p521_jmixadd_alt(b3,b1,b2);
     reference_jmixadd(k,b4,b1,b2,p_521);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p521_jscalarmul(void)
{ uint64_t t, k;
  printf("Testing p521_jscalarmul with %d cases\n",tests);
  k = 9;

  int c;
  for (t = 0; t < tests; ++t)
   {
     // With reasonable probability try scalars near the group order
     // and its negation

     random_bignum(k,b1);
     if ((rand() & 31) < 2)
      { bignum_copy(k,b1,k,n_521);
        if (rand() & 1)
          b1[0] += ((rand() & 1) ? random64d(5) : rand() & 63);
        else
          b1[0] -= ((rand() & 1) ? random64d(5) : rand() & 63);
        if (rand() & 1)
         { bignum_pow2(k,b2,521);
           bignum_sub(k,b1,k,b2,k,b1);
         }
      }

     // Select an affine point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.

     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p521,p_521,n_521,a_521);

     // Pick a nonzero z coordinate and scale things, except if
     // z = 0, in which case randomize x and y as well. This is
     // a representation of the point at infinity (group identity).

     random_bignum(k,b0);
     reference_mod(k,b2+2*k,b0,p_521);
     if (bignum_iszero(k,b2+2*k))
      { random_bignum(k,b2);
        random_bignum(k,b2+k);
      }
     else
      { bignum_sqr_p521_alt(b0,b2+2*k);
        bignum_mul_p521_alt(b2,b2,b0);
        bignum_mul_p521_alt(b0,b0,b2+2*k);
        bignum_mul_p521_alt(b2+k,b2+k,b0);
      }

     p521_jscalarmul(b5,b1,b2);
     bignum_tomont_p521(b5,b5);
     bignum_tomont_p521(b5+k,b5+k);
     bignum_tomont_p521(b5+2*k,b5+2*k);
     reference_to_affine(k,b3,b5,p_521);

     reference_jscalarmul(k,b6,b1,b2,p_521,n_521,aa_521);
     bignum_tomont_p521(b6,b6);
     bignum_tomont_p521(b6+k,b6+k);
     bignum_tomont_p521(b6+2*k,b6+2*k);
     reference_to_affine(k,b4,b6,p_521);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k],b4[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_p521_jscalarmul_alt(void)
{ uint64_t t, k;
  printf("Testing p521_jscalarmul_alt with %d cases\n",tests);
  k = 9;

  int c;
  for (t = 0; t < tests; ++t)
   {
     // With reasonable probability try scalars near the group order
     // and its negation

     random_bignum(k,b1);
     if ((rand() & 31) < 2)
      { bignum_copy(k,b1,k,n_521);
        if (rand() & 1)
          b1[0] += ((rand() & 1) ? random64d(5) : rand() & 63);
        else
          b1[0] -= ((rand() & 1) ? random64d(5) : rand() & 63);
        if (rand() & 1)
         { bignum_pow2(k,b2,521);
           bignum_sub(k,b1,k,b2,k,b1);
         }
      }

     // Select an affine point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.

     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_p521,p_521,n_521,a_521);

     // Pick a nonzero z coordinate and scale things, except if
     // z = 0, in which case randomize x and y as well. This is
     // a representation of the point at infinity (group identity).

     random_bignum(k,b0);
     reference_mod(k,b2+2*k,b0,p_521);
     if (bignum_iszero(k,b2+2*k))
      { random_bignum(k,b2);
        random_bignum(k,b2+k);
      }
     else
      { bignum_sqr_p521_alt(b0,b2+2*k);
        bignum_mul_p521_alt(b2,b2,b0);
        bignum_mul_p521_alt(b0,b0,b2+2*k);
        bignum_mul_p521_alt(b2+k,b2+k,b0);
      }

     p521_jscalarmul_alt(b5,b1,b2);
     bignum_tomont_p521(b5,b5);
     bignum_tomont_p521(b5+k,b5+k);
     bignum_tomont_p521(b5+2*k,b5+2*k);
     reference_to_affine(k,b3,b5,p_521);

     reference_jscalarmul(k,b6,b1,b2,p_521,n_521,aa_521);
     bignum_tomont_p521(b6,b6);
     bignum_tomont_p521(b6+k,b6+k);
     bignum_tomont_p521(b6+2*k,b6+2*k);
     reference_to_affine(k,b4,b6,p_521);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k],b4[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k]);
      }
   }
  printf("All OK\n");
  return 0;
}


int test_secp256k1_jadd(void)
{ uint64_t t, k;
  printf("Testing secp256k1_jadd with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_256k1);

     secp256k1_jadd(b3,b1,b2);
     reference_jadd(k,b4,b1,b2,p_256k1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_secp256k1_jadd_alt(void)
{ uint64_t t, k;
  printf("Testing secp256k1_jadd_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_256k1);

     secp256k1_jadd_alt(b3,b1,b2);
     reference_jadd(k,b4,b1,b2,p_256k1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_secp256k1_jdouble(void)
{ uint64_t t, k;
  printf("Testing secp256k1_jdouble with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256k1);
     bignum_of_word(k,b2,0);

     secp256k1_jdouble(b3,b1);
     reference_jdouble(k,b4,b1,b2,p_256k1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_secp256k1_jdouble_alt(void)
{ uint64_t t, k;
  printf("Testing secp256k1_jdouble_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256k1);
     bignum_of_word(k,b2,0);

     secp256k1_jdouble_alt(b3,b1);
     reference_jdouble(k,b4,b1,b2,p_256k1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_secp256k1_jmixadd(void)
{ uint64_t t, k;
  printf("Testing secp256k1_jmixadd with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_256k1);
     secp256k1_jmixadd(b3,b1,b2);
     reference_jmixadd(k,b4,b1,b2,p_256k1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_secp256k1_jmixadd_alt(void)
{ uint64_t t, k;
  printf("Testing secp256k1_jmixadd_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_256k1);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_256k1);
     secp256k1_jmixadd_alt(b3,b1,b2);
     reference_jmixadd(k,b4,b1,b2,p_256k1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_sm2_montjadd(void)
{ uint64_t t, k;
  printf("Testing sm2_montjadd with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_sm2);

     sm2_montjadd(b3,b1,b2);
     reference_montjadd(k,b4,b1,b2,p_sm2);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
              "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_sm2_montjadd_alt(void)
{ uint64_t t, k;
  printf("Testing sm2_montjadd_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2+2*k,b0,p_sm2);

     sm2_montjadd_alt(b3,b1,b2);
     reference_montjadd(k,b4,b1,b2,p_sm2);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
              "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_sm2_montjdouble(void)
{ uint64_t t, k;
  printf("Testing sm2_montjdouble with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_sm2);

     reference_montjdouble(k,b4,b1,a_sm2,p_sm2);
     sm2_montjdouble(b3,b1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_sm2_montjdouble_alt(void)
{ uint64_t t, k;
  printf("Testing sm2_montjdouble_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_sm2);

     reference_montjdouble(k,b4,b1,a_sm2,p_sm2);
     sm2_montjdouble_alt(b3,b1);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "2 * <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_sm2_montjmixadd(void)
{ uint64_t t, k;
  printf("Testing sm2_montjmixadd with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_sm2);
     sm2_montjmixadd(b3,b1,b2);
     reference_montjmixadd(k,b4,b1,b2,p_sm2);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_sm2_montjmixadd_alt(void)
{ uint64_t t, k;
  printf("Testing sm2_montjmixadd_alx with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b0); reference_mod(k,b1,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b1+2*k,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2,b0,p_sm2);
     random_bignum(k,b0); reference_mod(k,b2+k,b0,p_sm2);
     sm2_montjmixadd_alt(b3,b1,b2);
     reference_montjmixadd(k,b4,b1,b2,p_sm2);

     c = reference_compare(3*k,b3,3*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64"> not <...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64"> + <...0x%016"PRIx64"> = "
               "<...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0]);
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

int test_sm2_montjscalarmul(void)
{ uint64_t t, k;
  printf("Testing sm2_montjscalarmul with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);

     // Select an affine point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.

     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_sm2,p_sm2,n_sm2,a_sm2);

     // Map (x,y) into Montgomery form (x',y')
     bignum_tomont_sm2(b2,b2);
     bignum_tomont_sm2(b2+k,b2+k);

     // Pick a nonzero z coordinate and scale things, except if
     // z = 0, in which case randomize x and y as well. This is
     // a representation of the point at infinity (group identity).

     random_bignum(k,b0);
     reference_mod(k,b2+2*k,b0,p_sm2);
     if (bignum_iszero(k,b2+2*k))
      { random_bignum(k,b2);
        random_bignum(k,b2+k);
      }
     else
      { bignum_montsqr_sm2_alt(b0,b2+2*k);
        bignum_montmul_sm2_alt(b2,b2,b0);
        bignum_montmul_sm2_alt(b0,b0,b2+2*k);
        bignum_montmul_sm2_alt(b2+k,b2+k,b0);
      }

     sm2_montjscalarmul(b5,b1,b2);
     reference_to_affine(k,b3,b5,p_sm2);

     reference_montjscalarmul(k,b5,b1,b2,p_sm2,n_sm2,a_sm2);
     reference_to_affine(k,b4,b5,p_sm2);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k],b4[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_sm2_montjscalarmul_alt(void)
{ uint64_t t, k;
  printf("Testing sm2_montjscalarmul_alt with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);

     // Select an affine point actually on the curve to test.
     // In general it may not agree for random (x,y)
     // since algorithms often rely on points being on the curve.

     random_bignum(k,b0);
     reference_scalarmul(k,b2,b0,gen_sm2,p_sm2,n_sm2,a_sm2);

     // Map (x,y) into Montgomery form (x',y')
     bignum_tomont_sm2(b2,b2);
     bignum_tomont_sm2(b2+k,b2+k);

     // Pick a nonzero z coordinate and scale things, except if
     // z = 0, in which case randomize x and y as well. This is
     // a representation of the point at infinity (group identity).

     random_bignum(k,b0);
     reference_mod(k,b2+2*k,b0,p_sm2);
     if (bignum_iszero(k,b2+2*k))
      { random_bignum(k,b2);
        random_bignum(k,b2+k);
      }
     else
      { bignum_montsqr_sm2_alt(b0,b2+2*k);
        bignum_montmul_sm2_alt(b2,b2,b0);
        bignum_montmul_sm2_alt(b0,b0,b2+2*k);
        bignum_montmul_sm2_alt(b2+k,b2+k,b0);
      }

     sm2_montjscalarmul_alt(b5,b1,b2);
     reference_to_affine(k,b3,b5,p_sm2);

     reference_montjscalarmul(k,b5,b1,b2,p_sm2,n_sm2,a_sm2);
     reference_to_affine(k,b4,b5,p_sm2);

     c = reference_compare(2*k,b3,2*k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64"> not "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k],b4[0],b4[k]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "<...0x%016"PRIx64",-> * ...0x%016"PRIx64" = "
               "<...0x%016"PRIx64",...0x%016"PRIx64">\n",
               k,b1[0],b2[0],b3[0],b3[k]);
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

int test_word_divstep59(void)
{ uint64_t i;
  printf("Testing word_divstep59 with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { int64_t m1[2][2], m2[2][2];

     int64_t d = random64(); d &= 0xFFFFFFFFFFFFFFF; d |= 1;
     if ((rand() & 15) < 14) d &= 0xF;
     if (rand() & 1) d = -d;
     int64_t f = random64(); f |= 1;
     int64_t g = random64();

     int64_t d1 = word_divstep59(m1,d,f,g);
     int64_t d2 = reference_divstep(m2,59,d,f,g);

     if (!((d1 == d2) && (m1[0][0] == m2[0][0]) && (m1[0][1] == m2[0][1]) &&
           (m1[1][0] == m2[1][0]) && (m1[1][1] == m2[1][1])))
      { printf("### Inputs divstep59(0x%016"PRIx64",0x%016"PRIx64",0x%016"PRIx64"\n",d,f,g);
        printf("### Disparity-d: d = 0x%016"PRIx64" not 0x%016"PRIx64"\n",d1,d2);
        printf("### Disparity-m00: m1[0][0] = 0x%016"PRIx64" not 0x%016"PRIx64"\n",m1[0][0],m2[0][0]);
        printf("### Disparity-m01: m1[0][1] = 0x%016"PRIx64" not 0x%016"PRIx64"\n",m1[0][1],m2[0][1]);
        printf("### Disparity-m10: m1[1][0] = 0x%016"PRIx64" not 0x%016"PRIx64"\n",m1[1][0],m2[1][0]);
        printf("### Disparity-m11: m1[1][1] = 0x%016"PRIx64" not 0x%016"PRIx64"\n",m1[1][1],m2[1][1]);
        return 1;

      }
    else if (VERBOSE)
      { printf("### OK: m1[0][0] * f + m1[0][1] * g = 0x%016"PRIx64" * 0x%016"PRIx64" + 0x%016"PRIx64" * 0x%016"PRIx64
               " = 0x%016"PRIx64"\n",m1[0][0],f,m1[0][1],g,m1[0][0] * f + m1[0][1] * g);
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

int test_word_popcount(void)
{ uint64_t i, a, x, y;
  printf("Testing word_popcount with %d cases\n",tests);
  for (i = 0; i < tests; ++i)
   { a = random64();
     x = word_popcount(a);
     y = reference_wordpopcount(a);
     if (x != y)
      { printf("### Disparity: word_popcount(0x%016"PRIx64") = %"PRIu64" not %"PRIu64"\n",a,x,y);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: word_popcount(0x%016"PRIx64") = %"PRIu64"\n",a,x);
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

// ****************************************************************************
// Known value tests for certain operations
// ****************************************************************************

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

// ****************************************************************************
// Analogous testing of relevant functions against TweetNaCl as reference
//
// See https://tweetnacl.cr.yp.to/ for more info on TweetNaCl
// ****************************************************************************

#include "tweetnacl_excerpt.c"

void tweetnacl_curve25519x25519(uint64_t *z,uint64_t *n,uint64_t *x)
{ uint8_t *z_bytes = alloca(32), *n_bytes = alloca(32), *x_bytes = alloca(32);
  reference_tolebytes(32,x_bytes,4,x);
  reference_tolebytes(32,n_bytes,4,n);
  crypto_scalarmult(z_bytes,n_bytes,x_bytes);
  reference_fromlebytes(4,z,32,z_bytes);
}

void tweetnacl_curve25519x25519base(uint64_t *z,uint64_t *n)
{ uint8_t *z_bytes = alloca(32), *n_bytes = alloca(32);
  reference_tolebytes(32,n_bytes,4,n);
  crypto_scalarmult_base(z_bytes,n_bytes);
  reference_fromlebytes(4,z,32,z_bytes);
}

void tweetnacl_edwards25519scalarmulbase(uint64_t *z,uint64_t *n)
{ uint8_t *n_bytes = alloca(32), *x_bytes = alloca(32), *y_bytes = alloca(32);
  gf z_gf[4], x, y, zinv;
  reference_tolebytes(32,n_bytes,4,n);
  scalarbase(z_gf,n_bytes);
  inv25519(zinv,z_gf[2]);
  M(x,z_gf[0],zinv);
  M(y,z_gf[1],zinv);
  pack25519(x_bytes,x);
  pack25519(y_bytes,y);
  reference_fromlebytes(4,z,32,x_bytes);
  reference_fromlebytes(4,z+4,32,y_bytes);
}

int test_curve25519_x25519_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519 against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b2);
     random_bignum(k,b1);

     // With non-trivial probability, let X be in the cofactor 8-group

     if ((rand() & 15) == 0)
      { b2[3] = UINT64_C(0x57119fd0dd4e22d8);
        b2[2] = UINT64_C(0x868e1c58c45c4404);
        b2[1] = UINT64_C(0x5bef839c55b1d0b1);
        b2[0] = UINT64_C(0x248c50a3bc959c5f);
      }

     curve25519_x25519(b3,b1,b2);
     tweetnacl_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519_alt_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519_alt against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b2);
     random_bignum(k,b1);

     // With non-trivial probability, let X be in the cofactor 8-group

     if ((rand() & 15) == 0)
      { b2[3] = UINT64_C(0x57119fd0dd4e22d8);
        b2[2] = UINT64_C(0x868e1c58c45c4404);
        b2[1] = UINT64_C(0x5bef839c55b1d0b1);
        b2[0] = UINT64_C(0x248c50a3bc959c5f);
      }

     curve25519_x25519_alt(b3,b1,b2);
     tweetnacl_curve25519x25519(b4,b1,b2);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519base_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519base against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     reference_of_word(k,b2,UINT64_C(9));

     curve25519_x25519base(b3,b1);
     tweetnacl_curve25519x25519base(b4,b1);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519base_alt_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519base_alt against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     reference_of_word(k,b2,UINT64_C(9));

     curve25519_x25519base_alt(b3,b1);
     tweetnacl_curve25519x25519base(b4,b1);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}


int test_curve25519_x25519_byte_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519 against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b2);
     random_bignum(k,b1);

     // With non-trivial probability, let X be in the cofactor 8-group

     if ((rand() & 15) == 0)
      { b2[3] = UINT64_C(0x57119fd0dd4e22d8);
        b2[2] = UINT64_C(0x868e1c58c45c4404);
        b2[1] = UINT64_C(0x5bef839c55b1d0b1);
        b2[0] = UINT64_C(0x248c50a3bc959c5f);
      }

     reference_tolebytes(32,bb1,4,b1);
     reference_tolebytes(32,bb2,4,b2);
     curve25519_x25519_byte(bb3,bb1,bb2);
     crypto_scalarmult(bb4,bb1,bb2);
     reference_fromlebytes(4,b3,32,bb3);
     reference_fromlebytes(4,b4,32,bb4);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519_byte_alt_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519_alt against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b2);
     random_bignum(k,b1);

     // With non-trivial probability, let X be in the cofactor 8-group

     if ((rand() & 15) == 0)
      { b2[3] = UINT64_C(0x57119fd0dd4e22d8);
        b2[2] = UINT64_C(0x868e1c58c45c4404);
        b2[1] = UINT64_C(0x5bef839c55b1d0b1);
        b2[0] = UINT64_C(0x248c50a3bc959c5f);
      }

     reference_tolebytes(32,bb1,4,b1);
     reference_tolebytes(32,bb2,4,b2);
     curve25519_x25519_byte_alt(bb3,bb1,bb2);
     crypto_scalarmult(bb4,bb1,bb2);
     reference_fromlebytes(4,b3,32,bb3);
     reference_fromlebytes(4,b4,32,bb4);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519base_byte_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519base against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     reference_of_word(k,b2,UINT64_C(9));

     reference_tolebytes(32,bb1,4,b1);
     curve25519_x25519base_byte(bb3,bb1);
     crypto_scalarmult_base(bb4,bb1);
     reference_fromlebytes(4,b3,32,bb3);
     reference_fromlebytes(4,b4,32,bb4);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_curve25519_x25519base_byte_alt_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing curve25519_x25519base_alt against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);
     reference_of_word(k,b2,UINT64_C(9));

     reference_tolebytes(32,bb1,4,b1);
     curve25519_x25519base_byte_alt(bb3,bb1);
     crypto_scalarmult_base(bb4,bb1);
     reference_fromlebytes(4,b3,32,bb3);
     reference_fromlebytes(4,b4,32,bb4);

     c = reference_compare(k,b3,k,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],b2[3],b2[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_scalarmulbase_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing edwards25519_scalarmulbase against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);

     // With non-zero probability exercise values near multiples of
     // the basepoint element order

     if ((rand() & 0xF) == 0)
      { bignum_cmul(4,b1,(rand() & 0xF),4,n_25519);
        if ((rand() & 0x3) == 0) b1[0] += (rand() & 0x3);
      }

     // With non-zero probability exercise close to top
     // word of the basepoint order 2^252

     if ((rand() & 0x3F) == 0)
      { b1[3] = UINT64_C(0x1000000000000000) * rand();
        b1[2] = random64d(6);
        b1[1] = random64();
        b1[0] = random64();
      }

     edwards25519_scalarmulbase(b3,b1);
     tweetnacl_edwards25519scalarmulbase(b4,b1);

     c = reference_compare(8,b3,8,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],g_edwards25519[3],g_edwards25519[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],g_edwards25519[3],g_edwards25519[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

int test_edwards25519_scalarmulbase_alt_tweetnacl(void)
{ uint64_t t, k;
  printf("Testing edwards25519_scalarmulbase_alt against TweetNaCl with %d cases\n",tests);
  k = 4;

  int c;
  for (t = 0; t < tests; ++t)
   { random_bignum(k,b1);

     // With non-zero probability exercise values near multiples of
     // the basepoint element order

     if ((rand() & 0xF) == 0)
      { bignum_cmul(4,b1,(rand() & 0xF),4,n_25519);
        if ((rand() & 0x3) == 0) b1[0] += (rand() & 0x3);
      }

     // With non-zero probability exercise close to top
     // word of the basepoint order 2^252

     if ((rand() & 0x3F) == 0)
      { b1[3] = UINT64_C(0x1000000000000000) * rand();
        b1[2] = random64d(6);
        b1[1] = random64();
        b1[0] = random64();
      }

     edwards25519_scalarmulbase_alt(b3,b1);
     tweetnacl_edwards25519scalarmulbase(b4,b1);

     c = reference_compare(8,b3,8,b4);
     if (c != 0)
      { printf("### Disparity: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64"> not "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],g_edwards25519[3],g_edwards25519[0],b3[3],b3[0],b4[3],b4[0]);
        return 1;
      }
     else if (VERBOSE)
      { printf("OK: [size %4"PRIu64"] "
               "0x%016"PRIx64"...%016"PRIx64" * "
               "<0x%016"PRIx64"...%016"PRIx64"> = "
               "<...0x%016"PRIx64"...%016"PRIx64">\n",
               k,b1[3],b1[0],g_edwards25519[3],g_edwards25519[0],b3[3],b3[0]);
      }
   }
  printf("All OK\n");
  return 0;
}

// ****************************************************************************
// Main dispatching to appropriate test code
// ****************************************************************************

static char *function_to_test;
static int tested = 0;
static int successes = 0;
static int failures = 0;
static int skipped = 0;
static int inapplicable = 0;

// functionaltest runs f() if enabled is true and records the result.
// If the return value is nonzero, the test has failed.
void functionaltest(int enabled,char *name,int (*f)(void))
{ ++tested;
  // Only benchmark matching function name
  // Empty string matches everything, terminal _ matches everything

  char *spaceptr = strchr(name,' ');
  int compline = (spaceptr) ? spaceptr-name : strlen(name);
  int wantline = strlen(function_to_test);
  int testline = wantline;
  if (wantline == 0) testline = 0;
  else if (function_to_test[wantline-1] == '_') testline = wantline - 1;
  else if (testline < compline) testline = compline;
  if (strncmp(name,function_to_test,testline))
   { ++skipped;
     return;
   }

  // Only benchmark function using supported instructions (on x86)

  if (!enabled)
   { printf("Skipping %s because not applicable (x86 BMI/ADX support)\n",name);
     ++inapplicable;
     return;
   }

  if (f()) ++failures; else ++successes;
}

// Main function allowing various command-line options:
//
// ./test [-number_of_tests] [function]
// ./test [[+]number_of_tests] [function]
//
// the difference being that the second one also runs extra
// tests like known value tests even if not explicitly
// selected in the function list.
//
// The function can end in an underscore which is interpreted
// as a wildcard "*", e.g. "bignum_add_p_"

int main(int argc, char *argv[])
{ int bmi = get_arch_name() == ARCH_AARCH64 || supports_bmi2_and_adx();
  int all = 1;
  int extrastrigger = 1;

  char *argending;
  long negreps;
  function_to_test = "";
  tests = TESTS;

  if (argc >= 2)
   { negreps = strtol(argv[1],&argending,10);
     if (negreps <= 0) extrastrigger = 0;
     if (negreps >= 0) negreps = -negreps;
     if (argending == argv[1])
      { if (argc >= 3 || argv[1][0] == '-')
         { printf("Usage: ./test [-reps] [function_name]\n");
           printf(" e.g.: ./test -1000 bignum_add\n");
           printf("   or: ./test -25 bignum_mul_\n");
           return (-1);
         }
        else function_to_test = argv[1];
      }
     else
      { tests = -negreps;
        if (argc >= 3) function_to_test = argv[2];
      }
   }

  if (tests == 0) tests = TESTS;

  functionaltest(all,"bignum_add",test_bignum_add);
  functionaltest(all,"bignum_add_p25519",test_bignum_add_p25519);
  functionaltest(all,"bignum_add_p256",test_bignum_add_p256);
  functionaltest(all,"bignum_add_p256k1",test_bignum_add_p256k1);
  functionaltest(all,"bignum_add_p384",test_bignum_add_p384);
  functionaltest(all,"bignum_add_p521",test_bignum_add_p521);
  functionaltest(all,"bignum_add_sm2",test_bignum_add_sm2);
  functionaltest(all,"bignum_amontifier",test_bignum_amontifier);
  functionaltest(all,"bignum_amontmul",test_bignum_amontmul);
  functionaltest(all,"bignum_amontredc",test_bignum_amontredc);
  functionaltest(all,"bignum_amontsqr",test_bignum_amontsqr);
  functionaltest(all,"bignum_bigendian_4",test_bignum_bigendian_4);
  functionaltest(all,"bignum_bigendian_6",test_bignum_bigendian_6);
  functionaltest(all,"bignum_bitfield",test_bignum_bitfield);
  functionaltest(all,"bignum_bitsize",test_bignum_bitsize);
  functionaltest(all,"bignum_cdiv",test_bignum_cdiv);
  functionaltest(all,"bignum_cdiv_exact",test_bignum_cdiv_exact);
  functionaltest(all,"bignum_cld",test_bignum_cld);
  functionaltest(all,"bignum_clz",test_bignum_clz);
  functionaltest(all,"bignum_cmadd",test_bignum_cmadd);
  functionaltest(all,"bignum_cmnegadd",test_bignum_cmnegadd);
  functionaltest(all,"bignum_cmod",test_bignum_cmod);
  functionaltest(all,"bignum_cmul",test_bignum_cmul);
  functionaltest(bmi,"bignum_cmul_p25519",test_bignum_cmul_p25519);
  functionaltest(all,"bignum_cmul_p25519_alt",test_bignum_cmul_p25519_alt);
  functionaltest(bmi,"bignum_cmul_p256",test_bignum_cmul_p256);
  functionaltest(all,"bignum_cmul_p256_alt",test_bignum_cmul_p256_alt);
  functionaltest(bmi,"bignum_cmul_p256k1",test_bignum_cmul_p256k1);
  functionaltest(all,"bignum_cmul_p256k1_alt",test_bignum_cmul_p256k1_alt);
  functionaltest(bmi,"bignum_cmul_p384",test_bignum_cmul_p384);
  functionaltest(all,"bignum_cmul_p384_alt",test_bignum_cmul_p384_alt);
  functionaltest(bmi,"bignum_cmul_p521",test_bignum_cmul_p521);
  functionaltest(all,"bignum_cmul_p521_alt",test_bignum_cmul_p521_alt);
  functionaltest(bmi,"bignum_cmul_sm2",test_bignum_cmul_sm2);
  functionaltest(all,"bignum_cmul_sm2_alt",test_bignum_cmul_sm2_alt);
  functionaltest(all,"bignum_coprime",test_bignum_coprime);
  functionaltest(all,"bignum_copy",test_bignum_copy);
  functionaltest(all,"bignum_copy_row_from_table",test_bignum_copy_row_from_table);
  functionaltest(all,"bignum_ctd",test_bignum_ctd);
  functionaltest(all,"bignum_ctz",test_bignum_ctz);
  functionaltest(bmi,"bignum_deamont_p256",test_bignum_deamont_p256);
  functionaltest(all,"bignum_deamont_p256_alt",test_bignum_deamont_p256_alt);
  functionaltest(all,"bignum_deamont_p256k1",test_bignum_deamont_p256k1);
  functionaltest(bmi,"bignum_deamont_p384",test_bignum_deamont_p384);
  functionaltest(all,"bignum_deamont_p384_alt",test_bignum_deamont_p384_alt);
  functionaltest(all,"bignum_deamont_p521",test_bignum_deamont_p521);
  functionaltest(all,"bignum_deamont_sm2",test_bignum_deamont_sm2);
  functionaltest(all,"bignum_demont",test_bignum_demont);
  functionaltest(bmi,"bignum_demont_p256",test_bignum_demont_p256);
  functionaltest(all,"bignum_demont_p256_alt",test_bignum_demont_p256_alt);
  functionaltest(all,"bignum_demont_p256k1",test_bignum_demont_p256k1);
  functionaltest(bmi,"bignum_demont_p384",test_bignum_demont_p384);
  functionaltest(all,"bignum_demont_p384_alt",test_bignum_demont_p384_alt);
  functionaltest(all,"bignum_demont_p521",test_bignum_demont_p521);
  functionaltest(all,"bignum_demont_sm2",test_bignum_demont_sm2);
  functionaltest(all,"bignum_digit",test_bignum_digit);
  functionaltest(all,"bignum_digitsize",test_bignum_digitsize);
  functionaltest(all,"bignum_divmod10",test_bignum_divmod10);
  functionaltest(all,"bignum_double_p25519",test_bignum_double_p25519);
  functionaltest(all,"bignum_double_p256",test_bignum_double_p256);
  functionaltest(all,"bignum_double_p256k1",test_bignum_double_p256k1);
  functionaltest(all,"bignum_double_p384",test_bignum_double_p384);
  functionaltest(all,"bignum_double_p521",test_bignum_double_p521);
  functionaltest(all,"bignum_double_sm2",test_bignum_double_sm2);
  functionaltest(all,"bignum_emontredc",test_bignum_emontredc);
  functionaltest(bmi,"bignum_emontredc_8n",test_bignum_emontredc_8n);
  functionaltest(all,"bignum_eq",test_bignum_eq);
  functionaltest(all,"bignum_even",test_bignum_even);
  functionaltest(all,"bignum_frombebytes_4",test_bignum_frombebytes_4);
  functionaltest(all,"bignum_frombebytes_6",test_bignum_frombebytes_6);
  functionaltest(all,"bignum_fromlebytes_4",test_bignum_fromlebytes_4);
  functionaltest(all,"bignum_fromlebytes_6",test_bignum_fromlebytes_6);
  functionaltest(all,"bignum_fromlebytes_p521",test_bignum_fromlebytes_p521);
  functionaltest(all,"bignum_ge",test_bignum_ge);
  functionaltest(all,"bignum_gt",test_bignum_gt);
  functionaltest(all,"bignum_half_p256",test_bignum_half_p256);
  functionaltest(all,"bignum_half_p256k1",test_bignum_half_p256k1);
  functionaltest(all,"bignum_half_p384",test_bignum_half_p384);
  functionaltest(all,"bignum_half_p521",test_bignum_half_p521);
  functionaltest(all,"bignum_half_sm2",test_bignum_half_sm2);
  functionaltest(all,"bignum_inv_p25519",test_bignum_inv_p25519);
  functionaltest(all,"bignum_inv_p256",test_bignum_inv_p256);
  functionaltest(all,"bignum_inv_p384",test_bignum_inv_p384);
  functionaltest(all,"bignum_inv_p521",test_bignum_inv_p521);
  functionaltest(all,"bignum_inv_sm2",test_bignum_inv_sm2);
  functionaltest(bmi,"bignum_invsqrt_p25519",test_bignum_invsqrt_p25519);
  functionaltest(all,"bignum_invsqrt_p25519_alt",test_bignum_invsqrt_p25519_alt);
  functionaltest(all,"bignum_iszero",test_bignum_iszero);
  functionaltest(bmi,"bignum_kmul_16_32",test_bignum_kmul_16_32);
  functionaltest(bmi,"bignum_kmul_32_64", test_bignum_kmul_32_64);
  functionaltest(bmi,"bignum_ksqr_16_32",test_bignum_ksqr_16_32);
  functionaltest(bmi,"bignum_ksqr_32_64",test_bignum_ksqr_32_64);
  functionaltest(all,"bignum_le",test_bignum_le);
  functionaltest(all,"bignum_littleendian_4",test_bignum_littleendian_4);
  functionaltest(all,"bignum_littleendian_6",test_bignum_littleendian_6);
  functionaltest(all,"bignum_lt",test_bignum_lt);
  functionaltest(all,"bignum_madd",test_bignum_madd);
  functionaltest(bmi,"bignum_madd_n25519",test_bignum_madd_n25519);
  functionaltest(all,"bignum_madd_n25519_alt",test_bignum_madd_n25519_alt);
  functionaltest(all,"bignum_mod_m25519_4",test_bignum_mod_m25519_4);
  functionaltest(all,"bignum_mod_n25519",test_bignum_mod_n25519);
  functionaltest(all,"bignum_mod_n25519_4",test_bignum_mod_n25519_4);
  functionaltest(bmi,"bignum_mod_n256",test_bignum_mod_n256);
  functionaltest(all,"bignum_mod_n256_4",test_bignum_mod_n256_4);
  functionaltest(all,"bignum_mod_n256_alt",test_bignum_mod_n256_alt);
  functionaltest(all,"bignum_mod_n256k1_4",test_bignum_mod_n256k1_4);
  functionaltest(bmi,"bignum_mod_n384",test_bignum_mod_n384);
  functionaltest(all,"bignum_mod_n384_6",test_bignum_mod_n384_6);
  functionaltest(all,"bignum_mod_n384_alt",test_bignum_mod_n384_alt);
  functionaltest(bmi,"bignum_mod_n521_9",test_bignum_mod_n521_9);
  functionaltest(all,"bignum_mod_n521_9_alt",test_bignum_mod_n521_9_alt);
  functionaltest(bmi,"bignum_mod_nsm2",test_bignum_mod_nsm2);
  functionaltest(all,"bignum_mod_nsm2_4",test_bignum_mod_nsm2_4);
  functionaltest(all,"bignum_mod_nsm2_alt",test_bignum_mod_nsm2_alt);
  functionaltest(all,"bignum_mod_p25519_4",test_bignum_mod_p25519_4);
  functionaltest(bmi,"bignum_mod_p256",test_bignum_mod_p256);
  functionaltest(all,"bignum_mod_p256_4",test_bignum_mod_p256_4);
  functionaltest(all,"bignum_mod_p256_alt",test_bignum_mod_p256_alt);
  functionaltest(all,"bignum_mod_p256k1_4",test_bignum_mod_p256k1_4);
  functionaltest(bmi,"bignum_mod_p384",test_bignum_mod_p384);
  functionaltest(all,"bignum_mod_p384_6",test_bignum_mod_p384_6);
  functionaltest(all,"bignum_mod_p384_alt",test_bignum_mod_p384_alt);
  functionaltest(all,"bignum_mod_p521_9",test_bignum_mod_p521_9);
  functionaltest(all,"bignum_mod_sm2",test_bignum_mod_sm2);
  functionaltest(all,"bignum_mod_sm2_4",test_bignum_mod_sm2_4);
  functionaltest(all,"bignum_modadd",test_bignum_modadd);
  functionaltest(all,"bignum_moddouble",test_bignum_moddouble);
  functionaltest(all,"bignum_modexp",test_bignum_modexp);
  functionaltest(all,"bignum_modifier",test_bignum_modifier);
  functionaltest(all,"bignum_modinv",test_bignum_modinv);
  functionaltest(all,"bignum_modoptneg",test_bignum_modoptneg);
  functionaltest(all,"bignum_modsub",test_bignum_modsub);
  functionaltest(all,"bignum_montifier",test_bignum_montifier);
  functionaltest(all,"bignum_montinv_p256",test_bignum_montinv_p256);
  functionaltest(all,"bignum_montinv_p384",test_bignum_montinv_p384);
  functionaltest(all,"bignum_montinv_sm2",test_bignum_montinv_sm2);
  functionaltest(all,"bignum_montmul",test_bignum_montmul);
  functionaltest(bmi,"bignum_montmul_p256",test_bignum_montmul_p256);
  functionaltest(all,"bignum_montmul_p256_alt",test_bignum_montmul_p256_alt);
  functionaltest(bmi,"bignum_montmul_p256k1",test_bignum_montmul_p256k1);
  functionaltest(all,"bignum_montmul_p256k1_alt",test_bignum_montmul_p256k1_alt);
  functionaltest(bmi,"bignum_montmul_p384",test_bignum_montmul_p384);
  functionaltest(all,"bignum_montmul_p384_alt",test_bignum_montmul_p384_alt);
  functionaltest(bmi,"bignum_montmul_p521",test_bignum_montmul_p521);
  functionaltest(all,"bignum_montmul_p521_alt",test_bignum_montmul_p521_alt);
  functionaltest(bmi,"bignum_montmul_sm2",test_bignum_montmul_sm2);
  functionaltest(all,"bignum_montmul_sm2_alt",test_bignum_montmul_sm2_alt);
  functionaltest(all,"bignum_montredc",test_bignum_montredc);
  functionaltest(all,"bignum_montsqr",test_bignum_montsqr);
  functionaltest(bmi,"bignum_montsqr_p256",test_bignum_montsqr_p256);
  functionaltest(all,"bignum_montsqr_p256_alt",test_bignum_montsqr_p256_alt);
  functionaltest(bmi,"bignum_montsqr_p256k1",test_bignum_montsqr_p256k1);
  functionaltest(all,"bignum_montsqr_p256k1_alt",test_bignum_montsqr_p256k1_alt);
  functionaltest(bmi,"bignum_montsqr_p384",test_bignum_montsqr_p384);
  functionaltest(all,"bignum_montsqr_p384_alt",test_bignum_montsqr_p384_alt);
  functionaltest(bmi,"bignum_montsqr_p521",test_bignum_montsqr_p521);
  functionaltest(all,"bignum_montsqr_p521_alt",test_bignum_montsqr_p521_alt);
  functionaltest(bmi,"bignum_montsqr_sm2",test_bignum_montsqr_sm2);
  functionaltest(all,"bignum_montsqr_sm2_alt",test_bignum_montsqr_sm2_alt);
  functionaltest(all,"bignum_mul",test_bignum_mul);
  functionaltest(bmi,"bignum_mul_4_8",test_bignum_mul_4_8);
  functionaltest(all,"bignum_mul_4_8_alt",test_bignum_mul_4_8_alt);
  functionaltest(bmi,"bignum_mul_6_12",test_bignum_mul_6_12);
  functionaltest(all,"bignum_mul_6_12_alt",test_bignum_mul_6_12_alt);
  functionaltest(bmi,"bignum_mul_8_16",test_bignum_mul_8_16);
  functionaltest(all,"bignum_mul_8_16_alt",test_bignum_mul_8_16_alt);
  functionaltest(bmi,"bignum_mul_p25519",test_bignum_mul_p25519);
  functionaltest(all,"bignum_mul_p25519_alt",test_bignum_mul_p25519_alt);
  functionaltest(bmi,"bignum_mul_p256k1",test_bignum_mul_p256k1);
  functionaltest(all,"bignum_mul_p256k1_alt",test_bignum_mul_p256k1_alt);
  functionaltest(bmi,"bignum_mul_p521",test_bignum_mul_p521);
  functionaltest(all,"bignum_mul_p521_alt",test_bignum_mul_p521_alt);
  functionaltest(all,"bignum_muladd10",test_bignum_muladd10);
  functionaltest(all,"bignum_mux",test_bignum_mux);
  functionaltest(all,"bignum_mux16",test_bignum_mux16);
  functionaltest(all,"bignum_mux_4",test_bignum_mux_4);
  functionaltest(all,"bignum_mux_6",test_bignum_mux_6);
  functionaltest(all,"bignum_neg_p25519",test_bignum_neg_p25519);
  functionaltest(all,"bignum_neg_p256",test_bignum_neg_p256);
  functionaltest(all,"bignum_neg_p256k1",test_bignum_neg_p256k1);
  functionaltest(all,"bignum_neg_p384",test_bignum_neg_p384);
  functionaltest(all,"bignum_neg_p521",test_bignum_neg_p521);
  functionaltest(all,"bignum_neg_sm2",test_bignum_neg_sm2);
  functionaltest(all,"bignum_negmodinv",test_bignum_negmodinv);
  functionaltest(all,"bignum_nonzero",test_bignum_nonzero);
  functionaltest(all,"bignum_nonzero_4",test_bignum_nonzero_4);
  functionaltest(all,"bignum_nonzero_6",test_bignum_nonzero_6);
  functionaltest(all,"bignum_normalize",test_bignum_normalize);
  functionaltest(all,"bignum_odd",test_bignum_odd);
  functionaltest(all,"bignum_of_word",test_bignum_of_word);
  functionaltest(all,"bignum_optadd",test_bignum_optadd);
  functionaltest(all,"bignum_optneg",test_bignum_optneg);
  functionaltest(all,"bignum_optneg_p25519",test_bignum_optneg_p25519);
  functionaltest(all,"bignum_optneg_p256",test_bignum_optneg_p256);
  functionaltest(all,"bignum_optneg_p256k1",test_bignum_optneg_p256k1);
  functionaltest(all,"bignum_optneg_p384",test_bignum_optneg_p384);
  functionaltest(all,"bignum_optneg_p521",test_bignum_optneg_p521);
  functionaltest(all,"bignum_optneg_sm2",test_bignum_optneg_sm2);
  functionaltest(all,"bignum_optsub",test_bignum_optsub);
  functionaltest(all,"bignum_optsubadd",test_bignum_optsubadd);
  functionaltest(all,"bignum_pow2",test_bignum_pow2);
  functionaltest(all,"bignum_shl_small",test_bignum_shl_small);
  functionaltest(all,"bignum_shr_small",test_bignum_shr_small);
  functionaltest(all,"bignum_sqr",test_bignum_sqr);
  functionaltest(bmi,"bignum_sqr_4_8",test_bignum_sqr_4_8);
  functionaltest(all,"bignum_sqr_4_8_alt",test_bignum_sqr_4_8_alt);
  functionaltest(bmi,"bignum_sqr_6_12",test_bignum_sqr_6_12);
  functionaltest(all,"bignum_sqr_6_12_alt",test_bignum_sqr_6_12_alt);
  functionaltest(bmi,"bignum_sqr_8_16",test_bignum_sqr_8_16);
  functionaltest(all,"bignum_sqr_8_16_alt",test_bignum_sqr_8_16_alt);
  functionaltest(bmi,"bignum_sqr_p25519",test_bignum_sqr_p25519);
  functionaltest(all,"bignum_sqr_p25519_alt",test_bignum_sqr_p25519_alt);
  functionaltest(bmi,"bignum_sqr_p256k1",test_bignum_sqr_p256k1);
  functionaltest(all,"bignum_sqr_p256k1_alt",test_bignum_sqr_p256k1_alt);
  functionaltest(bmi,"bignum_sqr_p521",test_bignum_sqr_p521);
  functionaltest(all,"bignum_sqr_p521_alt",test_bignum_sqr_p521_alt);
  functionaltest(bmi,"bignum_sqrt_p25519",test_bignum_sqrt_p25519);
  functionaltest(all,"bignum_sqrt_p25519_alt",test_bignum_sqrt_p25519_alt);
  functionaltest(all,"bignum_sub",test_bignum_sub);
  functionaltest(all,"bignum_sub_p25519",test_bignum_sub_p25519);
  functionaltest(all,"bignum_sub_p256",test_bignum_sub_p256);
  functionaltest(all,"bignum_sub_p256k1",test_bignum_sub_p256k1);
  functionaltest(all,"bignum_sub_p384",test_bignum_sub_p384);
  functionaltest(all,"bignum_sub_p521",test_bignum_sub_p521);
  functionaltest(all,"bignum_sub_sm2",test_bignum_sub_sm2);
  functionaltest(all,"bignum_tobebytes_4",test_bignum_tobebytes_4);
  functionaltest(all,"bignum_tobebytes_6",test_bignum_tobebytes_6);
  functionaltest(all,"bignum_tolebytes_4",test_bignum_tolebytes_4);
  functionaltest(all,"bignum_tolebytes_6",test_bignum_tolebytes_6);
  functionaltest(all,"bignum_tolebytes_p521",test_bignum_tolebytes_p521);
  functionaltest(bmi,"bignum_tomont_p256",test_bignum_tomont_p256);
  functionaltest(all,"bignum_tomont_p256_alt",test_bignum_tomont_p256_alt);
  functionaltest(bmi,"bignum_tomont_p256k1",test_bignum_tomont_p256k1);
  functionaltest(all,"bignum_tomont_p256k1_alt",test_bignum_tomont_p256k1_alt);
  functionaltest(bmi,"bignum_tomont_p384",test_bignum_tomont_p384);
  functionaltest(all,"bignum_tomont_p384_alt",test_bignum_tomont_p384_alt);
  functionaltest(all,"bignum_tomont_p521",test_bignum_tomont_p521);
  functionaltest(all,"bignum_tomont_sm2",test_bignum_tomont_sm2);
  functionaltest(bmi,"bignum_triple_p256",test_bignum_triple_p256);
  functionaltest(all,"bignum_triple_p256_alt",test_bignum_triple_p256_alt);
  functionaltest(bmi,"bignum_triple_p256k1",test_bignum_triple_p256k1);
  functionaltest(all,"bignum_triple_p256k1_alt",test_bignum_triple_p256k1_alt);
  functionaltest(bmi,"bignum_triple_p384",test_bignum_triple_p384);
  functionaltest(all,"bignum_triple_p384_alt",test_bignum_triple_p384_alt);
  functionaltest(bmi,"bignum_triple_p521",test_bignum_triple_p521);
  functionaltest(all,"bignum_triple_p521_alt",test_bignum_triple_p521_alt);
  functionaltest(bmi,"bignum_triple_sm2",test_bignum_triple_sm2);
  functionaltest(all,"bignum_triple_sm2_alt",test_bignum_triple_sm2_alt);
  functionaltest(bmi,"curve25519_ladderstep",test_curve25519_ladderstep);
  functionaltest(all,"curve25519_ladderstep_alt",test_curve25519_ladderstep_alt);
  functionaltest(bmi,"curve25519_pxscalarmul",test_curve25519_pxscalarmul);
  functionaltest(all,"curve25519_pxscalarmul_alt",test_curve25519_pxscalarmul_alt);
  functionaltest(bmi,"curve25519_x25519",test_curve25519_x25519);
  functionaltest(all,"curve25519_x25519_alt",test_curve25519_x25519_alt);
  functionaltest(bmi,"curve25519_x25519_byte",test_curve25519_x25519_byte);
  functionaltest(all,"curve25519_x25519_byte_alt",test_curve25519_x25519_byte_alt);
  functionaltest(bmi,"curve25519_x25519base",test_curve25519_x25519base);
  functionaltest(all,"curve25519_x25519base_alt",test_curve25519_x25519base_alt);
  functionaltest(bmi,"curve25519_x25519base_byte",test_curve25519_x25519base_byte);
  functionaltest(all,"curve25519_x25519base_byte_alt",test_curve25519_x25519base_byte_alt);
  functionaltest(bmi,"edwards25519_decode",test_edwards25519_decode);
  functionaltest(all,"edwards25519_decode_alt",test_edwards25519_decode_alt);
  functionaltest(all,"edwards25519_encode",test_edwards25519_encode);
  functionaltest(bmi,"edwards25519_epadd",test_edwards25519_epadd);
  functionaltest(all,"edwards25519_epadd_alt",test_edwards25519_epadd_alt);
  functionaltest(bmi,"edwards25519_epdouble",test_edwards25519_epdouble);
  functionaltest(all,"edwards25519_epdouble_alt",test_edwards25519_epdouble_alt);
  functionaltest(bmi,"edwards25519_pdouble",test_edwards25519_pdouble);
  functionaltest(all,"edwards25519_pdouble_alt",test_edwards25519_pdouble_alt);
  functionaltest(bmi,"edwards25519_pepadd",test_edwards25519_pepadd);
  functionaltest(all,"edwards25519_pepadd_alt",test_edwards25519_pepadd_alt);
  functionaltest(bmi,"edwards25519_scalarmulbase",test_edwards25519_scalarmulbase);
  functionaltest(all,"edwards25519_scalarmulbase_alt",test_edwards25519_scalarmulbase_alt);
  functionaltest(bmi,"edwards25519_scalarmuldouble",test_edwards25519_scalarmuldouble);
  functionaltest(all,"edwards25519_scalarmuldouble_alt",test_edwards25519_scalarmuldouble_alt);
  functionaltest(bmi,"p256_montjadd",test_p256_montjadd);
  functionaltest(all,"p256_montjadd_alt",test_p256_montjadd_alt);
  functionaltest(bmi,"p256_montjdouble",test_p256_montjdouble);
  functionaltest(all,"p256_montjdouble_alt",test_p256_montjdouble_alt);
  functionaltest(bmi,"p256_montjmixadd",test_p256_montjmixadd);
  functionaltest(all,"p256_montjmixadd_alt",test_p256_montjmixadd_alt);
  functionaltest(bmi,"p256_montjscalarmul",test_p256_montjscalarmul);
  functionaltest(all,"p256_montjscalarmul_alt",test_p256_montjscalarmul_alt);
  functionaltest(bmi,"p256_scalarmul",test_p256_scalarmul);
  functionaltest(all,"p256_scalarmul_alt",test_p256_scalarmul_alt);
  functionaltest(bmi,"p256_scalarmulbase",test_p256_scalarmulbase);
  functionaltest(all,"p256_scalarmulbase_alt",test_p256_scalarmulbase_alt);
  functionaltest(bmi,"p384_montjadd",test_p384_montjadd);
  functionaltest(all,"p384_montjadd_alt",test_p384_montjadd_alt);
  functionaltest(bmi,"p384_montjdouble",test_p384_montjdouble);
  functionaltest(all,"p384_montjdouble_alt",test_p384_montjdouble_alt);
  functionaltest(bmi,"p384_montjmixadd",test_p384_montjmixadd);
  functionaltest(all,"p384_montjmixadd_alt",test_p384_montjmixadd_alt);
  functionaltest(bmi,"p384_montjscalarmul",test_p384_montjscalarmul);
  functionaltest(all,"p384_montjscalarmul_alt",test_p384_montjscalarmul_alt);
  functionaltest(bmi,"p521_jadd",test_p521_jadd);
  functionaltest(all,"p521_jadd_alt",test_p521_jadd_alt);
  functionaltest(bmi,"p521_jdouble",test_p521_jdouble);
  functionaltest(all,"p521_jdouble_alt",test_p521_jdouble_alt);
  functionaltest(bmi,"p521_jmixadd",test_p521_jmixadd);
  functionaltest(all,"p521_jmixadd_alt",test_p521_jmixadd_alt);
  functionaltest(bmi,"p521_jscalarmul",test_p521_jscalarmul);
  functionaltest(all,"p521_jscalarmul_alt",test_p521_jscalarmul_alt);
  functionaltest(bmi,"secp256k1_jadd",test_secp256k1_jadd);
  functionaltest(all,"secp256k1_jadd_alt",test_secp256k1_jadd_alt);
  functionaltest(bmi,"secp256k1_jdouble",test_secp256k1_jdouble);
  functionaltest(all,"secp256k1_jdouble_alt",test_secp256k1_jdouble_alt);
  functionaltest(bmi,"secp256k1_jmixadd",test_secp256k1_jmixadd);
  functionaltest(all,"secp256k1_jmixadd_alt",test_secp256k1_jmixadd_alt);
  functionaltest(bmi,"sm2_montjadd",test_sm2_montjadd);
  functionaltest(all,"sm2_montjadd_alt",test_sm2_montjadd_alt);
  functionaltest(bmi,"sm2_montjdouble",test_sm2_montjdouble);
  functionaltest(all,"sm2_montjdouble_alt",test_sm2_montjdouble_alt);
  functionaltest(bmi,"sm2_montjmixadd",test_sm2_montjmixadd);
  functionaltest(all,"sm2_montjmixadd_alt",test_sm2_montjmixadd_alt);
  functionaltest(bmi,"sm2_montjscalarmul",test_sm2_montjscalarmul);
  functionaltest(all,"sm2_montjscalarmul_alt",test_sm2_montjscalarmul_alt);
  functionaltest(all,"word_bytereverse",test_word_bytereverse);
  functionaltest(all,"word_clz",test_word_clz);
  functionaltest(all,"word_ctz",test_word_ctz);
  functionaltest(all,"word_divstep59",test_word_divstep59);
  functionaltest(all,"word_max",test_word_max);
  functionaltest(all,"word_min",test_word_min);
  functionaltest(all,"word_negmodinv",test_word_negmodinv);
  functionaltest(all,"word_popcount",test_word_popcount);
  functionaltest(all,"word_recip",test_word_recip);

  if (get_arch_name() == ARCH_AARCH64) {
    functionaltest(all,"bignum_copy_row_from_table_8n",test_bignum_copy_row_from_table_8n);
    functionaltest(all,"bignum_copy_row_from_table_16",test_bignum_copy_row_from_table_16);
    functionaltest(all,"bignum_copy_row_from_table_32",test_bignum_copy_row_from_table_32);
    functionaltest(all,"bignum_emontredc_8n_cdiff",test_bignum_emontredc_8n_cdiff);
  }

  if (extrastrigger) function_to_test = "_";

  functionaltest(bmi,"known value tests",test_known_values);

  functionaltest(bmi,"curve25519_x25519 (TweetNaCl)",test_curve25519_x25519_tweetnacl);
  functionaltest(all,"curve25519_x25519_alt (TweetNaCl)",test_curve25519_x25519_alt_tweetnacl);
  functionaltest(bmi,"curve25519_x25519_byte (TweetNaCl)",test_curve25519_x25519_byte_tweetnacl);
  functionaltest(all,"curve25519_x25519_byte+alt (TweetNaCl)",test_curve25519_x25519_byte_alt_tweetnacl);
  functionaltest(bmi,"curve25519_x25519base (TweetNaCl)",test_curve25519_x25519base_tweetnacl);
  functionaltest(all,"curve25519_x25519base_alt (TweetNaCl)",test_curve25519_x25519base_alt_tweetnacl);
  functionaltest(bmi,"curve25519_x25519base_byte (TweetNaCl)",test_curve25519_x25519base_byte_tweetnacl);
  functionaltest(all,"curve25519_x25519base_byte_alt (TweetNaCl)",test_curve25519_x25519base_byte_alt_tweetnacl);
  functionaltest(bmi,"edwards25519_scalarmulbase (TweetNaCl)",test_edwards25519_scalarmulbase_tweetnacl);
  functionaltest(all,"edwards25519_scalarmulbase_alt (TweetNaCl)",test_edwards25519_scalarmulbase_alt_tweetnacl);

  if (successes == tested)
   { printf("All %d tests run, all passed\n",successes);
     return 0;
   }

  if (successes + skipped == tested)
   { printf("Skipped %d but all %d selected tests passed\n",skipped,successes);
     return 1;
   }

  if (failures != 0) printf("***** FAILED %d tests\n",failures);
  else printf("Testing all passed but is incomplete\n");
  printf("                     Total operations to test = %3d\n",tested);
  printf("                                       Passed = %3d\n",successes);
  printf("                                      Failed  = %3d\n",failures);
  printf("         Skipped because not selected by user = %3d\n",skipped);
  printf("Skipped because inapplicable (no x86 BMI/ADX) = %3d\n",inapplicable);
  return 1;
}
