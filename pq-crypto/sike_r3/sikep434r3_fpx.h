// -----------------------------------------------------------------------------
// Supersingular Isogeny Key Encapsulation Library
//
// Abstract: core functions over GF(p) and GF(p^2)
// Note that currently there is no need to differentiate these methods using namespace
// as this is only the SIKE integration.
// -----------------------------------------------------------------------------

#pragma once

#include <string.h>
#include "sikep434r3.h"
#include "sikep434r3_fp.h"

void fp2_encode(const f2elm_t *x, unsigned char *enc);

void fp2_decode(const unsigned char *x, f2elm_t *dec);

void copy_words(const digit_t* a, digit_t* c, const unsigned int nwords);

void fp2copy(const f2elm_t *a, f2elm_t *c);

void fp2div2(const f2elm_t *a, f2elm_t *c);

unsigned int mp_add(const digit_t* a, const digit_t* b, digit_t* c, const unsigned int nwords);

void fp2sqr_mont(const f2elm_t *a, f2elm_t *c);

void fp2mul_mont(const f2elm_t *a, const f2elm_t *b, f2elm_t *c);

void fp2inv_mont(f2elm_t *a);

void mp_shiftr1(digit_t* x, const unsigned int nwords);

void decode_to_digits(const unsigned char* x, digit_t* dec, int nbytes, int ndigits);

void fpcopy(const felm_t a, felm_t c);

void fpzero(felm_t a);

void fp2add(const f2elm_t *a, const f2elm_t *b, f2elm_t *c);

void fp2sub(const f2elm_t *a, const f2elm_t *b, f2elm_t *c);

void mp_addfast(const digit_t* a, const digit_t* b, digit_t* c);

void mp2_add(const f2elm_t *a, const f2elm_t *b, f2elm_t *c);

void mp2_sub_p2(const f2elm_t *a, const f2elm_t *b, f2elm_t *c);

// Conditional move in constant time
void ct_cmov(uint8_t *r, const uint8_t *a, unsigned int len, int8_t selector);

// Compare two byte arrays in constant time
int8_t ct_compare(const uint8_t *a, const uint8_t *b, unsigned int len);
