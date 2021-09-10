// -----------------------------------------------------------------------------
// Supersingular Isogeny Key Encapsulation Library
//
// Abstract: modular arithmetic for P434
// Note that currently there is no need to differentiate these methods using namespace
// as this is only the SIKE integration.
// -----------------------------------------------------------------------------

#pragma once

#include "sikep434r3.h"

void mp_sub434_p2(const digit_t* a, const digit_t* b, digit_t* c);

void mp_sub434_p4(const digit_t* a, const digit_t* b, digit_t* c);

void fpadd434(const digit_t* a, const digit_t* b, digit_t* c);

void fpsub434(const digit_t* a, const digit_t* b, digit_t* c);

void fpneg434(digit_t* a);

void fpdiv2_434(const digit_t* a, digit_t* c);

void fpcorrection434(digit_t* a);

void digit_x_digit(const digit_t a, const digit_t b, digit_t* c);

void mp_mul(const digit_t* a, const digit_t* b, digit_t* c, const unsigned int nwords);

void rdc_mont(digit_t* ma, digit_t* mc);
