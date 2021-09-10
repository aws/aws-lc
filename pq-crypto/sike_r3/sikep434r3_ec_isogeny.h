// -----------------------------------------------------------------------------
// Supersingular Isogeny Key Encapsulation Library
//
// Abstract: elliptic curve and isogeny functions
// -----------------------------------------------------------------------------

#pragma once

#include "sikep434r3.h"

void xDBL(const point_proj_t P, point_proj_t Q, const f2elm_t *A24plus, const f2elm_t *C24);

void xDBLe(const point_proj_t P, point_proj_t Q, const f2elm_t *A24plus, const f2elm_t *C24, const int e);

void get_4_isog(const point_proj_t P, f2elm_t *A24plus, f2elm_t *C24, f2elm_t *coeff);

void eval_4_isog(point_proj_t P, f2elm_t* coeff);

void xTPL(const point_proj_t P, point_proj_t Q, const f2elm_t *A24minus, const f2elm_t *A24plus);

void xTPLe(const point_proj_t P, point_proj_t Q, const f2elm_t *A24minus, const f2elm_t *A24plus, const int e);

void get_3_isog(const point_proj_t P, f2elm_t *A24minus, f2elm_t *A24plus, f2elm_t *coeff);

void eval_3_isog(point_proj_t Q, const f2elm_t *coeff);

void inv_3_way(f2elm_t *z1, f2elm_t *z2, f2elm_t *z3);

void get_A(const f2elm_t *xP, const f2elm_t *xQ, const f2elm_t *xR, f2elm_t *A);

void j_inv(const f2elm_t *A, const f2elm_t *C, f2elm_t *jinv);

void LADDER3PT(const f2elm_t *xP, const f2elm_t *xQ, const f2elm_t *xPQ, const digit_t *m,
        const unsigned int AliceOrBob, point_proj_t R, const f2elm_t *A);
