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

// ----------------------------------------------------------------------------
// Single-word negated modular inverse (-1/a) mod 2^64
// Input a; output function return
//
//    extern uint64_t word_negmodinv (uint64_t a);
//
// A 64-bit function that returns a negated multiplicative inverse mod 2^64
// of its input, assuming that input is odd. Given odd input a, the result z
// will satisfy a * z + 1 == 0 (mod 2^64), i.e. a 64-bit word multiplication
// a * z will give -1.
//
// Standard ARM ABI: X0 = a, returns X0
// ----------------------------------------------------------------------------

.text
.globl word_negmodinv

// Use some more intuitive variable names but these in general are aliased
// to each other so need care when interpreting. Overall we only use the
// registers x0, x1 and x2.
//
// There does seem a slight efficiency advantage in putting e' = e^2
// before the x' = x (1 + e) each time. That's the only reason for not
// reversing those and hence being able to alias all the e values to the
// same register.

#define a x0
#define x x1
#define one x2

#define e1 x2
#define e2 x0
#define e4 x2
#define e8 x0

word_negmodinv:

// Initial magical 5-bit approximation x = (a - a<<2) xor 2

                lsl     x, a, #2
                sub     x, a, x
                eor     x, x, #2

// Get error e = a * x + 1 for subsequent correction steps

                mov     one, #1
                madd    e1, a, x, one

// e2 = e^2, x' = x (1 + e) is good to 10 bits

                mul     e2, e1, e1
                madd    x, e1, x, x

// e4 = e^4, x' = x (1 + e^2) is good to 20 bits

                mul     e4, e2, e2
                madd    x, e2, x, x

// e8 = e^8, x' = x (1 + e^4) is good to 40 bits

                mul     e8, e4, e4
                madd    x, e4, x, x

// Final x' = x (1 + e^8) is good to the 64-bit word size

                madd    x0, e8, x, x

                ret
