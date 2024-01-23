#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = bignum_add_p25519.o \
      bignum_cmul_p25519.o \
      bignum_cmul_p25519_alt.o \
      bignum_double_p25519.o \
      bignum_inv_p25519.o \
      bignum_invsqrt_p25519.o \
      bignum_invsqrt_p25519_alt.o \
      bignum_madd_n25519.o \
      bignum_madd_n25519_alt.o \
      bignum_mod_m25519_4.o \
      bignum_mod_n25519.o \
      bignum_mod_n25519_4.o \
      bignum_mod_p25519_4.o \
      bignum_mul_p25519.o \
      bignum_mul_p25519_alt.o \
      bignum_neg_p25519.o \
      bignum_optneg_p25519.o \
      bignum_sqr_p25519.o \
      bignum_sqr_p25519_alt.o \
      bignum_sqrt_p25519.o \
      bignum_sqrt_p25519_alt.o \
      bignum_sub_p25519.o \
      curve25519_ladderstep.o \
      curve25519_ladderstep_alt.o \
      curve25519_pxscalarmul.o \
      curve25519_pxscalarmul_alt.o \
      curve25519_x25519.o \
      curve25519_x25519_alt.o \
      curve25519_x25519base.o \
      curve25519_x25519base_alt.o \
      edwards25519_decode.o \
      edwards25519_decode_alt.o \
      edwards25519_encode.o \
      edwards25519_epadd.o \
      edwards25519_epadd_alt.o \
      edwards25519_epdouble.o \
      edwards25519_epdouble_alt.o \
      edwards25519_pdouble.o \
      edwards25519_pdouble_alt.o \
      edwards25519_pepadd.o \
      edwards25519_pepadd_alt.o \
      edwards25519_scalarmulbase.o \
      edwards25519_scalarmulbase_alt.o \
      edwards25519_scalarmuldouble.o \
      edwards25519_scalarmuldouble_alt.o

%.o : %.S ; $(CC) -E -I../../include $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
