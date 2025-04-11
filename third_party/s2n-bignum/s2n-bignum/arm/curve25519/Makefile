#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

# If actually on an ARM8 machine, just use the GNU assembler (as). Otherwise
# use a cross-assembling version so that the code can still be assembled
# and the proofs checked against the object files (though you won't be able
# to run code without additional emulation infrastructure). The aarch64
# cross-assembling version can be installed manually by something like:
#
#  sudo apt-get install binutils-aarch64-linux-gnu

UNAME_RESULT=$(shell uname -p)

ifeq ($(UNAME_RESULT),aarch64)
GAS=as
else
GAS=aarch64-linux-gnu-as
endif

# List of object files

OBJ = bignum_add_p25519.o \
      bignum_cmul_p25519.o \
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
      curve25519_x25519_byte.o \
      curve25519_x25519_byte_alt.o \
      curve25519_x25519base.o \
      curve25519_x25519base_alt.o \
      curve25519_x25519base_byte.o \
      curve25519_x25519base_byte_alt.o \
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

%.o : %.S ; $(CC) -E -I../../include $< | $(GAS) -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
