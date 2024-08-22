#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = bignum_add_p384.o \
      bignum_bigendian_6.o \
      bignum_cmul_p384.o \
      bignum_cmul_p384_alt.o \
      bignum_deamont_p384.o \
      bignum_deamont_p384_alt.o \
      bignum_demont_p384.o \
      bignum_demont_p384_alt.o \
      bignum_double_p384.o \
      bignum_half_p384.o \
      bignum_inv_p384.o \
      bignum_littleendian_6.o \
      bignum_mod_n384.o \
      bignum_mod_n384_alt.o \
      bignum_mod_n384_6.o \
      bignum_mod_p384.o \
      bignum_mod_p384_alt.o \
      bignum_mod_p384_6.o \
      bignum_montinv_p384.o \
      bignum_montmul_p384.o \
      bignum_montmul_p384_alt.o \
      bignum_montsqr_p384.o \
      bignum_montsqr_p384_alt.o \
      bignum_mux_6.o \
      bignum_neg_p384.o \
      bignum_nonzero_6.o \
      bignum_optneg_p384.o \
      bignum_sub_p384.o \
      bignum_tomont_p384.o \
      bignum_tomont_p384_alt.o \
      bignum_triple_p384.o \
      bignum_triple_p384_alt.o \
      p384_montjadd.o \
      p384_montjadd_alt.o \
      p384_montjdouble.o \
      p384_montjdouble_alt.o \
      p384_montjmixadd.o \
      p384_montjmixadd_alt.o \
      p384_montjscalarmul.o \
      p384_montjscalarmul_alt.o

%.o : %.S ; $(CC) -E -I../../include $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
