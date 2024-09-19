#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = bignum_add_p521.o \
      bignum_cmul_p521.o \
      bignum_cmul_p521_alt.o \
      bignum_deamont_p521.o \
      bignum_demont_p521.o \
      bignum_double_p521.o \
      bignum_fromlebytes_p521.o \
      bignum_half_p521.o \
      bignum_inv_p521.o \
      bignum_mod_n521_9.o \
      bignum_mod_n521_9_alt.o \
      bignum_mod_p521_9.o \
      bignum_montmul_p521.o \
      bignum_montmul_p521_alt.o \
      bignum_montsqr_p521.o \
      bignum_montsqr_p521_alt.o \
      bignum_mul_p521.o \
      bignum_mul_p521_alt.o \
      bignum_neg_p521.o \
      bignum_optneg_p521.o \
      bignum_sqr_p521.o \
      bignum_sqr_p521_alt.o \
      bignum_sub_p521.o \
      bignum_tolebytes_p521.o \
      bignum_tomont_p521.o \
      bignum_triple_p521.o \
      bignum_triple_p521_alt.o \
      p521_jadd.o \
      p521_jadd_alt.o \
      p521_jdouble.o \
      p521_jdouble_alt.o \
      p521_jmixadd.o \
      p521_jmixadd_alt.o \
      p521_jscalarmul.o \
      p521_jscalarmul_alt.o

%.o : %.S ; $(CC) -E -I../../include $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
