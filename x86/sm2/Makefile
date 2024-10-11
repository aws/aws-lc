#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = bignum_add_sm2.o \
      bignum_cmul_sm2.o \
      bignum_cmul_sm2_alt.o \
      bignum_deamont_sm2.o \
      bignum_demont_sm2.o \
      bignum_double_sm2.o \
      bignum_half_sm2.o \
      bignum_inv_sm2.o \
      bignum_mod_nsm2.o \
      bignum_mod_nsm2_alt.o \
      bignum_mod_nsm2_4.o \
      bignum_mod_sm2.o \
      bignum_mod_sm2_4.o \
      bignum_montinv_sm2.o \
      bignum_montmul_sm2.o \
      bignum_montmul_sm2_alt.o \
      bignum_montsqr_sm2.o \
      bignum_montsqr_sm2_alt.o \
      bignum_neg_sm2.o \
      bignum_optneg_sm2.o \
      bignum_sub_sm2.o \
      bignum_tomont_sm2.o \
      bignum_triple_sm2.o \
      bignum_triple_sm2_alt.o \
      sm2_montjadd.o \
      sm2_montjadd_alt.o \
      sm2_montjdouble.o \
      sm2_montjdouble_alt.o \
      sm2_montjmixadd.o \
      sm2_montjmixadd_alt.o \
      sm2_montjscalarmul.o \
      sm2_montjscalarmul_alt.o

%.o : %.S ; $(CC) -E -I../../include $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
