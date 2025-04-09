#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = bignum_add_p256k1.o \
      bignum_cmul_p256k1.o \
      bignum_cmul_p256k1_alt.o \
      bignum_deamont_p256k1.o \
      bignum_demont_p256k1.o \
      bignum_double_p256k1.o \
      bignum_half_p256k1.o \
      bignum_mod_n256k1_4.o \
      bignum_mod_p256k1_4.o \
      bignum_montmul_p256k1.o \
      bignum_montmul_p256k1_alt.o \
      bignum_montsqr_p256k1.o \
      bignum_montsqr_p256k1_alt.o \
      bignum_mul_p256k1.o \
      bignum_mul_p256k1_alt.o \
      bignum_neg_p256k1.o \
      bignum_optneg_p256k1.o \
      bignum_sqr_p256k1.o \
      bignum_sqr_p256k1_alt.o \
      bignum_sub_p256k1.o \
      bignum_tomont_p256k1.o \
      bignum_tomont_p256k1_alt.o \
      bignum_triple_p256k1.o \
      bignum_triple_p256k1_alt.o \
      secp256k1_jadd.o \
      secp256k1_jadd_alt.o \
      secp256k1_jdouble.o \
      secp256k1_jdouble_alt.o \
      secp256k1_jmixadd.o \
      secp256k1_jmixadd_alt.o

%.o : %.S ; $(CC) -E -I../../include $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
