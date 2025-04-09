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

OBJ = bignum_add_p256k1.o \
      bignum_cmul_p256k1.o \
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
      bignum_triple_p256k1.o \
      secp256k1_jadd.o \
      secp256k1_jadd_alt.o \
      secp256k1_jdouble.o \
      secp256k1_jdouble_alt.o \
      secp256k1_jmixadd.o \
      secp256k1_jmixadd_alt.o

%.o : %.S ; $(CC) -E -I../../include $< | $(GAS) -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
