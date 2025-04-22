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

OBJ = bignum_add_sm2.o \
      bignum_cmul_sm2.o \
      bignum_deamont_sm2.o \
      bignum_demont_sm2.o \
      bignum_double_sm2.o \
      bignum_half_sm2.o \
      bignum_inv_sm2.o \
      bignum_mod_nsm2.o \
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
      sm2_montjadd.o \
      sm2_montjadd_alt.o \
      sm2_montjdouble.o \
      sm2_montjdouble_alt.o \
      sm2_montjmixadd.o \
      sm2_montjmixadd_alt.o \
      sm2_montjscalarmul.o \
      sm2_montjscalarmul_alt.o

%.o : %.S ; $(CC) -E -I../../include $< | $(GAS) -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
