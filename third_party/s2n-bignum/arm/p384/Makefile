#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#############################################################################

# If actually on an ARM8 machine, just use the GNU assmbler (as). Otherwise
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

OBJ = bignum_add_p384.o \
      bignum_bigendian_6.o \
      bignum_cmul_p384.o \
      bignum_deamont_p384.o \
      bignum_demont_p384.o \
      bignum_double_p384.o \
      bignum_half_p384.o \
      bignum_littleendian_6.o \
      bignum_mod_n384.o \
      bignum_mod_n384_6.o \
      bignum_mod_p384.o \
      bignum_mod_p384_6.o \
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
      bignum_triple_p384.o \
      p384_montjadd.o \
      p384_montjdouble.o \
      p384_montjmixadd.o

%.o : %.S ; $(CC) -E -I../../include $< | $(GAS) -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
