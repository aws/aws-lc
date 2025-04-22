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

OBJ = bignum_emontredc_8n.o \
      bignum_emontredc_8n_cdiff.o \
      bignum_kmul_16_32.o \
      bignum_kmul_32_64.o \
      bignum_ksqr_16_32.o \
      bignum_ksqr_32_64.o \
      bignum_mul_4_8.o \
      bignum_mul_4_8_alt.o \
      bignum_mul_6_12.o \
      bignum_mul_6_12_alt.o \
      bignum_mul_8_16.o \
      bignum_mul_8_16_alt.o \
      bignum_sqr_4_8.o \
      bignum_sqr_4_8_alt.o \
      bignum_sqr_6_12.o \
      bignum_sqr_6_12_alt.o \
      bignum_sqr_8_16.o \
      bignum_sqr_8_16_alt.o \

%.o : %.S ; $(CC) -E -I../../include $< | $(GAS) -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
