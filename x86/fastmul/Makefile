#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = bignum_emontredc_8n.o \
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
      bignum_sqr_8_16_alt.o

%.o : %.S ; $(CC) -E -I../../include $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
