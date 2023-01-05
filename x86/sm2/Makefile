#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#############################################################################

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = bignum_add_sm2.o \
      bignum_cmul_sm2.o \
      bignum_cmul_sm2_alt.o \
      bignum_deamont_sm2.o \
      bignum_demont_sm2.o \
      bignum_mod_nsm2.o \
      bignum_mod_nsm2_alt.o \
      bignum_mod_nsm2_4.o \
      bignum_mod_sm2.o \
      bignum_mod_sm2_4.o \
      bignum_sub_sm2.o

%.o : %.S ; $(CC) -E -I../../include $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
