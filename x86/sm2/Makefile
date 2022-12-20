#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#############################################################################

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = bignum_add_sm2.o \
      bignum_sub_sm2.o

%.o : %.S ; $(CC) -E -I../../include $< | as -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
