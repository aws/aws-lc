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

#UNAME_RESULT=$(shell uname -p)
OSTYPE_RESULT=$(shell uname -s)
ARCHTYPE_RESULT=$(shell uname -m)

ifeq ($(ARCHTYPE_RESULT),aarch64)
GAS=as
else
ifeq ($(OSTYPE_RESULT),Darwin)
GAS=as -arch arm64
OBJDUMP=otool -tvV
else
GAS=aarch64-linux-gnu-as
endif
endif

# List of object files

OBJ = aes_xts_decrypt.o \
      aes_xts_encrypt.o


%.o : %.S ; $(CC) -E -I../../include $< | $(GAS) -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
