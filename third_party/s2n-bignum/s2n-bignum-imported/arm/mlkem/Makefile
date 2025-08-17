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

OBJ = mlkem_basemul_k2.o \
      mlkem_basemul_k3.o \
      mlkem_basemul_k4.o \
      mlkem_intt.o \
      mlkem_mulcache_compute.o \
      mlkem_ntt.o \
      mlkem_reduce.o \
      mlkem_tobytes.o \
      mlkem_tomont.o \
      mlkem_rej_uniform_VARIABLE_TIME.o

%.o : %.S ; $(CC) -E -I../../include $< | $(GAS) -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct unopt/*.o
