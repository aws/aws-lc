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

OBJ = bignum_add.o \
      bignum_amontifier.o \
      bignum_amontmul.o \
      bignum_amontredc.o \
      bignum_amontsqr.o \
      bignum_bitfield.o \
      bignum_bitsize.o \
      bignum_cdiv.o \
      bignum_cdiv_exact.o \
      bignum_cld.o \
      bignum_clz.o \
      bignum_cmadd.o \
      bignum_cmnegadd.o \
      bignum_cmod.o \
      bignum_cmul.o \
      bignum_coprime.o \
      bignum_copy.o \
      bignum_copy_row_from_table.o \
      bignum_copy_row_from_table_8n.o \
      bignum_copy_row_from_table_16.o \
      bignum_copy_row_from_table_32.o \
      bignum_ctd.o \
      bignum_ctz.o \
      bignum_demont.o \
      bignum_digit.o \
      bignum_digitsize.o \
      bignum_divmod10.o \
      bignum_emontredc.o \
      bignum_eq.o \
      bignum_even.o \
      bignum_ge.o \
      bignum_gt.o \
      bignum_iszero.o \
      bignum_le.o \
      bignum_lt.o \
      bignum_madd.o \
      bignum_modadd.o \
      bignum_moddouble.o \
      bignum_modexp.o \
      bignum_modifier.o \
      bignum_modinv.o \
      bignum_modoptneg.o \
      bignum_modsub.o \
      bignum_montifier.o \
      bignum_montmul.o \
      bignum_montredc.o \
      bignum_montsqr.o \
      bignum_mul.o \
      bignum_muladd10.o \
      bignum_mux.o \
      bignum_mux16.o \
      bignum_negmodinv.o \
      bignum_nonzero.o \
      bignum_normalize.o \
      bignum_odd.o \
      bignum_of_word.o \
      bignum_optadd.o \
      bignum_optneg.o \
      bignum_optsub.o \
      bignum_optsubadd.o \
      bignum_pow2.o \
      bignum_shl_small.o \
      bignum_shr_small.o \
      bignum_sqr.o \
      bignum_sub.o \
      word_bytereverse.o \
      word_clz.o \
      word_ctz.o \
      word_divstep59.o \
      word_max.o \
      word_min.o \
      word_negmodinv.o \
      word_popcount.o \
      word_recip.o

%.o : %.S ; $(CC) -E -I../../include $< | $(GAS) -o $@ -

default: $(OBJ);

clean:; rm -f *.o *.correct
