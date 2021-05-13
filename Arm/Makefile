#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
#
#  http://aws.amazon.com/apache2.0
#
# or in the "LICENSE" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
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

OBJ = bignum_add.o \
      bignum_add_p256.o \
      bignum_add_p384.o \
      bignum_amontifier.o \
      bignum_amontmul.o \
      bignum_amontmul_p256.o \
      bignum_amontmul_p384.o \
      bignum_amontredc.o \
      bignum_amontsqr.o \
      bignum_amontsqr_p256.o \
      bignum_amontsqr_p384.o \
      bignum_bitfield.o \
      bignum_bitsize.o \
      bignum_cld.o \
      bignum_clz.o \
      bignum_cmadd.o \
      bignum_cmul.o \
      bignum_cmul_p256.o \
      bignum_cmul_p384.o \
      bignum_coprime.o \
      bignum_copy.o \
      bignum_ctd.o \
      bignum_ctz.o \
      bignum_deamont_p256.o \
      bignum_deamont_p384.o \
      bignum_demont.o \
      bignum_demont_p256.o \
      bignum_demont_p384.o \
      bignum_digit.o \
      bignum_digitsize.o \
      bignum_double_p256.o \
      bignum_double_p384.o \
      bignum_emontredc.o \
      bignum_emontredc_8n.o \
      bignum_eq.o \
      bignum_even.o \
      bignum_ge.o \
      bignum_gt.o \
      bignum_half_p256.o \
      bignum_half_p384.o \
      bignum_iszero.o \
      bignum_ksqr_16_32.o \
      bignum_le.o \
      bignum_lt.o \
      bignum_madd.o \
      bignum_mod_n256.o \
      bignum_mod_n256_4.o \
      bignum_mod_n384.o \
      bignum_mod_n384_6.o \
      bignum_mod_p256.o \
      bignum_mod_p256_4.o \
      bignum_mod_p384.o \
      bignum_mod_p384_6.o \
      bignum_modadd.o \
      bignum_moddouble.o \
      bignum_modifier.o \
      bignum_modinv.o \
      bignum_modoptneg.o \
      bignum_modsub.o \
      bignum_montifier.o \
      bignum_montmul.o \
      bignum_montmul_p256.o \
      bignum_montmul_p384.o \
      bignum_montredc.o \
      bignum_montsqr.o \
      bignum_montsqr_p256.o \
      bignum_montsqr_p384.o \
      bignum_mul.o \
      bignum_mul_4_8.o \
      bignum_mul_6_12.o \
      bignum_mul_8_16.o \
      bignum_mux.o \
      bignum_mux16.o \
      bignum_neg_p256.o \
      bignum_neg_p384.o \
      bignum_negmodinv.o \
      bignum_nonzero.o \
      bignum_normalize.o \
      bignum_odd.o \
      bignum_of_word.o \
      bignum_optadd.o \
      bignum_optneg.o \
      bignum_optneg_p256.o \
      bignum_optneg_p384.o \
      bignum_optsub.o \
      bignum_optsubadd.o \
      bignum_pow2.o \
      bignum_shl_small.o \
      bignum_shr_small.o \
      bignum_sqr_4_8.o \
      bignum_sqr_6_12.o \
      bignum_sqr_8_16.o \
      bignum_sub.o \
      bignum_sub_p256.o \
      bignum_sub_p384.o \
      bignum_tomont_p256.o \
      bignum_tomont_p384.o \
      bignum_triple_p256.o \
      bignum_triple_p384.o \
      word_clz.o \
      word_ctz.o \
      word_negmodinv.o

%.o : %.S ; cpp $< | $(GAS) -o $@ -

libs2nbignum.a: $(OBJ) ; ar -rc libs2nbignum.a $(OBJ)

clean:; rm -f libs2nbignum.a *.o *.correct

# Proof-related parts
#
# The proof files are all independent, though each one loads the
# same common infrastructure "base.ml". So you can potentially
# run the proofs in parallel for more speed, e.g.
#
#    nohup make -j 16 proofs &
#
# On debian, the underlying prover HOL Light can be installed as a package
# by something like
#
#    sudo apt-get install hol-light
#
# for which you would set this below:
#
#    HOLDIR=/usr/share/hol-light
#
# If you build hol-light yourself (see https://github.com/jrh13/hol-light)
# in your home directory, and do "make" inside the subdirectory hol-light,
# then the following HOLDIR setting should be right:

HOLDIR=$(HOME)/hol-light
HOLLIGHT:=HOLLIGHT_DIR=$(HOLDIR) ocaml -init $(HOLDIR)/hol.ml

PROOFS = $(OBJ:.o=.correct)

%.correct: %.ml %.o ; (cd ..; (echo 'loadt "Arm/base.ml";;'; echo 'loadt "Arm/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@

proofs: $(PROOFS);
