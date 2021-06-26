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

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = fastmul/bignum_emontredc_8n.o \
      fastmul/bignum_kmul_16_32.o \
      fastmul/bignum_ksqr_16_32.o \
      fastmul/bignum_ksqr_32_64.o \
      fastmul/bignum_mul_4_8.o \
      fastmul/bignum_mul_6_12.o \
      fastmul/bignum_mul_8_16.o \
      fastmul/bignum_sqr_4_8.o \
      fastmul/bignum_sqr_6_12.o \
      fastmul/bignum_sqr_8_16.o \
      generic/bignum_add.o \
      generic/bignum_amontifier.o \
      generic/bignum_amontmul.o \
      generic/bignum_amontredc.o \
      generic/bignum_amontsqr.o \
      generic/bignum_bitfield.o \
      generic/bignum_bitsize.o \
      generic/bignum_cld.o \
      generic/bignum_clz.o \
      generic/bignum_cmadd.o \
      generic/bignum_cmul.o \
      generic/bignum_coprime.o \
      generic/bignum_copy.o \
      generic/bignum_ctd.o \
      generic/bignum_ctz.o \
      generic/bignum_demont.o \
      generic/bignum_digit.o \
      generic/bignum_digitsize.o \
      generic/bignum_emontredc.o \
      generic/bignum_eq.o \
      generic/bignum_even.o \
      generic/bignum_ge.o \
      generic/bignum_gt.o \
      generic/bignum_iszero.o \
      generic/bignum_le.o \
      generic/bignum_lt.o \
      generic/bignum_madd.o \
      generic/bignum_modadd.o \
      generic/bignum_moddouble.o \
      generic/bignum_modifier.o \
      generic/bignum_modinv.o \
      generic/bignum_modoptneg.o \
      generic/bignum_modsub.o \
      generic/bignum_montifier.o \
      generic/bignum_montmul.o \
      generic/bignum_montredc.o \
      generic/bignum_montsqr.o \
      generic/bignum_mul.o \
      generic/bignum_mux.o \
      generic/bignum_mux16.o \
      generic/bignum_negmodinv.o \
      generic/bignum_nonzero.o \
      generic/bignum_normalize.o \
      generic/bignum_odd.o \
      generic/bignum_of_word.o \
      generic/bignum_optadd.o \
      generic/bignum_optneg.o \
      generic/bignum_optsub.o \
      generic/bignum_optsubadd.o \
      generic/bignum_pow2.o \
      generic/bignum_shl_small.o \
      generic/bignum_shr_small.o \
      generic/bignum_sub.o \
      generic/word_bytereverse.o \
      generic/word_clz.o \
      generic/word_ctz.o \
      generic/word_negmodinv.o \
      p256/bignum_add_p256.o \
      p256/bignum_amontmul_p256.o \
      p256/bignum_amontsqr_p256.o \
      p256/bignum_bigendian_4.o \
      p256/bignum_cmul_p256.o \
      p256/bignum_deamont_p256.o \
      p256/bignum_demont_p256.o \
      p256/bignum_double_p256.o \
      p256/bignum_half_p256.o \
      p256/bignum_mod_n256.o \
      p256/bignum_mod_n256_4.o \
      p256/bignum_mod_p256.o \
      p256/bignum_mod_p256_4.o \
      p256/bignum_montmul_p256.o \
      p256/bignum_montsqr_p256.o \
      p256/bignum_neg_p256.o \
      p256/bignum_optneg_p256.o \
      p256/bignum_sub_p256.o \
      p256/bignum_tomont_p256.o \
      p256/bignum_triple_p256.o \
      p384/bignum_add_p384.o \
      p384/bignum_amontmul_p384.o \
      p384/bignum_amontsqr_p384.o \
      p384/bignum_bigendian_6.o \
      p384/bignum_cmul_p384.o \
      p384/bignum_deamont_p384.o \
      p384/bignum_demont_p384.o \
      p384/bignum_double_p384.o \
      p384/bignum_half_p384.o \
      p384/bignum_mod_n384.o \
      p384/bignum_mod_n384_6.o \
      p384/bignum_mod_p384.o \
      p384/bignum_mod_p384_6.o \
      p384/bignum_montmul_p384.o \
      p384/bignum_montsqr_p384.o \
      p384/bignum_neg_p384.o \
      p384/bignum_optneg_p384.o \
      p384/bignum_sub_p384.o \
      p384/bignum_tomont_p384.o \
      p384/bignum_triple_p384.o

%.o : %.S ; cpp $< | as -o $@ -

libs2nbignum.a: $(OBJ) ; ar -rc libs2nbignum.a $(OBJ)

clean:; rm -f libs2nbignum.a */*.o */*.correct

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

fastmul/%.correct: proofs/%.ml fastmul/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@
generic/%.correct: proofs/%.ml generic/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@
p256/%.correct: proofs/%.ml p256/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@
p384/%.correct: proofs/%.ml p384/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@

proofs: $(PROOFS);
