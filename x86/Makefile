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

OSTYPE_RESULT=$(shell uname -s)
ARCHTYPE_RESULT=$(shell uname -m)

# Add explicit language input parameter to cpp, otherwise the use of #n for
# numeric literals in ARM code is a problem when used inside #define macros
# since normally that means stringization.
#
# Some clang-based preprocessors seem to behave differently, and get confused
# by single-quote characters in comments, so we eliminate // comments first.

ifeq ($(OSTYPE_RESULT),Darwin)
PREPROCESS=sed -e 's/\/\/.*//' | cpp -xassembler-with-cpp -
else
PREPROCESS=cpp -xassembler-with-cpp -
endif

# Generally GNU-type assemblers are happy with multiple instructions on
# a line, but we split them up anyway just in case.

SPLIT=tr ';' '\n'

# Name mangling for OS X, adding an underscore to external symbols.
# This makes the functions accessible from C by their basic names.

ifeq ($(OSTYPE_RESULT),Darwin)
MANGLE=sed -e 's/bignum_/_bignum_/; s/word_/_word_/'
else
MANGLE=cat
endif

# If actually on an x86 machine, just use the assembler (as). Otherwise
# use a cross-assembling version so that the code can still be assembled
# and the proofs checked against the object files (though you won't be able
# to run code without additional emulation infrastructure). For the clang
# version on OS X we just add the "-arch x86_64" option. For the Linux/gcc
# toolchain we assume the presence of the special cross-assembler. This
# can be installed via something like:
#
#  sudo apt-get install binutils-x86-64-linux-gnu

ifeq ($(ARCHTYPE_RESULT),x86_64)
ASSEMBLE=as
else
ifeq ($(OSTYPE_RESULT),Darwin)
ASSEMBLE=as -arch x86_64
else
ASSEMBLE=x86_64-linux-gnu-as
endif
endif

# The x86 assembly (.S) files are all written for the GNU assembler

OBJ = fastmul/bignum_emontredc_8n.o \
      fastmul/bignum_kmul_16_32.o \
      fastmul/bignum_kmul_32_64.o \
      fastmul/bignum_ksqr_16_32.o \
      fastmul/bignum_ksqr_32_64.o \
      fastmul/bignum_mul_4_8.o \
      fastmul/bignum_mul_4_8_alt.o \
      fastmul/bignum_mul_6_12.o \
      fastmul/bignum_mul_6_12_alt.o \
      fastmul/bignum_mul_8_16.o \
      fastmul/bignum_mul_8_16_alt.o \
      fastmul/bignum_sqr_4_8.o \
      fastmul/bignum_sqr_4_8_alt.o \
      fastmul/bignum_sqr_6_12.o \
      fastmul/bignum_sqr_6_12_alt.o \
      fastmul/bignum_sqr_8_16.o \
      fastmul/bignum_sqr_8_16_alt.o \
      generic/bignum_add.o \
      generic/bignum_amontifier.o \
      generic/bignum_amontmul.o \
      generic/bignum_amontredc.o \
      generic/bignum_amontsqr.o \
      generic/bignum_bitfield.o \
      generic/bignum_bitsize.o \
      generic/bignum_cdiv.o \
      generic/bignum_cdiv_exact.o \
      generic/bignum_cld.o \
      generic/bignum_clz.o \
      generic/bignum_cmadd.o \
      generic/bignum_cmnegadd.o \
      generic/bignum_cmod.o \
      generic/bignum_cmul.o \
      generic/bignum_coprime.o \
      generic/bignum_copy.o \
      generic/bignum_ctd.o \
      generic/bignum_ctz.o \
      generic/bignum_demont.o \
      generic/bignum_digit.o \
      generic/bignum_digitsize.o \
      generic/bignum_divmod10.o \
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
      generic/bignum_muladd10.o \
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
      generic/bignum_sqr.o \
      generic/bignum_sub.o \
      generic/word_bytereverse.o \
      generic/word_clz.o \
      generic/word_ctz.o \
      generic/word_max.o \
      generic/word_min.o \
      generic/word_negmodinv.o \
      generic/word_recip.o \
      p256/bignum_add_p256.o \
      p256/bignum_bigendian_4.o \
      p256/bignum_cmul_p256.o \
      p256/bignum_cmul_p256_alt.o \
      p256/bignum_deamont_p256.o \
      p256/bignum_deamont_p256_alt.o \
      p256/bignum_demont_p256.o \
      p256/bignum_demont_p256_alt.o \
      p256/bignum_double_p256.o \
      p256/bignum_half_p256.o \
      p256/bignum_littleendian_4.o \
      p256/bignum_mod_n256.o \
      p256/bignum_mod_n256_alt.o \
      p256/bignum_mod_n256_4.o \
      p256/bignum_mod_p256.o \
      p256/bignum_mod_p256_alt.o \
      p256/bignum_mod_p256_4.o \
      p256/bignum_montmul_p256.o \
      p256/bignum_montmul_p256_alt.o \
      p256/bignum_montsqr_p256.o \
      p256/bignum_montsqr_p256_alt.o \
      p256/bignum_mux_4.o \
      p256/bignum_neg_p256.o \
      p256/bignum_nonzero_4.o \
      p256/bignum_optneg_p256.o \
      p256/bignum_sub_p256.o \
      p256/bignum_tomont_p256.o \
      p256/bignum_tomont_p256_alt.o \
      p256/bignum_triple_p256.o \
      p256/bignum_triple_p256_alt.o \
      p384/bignum_add_p384.o \
      p384/bignum_bigendian_6.o \
      p384/bignum_cmul_p384.o \
      p384/bignum_cmul_p384_alt.o \
      p384/bignum_deamont_p384.o \
      p384/bignum_deamont_p384_alt.o \
      p384/bignum_demont_p384.o \
      p384/bignum_demont_p384_alt.o \
      p384/bignum_double_p384.o \
      p384/bignum_half_p384.o \
      p384/bignum_littleendian_6.o \
      p384/bignum_mod_n384.o \
      p384/bignum_mod_n384_alt.o \
      p384/bignum_mod_n384_6.o \
      p384/bignum_mod_p384.o \
      p384/bignum_mod_p384_alt.o \
      p384/bignum_mod_p384_6.o \
      p384/bignum_montmul_p384.o \
      p384/bignum_montmul_p384_alt.o \
      p384/bignum_montsqr_p384.o \
      p384/bignum_montsqr_p384_alt.o \
      p384/bignum_mux_6.o \
      p384/bignum_neg_p384.o \
      p384/bignum_nonzero_6.o \
      p384/bignum_optneg_p384.o \
      p384/bignum_sub_p384.o \
      p384/bignum_tomont_p384.o \
      p384/bignum_tomont_p384_alt.o \
      p384/bignum_triple_p384.o \
      p384/bignum_triple_p384_alt.o \
      p521/bignum_add_p521.o \
      p521/bignum_cmul_p521.o \
      p521/bignum_deamont_p521.o \
      p521/bignum_demont_p521.o \
      p521/bignum_double_p521.o \
      p521/bignum_half_p521.o \
      p521/bignum_mod_n521_9.o \
      p521/bignum_mod_p521_9.o \
      p521/bignum_montmul_p521.o \
      p521/bignum_montmul_p521_alt.o \
      p521/bignum_montsqr_p521.o \
      p521/bignum_montsqr_p521_alt.o \
      p521/bignum_mul_p521.o \
      p521/bignum_mul_p521_alt.o \
      p521/bignum_neg_p521.o \
      p521/bignum_optneg_p521.o \
      p521/bignum_sqr_p521.o \
      p521/bignum_sqr_p521_alt.o \
      p521/bignum_sub_p521.o \
      p521/bignum_tomont_p521.o \
      p521/bignum_triple_p521.o \
      secp256k1/bignum_add_p256k1.o \
      secp256k1/bignum_cmul_p256k1.o \
      secp256k1/bignum_cmul_p256k1_alt.o \
      secp256k1/bignum_deamont_p256k1.o \
      secp256k1/bignum_demont_p256k1.o \
      secp256k1/bignum_double_p256k1.o \
      secp256k1/bignum_half_p256k1.o \
      secp256k1/bignum_mod_n256k1_4.o \
      secp256k1/bignum_mod_p256k1_4.o \
      secp256k1/bignum_montmul_p256k1.o \
      secp256k1/bignum_montmul_p256k1_alt.o \
      secp256k1/bignum_montsqr_p256k1.o \
      secp256k1/bignum_montsqr_p256k1_alt.o \
      secp256k1/bignum_mul_p256k1.o \
      secp256k1/bignum_mul_p256k1_alt.o \
      secp256k1/bignum_neg_p256k1.o \
      secp256k1/bignum_optneg_p256k1.o \
      secp256k1/bignum_sqr_p256k1.o \
      secp256k1/bignum_sqr_p256k1_alt.o \
      secp256k1/bignum_sub_p256k1.o \
      secp256k1/bignum_tomont_p256k1.o \
      secp256k1/bignum_tomont_p256k1_alt.o \
      secp256k1/bignum_triple_p256k1.o \
      secp256k1/bignum_triple_p256k1_alt.o

.PHONY: bmi clean clobber

%.o : %.S ; cat $< | $(PREPROCESS) | $(SPLIT) | $(MANGLE) | $(ASSEMBLE) -o $@ -

libs2nbignum.a: $(OBJ) ; ar -rc libs2nbignum.a $(OBJ)

clean:; rm -f libs2nbignum.a */*.o */*.correct

# Dynamically regenerate or destroy the files recording which functions
# use BMI and/or ADX instructions in the x86 versions. These won't run
# on some older x86 machines

yesbmi_functions: $(OBJ) ; for i in */*.o; do objdump -d $$i | (egrep -qi '(mulx|adcx|adox)' && grep '\.globl' `echo $$i | sed -e 's/o$$/S/'`) ; done | sed -e 's/.globl//; s/ *//g' | sort >yesbmi_functions
nonbmi_functions: $(OBJ) ; for i in */*.o; do objdump -d $$i | (egrep -qi '(mulx|adcx|adox)' || grep '\.globl' `echo $$i | sed -e 's/o$$/S/'`) ; done | sed -e 's/.globl//; s/ *//g' | sort >nonbmi_functions

bmi: yesbmi_functions nonbmi_functions ; [ `cat ???bmi_functions | sort | uniq | wc -l` -eq `grep '^extern' ../include/s2n-bignum.h | wc -l` ]

clobber: clean ; rm -f yesbmi_functions nonbmi_functions

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

HOLDIR?=$(HOME)/hol-light
HOLLIGHT:=HOLLIGHT_DIR=$(HOLDIR) ocaml -init $(HOLDIR)/hol.ml

PROOFS = $(OBJ:.o=.correct)

fastmul/%.correct: proofs/%.ml fastmul/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@
generic/%.correct: proofs/%.ml generic/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@
p256/%.correct: proofs/%.ml p256/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@
p384/%.correct: proofs/%.ml p384/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@
p521/%.correct: proofs/%.ml p521/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@
secp256k1/%.correct: proofs/%.ml secp256k1/%.o ; (cd ..; (echo 'loadt "x86/proofs/base.ml";;'; echo 'loadt "x86/proofs/$*.ml";;') | $(HOLLIGHT) 2>&1) >$@

run_proofs: $(PROOFS);

proofs: run_proofs ; [ `grep SUBROUTINE_CORRECT proofs/*.ml | wc -l` -eq  `grep 'SUBROUTINE_CORRECT : thm' */*.correct | wc -l` ]
