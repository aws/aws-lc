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
      word_negmodinv.o \

%.o : %.asm ; nasm -felf64 $<

libs2nbignum.a: $(OBJ) ; ar -rc libs2nbignum.a $(OBJ)

clean:; rm -f libs2nbignum.a *.o
