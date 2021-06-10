(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Load all ARM bignum proofs in alphabetical order.                         *)
(* ========================================================================= *)

loadt "update_database.ml";;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Some background theory from the standard libraries.                       *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;
needs "Library/rstc.ml";;
needs "Library/bitsize.ml";;
needs "Library/pocklington.ml";;
needs "Library/integer.ml";;
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;

(* ------------------------------------------------------------------------- *)
(* common ARM-x86 proof infrastructure.                                      *)
(* ------------------------------------------------------------------------- *)

loadt "common/overlap.ml";;
loadt "common/for_hollight.ml";;
loadt "common/words2.ml";;
loadt "common/misc.ml";;
loadt "common/components.ml";;
loadt "common/records.ml";;
loadt "common/relational.ml";;
loadt "common/interval.ml";;
loadt "common/elf.ml";;

loadt "arm/proofs/instruction.ml";;
loadt "arm/proofs/decode.ml";;
loadt "arm/proofs/arm.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "common/bignum.ml";;

(* ------------------------------------------------------------------------- *)
(* Load the individual proofs (in alphabetical order)                        *)
(* ------------------------------------------------------------------------- *)

loadt "arm/proofs/bignum_add.ml";;
loadt "arm/proofs/bignum_add_p256.ml";;
loadt "arm/proofs/bignum_add_p384.ml";;
loadt "arm/proofs/bignum_amontifier.ml";;
loadt "arm/proofs/bignum_amontmul.ml";;
loadt "arm/proofs/bignum_amontmul_p256.ml";;
loadt "arm/proofs/bignum_amontmul_p384.ml";;
loadt "arm/proofs/bignum_amontredc.ml";;
loadt "arm/proofs/bignum_amontsqr.ml";;
loadt "arm/proofs/bignum_amontsqr_p256.ml";;
loadt "arm/proofs/bignum_amontsqr_p384.ml";;
loadt "arm/proofs/bignum_bitfield.ml";;
loadt "arm/proofs/bignum_bitsize.ml";;
loadt "arm/proofs/bignum_cld.ml";;
loadt "arm/proofs/bignum_clz.ml";;
loadt "arm/proofs/bignum_cmadd.ml";;
loadt "arm/proofs/bignum_cmul.ml";;
loadt "arm/proofs/bignum_cmul_p256.ml";;
loadt "arm/proofs/bignum_cmul_p384.ml";;
loadt "arm/proofs/bignum_coprime.ml";;
loadt "arm/proofs/bignum_copy.ml";;
loadt "arm/proofs/bignum_ctd.ml";;
loadt "arm/proofs/bignum_ctz.ml";;
loadt "arm/proofs/bignum_deamont_p256.ml";;
loadt "arm/proofs/bignum_deamont_p384.ml";;
loadt "arm/proofs/bignum_demont.ml";;
loadt "arm/proofs/bignum_demont_p256.ml";;
loadt "arm/proofs/bignum_demont_p384.ml";;
loadt "arm/proofs/bignum_digit.ml";;
loadt "arm/proofs/bignum_digitsize.ml";;
loadt "arm/proofs/bignum_double_p256.ml";;
loadt "arm/proofs/bignum_double_p384.ml";;
loadt "arm/proofs/bignum_emontredc.ml";;
loadt "arm/proofs/bignum_emontredc_8n.ml";;
loadt "arm/proofs/bignum_eq.ml";;
loadt "arm/proofs/bignum_even.ml";;
loadt "arm/proofs/bignum_ge.ml";;
loadt "arm/proofs/bignum_gt.ml";;
loadt "arm/proofs/bignum_half_p256.ml";;
loadt "arm/proofs/bignum_half_p384.ml";;
loadt "arm/proofs/bignum_iszero.ml";;
loadt "arm/proofs/bignum_le.ml";;
loadt "arm/proofs/bignum_lt.ml";;
loadt "arm/proofs/bignum_madd.ml";;
loadt "arm/proofs/bignum_mod_n256.ml";;
loadt "arm/proofs/bignum_mod_n256_4.ml";;
loadt "arm/proofs/bignum_mod_n384.ml";;
loadt "arm/proofs/bignum_mod_n384_6.ml";;
loadt "arm/proofs/bignum_mod_p256.ml";;
loadt "arm/proofs/bignum_mod_p256_4.ml";;
loadt "arm/proofs/bignum_mod_p384.ml";;
loadt "arm/proofs/bignum_mod_p384_6.ml";;
loadt "arm/proofs/bignum_modadd.ml";;
loadt "arm/proofs/bignum_moddouble.ml";;
loadt "arm/proofs/bignum_modifier.ml";;
loadt "arm/proofs/bignum_modinv.ml";;
loadt "arm/proofs/bignum_modoptneg.ml";;
loadt "arm/proofs/bignum_modsub.ml";;
loadt "arm/proofs/bignum_montifier.ml";;
loadt "arm/proofs/bignum_montmul.ml";;
loadt "arm/proofs/bignum_montmul_p256.ml";;
loadt "arm/proofs/bignum_montmul_p384.ml";;
loadt "arm/proofs/bignum_montredc.ml";;
loadt "arm/proofs/bignum_montsqr.ml";;
loadt "arm/proofs/bignum_montsqr_p256.ml";;
loadt "arm/proofs/bignum_montsqr_p384.ml";;
loadt "arm/proofs/bignum_mul.ml";;
loadt "arm/proofs/bignum_mul_4_8.ml";;
loadt "arm/proofs/bignum_mul_6_12.ml";;
loadt "arm/proofs/bignum_mul_8_16.ml";;
loadt "arm/proofs/bignum_mux.ml";;
loadt "arm/proofs/bignum_mux16.ml";;
loadt "arm/proofs/bignum_neg_p256.ml";;
loadt "arm/proofs/bignum_neg_p384.ml";;
loadt "arm/proofs/bignum_negmodinv.ml";;
loadt "arm/proofs/bignum_nonzero.ml";;
loadt "arm/proofs/bignum_normalize.ml";;
loadt "arm/proofs/bignum_odd.ml";;
loadt "arm/proofs/bignum_of_word.ml";;
loadt "arm/proofs/bignum_optadd.ml";;
loadt "arm/proofs/bignum_optneg.ml";;
loadt "arm/proofs/bignum_optneg_p256.ml";;
loadt "arm/proofs/bignum_optneg_p384.ml";;
loadt "arm/proofs/bignum_optsub.ml";;
loadt "arm/proofs/bignum_optsubadd.ml";;
loadt "arm/proofs/bignum_pow2.ml";;
loadt "arm/proofs/bignum_shl_small.ml";;
loadt "arm/proofs/bignum_shr_small.ml";;
loadt "arm/proofs/bignum_sqr_4_8.ml";;
loadt "arm/proofs/bignum_sqr_6_12.ml";;
loadt "arm/proofs/bignum_sqr_8_16.ml";;
loadt "arm/proofs/bignum_sub.ml";;
loadt "arm/proofs/bignum_sub_p256.ml";;
loadt "arm/proofs/bignum_sub_p384.ml";;
loadt "arm/proofs/bignum_tomont_p256.ml";;
loadt "arm/proofs/bignum_tomont_p384.ml";;
loadt "arm/proofs/bignum_triple_p256.ml";;
loadt "arm/proofs/bignum_triple_p384.ml";;
loadt "arm/proofs/word_clz.ml";;
loadt "arm/proofs/word_ctz.ml";;
loadt "arm/proofs/word_negmodinv.ml";;
