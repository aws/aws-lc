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
(* Common ARM-X86 proof infrastructure.                                      *)
(* ------------------------------------------------------------------------- *)

loadt "Common/overlap.ml";;
loadt "Common/for_hollight.ml";;
loadt "Common/words2.ml";;
loadt "Common/misc.ml";;
loadt "Common/components.ml";;
loadt "Common/records.ml";;
loadt "Common/relational.ml";;
loadt "Common/interval.ml";;
loadt "Common/elf.ml";;

loadt "Arm/instruction.ml";;
loadt "Arm/decode.ml";;
loadt "Arm/arm.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "Common/bignum.ml";;

(* ------------------------------------------------------------------------- *)
(* Load the individual proofs (in alphabetical order)                        *)
(* ------------------------------------------------------------------------- *)

loadt "Arm/bignum_add.ml";;
loadt "Arm/bignum_add_p256.ml";;
loadt "Arm/bignum_add_p384.ml";;
loadt "Arm/bignum_amontifier.ml";;
loadt "Arm/bignum_amontmul.ml";;
loadt "Arm/bignum_amontmul_p256.ml";;
loadt "Arm/bignum_amontmul_p384.ml";;
loadt "Arm/bignum_amontredc.ml";;
loadt "Arm/bignum_amontsqr.ml";;
loadt "Arm/bignum_amontsqr_p256.ml";;
loadt "Arm/bignum_amontsqr_p384.ml";;
loadt "Arm/bignum_bitfield.ml";;
loadt "Arm/bignum_bitsize.ml";;
loadt "Arm/bignum_cld.ml";;
loadt "Arm/bignum_clz.ml";;
loadt "Arm/bignum_cmadd.ml";;
loadt "Arm/bignum_cmul.ml";;
loadt "Arm/bignum_cmul_p256.ml";;
loadt "Arm/bignum_cmul_p384.ml";;
loadt "Arm/bignum_coprime.ml";;
loadt "Arm/bignum_copy.ml";;
loadt "Arm/bignum_ctd.ml";;
loadt "Arm/bignum_ctz.ml";;
loadt "Arm/bignum_deamont_p256.ml";;
loadt "Arm/bignum_deamont_p384.ml";;
loadt "Arm/bignum_demont.ml";;
loadt "Arm/bignum_demont_p256.ml";;
loadt "Arm/bignum_demont_p384.ml";;
loadt "Arm/bignum_digit.ml";;
loadt "Arm/bignum_digitsize.ml";;
loadt "Arm/bignum_double_p256.ml";;
loadt "Arm/bignum_double_p384.ml";;
loadt "Arm/bignum_emontredc.ml";;
loadt "Arm/bignum_emontredc_8n.ml";;
loadt "Arm/bignum_eq.ml";;
loadt "Arm/bignum_even.ml";;
loadt "Arm/bignum_ge.ml";;
loadt "Arm/bignum_gt.ml";;
loadt "Arm/bignum_half_p256.ml";;
loadt "Arm/bignum_half_p384.ml";;
loadt "Arm/bignum_iszero.ml";;
loadt "Arm/bignum_le.ml";;
loadt "Arm/bignum_lt.ml";;
loadt "Arm/bignum_madd.ml";;
loadt "Arm/bignum_mod_n256.ml";;
loadt "Arm/bignum_mod_n256_4.ml";;
loadt "Arm/bignum_mod_n384.ml";;
loadt "Arm/bignum_mod_n384_6.ml";;
loadt "Arm/bignum_mod_p256.ml";;
loadt "Arm/bignum_mod_p256_4.ml";;
loadt "Arm/bignum_mod_p384.ml";;
loadt "Arm/bignum_mod_p384_6.ml";;
loadt "Arm/bignum_modadd.ml";;
loadt "Arm/bignum_moddouble.ml";;
loadt "Arm/bignum_modifier.ml";;
loadt "Arm/bignum_modinv.ml";;
loadt "Arm/bignum_modoptneg.ml";;
loadt "Arm/bignum_modsub.ml";;
loadt "Arm/bignum_montifier.ml";;
loadt "Arm/bignum_montmul.ml";;
loadt "Arm/bignum_montmul_p256.ml";;
loadt "Arm/bignum_montmul_p384.ml";;
loadt "Arm/bignum_montredc.ml";;
loadt "Arm/bignum_montsqr.ml";;
loadt "Arm/bignum_montsqr_p256.ml";;
loadt "Arm/bignum_montsqr_p384.ml";;
loadt "Arm/bignum_mul.ml";;
loadt "Arm/bignum_mul_4_8.ml";;
loadt "Arm/bignum_mul_6_12.ml";;
loadt "Arm/bignum_mul_8_16.ml";;
loadt "Arm/bignum_mux.ml";;
loadt "Arm/bignum_mux16.ml";;
loadt "Arm/bignum_neg_p256.ml";;
loadt "Arm/bignum_neg_p384.ml";;
loadt "Arm/bignum_negmodinv.ml";;
loadt "Arm/bignum_nonzero.ml";;
loadt "Arm/bignum_normalize.ml";;
loadt "Arm/bignum_odd.ml";;
loadt "Arm/bignum_of_word.ml";;
loadt "Arm/bignum_optadd.ml";;
loadt "Arm/bignum_optneg.ml";;
loadt "Arm/bignum_optneg_p256.ml";;
loadt "Arm/bignum_optneg_p384.ml";;
loadt "Arm/bignum_optsub.ml";;
loadt "Arm/bignum_optsubadd.ml";;
loadt "Arm/bignum_pow2.ml";;
loadt "Arm/bignum_shl_small.ml";;
loadt "Arm/bignum_shr_small.ml";;
loadt "Arm/bignum_sqr_4_8.ml";;
loadt "Arm/bignum_sqr_6_12.ml";;
loadt "Arm/bignum_sqr_8_16.ml";;
loadt "Arm/bignum_sub.ml";;
loadt "Arm/bignum_sub_p256.ml";;
loadt "Arm/bignum_sub_p384.ml";;
loadt "Arm/bignum_tomont_p256.ml";;
loadt "Arm/bignum_tomont_p384.ml";;
loadt "Arm/bignum_triple_p256.ml";;
loadt "Arm/bignum_triple_p384.ml";;
loadt "Arm/word_clz.ml";;
loadt "Arm/word_ctz.ml";;
loadt "Arm/word_negmodinv.ml";;
