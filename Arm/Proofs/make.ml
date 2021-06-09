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

loadt "Arm/Proofs/instruction.ml";;
loadt "Arm/Proofs/decode.ml";;
loadt "Arm/Proofs/arm.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "Common/bignum.ml";;

(* ------------------------------------------------------------------------- *)
(* Load the individual proofs (in alphabetical order)                        *)
(* ------------------------------------------------------------------------- *)

loadt "Arm/Proofs/bignum_add.ml";;
loadt "Arm/Proofs/bignum_add_p256.ml";;
loadt "Arm/Proofs/bignum_add_p384.ml";;
loadt "Arm/Proofs/bignum_amontifier.ml";;
loadt "Arm/Proofs/bignum_amontmul.ml";;
loadt "Arm/Proofs/bignum_amontmul_p256.ml";;
loadt "Arm/Proofs/bignum_amontmul_p384.ml";;
loadt "Arm/Proofs/bignum_amontredc.ml";;
loadt "Arm/Proofs/bignum_amontsqr.ml";;
loadt "Arm/Proofs/bignum_amontsqr_p256.ml";;
loadt "Arm/Proofs/bignum_amontsqr_p384.ml";;
loadt "Arm/Proofs/bignum_bitfield.ml";;
loadt "Arm/Proofs/bignum_bitsize.ml";;
loadt "Arm/Proofs/bignum_cld.ml";;
loadt "Arm/Proofs/bignum_clz.ml";;
loadt "Arm/Proofs/bignum_cmadd.ml";;
loadt "Arm/Proofs/bignum_cmul.ml";;
loadt "Arm/Proofs/bignum_cmul_p256.ml";;
loadt "Arm/Proofs/bignum_cmul_p384.ml";;
loadt "Arm/Proofs/bignum_coprime.ml";;
loadt "Arm/Proofs/bignum_copy.ml";;
loadt "Arm/Proofs/bignum_ctd.ml";;
loadt "Arm/Proofs/bignum_ctz.ml";;
loadt "Arm/Proofs/bignum_deamont_p256.ml";;
loadt "Arm/Proofs/bignum_deamont_p384.ml";;
loadt "Arm/Proofs/bignum_demont.ml";;
loadt "Arm/Proofs/bignum_demont_p256.ml";;
loadt "Arm/Proofs/bignum_demont_p384.ml";;
loadt "Arm/Proofs/bignum_digit.ml";;
loadt "Arm/Proofs/bignum_digitsize.ml";;
loadt "Arm/Proofs/bignum_double_p256.ml";;
loadt "Arm/Proofs/bignum_double_p384.ml";;
loadt "Arm/Proofs/bignum_emontredc.ml";;
loadt "Arm/Proofs/bignum_emontredc_8n.ml";;
loadt "Arm/Proofs/bignum_eq.ml";;
loadt "Arm/Proofs/bignum_even.ml";;
loadt "Arm/Proofs/bignum_ge.ml";;
loadt "Arm/Proofs/bignum_gt.ml";;
loadt "Arm/Proofs/bignum_half_p256.ml";;
loadt "Arm/Proofs/bignum_half_p384.ml";;
loadt "Arm/Proofs/bignum_iszero.ml";;
loadt "Arm/Proofs/bignum_le.ml";;
loadt "Arm/Proofs/bignum_lt.ml";;
loadt "Arm/Proofs/bignum_madd.ml";;
loadt "Arm/Proofs/bignum_mod_n256.ml";;
loadt "Arm/Proofs/bignum_mod_n256_4.ml";;
loadt "Arm/Proofs/bignum_mod_n384.ml";;
loadt "Arm/Proofs/bignum_mod_n384_6.ml";;
loadt "Arm/Proofs/bignum_mod_p256.ml";;
loadt "Arm/Proofs/bignum_mod_p256_4.ml";;
loadt "Arm/Proofs/bignum_mod_p384.ml";;
loadt "Arm/Proofs/bignum_mod_p384_6.ml";;
loadt "Arm/Proofs/bignum_modadd.ml";;
loadt "Arm/Proofs/bignum_moddouble.ml";;
loadt "Arm/Proofs/bignum_modifier.ml";;
loadt "Arm/Proofs/bignum_modinv.ml";;
loadt "Arm/Proofs/bignum_modoptneg.ml";;
loadt "Arm/Proofs/bignum_modsub.ml";;
loadt "Arm/Proofs/bignum_montifier.ml";;
loadt "Arm/Proofs/bignum_montmul.ml";;
loadt "Arm/Proofs/bignum_montmul_p256.ml";;
loadt "Arm/Proofs/bignum_montmul_p384.ml";;
loadt "Arm/Proofs/bignum_montredc.ml";;
loadt "Arm/Proofs/bignum_montsqr.ml";;
loadt "Arm/Proofs/bignum_montsqr_p256.ml";;
loadt "Arm/Proofs/bignum_montsqr_p384.ml";;
loadt "Arm/Proofs/bignum_mul.ml";;
loadt "Arm/Proofs/bignum_mul_4_8.ml";;
loadt "Arm/Proofs/bignum_mul_6_12.ml";;
loadt "Arm/Proofs/bignum_mul_8_16.ml";;
loadt "Arm/Proofs/bignum_mux.ml";;
loadt "Arm/Proofs/bignum_mux16.ml";;
loadt "Arm/Proofs/bignum_neg_p256.ml";;
loadt "Arm/Proofs/bignum_neg_p384.ml";;
loadt "Arm/Proofs/bignum_negmodinv.ml";;
loadt "Arm/Proofs/bignum_nonzero.ml";;
loadt "Arm/Proofs/bignum_normalize.ml";;
loadt "Arm/Proofs/bignum_odd.ml";;
loadt "Arm/Proofs/bignum_of_word.ml";;
loadt "Arm/Proofs/bignum_optadd.ml";;
loadt "Arm/Proofs/bignum_optneg.ml";;
loadt "Arm/Proofs/bignum_optneg_p256.ml";;
loadt "Arm/Proofs/bignum_optneg_p384.ml";;
loadt "Arm/Proofs/bignum_optsub.ml";;
loadt "Arm/Proofs/bignum_optsubadd.ml";;
loadt "Arm/Proofs/bignum_pow2.ml";;
loadt "Arm/Proofs/bignum_shl_small.ml";;
loadt "Arm/Proofs/bignum_shr_small.ml";;
loadt "Arm/Proofs/bignum_sqr_4_8.ml";;
loadt "Arm/Proofs/bignum_sqr_6_12.ml";;
loadt "Arm/Proofs/bignum_sqr_8_16.ml";;
loadt "Arm/Proofs/bignum_sub.ml";;
loadt "Arm/Proofs/bignum_sub_p256.ml";;
loadt "Arm/Proofs/bignum_sub_p384.ml";;
loadt "Arm/Proofs/bignum_tomont_p256.ml";;
loadt "Arm/Proofs/bignum_tomont_p384.ml";;
loadt "Arm/Proofs/bignum_triple_p256.ml";;
loadt "Arm/Proofs/bignum_triple_p384.ml";;
loadt "Arm/Proofs/word_clz.ml";;
loadt "Arm/Proofs/word_ctz.ml";;
loadt "Arm/Proofs/word_negmodinv.ml";;
