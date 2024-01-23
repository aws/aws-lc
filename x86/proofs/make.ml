(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Load all x86 bignum proofs in alphabetical order.                         *)
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

loadt "x86/proofs/instruction.ml";;
loadt "x86/proofs/decode.ml";;
loadt "x86/proofs/x86.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "common/bignum.ml";;

(* ------------------------------------------------------------------------- *)
(* Load the individual proofs (in alphabetical order)                        *)
(* ------------------------------------------------------------------------- *)

loadt "x86/proofs/bignum_add.ml";;
loadt "x86/proofs/bignum_add_p256.ml";;
loadt "x86/proofs/bignum_add_p384.ml";;
loadt "x86/proofs/bignum_amontifier.ml";;
loadt "x86/proofs/bignum_amontmul.ml";;
loadt "x86/proofs/bignum_amontredc.ml";;
loadt "x86/proofs/bignum_amontsqr.ml";;
loadt "x86/proofs/bignum_bigendian_4.ml";;
loadt "x86/proofs/bignum_bigendian_6.ml";;
loadt "x86/proofs/bignum_bitfield.ml";;
loadt "x86/proofs/bignum_bitsize.ml";;
loadt "x86/proofs/bignum_cld.ml";;
loadt "x86/proofs/bignum_clz.ml";;
loadt "x86/proofs/bignum_cmadd.ml";;
loadt "x86/proofs/bignum_cmul.ml";;
loadt "x86/proofs/bignum_cmul_p256.ml";;
loadt "x86/proofs/bignum_cmul_p384.ml";;
loadt "x86/proofs/bignum_coprime.ml";;
loadt "x86/proofs/bignum_copy.ml";;
loadt "x86/proofs/bignum_ctd.ml";;
loadt "x86/proofs/bignum_ctz.ml";;
loadt "x86/proofs/bignum_deamont_p256.ml";;
loadt "x86/proofs/bignum_deamont_p384.ml";;
loadt "x86/proofs/bignum_demont.ml";;
loadt "x86/proofs/bignum_demont_p256.ml";;
loadt "x86/proofs/bignum_demont_p384.ml";;
loadt "x86/proofs/bignum_digit.ml";;
loadt "x86/proofs/bignum_digitsize.ml";;
loadt "x86/proofs/bignum_double_p256.ml";;
loadt "x86/proofs/bignum_double_p384.ml";;
loadt "x86/proofs/bignum_emontredc.ml";;
loadt "x86/proofs/bignum_emontredc_8n.ml";;
loadt "x86/proofs/bignum_eq.ml";;
loadt "x86/proofs/bignum_even.ml";;
loadt "x86/proofs/bignum_ge.ml";;
loadt "x86/proofs/bignum_gt.ml";;
loadt "x86/proofs/bignum_half_p256.ml";;
loadt "x86/proofs/bignum_half_p384.ml";;
loadt "x86/proofs/bignum_iszero.ml";;
loadt "x86/proofs/bignum_kmul_16_32.ml";;
loadt "x86/proofs/bignum_ksqr_16_32.ml";;
loadt "x86/proofs/bignum_ksqr_32_64.ml";;
loadt "x86/proofs/bignum_le.ml";;
loadt "x86/proofs/bignum_lt.ml";;
loadt "x86/proofs/bignum_madd.ml";;
loadt "x86/proofs/bignum_mod_n256.ml";;
loadt "x86/proofs/bignum_mod_n256_4.ml";;
loadt "x86/proofs/bignum_mod_n384.ml";;
loadt "x86/proofs/bignum_mod_n384_6.ml";;
loadt "x86/proofs/bignum_mod_p256.ml";;
loadt "x86/proofs/bignum_mod_p256_4.ml";;
loadt "x86/proofs/bignum_mod_p384.ml";;
loadt "x86/proofs/bignum_mod_p384_6.ml";;
loadt "x86/proofs/bignum_modadd.ml";;
loadt "x86/proofs/bignum_moddouble.ml";;
loadt "x86/proofs/bignum_modifier.ml";;
loadt "x86/proofs/bignum_modinv.ml";;
loadt "x86/proofs/bignum_modoptneg.ml";;
loadt "x86/proofs/bignum_modsub.ml";;
loadt "x86/proofs/bignum_montifier.ml";;
loadt "x86/proofs/bignum_montmul.ml";;
loadt "x86/proofs/bignum_montmul_p256.ml";;
loadt "x86/proofs/bignum_montmul_p384.ml";;
loadt "x86/proofs/bignum_montredc.ml";;
loadt "x86/proofs/bignum_montsqr.ml";;
loadt "x86/proofs/bignum_montsqr_p256.ml";;
loadt "x86/proofs/bignum_montsqr_p384.ml";;
loadt "x86/proofs/bignum_mul.ml";;
loadt "x86/proofs/bignum_mul_4_8.ml";;
loadt "x86/proofs/bignum_mul_6_12.ml";;
loadt "x86/proofs/bignum_mul_8_16.ml";;
loadt "x86/proofs/bignum_mux.ml";;
loadt "x86/proofs/bignum_mux16.ml";;
loadt "x86/proofs/bignum_mux_4.ml";;
loadt "x86/proofs/bignum_mux_6.ml";;
loadt "x86/proofs/bignum_neg_p256.ml";;
loadt "x86/proofs/bignum_neg_p384.ml";;
loadt "x86/proofs/bignum_negmodinv.ml";;
loadt "x86/proofs/bignum_nonzero.ml";;
loadt "x86/proofs/bignum_nonzero_4.ml";;
loadt "x86/proofs/bignum_nonzero_6.ml";;
loadt "x86/proofs/bignum_normalize.ml";;
loadt "x86/proofs/bignum_odd.ml";;
loadt "x86/proofs/bignum_of_word.ml";;
loadt "x86/proofs/bignum_optadd.ml";;
loadt "x86/proofs/bignum_optneg.ml";;
loadt "x86/proofs/bignum_optneg_p256.ml";;
loadt "x86/proofs/bignum_optneg_p384.ml";;
loadt "x86/proofs/bignum_optsub.ml";;
loadt "x86/proofs/bignum_optsubadd.ml";;
loadt "x86/proofs/bignum_pow2.ml";;
loadt "x86/proofs/bignum_shl_small.ml";;
loadt "x86/proofs/bignum_shr_small.ml";;
loadt "x86/proofs/bignum_sqr_4_8.ml";;
loadt "x86/proofs/bignum_sqr_6_12.ml";;
loadt "x86/proofs/bignum_sqr_8_16.ml";;
loadt "x86/proofs/bignum_sub.ml";;
loadt "x86/proofs/bignum_sub_p256.ml";;
loadt "x86/proofs/bignum_sub_p384.ml";;
loadt "x86/proofs/bignum_tomont_p256.ml";;
loadt "x86/proofs/bignum_tomont_p384.ml";;
loadt "x86/proofs/bignum_triple_p256.ml";;
loadt "x86/proofs/bignum_triple_p384.ml";;
loadt "x86/proofs/word_bytereverse.ml";;
loadt "x86/proofs/word_clz.ml";;
loadt "x86/proofs/word_ctz.ml";;
loadt "x86/proofs/word_negmodinv.ml";;
