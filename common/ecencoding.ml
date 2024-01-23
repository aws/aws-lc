(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Additional encoding etc. used in elliptic curve point operations.         *)
(* ========================================================================= *)

let bignum_pair_from_memory = new_definition
 `bignum_pair_from_memory (a,k) s =
  (bignum_from_memory (a,k) s,
   bignum_from_memory (word_add a (word(8 * k)),k) s)`;;

let bignum_triple_from_memory = new_definition
 `bignum_triple_from_memory (a,k) s =
  (bignum_from_memory (a,k) s,
   bignum_from_memory (word_add a (word(8 * k)),k) s,
   bignum_from_memory (word_add a (word(16 * k)),k) s)`;;

let bignum_quadruple_from_memory = new_definition
 `bignum_quadruple_from_memory (a,k) s =
  (bignum_from_memory (a,k) s,
   bignum_from_memory (word_add a (word(8 * k)),k) s,
   bignum_from_memory (word_add a (word(16 * k)),k) s,
   bignum_from_memory (word_add a (word(24 * k)),k) s)`;;

let bignum_pairpair_from_memory = new_definition
 `bignum_pairpair_from_memory (a,k) s =
  (bignum_pair_from_memory (a,k) s,
   bignum_pair_from_memory (word_add a (word(16 * k)),k) s)`;;

let reduced_pair = new_definition
 `reduced_pair (p:num) (m,n) <=> m < p /\ n < p`;;

let reduced_triple = new_definition
 `reduced_triple (p:num) (m,n,r) <=> m < p /\ n < p /\ r < p`;;

let reduced_quadruple = new_definition
 `reduced_quadruple (p:num) (m,n,r) <=> m < p /\ n < p /\ r < p`;;

let reduced_pairpair = new_definition
 `reduced_pairpair (p:num) ((m,n),(r,s)) <=>
    m < p /\ n < p /\ r < p /\ s < p`;;

simulation_precanon_thms :=
 union [bignum_pairpair_from_memory; bignum_quadruple_from_memory;
        bignum_triple_from_memory; bignum_pair_from_memory]
       (!simulation_precanon_thms);;

(* ------------------------------------------------------------------------- *)
(* Plain encoding (just transitioning between N and Z, with reduction).      *)
(* ------------------------------------------------------------------------- *)

let modular_encode = new_definition
 `modular_encode (k:num,p) x = num_of_int(x rem &p)`;;

let modular_decode = new_definition
 `modular_decode (k:num,p) n = &n rem &p`;;

let MODULAR_ENCODE = prove
 (`!k p x. modular_encode (k:num,p) x < p <=> ~(p = 0)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[ODD] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; modular_encode] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS; INT_OF_NUM_EQ;
               INT_LT_REM_EQ] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN ASM_ARITH_TAC);;

let MODULAR_DECODE = prove
 (`!k p n. ~(p = 0)
           ==> &0 <= modular_decode (k,p) n /\
               modular_decode (k,p) n < &p`,
  REWRITE_TAC[modular_decode; INT_LT_REM_EQ; INT_REM_POS_EQ] THEN
  SIMP_TAC[INT_OF_NUM_EQ; INT_OF_NUM_CLAUSES; LE_1]);;

let MODULAR_ENCODE_DECODE = prove
 (`!k p n. n < p
           ==> modular_encode (k,p) (modular_decode (k,p) n) = n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[LT] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[modular_encode; modular_decode] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  ASM_SIMP_TAC[INT_REM_LT; INT_POS]);;

let MODULAR_DECODE_ENCODE = prove
 (`!k p x. &0 <= x /\ x < &p
           ==> modular_decode (k,p) (modular_encode (k,p) x) = x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[INT_LET_ANTISYM] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[modular_encode; modular_decode] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN ASM_SIMP_TAC[INT_REM_LT]);;

(* ------------------------------------------------------------------------- *)
(* Montgomery encoding, as well as switching between N and Z.                *)
(* ------------------------------------------------------------------------- *)

let montgomery_encode = new_definition
 `montgomery_encode (k,p) x = num_of_int((&2 pow k * x) rem &p)`;;

let montgomery_decode = new_definition
 `montgomery_decode (k,p) n = &(inverse_mod p (2 EXP k) * n) rem &p`;;

let MONTGOMERY_ENCODE = prove
 (`!k p x. ODD p ==> montgomery_encode (k,p) x < p`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[ODD] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; montgomery_encode] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS; INT_OF_NUM_EQ;
               INT_LT_REM_EQ] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN ASM_ARITH_TAC);;

let MONTGOMERY_DECODE = prove
 (`!k p n. ODD p
           ==> &0 <= montgomery_decode (k,p) n /\
               montgomery_decode (k,p) n < &p`,
  REWRITE_TAC[montgomery_decode; INT_LT_REM_EQ; INT_REM_POS_EQ] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[ODD] THEN ASM_ARITH_TAC);;

let MONTGOMERY_ENCODE_DECODE = prove
 (`!k p n. ODD p /\ n < p
           ==> montgomery_encode (k,p) (montgomery_decode (k,p) n) = n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[LT] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[montgomery_encode; montgomery_decode] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  ASM_REWRITE_TAC[INT_REM_UNIQUE; INT_POS; INT_ABS_NUM] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(i * x == 1) (mod p) ==> (i * x * n == n) (mod p)`) THEN
  ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2]);;

let MONTGOMERY_DECODE_ENCODE = prove
 (`!k p x. ODD p /\ &0 <= x /\ x < &p
           ==> montgomery_decode (k,p) (montgomery_encode (k,p) x) = x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[INT_LET_ANTISYM] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[montgomery_encode; montgomery_decode] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  ASM_REWRITE_TAC[INT_REM_UNIQUE; INT_POS; INT_ABS_NUM] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(i * x:int == &1) (mod p) ==> (i * x * n == n) (mod p)`) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  ASM_REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2]);;

(* ------------------------------------------------------------------------- *)
(* Various tupled elaborations.                                              *)
(* ------------------------------------------------------------------------- *)

let paired = new_definition
 `paired f (x,y) = (f x,f y)`;;

let tripled = new_definition
 `tripled f (x,y,z) = (f x,f y,f z)`;;

let quadrupled = new_definition
 `quadrupled f (w,x,y,z) = (f w,f x,f y,f z)`;;

let pairpaired = new_definition
 `pairpaired f ((w,x),(y,z)) = ((f w,f x),(f y,f z))`;;
