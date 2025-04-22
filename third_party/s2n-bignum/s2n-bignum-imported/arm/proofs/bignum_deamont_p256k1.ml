(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of almost-Montgomery representation modulo p_256k1.           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_deamont_p256k1.o";;
 ****)

let bignum_deamont_p256k1_mc =
  define_assert_from_elf "bignum_deamont_p256k1_mc" "arm/secp256k1/bignum_deamont_p256k1.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xd286a627;       (* arm_MOV X7 (rvalue (word 13617)) *)
  0xf2ba44a7;       (* arm_MOVK X7 (word 53797) 16 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xf2c123a7;       (* arm_MOVK X7 (word 2333) 32 *)
  0xf2fb0707;       (* arm_MOVK X7 (word 55352) 48 *)
  0xd2807a28;       (* arm_MOV X8 (rvalue (word 977)) *)
  0xb2600108;       (* arm_ORR X8 X8 (rvalue (word 4294967296)) *)
  0x9b027ce2;       (* arm_MUL X2 X7 X2 *)
  0x9bc87c46;       (* arm_UMULH X6 X2 X8 *)
  0xeb060063;       (* arm_SUBS X3 X3 X6 *)
  0x9b037ce3;       (* arm_MUL X3 X7 X3 *)
  0x9bc87c66;       (* arm_UMULH X6 X3 X8 *)
  0x8a030049;       (* arm_AND X9 X2 X3 *)
  0xfa060084;       (* arm_SBCS X4 X4 X6 *)
  0x9b047ce4;       (* arm_MUL X4 X7 X4 *)
  0x9bc87c86;       (* arm_UMULH X6 X4 X8 *)
  0x8a040129;       (* arm_AND X9 X9 X4 *)
  0xfa0600a5;       (* arm_SBCS X5 X5 X6 *)
  0x9b057ce5;       (* arm_MUL X5 X7 X5 *)
  0x9bc87ca6;       (* arm_UMULH X6 X5 X8 *)
  0x8a050129;       (* arm_AND X9 X9 X5 *)
  0xfa060042;       (* arm_SBCS X2 X2 X6 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0x8b020108;       (* arm_ADD X8 X8 X2 *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0x9a820102;       (* arm_CSEL X2 X8 X2 Condition_EQ *)
  0x9a8303e3;       (* arm_CSEL X3 XZR X3 Condition_EQ *)
  0x9a8403e4;       (* arm_CSEL X4 XZR X4 Condition_EQ *)
  0x9a8503e5;       (* arm_CSEL X5 XZR X5 Condition_EQ *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DEAMONT_P256K1_EXEC = ARM_MK_EXEC_RULE bignum_deamont_p256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let P_256K1_AS_WORDLIST = prove
 (`p_256k1 =
   bignum_of_wordlist
    [word 0xfffffffefffffc2f;
     word_not(word 0);word_not(word 0);word_not(word 0)]`,
  REWRITE_TAC[p_256k1; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(15580212934572586289 * val(x:int64)):int64)) * &4294968273
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(15580212934572586289 * val(x:int64)):int64)) *
            &4294968273`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; VAL_WORD_MUL; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_DEAMONT_P256K1_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x8c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_deamont_p256k1_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x88) /\
                  bignum_from_memory (z,4) s =
                    (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1)
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Special-case a = p_256k1 by explicit calculation ***)

  ASM_CASES_TAC `a = p_256k1` THENL
   [FIRST_ASSUM MP_TAC THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[P_256K1_AS_WORDLIST; BIGNUM_OF_WORDLIST_EQ] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    ARM_STEPS_TAC BIGNUM_DEAMONT_P256K1_EXEC (1--34) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT];
    ALL_TAC] THEN

  (*** Main simulation of the general case ***)

  ARM_ACCSTEPS_TAC BIGNUM_DEAMONT_P256K1_EXEC
   [10;11;13;15;17;19;21;23;24;25;26] (1--34) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Identify cofactor and collapse the computed test ***)

  ABBREV_TAC
   `q = bignum_of_wordlist
         [word(15580212934572586289 * val(x_0:int64));
          word(15580212934572586289 * val(sum_s11:int64));
          word(15580212934572586289 * val(sum_s15:int64));
          word(15580212934572586289 * val(sum_s19:int64))]` THEN
  REWRITE_TAC[VAL_EQ_0; WORD_RULE
   `word_add x (word 1) = word 0 <=> word_not x = word 0`] THEN
  REWRITE_TAC[WORD_NOT_AND; WORD_OR_EQ_0] THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `\x. x = 2 EXP 256 - 1`) THEN
  SIMP_TAC[BIGNUM_OF_WORDLIST_EQ_MAX; LENGTH; ARITH_MULT; ARITH_ADD; ARITH_SUC;
           ALL; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[WORD_RULE `x = word_not(word 0) <=> word_not x = word 0`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN

  (*** The unchecked result from the Montgomery array ***)

  SUBGOAL_THEN
   `2 EXP 256 * bignum_of_wordlist [sum_s23; sum_s24; sum_s25; sum_s26] =
    a + q * p_256k1`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "a"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Show the result is in fact reduced ***)

  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    REWRITE_TAC[ARITH_RULE
      `2 EXP 256 * x = a + (2 EXP 256 - 1) * p <=>
       2 EXP 256 * x + p = a + 2 EXP 256 * p`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(e * x + p:num = a + e * p) ==> (a == p) (mod e)`)) THEN
    UNDISCH_TAC `~(a = p_256k1)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[p_256k1] THEN EXPAND_TAC "a" THEN
    BOUNDER_TAC[];
    DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `a < b <=> 2 EXP 256 * a < 2 EXP 256 * b`] THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `a + q * p:num < e * p <=> a < e * p - q * p`] THEN
    TRANS_TAC LTE_TRANS `2 * p_256k1` THEN CONJ_TAC THENL
     [REWRITE_TAC[p_256k1] THEN EXPAND_TAC "a" THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `q < 2 EXP 256 - 1 ==> 2 <= 2 EXP 256 - q`) THEN
      ASM_REWRITE_TAC[LT_LE] THEN EXPAND_TAC "q" THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]];
    MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `2 EXP 256` THEN
    ASM_REWRITE_TAC[COPRIME_LEXP; COPRIME_2] THEN CONJ_TAC THENL
     [REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `(e * i == 1) (mod p) ==> (e * i * a == a + q * p) (mod p)`) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV]);;

let BIGNUM_DEAMONT_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x8c) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_deamont_p256k1_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,4) s =
                    (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_DEAMONT_P256K1_EXEC BIGNUM_DEAMONT_P256K1_CORRECT);;
