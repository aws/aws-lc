(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo p_521, the field characteristic of the NIST curve P-521. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_mod_p521_9.o";;
 ****)

let bignum_mod_p521_9_mc =
  define_assert_from_elf "bignum_mod_p521_9_mc" "arm/p521/bignum_mod_p521_9.o"
[
  0xf940202c;       (* arm_LDR X12 X1 (Immediate_Offset (word 64)) *)
  0xd349fd82;       (* arm_LSR X2 X12 (rvalue (word 9)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xa9401424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xba02009f;       (* arm_ADCS XZR X4 X2 *)
  0xba1f00bf;       (* arm_ADCS XZR X5 XZR *)
  0xa9411c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0x8a0700c3;       (* arm_AND X3 X6 X7 *)
  0xba1f007f;       (* arm_ADCS XZR X3 XZR *)
  0xa9422428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&32))) *)
  0x8a090103;       (* arm_AND X3 X8 X9 *)
  0xba1f007f;       (* arm_ADCS XZR X3 XZR *)
  0xa9432c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&48))) *)
  0x8a0b0143;       (* arm_AND X3 X10 X11 *)
  0xba1f007f;       (* arm_ADCS XZR X3 XZR *)
  0xb277d983;       (* arm_ORR X3 X12 (rvalue (word 18446744073709551104)) *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xba020084;       (* arm_ADCS X4 X4 X2 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0x9240218c;       (* arm_AND X12 X12 (rvalue (word 511)) *)
  0xa9001404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&32))) *)
  0xa9032c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200c;       (* arm_STR X12 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MOD_P521_9_EXEC = ARM_MK_EXEC_RULE bignum_mod_p521_9_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_MOD_P521_9_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x84) (z,8 * 9)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p521_9_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read PC s = word (pc + 0x80) /\
                bignum_from_memory (z,9) s = n MOD p_521)
          (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN

  (*** Breaking the problem down to (H + L) MOD p_521 ***)

  SUBGOAL_THEN `n MOD p_521 = (n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `n = 2 EXP 521 * n DIV 2 EXP 521 + n MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `n DIV 2 EXP 521 < 2 EXP 55 /\ n MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; ARITH_RULE
     `n DIV 2 EXP 521 < 2 EXP 55 <=> n < 2 EXP (64 * 9)`] THEN
    EXPAND_TAC "n" THEN MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC
    `l = bignum_of_wordlist[n_0; n_1; n_2; n_3; n_4; n_5; n_6; n_7;
                            word_and n_8 (word 511)]` THEN
  ABBREV_TAC `h:int64 = word_ushr n_8 9` THEN

  SUBGOAL_THEN
   `n DIV 2 EXP 521 = val(h:int64) /\ n MOD 2 EXP 521 = l`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["n"; "h"; "l"] THEN CONJ_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_AND_MASK_WORD];
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
      SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD;
               ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
               MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; ADD_CLAUSES] THEN
      REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ADD_CLAUSES] THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Initial condensed comparison H + L + 1 >= 2 EXP 521  ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_P521_9_EXEC
   [5;6;9;12;15;17] (1--17) THEN

  SUBGOAL_THEN `carry_s17 <=> p_521 <= val(h:int64) + l` SUBST_ALL_TAC THENL
   [TRANS_TAC EQ_TRANS
     `2 EXP 329 <=
      bignum_of_wordlist [n_0; n_1; word_and n_2 n_3; word_and n_4 n_5;
                          word_and n_6 n_7; word_and n_8 (word 511)] +
      val(h:int64) + 1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      SUBGOAL_THEN
       `&(val(word_or n_8 (word 18446744073709551104):int64)):real =
         &2 pow 9 * (&2 pow 55 - &1) + &(val(word_and n_8 (word 511)))`
      SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
         `word_or a b = word_or b (word_and a (word_not b))`] THEN
        SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
         `word_and x (word_and y (word_not x)) = word 0`] THEN
        CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[REAL_OF_NUM_ADD];
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
      EXPAND_TAC "l"] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    MP_TAC(ARITH_RULE `val(n_8:int64) MOD 2 EXP 9 < 2 EXP 9`) THEN
    SPEC_TAC(`val(n_8:int64) MOD 2 EXP 9`,`n8:num`) THEN GEN_TAC THEN
    UNDISCH_TAC `val(h:int64) < 2 EXP 55` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MP_TAC(ISPECL [`n_2:int64`; `n_3:int64`] VAL_WORD_AND_EQ_MAX) THEN
    MP_TAC(ISPECL [`n_4:int64`; `n_5:int64`] VAL_WORD_AND_EQ_MAX) THEN
    MP_TAC(ISPECL [`n_6:int64`; `n_7:int64`] VAL_WORD_AND_EQ_MAX) THEN
    REWRITE_TAC[TAUT `(p <=> q /\ r) <=> ~p /\ (~q \/ ~r) \/ p /\ q /\ r`] THEN
    SIMP_TAC[VAL_BOUND; ARITH_RULE
     `n < e ==> (~(n = e - 1) <=> n < e - 1)`] THEN
    MAP_EVERY (MP_TAC o C SPEC VAL_BOUND_64)
     [`n_0:int64`; `n_1:int64`; `n_2:int64`; `n_3:int64`;
      `n_4:int64`; `n_5:int64`; `n_6:int64`; `n_7:int64`;
      `word_and n_2 n_3:int64`;
      `word_and n_4 n_5:int64`;
      `word_and n_6 n_7:int64`] THEN
    REWRITE_TAC[DIMINDEX_64; p_521] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY ASM_ARITH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC o MATCH_MP
     (ARITH_RULE `n < 2 EXP 9 ==> n = 2 EXP 9 - 1 \/ n < 2 EXP 9 - 1`)) THEN
    ASM_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The final optional addition of 1 and masking ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_P521_9_EXEC (18--26) (18--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if val(h:int64) + l < p_521
     then &(val(h:int64) + l) else &(val(h:int64) + l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`l < 2 EXP 521`; `val(h:int64) < 2 EXP 55`] THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ABBREV_TAC `bb <=> val(h:int64) + l < p_521` THEN
  EXPAND_TAC "l" THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_MOD; p_521] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_P521_9_SUBROUTINE_CORRECT = time prove
 (`!z x n pc returnaddress.
      nonoverlapping (word pc,0x84) (z,8 * 9)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p521_9_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,9) s = n MOD p_521)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_MOD_P521_9_EXEC BIGNUM_MOD_P521_9_CORRECT);;
