(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_521 of a single word and a bignum < p_521.        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_cmul_p521.o";;
 ****)

let bignum_cmul_p521_mc = define_assert_from_elf "bignum_cmul_p521_mc" "arm/p521/bignum_cmul_p521.o"
[
  0xa9401c46;       (* arm_LDP X6 X7 X2 (Immediate_Offset (iword (&0))) *)
  0x9b067c23;       (* arm_MUL X3 X1 X6 *)
  0x9b077c24;       (* arm_MUL X4 X1 X7 *)
  0x9bc67c26;       (* arm_UMULH X6 X1 X6 *)
  0xab060084;       (* arm_ADDS X4 X4 X6 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0xa9412448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&16))) *)
  0x9b087c25;       (* arm_MUL X5 X1 X8 *)
  0x9b097c26;       (* arm_MUL X6 X1 X9 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0xba0700a5;       (* arm_ADCS X5 X5 X7 *)
  0x8a05008f;       (* arm_AND X15 X4 X5 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0xba0800c6;       (* arm_ADCS X6 X6 X8 *)
  0x8a0601ef;       (* arm_AND X15 X15 X6 *)
  0xa9422c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&32))) *)
  0x9b0a7c27;       (* arm_MUL X7 X1 X10 *)
  0x9b0b7c28;       (* arm_MUL X8 X1 X11 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xba0900e7;       (* arm_ADCS X7 X7 X9 *)
  0x8a0701ef;       (* arm_AND X15 X15 X7 *)
  0x9bcb7c2b;       (* arm_UMULH X11 X1 X11 *)
  0xba0a0108;       (* arm_ADCS X8 X8 X10 *)
  0x8a0801ef;       (* arm_AND X15 X15 X8 *)
  0xa943344c;       (* arm_LDP X12 X13 X2 (Immediate_Offset (iword (&48))) *)
  0x9b0c7c29;       (* arm_MUL X9 X1 X12 *)
  0x9b0d7c2a;       (* arm_MUL X10 X1 X13 *)
  0x9bcc7c2c;       (* arm_UMULH X12 X1 X12 *)
  0xba0b0129;       (* arm_ADCS X9 X9 X11 *)
  0x8a0901ef;       (* arm_AND X15 X15 X9 *)
  0x9bcd7c2d;       (* arm_UMULH X13 X1 X13 *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xf940204e;       (* arm_LDR X14 X2 (Immediate_Offset (word 64)) *)
  0x9b0e7c2b;       (* arm_MUL X11 X1 X14 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0x9bce7c2e;       (* arm_UMULH X14 X1 X14 *)
  0x9a0e03ec;       (* arm_ADC X12 XZR X14 *)
  0x93cb258c;       (* arm_EXTR X12 X12 X11 (rvalue (word 9)) *)
  0xb277d96b;       (* arm_ORR X11 X11 (rvalue (word 18446744073709551104)) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0xba0c007f;       (* arm_ADCS XZR X3 X12 *)
  0xba1f01ff;       (* arm_ADCS XZR X15 XZR *)
  0xba1f017f;       (* arm_ADCS XZR X11 XZR *)
  0xba0c0063;       (* arm_ADCS X3 X3 X12 *)
  0xba1f0084;       (* arm_ADCS X4 X4 XZR *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0xba1f0129;       (* arm_ADCS X9 X9 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0x9240216b;       (* arm_AND X11 X11 (rvalue (word 511)) *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&32))) *)
  0xa9032809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&48))) *)
  0xf900200b;       (* arm_STR X11 X0 (Immediate_Offset (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CMUL_P521_EXEC = ARM_MK_EXEC_RULE bignum_cmul_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_CMUL_P521_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0xf0) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_p521_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,9) s = a)
             (\s. read PC s = word (pc + 0xec) /\
                  (a < p_521
                   ==> bignum_from_memory (z,9) s = (val c * a) MOD p_521))
             (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8;
                         X9; X10; X11; X12; X13; X14; X15] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_521` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_CMUL_P521_EXEC (1--59)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,9) s0` THEN

  (*** The initial basic multiply, after which we forget a and c ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P521_EXEC (1--38) (1--38) THEN
  ABBREV_TAC `n = val(c:int64) * a` THEN
  SUBGOAL_THEN `n < 2 EXP 585` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 EXP 585 = 2 EXP 64 * 2 EXP 521`] THEN
    EXPAND_TAC "n" THEN MATCH_MP_TAC LT_MULT2 THEN UNDISCH_TAC `a < p_521` THEN
    REWRITE_TAC[VAL_BOUND_64; p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [mullo_s2; sum_s5; sum_s11; sum_s14; sum_s20;
      sum_s23; sum_s29; sum_s32; sum_s36; sum_s38] = n`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n"; "a"] THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`word(a):int64 = c`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `c:int64` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `n MOD p_521 = (n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `n = 2 EXP 521 * n DIV 2 EXP 521 + n MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n DIV 2 EXP 521 < 2 EXP 64 /\ n MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `n < 2 EXP 585` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  ARM_STEPS_TAC BIGNUM_CMUL_P521_EXEC (39--41) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64;
      NUM_REDUCE_CONV `9 MOD 64`]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 =
     word_subword(word_join (sum_s38:int64) (sum_s36:int64):int128) (9,64)`;
    `d:int64 = word_or sum_s36 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s5 (word_and sum_s11 (word_and sum_s14
      (word_and sum_s20 (word_and sum_s23 (word_and sum_s29 sum_s32)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P521_EXEC (42--44) (42--44) THEN
  SUBGOAL_THEN
   `carry_s44 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(mullo_s2:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P521_EXEC (45--53) (45--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s59" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s36:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s36:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [mullo_s2; sum_s5; sum_s11; sum_s14; sum_s20; sum_s23; sum_s29; sum_s32] =
    n MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,2)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN
     `bignum_of_wordlist[sum_s36; sum_s38] MOD 2 EXP 9 =
      val sum_s36 MOD 2 EXP 9`
    SUBST1_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; MOD_MULT_ADD; GSYM MULT_ASSOC;
                  ARITH_RULE `2 EXP 64 = 2 EXP 9 * 2 EXP 55`];
      ARITH_TAC];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= n MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s44`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s44" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s5; sum_s11; sum_s14; sum_s20; sum_s23; sum_s29; sum_s32] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `mullo_s2:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s36:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s36:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `mullo_s2:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = n DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LT; ARITH_LE] THEN
    MATCH_MP_TAC(MESON[MOD_LT] `x = y /\ y < d ==> x MOD d = y`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(ARITH_RULE
     `n DIV 2 EXP 512 = x ==> x DIV 2 EXP 9 = n DIV 2 EXP 521`) THEN
    EXPAND_TAC "n" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= n MOD 2 EXP 521 + n DIV 2 EXP 521 + 1 <=>
    p_521 <= n DIV 2 EXP 521 + n MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if n DIV 2 EXP 521 + n MOD 2 EXP 521 < p_521
     then &(n DIV 2 EXP 521 + n MOD 2 EXP 521)
     else &(n DIV 2 EXP 521 + n MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `n < 2 EXP 585` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_CMUL_P521_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc returnaddress.
        nonoverlapping (word pc,0xf0) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_p521_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,9) s = a)
             (\s. read PC s = returnaddress /\
                  (a < p_521
                   ==> bignum_from_memory (z,9) s = (val c * a) MOD p_521))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,9)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CMUL_P521_EXEC BIGNUM_CMUL_P521_CORRECT);;
