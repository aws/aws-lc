(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_25519 of a single word and a bignum < p_25519.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_cmul_p25519.o";;
 ****)

let bignum_cmul_p25519_mc = define_assert_from_elf "bignum_cmul_p25519_mc" "arm/curve25519/bignum_cmul_p25519.o"
[
  0xa9402047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&16))) *)
  0x9b077c23;       (* arm_MUL X3 X1 X7 *)
  0x9b087c24;       (* arm_MUL X4 X1 X8 *)
  0x9b097c25;       (* arm_MUL X5 X1 X9 *)
  0x9b0a7c26;       (* arm_MUL X6 X1 X10 *)
  0x9bc77c27;       (* arm_UMULH X7 X1 X7 *)
  0x9bc87c28;       (* arm_UMULH X8 X1 X8 *)
  0x9bc97c29;       (* arm_UMULH X9 X1 X9 *)
  0x9bca7c2a;       (* arm_UMULH X10 X1 X10 *)
  0xab070084;       (* arm_ADDS X4 X4 X7 *)
  0xba0800a5;       (* arm_ADCS X5 X5 X8 *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x91000548;       (* arm_ADD X8 X10 (rvalue (word 1)) *)
  0xab0600df;       (* arm_CMN X6 X6 *)
  0xb24100c6;       (* arm_ORR X6 X6 (rvalue (word 9223372036854775808)) *)
  0x9a0a0108;       (* arm_ADC X8 X8 X10 *)
  0xd2800269;       (* arm_MOV X9 (rvalue (word 19)) *)
  0x9b097d07;       (* arm_MUL X7 X8 X9 *)
  0x9bc97d0a;       (* arm_UMULH X10 X8 X9 *)
  0xab070063;       (* arm_ADDS X3 X3 X7 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0xba1f00a5;       (* arm_ADCS X5 X5 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a9f3129;       (* arm_CSEL X9 X9 XZR Condition_CC *)
  0xeb090063;       (* arm_SUBS X3 X3 X9 *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xda1f00c6;       (* arm_SBC X6 X6 XZR *)
  0x9240f8c6;       (* arm_AND X6 X6 (rvalue (word 9223372036854775807)) *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_CMUL_P25519_EXEC = ARM_MK_EXEC_RULE bignum_cmul_p25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let BIGNUM_CMUL_P25519_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0x88) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_p25519_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = word (pc + 0x84) /\
                  (a < p_25519
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_25519))
          (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_25519 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_25519` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_CMUL_P25519_EXEC (1--33)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `val(c:int64) * a` p25519redlemma) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN
    MP_TAC(ISPEC `c:int64` VAL_BOUND) THEN UNDISCH_TAC `a < p_25519` THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Intermediate result from initial multiply ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P25519_EXEC (1--14) (1--14) THEN
  ABBREV_TAC
  `ca = bignum_of_wordlist [mullo_s3; sum_s11; sum_s12; sum_s13; sum_s14]` THEN
  SUBGOAL_THEN `val(c:int64) * a = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check((fun l -> not(l = [])) o
        intersect [`a:num`; `x:int64`; `c:int64`] o frees o concl))) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P25519_EXEC [15;16;18] (15--18) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [mullo_s3; sum_s11; sum_s12;word_or sum_s13 (word 9223372036854775808)]` THEN
    SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [mullo_s3; sum_s11; sum_s12] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN

  SUBGOAL_THEN `&(val(sum_s18:int64)) = &(ca DIV 2 EXP 255) + &1`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN
    UNDISCH_TAC `ca DIV 2 EXP 255 + 1 < 2 EXP 64` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 63 + 1 = (2 * n + 2 EXP 64) DIV 2 EXP 64`] THEN
    SUBST1_TAC(SYM(BIGNUM_OF_WORDLIST_DIV_CONV
     `bignum_of_wordlist [sum_s16; sum_s18] DIV 2 EXP 64`)) THEN
    MATCH_MP_TAC CONG_DIV2 THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  ABBREV_TAC `hw = ca DIV 2 EXP 255` THEN

  (*** The rest of the computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_CMUL_P25519_EXEC
   [20;22;23;24;25;27;28;29;30] (19--33) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`hw + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (hw + 1) * p_25519 <=> ~carry_s25`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s25:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_CMUL_P25519_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc returnaddress.
        nonoverlapping (word pc,0x88) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_cmul_p25519_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read PC s = returnaddress /\
                  (a < p_25519
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_25519))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_CMUL_P25519_EXEC BIGNUM_CMUL_P25519_CORRECT);;
