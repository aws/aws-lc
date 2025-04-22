(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo p_384, the field characteristic for NIST curve P-384.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_mod_p384.o";;
 ****)

let bignum_mod_p384_mc =
  define_assert_from_elf "bignum_mod_p384_mc" "arm/p384/bignum_mod_p384.o"
[
  0xf100183f;       (* arm_CMP X1 (rvalue (word 6)) *)
  0x54000763;       (* arm_BCC (word 236) *)
  0xd1001821;       (* arm_SUB X1 X1 (rvalue (word 6)) *)
  0xd37df029;       (* arm_LSL X9 X1 (rvalue (word 3)) *)
  0x8b020129;       (* arm_ADD X9 X9 X2 *)
  0xa9422127;       (* arm_LDP X7 X8 X9 (Immediate_Offset (iword (&32))) *)
  0xa9411925;       (* arm_LDP X5 X6 X9 (Immediate_Offset (iword (&16))) *)
  0xa9401123;       (* arm_LDP X3 X4 X9 (Immediate_Offset (iword (&0))) *)
  0xb2407fef;       (* arm_MOV X15 (rvalue (word 4294967295)) *)
  0xb2607ff0;       (* arm_MOV X16 (rvalue (word 18446744069414584320)) *)
  0x92800031;       (* arm_MOVN X17 (word 1) 0 *)
  0xeb0f0069;       (* arm_SUBS X9 X3 X15 *)
  0xfa10008a;       (* arm_SBCS X10 X4 X16 *)
  0xfa1100ab;       (* arm_SBCS X11 X5 X17 *)
  0xba1f00cc;       (* arm_ADCS X12 X6 XZR *)
  0xba1f00ed;       (* arm_ADCS X13 X7 XZR *)
  0xba1f010e;       (* arm_ADCS X14 X8 XZR *)
  0x9a893063;       (* arm_CSEL X3 X3 X9 Condition_CC *)
  0x9a8a3084;       (* arm_CSEL X4 X4 X10 Condition_CC *)
  0x9a8b30a5;       (* arm_CSEL X5 X5 X11 Condition_CC *)
  0x9a8c30c6;       (* arm_CSEL X6 X6 X12 Condition_CC *)
  0x9a8d30e7;       (* arm_CSEL X7 X7 X13 Condition_CC *)
  0x9a8e3108;       (* arm_CSEL X8 X8 X14 Condition_CC *)
  0xb4000421;       (* arm_CBZ X1 (word 132) *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xf861784e;       (* arm_LDR X14 X2 (Shiftreg_Offset X1 3) *)
  0xb1000508;       (* arm_ADDS X8 X8 (rvalue (word 1)) *)
  0xda9f33ec;       (* arm_CSETM X12 Condition_CS *)
  0x8b0c0108;       (* arm_ADD X8 X8 X12 *)
  0xaa2c03f0;       (* arm_ORN X16 XZR X12 *)
  0xd100050b;       (* arm_SUB X11 X8 (rvalue (word 1)) *)
  0xcb0803ea;       (* arm_NEG X10 X8 *)
  0xd3607d49;       (* arm_LSL X9 X10 (rvalue (word 32)) *)
  0x93ca816a;       (* arm_EXTR X10 X11 X10 (rvalue (word 32)) *)
  0xd360fd6b;       (* arm_LSR X11 X11 (rvalue (word 32)) *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0xab0901c9;       (* arm_ADDS X9 X14 X9 *)
  0xba0a006a;       (* arm_ADCS X10 X3 X10 *)
  0xba0b008b;       (* arm_ADCS X11 X4 X11 *)
  0xba0800ac;       (* arm_ADCS X12 X5 X8 *)
  0xba1f00cd;       (* arm_ADCS X13 X6 XZR *)
  0xba1f00ee;       (* arm_ADCS X14 X7 XZR *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x8a1001e8;       (* arm_AND X8 X15 X16 *)
  0xab080123;       (* arm_ADDS X3 X9 X8 *)
  0xca100108;       (* arm_EOR X8 X8 X16 *)
  0xba080144;       (* arm_ADCS X4 X10 X8 *)
  0x8a100228;       (* arm_AND X8 X17 X16 *)
  0xba080165;       (* arm_ADCS X5 X11 X8 *)
  0xba100186;       (* arm_ADCS X6 X12 X16 *)
  0xba1001a7;       (* arm_ADCS X7 X13 X16 *)
  0x9a1001c8;       (* arm_ADC X8 X14 X16 *)
  0xb5fffc21;       (* arm_CBNZ X1 (word 2097028) *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xb4fffec1;       (* arm_CBZ X1 (word 2097112) *)
  0xf9400043;       (* arm_LDR X3 X2 (Immediate_Offset (word 0)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffe60;       (* arm_BEQ (word 2097100) *)
  0xf9400444;       (* arm_LDR X4 X2 (Immediate_Offset (word 8)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffe00;       (* arm_BEQ (word 2097088) *)
  0xf9400845;       (* arm_LDR X5 X2 (Immediate_Offset (word 16)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffda0;       (* arm_BEQ (word 2097076) *)
  0xf9400c46;       (* arm_LDR X6 X2 (Immediate_Offset (word 24)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffd40;       (* arm_BEQ (word 2097064) *)
  0xf9401047;       (* arm_LDR X7 X2 (Immediate_Offset (word 32)) *)
  0x17ffffe8        (* arm_B (word 268435360) *)
];;

let BIGNUM_MOD_P384_EXEC = ARM_MK_EXEC_RULE bignum_mod_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let p384longredlemma = prove
 (`!n. n < 2 EXP 64 * p_384
       ==> let q = MIN (n DIV 2 EXP 384 + 1) (2 EXP 64 - 1) in
           q < 2 EXP 64 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let BIGNUM_MOD_P384_CORRECT = time prove
 (`!z k x n pc.
      nonoverlapping (word pc,0x144) (z,48)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p384_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = word (pc + 0xec) /\
                bignum_from_memory (z,6) s = n MOD p_384)
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  X_GEN_TAC `z:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Case split over the k < 6 case, which is a different path ***)

  ASM_CASES_TAC `k < 6` THENL
   [SUBGOAL_THEN `n MOD p_384 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP (64 * 5)` THEN
      ASM_REWRITE_TAC[LE_EXP; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
   BIGNUM_DIGITIZE_TAC "n_" `read(memory :> bytes(x,8 * 6)) s0` THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `k < 6 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5`)) THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
   EXPAND_TAC "n" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
   ASM_REWRITE_TAC[] THENL
    [ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (1--12);
     ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (1--15);
     ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (1--18);
     ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (1--21);
     ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (1--24);
     ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (1--26)] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
   ARITH_TAC;
   FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN

  (*** Initial 6-digit modulus ***)

  ENSURES_SEQUENCE_TAC `pc + 0x5c`
   `\s. bignum_from_memory(x,k) s = n /\
        read X0 s = z /\
        read X2 s = x /\
        read X1 s = word(k - 6) /\
        read X15 s = word 0x00000000ffffffff /\
        read X16 s = word 0xffffffff00000000 /\
        read X17 s = word 0xfffffffffffffffe /\
        bignum_of_wordlist[read X3 s; read X4 s; read X5 s;
                           read X6 s; read X7 s; read X8 s] =
        (highdigits n (k - 6)) MOD p_384` THEN
  CONJ_TAC THENL
   [ABBREV_TAC `j = k - 6` THEN VAL_INT64_TAC `j:num` THEN
    SUBGOAL_THEN `word_sub (word k) (word 6):int64 = word j` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `k - 6 = j`)) THEN
      REWRITE_TAC[WORD_SUB] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[highdigits] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_DIV] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    SUBST1_TAC(SYM(ASSUME `k - 6 = j`)) THEN
    ASM_SIMP_TAC[ARITH_RULE `6 <= k ==> k - (k - 6) = 6`] THEN
    ABBREV_TAC `m = bignum_from_memory(word_add x (word (8 * j)),6) s0` THEN
    SUBGOAL_THEN `m < 2 EXP (64 * 6)` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV)) THEN
    BIGNUM_DIGITIZE_TAC "m_"
     `read (memory :> bytes (word_add x (word(8 * j)),8 * 6)) s0` THEN
    ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (1--5) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_shl (word j) 3) x = word_add x (word(8 * j))`]) THEN
    ARM_ACCSTEPS_TAC BIGNUM_MOD_P384_EXEC (12--17) (6--23) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [REAL_BITVAL_NOT; ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `carry_s17 <=> p_384 <= m` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN BOUNDER_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN
    REWRITE_TAC[NOT_LE] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`64 * 6`; `if m < p_384 then &m:real else &(m - p_384)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      REWRITE_TAC[p_384] THEN ARITH_TAC;
      ALL_TAC;
      REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MOD_CASES THEN UNDISCH_TAC `m < 2 EXP (64 * 6)` THEN
      REWRITE_TAC[p_384] THEN ARITH_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXPAND_TAC "m" THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      REAL_INTEGER_TAC;
      FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[p_384; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Finish off the k = 6 case which is now just the writeback ***)

  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o MATCH_MP (ARITH_RULE
   `6 <= k ==> k = 6 \/ 6 < k`))
  THENL
   [GHOST_INTRO_TAC `d0:int64` `read X3` THEN
    GHOST_INTRO_TAC `d1:int64` `read X4` THEN
    GHOST_INTRO_TAC `d2:int64` `read X5` THEN
    GHOST_INTRO_TAC `d3:int64` `read X6` THEN
    GHOST_INTRO_TAC `d4:int64` `read X7` THEN
    GHOST_INTRO_TAC `d5:int64` `read X8` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `0 < k - 6 /\ ~(k - 6 = 0)` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Setup of loop invariant ***)

  ENSURES_WHILE_DOWN_TAC `k - 6` `pc + 0x60` `pc + 0xdc`
   `\i s. bignum_from_memory(x,k) s = n /\
          read X0 s = z /\
          read X2 s = x /\
          read X1 s = word i /\
          read X15 s = word 0x00000000ffffffff /\
          read X17 s = word 0xfffffffffffffffe /\
          bignum_of_wordlist[read X3 s; read X4 s; read X5 s;
                             read X6 s; read X7 s; read X8 s] =
          (highdigits n i) MOD p_384` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [VAL_INT64_TAC `k - 6` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `d0:int64` `read X3` THEN
    GHOST_INTRO_TAC `d1:int64` `read X4` THEN
    GHOST_INTRO_TAC `d2:int64` `read X5` THEN
    GHOST_INTRO_TAC `d3:int64` `read X6` THEN
    GHOST_INTRO_TAC `d4:int64` `read X7` THEN
    GHOST_INTRO_TAC `d5:int64` `read X8` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN

  (*** Mathematics of main loop with decomposition and quotient estimate ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `m1:int64` `read X3` THEN
  GHOST_INTRO_TAC `m2:int64` `read X4` THEN
  GHOST_INTRO_TAC `m3:int64` `read X5` THEN
  GHOST_INTRO_TAC `m4:int64` `read X6` THEN
  GHOST_INTRO_TAC `m5:int64` `read X7` THEN
  GHOST_INTRO_TAC `m6:int64` `read X8` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m0:int64 = word(bigdigit n i)` THEN
  ABBREV_TAC `m = bignum_of_wordlist[m0; m1; m2; m3; m4; m5; m6]` THEN
  SUBGOAL_THEN `m < 2 EXP 64 * p_384` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MP_TAC(SPEC `m0:int64` VAL_BOUND_64) THEN
    ASM_REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `highdigits n i MOD p_384 = m MOD p_384` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
    EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    EXPAND_TAC "m0" THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` p384longredlemma) THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN STRIP_TAC THEN

  (*** The next digit in the current state ***)

  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `x:int64`; `s0:armstate`; `i:num`]
        BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word:num->int64` o SYM) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN DISCH_TAC THEN

  (*** The computation of the quotient estimate q ***)

  ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (i + 1)) (word 1):int64 = word i`]) THEN
  ARM_ACCSTEPS_TAC BIGNUM_MOD_P384_EXEC [3] (2--3) THEN
  SUBGOAL_THEN
   `2 EXP 64 * bitval(read CF s3) + val(read X8 s3) = m DIV 2 EXP 384 + 1`
  MP_TAC THENL
   [EXPAND_TAC "m" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (4--5) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word q:int64` o MATCH_MP (MESON[]
   `!q. read X8 s = q' ==> q' = q ==> read X8 s = q`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "q" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0] THEN
    SIMP_TAC[VAL_BOUND_64; WORD_VAL; ARITH_RULE
     `n < 2 EXP 64 ==> MIN n (2 EXP 64 - 1) = n`] THEN
    REWRITE_TAC[ARITH_RULE
     `MIN (2 EXP 64 + a) (2 EXP 64 - 1) = 2 EXP 64 - 1`] THEN
    UNDISCH_TAC
     `&2 pow 64 * &(bitval carry_s3) + &(val(sum_s3:int64)):real =
      &(val(m6:int64)) + &1` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_RULE `word_add y x:int64 = x <=> y = word 0`] THEN
    REWRITE_TAC[GSYM VAL_EQ_0] THEN
    MP_TAC(SPEC `m6:int64` VAL_BOUND_64) THEN ARITH_TAC;
    DISCH_TAC THEN VAL_INT64_TAC `q:num`] THEN

  (*** A bit of fiddle to make the accumulation tactics work ***)

  ABBREV_TAC `w:int64 = word q` THEN
  UNDISCH_THEN `val(w:int64) = q` (SUBST_ALL_TAC o SYM) THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC o end_itlist CONJ) THEN

  (*** More fiddly intermediate values ***)

  ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC [6] THEN
  FIRST_X_ASSUM(MP_TAC o
   SPEC `word_neg(word(bitval(val(m6:int64) + 1 < 2 EXP 64))):int64` o
   MATCH_MP (MESON[] `!m. read X16 s = m' ==> m' = m ==> read X16 s = m`)) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC
     `2 EXP 64 * bitval carry_s3 + val(sum_s3:int64) =
      m DIV 2 EXP 384 + 1` THEN
    EXPAND_TAC "m" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES;
                    VAL_BOUND_64; ARITH_RULE `~(e + n:num < e)`] THEN
    CONV_TAC WORD_REDUCE_CONV;
    DISCH_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
   `MIN (e + 1) (2 EXP 64 - 1) = q ==> ~(q = 0)`)) THEN

  (*** Computation of the q * r term ***)

  ARM_STEPS_TAC BIGNUM_MOD_P384_EXEC (7--11) THEN
  SUBGOAL_THEN
   `&(bignum_of_wordlist[read X9 s11; read X10 s11; read X11 s11]):real =
    (&2 pow 96 - &2 pow 32) * &(val(w:int64))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    SIMP_TAC[VAL_WORD_SHL; VAL_WORD_USHR; GSYM REAL_OF_NUM_CLAUSES] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_0; VAL_WORD_1] THEN
    ASM_REWRITE_TAC[DIMINDEX_64; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_REWRITE_TAC[CONJUNCT1 LE; REAL_ARITH
     `a:real = (b - c) * d <=> a + c * d = b * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(val(w:int64) = 0)`; `val(w:int64) < 2 EXP 64`] THEN
    REWRITE_TAC[EXP_ADD; MOD_MULT2; ARITH_RULE `64 = 32 + 32`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY REABBREV_TAC
   [`a0 = read X9 s11`; `a1 = read X10 s11`; `a2 = read X11 s11`] THEN

  ARM_ACCSTEPS_TAC BIGNUM_MOD_P384_EXEC (12--22) (12--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  SUBGOAL_THEN
   `read X16 s22 = word_neg (word (bitval(m < val(w:int64) * p_384))) /\
    &(bignum_of_wordlist
        [read X9 s22; read X10 s22; read X11 s22; read X12 s22; read X13 s22;
         read X14 s22]) =
    if m < val(w:int64) * p_384
    then &m - &(val(w:int64) * p_384) + &2 pow 384
    else &m - &(val(w:int64) * p_384)`
  MP_TAC THENL
   [MATCH_MP_TAC MASK_AND_VALUE_FROM_CARRY_LT THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(w:int64) * p_384 <= m + p_384`;
        `m < val(w:int64) * p_384 + p_384`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&(val(w:int64)) * &p_384:real =
      (&2 pow 384 - &2 pow 128) * &(val(w:int64)) -
      (&(bignum_of_wordlist[a0; a1; a2]) + &(val(w:int64)))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[p_384] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_VAL_WORD_MASK; DIMINDEX_64]) THEN
    SUBGOAL_THEN
     `&(bitval(val(m6:int64) + 1 < 2 EXP 64)) = &(val(w:int64)) - &(val m6)`
    SUBST_ALL_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `MIN (x + 1) (2 EXP 64 - 1) = q
        ==> x < 2 EXP 64
            ==> q = if x + 1 < 2 EXP 64 then x + 1 else x`)) THEN
      EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[VAL_BOUND_64] THEN DISCH_THEN SUBST1_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)] THEN

  (*** Finale ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_P384_EXEC (23--31) (23--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(w:int64):num`; `384`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(a - b) - (c - d) * p:real = (a - c * p) + (d * p - b)`] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  REWRITE_TAC[REAL_ARITH
    `(x:real = if p then y + e else y) <=>
     (y = if p then x - e else x)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[WORD_AND_MASK; GSYM REAL_OF_NUM_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[p_384] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_P384_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc returnaddress.
      nonoverlapping (word pc,0x144) (z,48)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p384_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,6) s = n MOD p_384)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MOD_P384_EXEC BIGNUM_MOD_P384_CORRECT);;
