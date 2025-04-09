(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_384, the order of the NIST curve P-384                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_mod_n384.o";;
 ****)

let bignum_mod_n384_mc =
  define_assert_from_elf "bignum_mod_n384_mc" "arm/p384/bignum_mod_n384.o"
[
  0xf100183f;       (* arm_CMP X1 (rvalue (word 6)) *)
  0x540008a3;       (* arm_BCC (word 276) *)
  0xd1001821;       (* arm_SUB X1 X1 (rvalue (word 6)) *)
  0xd37df029;       (* arm_LSL X9 X1 (rvalue (word 3)) *)
  0x8b020129;       (* arm_ADD X9 X9 X2 *)
  0xa9422127;       (* arm_LDP X7 X8 X9 (Immediate_Offset (iword (&32))) *)
  0xa9411925;       (* arm_LDP X5 X6 X9 (Immediate_Offset (iword (&16))) *)
  0xa9401123;       (* arm_LDP X3 X4 X9 (Immediate_Offset (iword (&0))) *)
  0xd29ad1af;       (* arm_MOV X15 (rvalue (word 54925)) *)
  0xf2a6674f;       (* arm_MOVK X15 (word 13114) 16 *)
  0xf2dcd2af;       (* arm_MOVK X15 (word 59029) 32 *)
  0xf2e2626f;       (* arm_MOVK X15 (word 4883) 48 *)
  0xd28b10b0;       (* arm_MOV X16 (rvalue (word 22661)) *)
  0xf2b6e9f0;       (* arm_MOVK X16 (word 46927) 16 *)
  0xf2de49b0;       (* arm_MOVK X16 (word 62029) 32 *)
  0xf2f4fcb0;       (* arm_MOVK X16 (word 42981) 48 *)
  0xd29a4411;       (* arm_MOV X17 (rvalue (word 53792)) *)
  0xf2a17911;       (* arm_MOVK X17 (word 3016) 16 *)
  0xf2d64fd1;       (* arm_MOVK X17 (word 45694) 32 *)
  0xf2e71391;       (* arm_MOVK X17 (word 14492) 48 *)
  0xab0f0069;       (* arm_ADDS X9 X3 X15 *)
  0xba10008a;       (* arm_ADCS X10 X4 X16 *)
  0xba1100ab;       (* arm_ADCS X11 X5 X17 *)
  0xba1f00cc;       (* arm_ADCS X12 X6 XZR *)
  0xba1f00ed;       (* arm_ADCS X13 X7 XZR *)
  0xba1f010e;       (* arm_ADCS X14 X8 XZR *)
  0x9a893063;       (* arm_CSEL X3 X3 X9 Condition_CC *)
  0x9a8a3084;       (* arm_CSEL X4 X4 X10 Condition_CC *)
  0x9a8b30a5;       (* arm_CSEL X5 X5 X11 Condition_CC *)
  0x9a8c30c6;       (* arm_CSEL X6 X6 X12 Condition_CC *)
  0x9a8d30e7;       (* arm_CSEL X7 X7 X13 Condition_CC *)
  0x9a8e3108;       (* arm_CSEL X8 X8 X14 Condition_CC *)
  0xb4000441;       (* arm_CBZ X1 (word 136) *)
  0xb100050d;       (* arm_ADDS X13 X8 (rvalue (word 1)) *)
  0xda9f33e9;       (* arm_CSETM X9 Condition_CS *)
  0xaa0901ad;       (* arm_ORR X13 X13 X9 *)
  0x9b0d7de9;       (* arm_MUL X9 X15 X13 *)
  0x9b0d7e0a;       (* arm_MUL X10 X16 X13 *)
  0x9b0d7e2b;       (* arm_MUL X11 X17 X13 *)
  0x9bcd7dec;       (* arm_UMULH X12 X15 X13 *)
  0xab0c014a;       (* arm_ADDS X10 X10 X12 *)
  0x9bcd7e0c;       (* arm_UMULH X12 X16 X13 *)
  0xba0c016b;       (* arm_ADCS X11 X11 X12 *)
  0x9bcd7e2c;       (* arm_UMULH X12 X17 X13 *)
  0x9a0c03ec;       (* arm_ADC X12 XZR X12 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xf861784e;       (* arm_LDR X14 X2 (Shiftreg_Offset X1 3) *)
  0xcb0d0108;       (* arm_SUB X8 X8 X13 *)
  0xab0901c9;       (* arm_ADDS X9 X14 X9 *)
  0xba0a006a;       (* arm_ADCS X10 X3 X10 *)
  0xba0b008b;       (* arm_ADCS X11 X4 X11 *)
  0xba0c00ac;       (* arm_ADCS X12 X5 X12 *)
  0xba1f00cd;       (* arm_ADCS X13 X6 XZR *)
  0xba1f00e7;       (* arm_ADCS X7 X7 XZR *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0x8a0f010e;       (* arm_AND X14 X8 X15 *)
  0xeb0e0123;       (* arm_SUBS X3 X9 X14 *)
  0x8a10010e;       (* arm_AND X14 X8 X16 *)
  0xfa0e0144;       (* arm_SBCS X4 X10 X14 *)
  0x8a11010e;       (* arm_AND X14 X8 X17 *)
  0xfa0e0165;       (* arm_SBCS X5 X11 X14 *)
  0xfa1f0186;       (* arm_SBCS X6 X12 XZR *)
  0xfa1f01ae;       (* arm_SBCS X14 X13 XZR *)
  0xda1f00e8;       (* arm_SBC X8 X7 XZR *)
  0xaa0e03e7;       (* arm_MOV X7 X14 *)
  0xb5fffc01;       (* arm_CBNZ X1 (word 2097024) *)
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

let BIGNUM_MOD_N384_EXEC = ARM_MK_EXEC_RULE bignum_mod_n384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_384 = new_definition `n_384 = 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643`;;

let n384longredlemma = prove
 (`!n. n < 2 EXP 64 * n_384
       ==> let q = MIN (n DIV 2 EXP 384 + 1) (2 EXP 64 - 1) in
           q < 2 EXP 64 /\
           q * n_384 <= n + n_384 /\
           n < q * n_384 + n_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[n_384] THEN ARITH_TAC);;

let BIGNUM_MOD_N384_CORRECT = time prove
 (`!z k x n pc.
      nonoverlapping (word pc,0x16c) (z,48)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n384_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = word (pc + 0x114) /\
                bignum_from_memory (z,6) s = n MOD n_384)
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
   [SUBGOAL_THEN `n MOD n_384 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP (64 * 5)` THEN
      ASM_REWRITE_TAC[LE_EXP; n_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
   BIGNUM_DIGITIZE_TAC "n_" `read(memory :> bytes(x,8 * 6)) s0` THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `k < 6 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5`)) THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
   EXPAND_TAC "n" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
   ASM_REWRITE_TAC[] THENL
    [ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (1--12);
     ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (1--15);
     ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (1--18);
     ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (1--21);
     ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (1--24);
     ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (1--26)] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
   ARITH_TAC;
   FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN

  (*** Initial 6-digit modulus ***)

  ENSURES_SEQUENCE_TAC `pc + 0x80`
   `\s. bignum_from_memory(x,k) s = n /\
        read X0 s = z /\
        read X2 s = x /\
        read X1 s = word(k - 6) /\
        read X15 s = word 0x1313e695333ad68d /\
        read X16 s = word 0xa7e5f24db74f5885 /\
        read X17 s = word 0x389cb27e0bc8d220 /\
        bignum_of_wordlist[read X3 s; read X4 s; read X5 s;
                           read X6 s; read X7 s; read X8 s] =
        (highdigits n (k - 6)) MOD n_384` THEN
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
    ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (1--5) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_shl (word j) 3) x = word_add x (word(8 * j))`]) THEN
    ARM_ACCSTEPS_TAC BIGNUM_MOD_N384_EXEC (21--26) (6--26) THEN
    SUBGOAL_THEN `carry_s26 <=> n_384 <= m` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[n_384; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (27--32) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s32" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
    ANTS_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * 6)` THEN
      ASM_REWRITE_TAC[n_384] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      UNDISCH_TAC `m < 2 EXP (64 * 6)` THEN REWRITE_TAC[n_384] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; n_384] THEN
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
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `0 < k - 6 /\ ~(k - 6 = 0)` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Setup of loop invariant ***)

  ENSURES_WHILE_DOWN_TAC `k - 6` `pc + 0x84` `pc + 0x104`
   `\i s. bignum_from_memory(x,k) s = n /\
          read X0 s = z /\
          read X2 s = x /\
          read X1 s = word i /\
          read X15 s = word 0x1313e695333ad68d /\
          read X16 s = word 0xa7e5f24db74f5885 /\
          read X17 s = word 0x389cb27e0bc8d220 /\
          bignum_of_wordlist[read X3 s; read X4 s; read X5 s;
                             read X6 s; read X7 s; read X8 s] =
          (highdigits n i) MOD n_384` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [VAL_INT64_TAC `k - 6` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `d0:int64` `read X3` THEN
    GHOST_INTRO_TAC `d1:int64` `read X4` THEN
    GHOST_INTRO_TAC `d2:int64` `read X5` THEN
    GHOST_INTRO_TAC `d3:int64` `read X6` THEN
    GHOST_INTRO_TAC `d4:int64` `read X7` THEN
    GHOST_INTRO_TAC `d5:int64` `read X8` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (1--4) THEN
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
  SUBGOAL_THEN `m < 2 EXP 64 * n_384` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MP_TAC(SPEC `m0:int64` VAL_BOUND_64) THEN
    ASM_REWRITE_TAC[n_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `highdigits n i MOD n_384 = m MOD n_384` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
    EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    EXPAND_TAC "m0" THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` n384longredlemma) THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN STRIP_TAC THEN

  (*** The computation of the quotient estimate q ***)

  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC BIGNUM_MOD_N384_EXEC [1] [1] THEN
  SUBGOAL_THEN
   `2 EXP 64 * bitval(read CF s1) + val(read X13 s1) = m DIV 2 EXP 384 + 1`
  MP_TAC THENL
   [EXPAND_TAC "m" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ARM_STEPS_TAC BIGNUM_MOD_N384_EXEC (2--3) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word q:int64` o MATCH_MP (MESON[]
   `!q. read X13 s = q' ==> q' = q ==> read X13 s = q`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "q" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[COND_SWAP] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES; WORD_OR_0] THEN
    SIMP_TAC[VAL_BOUND_64; WORD_VAL; ARITH_RULE
     `n < 2 EXP 64 ==> MIN n (2 EXP 64 - 1) = n`] THEN
    REWRITE_TAC[ARITH_RULE
     `MIN (2 EXP 64 + a) (2 EXP 64 - 1) = 2 EXP 64 - 1`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)] THEN
    REWRITE_TAC[WORD_OR_NOT0];
    DISCH_TAC THEN VAL_INT64_TAC `q:num`] THEN

  (*** The next digit in the current state ***)

  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `x:int64`; `s3:armstate`; `i:num`]
        BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word:num->int64` o SYM) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN DISCH_TAC THEN

  (*** A bit of fiddle to make the accumulation tactics work ***)

  ABBREV_TAC `w:int64 = word q` THEN
  UNDISCH_THEN `val(w:int64) = q` (SUBST_ALL_TAC o SYM) THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC o end_itlist CONJ) THEN

  (*** Subtraction of q * n_384 ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N384_EXEC (4--12) (4--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (i + 1)) (word 1):int64 = word i`]) THEN
  ARM_ACCSTEPS_TAC BIGNUM_MOD_N384_EXEC (15--22) (14--22) THEN
  SUBGOAL_THEN
   `sum_s22:int64 = word_neg(word(bitval(m < val(w:int64) * n_384))) /\
    &(bignum_of_wordlist
       [sum_s16; sum_s17; sum_s18; sum_s19; sum_s20; sum_s21]) =
        if m < val w * n_384 then &m - &(val w * n_384) + &2 pow 384
        else &m - &(val w * n_384)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MASK_AND_VALUE_FROM_CARRY_LT THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(w:int64) * n_384 <= m + n_384`;
        `m < val(w:int64) * n_384 + n_384`] THEN
      REWRITE_TAC[n_384; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV)] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; n_384] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REPEAT(MATCH_MP_TAC INTEGER_ADD THEN CONJ_TAC) THEN
    TRY REAL_INTEGER_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N384_EXEC [24;26;28;29;30;31] (23--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(w:int64)`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b <=> m < val(w:int64) * n_384` THEN
  REWRITE_TAC[REAL_ARITH
   `m - s - (w - b) * n:real = (m - w * n) + (b * n - s)`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[REAL_ADD_RID]
   `x = (if p then y + z else y) ==> x = y + (if p then z else &0)`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; n_384] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `x:real = y + z <=> y = x - z`] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_N384_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc returnaddress.
      nonoverlapping (word pc,0x16c) (z,48)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n384_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,6) s = n MOD n_384)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MOD_N384_EXEC BIGNUM_MOD_N384_CORRECT);;
