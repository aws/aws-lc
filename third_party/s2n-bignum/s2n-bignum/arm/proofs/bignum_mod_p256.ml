(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo p_256, the field characteristic for NIST curve P-256.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p256/bignum_mod_p256.o";;
 ****)

let bignum_mod_p256_mc =
  define_assert_from_elf "bignum_mod_p256_mc" "arm/p256/bignum_mod_p256.o"
[
  0xf100103f;       (* arm_CMP X1 (rvalue (word 4)) *)
  0x54000603;       (* arm_BCC (word 192) *)
  0xd1001021;       (* arm_SUB X1 X1 (rvalue (word 4)) *)
  0xd37df027;       (* arm_LSL X7 X1 (rvalue (word 3)) *)
  0x8b0200e7;       (* arm_ADD X7 X7 X2 *)
  0xa94118e5;       (* arm_LDP X5 X6 X7 (Immediate_Offset (iword (&16))) *)
  0xa94010e3;       (* arm_LDP X3 X4 X7 (Immediate_Offset (iword (&0))) *)
  0xb2407fec;       (* arm_MOV X12 (rvalue (word 4294967295)) *)
  0xb26083ed;       (* arm_MOV X13 (rvalue (word 18446744069414584321)) *)
  0xb1000467;       (* arm_ADDS X7 X3 (rvalue (word 1)) *)
  0xfa0c0088;       (* arm_SBCS X8 X4 X12 *)
  0xfa1f00a9;       (* arm_SBCS X9 X5 XZR *)
  0xfa0d00ca;       (* arm_SBCS X10 X6 X13 *)
  0x9a873063;       (* arm_CSEL X3 X3 X7 Condition_CC *)
  0x9a883084;       (* arm_CSEL X4 X4 X8 Condition_CC *)
  0x9a8930a5;       (* arm_CSEL X5 X5 X9 Condition_CC *)
  0x9a8a30c6;       (* arm_CSEL X6 X6 X10 Condition_CC *)
  0xb40003a1;       (* arm_CBZ X1 (word 116) *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xf8617847;       (* arm_LDR X7 X2 (Shiftreg_Offset X1 3) *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93c580ce;       (* arm_EXTR X14 X6 X5 (rvalue (word 32)) *)
  0xba0e00bf;       (* arm_ADCS XZR X5 X14 *)
  0xd360fcce;       (* arm_LSR X14 X6 (rvalue (word 32)) *)
  0xba0e00ce;       (* arm_ADCS X14 X6 X14 *)
  0xda9f33e8;       (* arm_CSETM X8 Condition_CS *)
  0xaa0801ce;       (* arm_ORR X14 X14 X8 *)
  0xd3607dc8;       (* arm_LSL X8 X14 (rvalue (word 32)) *)
  0xd360fdc9;       (* arm_LSR X9 X14 (rvalue (word 32)) *)
  0xab0800aa;       (* arm_ADDS X10 X5 X8 *)
  0x9a0900cb;       (* arm_ADC X11 X6 X9 *)
  0xeb0e03e6;       (* arm_NEGS X6 X14 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xeb0600e7;       (* arm_SUBS X7 X7 X6 *)
  0xfa080068;       (* arm_SBCS X8 X3 X8 *)
  0xfa090089;       (* arm_SBCS X9 X4 X9 *)
  0xfa0e014a;       (* arm_SBCS X10 X10 X14 *)
  0xda0e016b;       (* arm_SBC X11 X11 X14 *)
  0xab0b00e3;       (* arm_ADDS X3 X7 X11 *)
  0x8a0b0187;       (* arm_AND X7 X12 X11 *)
  0xba070104;       (* arm_ADCS X4 X8 X7 *)
  0xba1f0125;       (* arm_ADCS X5 X9 XZR *)
  0x8a0b01a7;       (* arm_AND X7 X13 X11 *)
  0x9a070146;       (* arm_ADC X6 X10 X7 *)
  0xb5fffca1;       (* arm_CBNZ X1 (word 2097044) *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xb4ffff21;       (* arm_CBZ X1 (word 2097124) *)
  0xf9400043;       (* arm_LDR X3 X2 (Immediate_Offset (word 0)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffec0;       (* arm_BEQ (word 2097112) *)
  0xf9400444;       (* arm_LDR X4 X2 (Immediate_Offset (word 8)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffe60;       (* arm_BEQ (word 2097100) *)
  0xf9400845;       (* arm_LDR X5 X2 (Immediate_Offset (word 16)) *)
  0x17fffff1        (* arm_B (word 268435396) *)
];;

let BIGNUM_MOD_P256_EXEC = ARM_MK_EXEC_RULE bignum_mod_p256_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let p256longredlemma = prove
 (`!n. n < 2 EXP 64 * p_256
       ==> let q = MIN ((n DIV 2 EXP 192 + n DIV 2 EXP 224 + 1) DIV 2 EXP 64)
                       (2 EXP 64 - 1) in
           q < 2 EXP 64 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

let BIGNUM_MOD_P256_CORRECT = time prove
 (`!z k x n pc.
      nonoverlapping (word pc,0xf8) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p256_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = word (pc + 0xc0) /\
                bignum_from_memory (z,4) s = n MOD p_256)
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X_GEN_TAC `z:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Case split over the k < 4 case, which is a different path ***)

  ASM_CASES_TAC `k < 4` THENL
   [SUBGOAL_THEN `n MOD p_256 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP (64 * 3)` THEN
      ASM_REWRITE_TAC[LE_EXP; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
   BIGNUM_DIGITIZE_TAC "n_" `read(memory :> bytes(x,8 * 4)) s0` THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `k < 4 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`)) THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
   EXPAND_TAC "n" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
   ASM_REWRITE_TAC[] THENL
    [ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC (1--9);
     ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC (1--12);
     ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC (1--15);
     ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC (1--17)] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
   ARITH_TAC;
   FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN

  (*** Initial 4-digit modulus ***)

  ENSURES_SEQUENCE_TAC `pc + 0x44`
   `\s. bignum_from_memory(x,k) s = n /\
        read X0 s = z /\
        read X2 s = x /\
        read X1 s = word(k - 4) /\
        read X12 s = word 0xffffffff /\
        read X13 s = word 0xffffffff00000001 /\
        bignum_of_wordlist[read X3 s; read X4 s; read X5 s; read X6 s] =
        (highdigits n (k - 4)) MOD p_256` THEN
  CONJ_TAC THENL
   [ABBREV_TAC `j = k - 4` THEN VAL_INT64_TAC `j:num` THEN
    SUBGOAL_THEN `word_sub (word k) (word 4):int64 = word j` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `k - 4 = j`)) THEN
      REWRITE_TAC[WORD_SUB] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[highdigits] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_DIV] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    SUBST1_TAC(SYM(ASSUME `k - 4 = j`)) THEN
    ASM_SIMP_TAC[ARITH_RULE `4 <= k ==> k - (k - 4) = 4`] THEN
    ABBREV_TAC `m = bignum_from_memory(word_add x (word (8 * j)),4) s0` THEN
    SUBGOAL_THEN `m < 2 EXP (64 * 4)` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV)) THEN
    BIGNUM_DIGITIZE_TAC "m_"
     `read (memory :> bytes (word_add x (word(8 * j)),8 * 4)) s0` THEN
    ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC (1--5) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_shl (word j) 3) x = word_add x (word(8 * j))`]) THEN
    ARM_ACCSTEPS_TAC BIGNUM_MOD_P256_EXEC (10--13) (6--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_BITVAL_NOT]) THEN
    SUBGOAL_THEN `carry_s13 <=> m < p_256` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`64 * 4`; `if m < p_256 then &m:real else &(m - p_256)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[p_256] THEN ARITH_TAC;
      REWRITE_TAC[p_256] THEN ARITH_TAC;
      ALL_TAC;
      REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MOD_CASES THEN UNDISCH_TAC `m < 2 EXP (64 * 4)` THEN
      REWRITE_TAC[p_256] THEN ARITH_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXPAND_TAC "m" THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      REAL_INTEGER_TAC;
      FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Finish off the k = 4 case which is now just the writeback ***)

  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o MATCH_MP (ARITH_RULE
   `4 <= k ==> k = 4 \/ 4 < k`))
  THENL
   [GHOST_INTRO_TAC `d0:int64` `read X3` THEN
    GHOST_INTRO_TAC `d1:int64` `read X4` THEN
    GHOST_INTRO_TAC `d2:int64` `read X5` THEN
    GHOST_INTRO_TAC `d3:int64` `read X6` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `0 < k - 4 /\ ~(k - 4 = 0)` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Setup of loop invariant ***)

  ENSURES_WHILE_DOWN_TAC `k - 4` `pc + 0x48` `pc + 0xb4`
   `\i s. bignum_from_memory(x,k) s = n /\
          read X0 s = z /\
          read X2 s = x /\
          read X1 s = word i /\
          read X12 s = word 0xffffffff /\
          read X13 s = word 0xffffffff00000001 /\
          bignum_of_wordlist[read X3 s; read X4 s; read X5 s; read X6 s] =
          (highdigits n i) MOD p_256` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [VAL_INT64_TAC `k - 4` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `d0:int64` `read X3` THEN
    GHOST_INTRO_TAC `d1:int64` `read X4` THEN
    GHOST_INTRO_TAC `d2:int64` `read X5` THEN
    GHOST_INTRO_TAC `d3:int64` `read X6` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC (1--3) THEN
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
  GLOBALIZE_PRECONDITION_TAC THEN
  ABBREV_TAC `m0:int64 = word(bigdigit n i)` THEN
  ABBREV_TAC `m = bignum_of_wordlist[m0; m1; m2; m3; m4]` THEN
  SUBGOAL_THEN `m < 2 EXP 64 * p_256` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MP_TAC(SPEC `m0:int64` VAL_BOUND_64) THEN
    ASM_REWRITE_TAC[p_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `highdigits n i MOD p_256 = m MOD p_256` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
    EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    EXPAND_TAC "m0" THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` p256longredlemma) THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN STRIP_TAC THEN

  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  (*** The next digit in the current state ***)

  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `x:int64`; `s0:armstate`; `i:num`]
        BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word:num->int64` o SYM) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN DISCH_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (i + 1)) (word 1) = word i`]) THEN

  (*** The computation of the quotient estimate q ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_P256_EXEC [5;7] (2--7) THEN

  SUBGOAL_THEN
   `2 EXP 64 * bitval(read CF s7) + val(read X14 s7) =
    (m DIV 2 EXP 192 + m DIV 2 EXP 224 + 1) DIV 2 EXP 64`
  MP_TAC THENL
   [EXPAND_TAC "m" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT; VAL_WORD_USHR] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    W(MP_TAC o C SPEC VAL_BOUND_64 o rand o rand o lhand o lhand o snd) THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ARM_STEPS_TAC BIGNUM_MOD_P256_EXEC (8--9) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word q:int64` o MATCH_MP (MESON[]
   `!q. read X14 s = q' ==> q' = q ==> read X14 s = q`)) THEN
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

  (*** A bit of fiddle to make the accumulation tactics work ***)

  ABBREV_TAC `w:int64 = word q` THEN
  UNDISCH_THEN `val(w:int64) = q` (SUBST_ALL_TAC o SYM) THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC o end_itlist CONJ) THEN

  (*** Main subtraction of q * p_256 ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_P256_EXEC (11--21) (10--21) THEN

  SUBGOAL_THEN
   `2 EXP 320 * bitval carry_s13 +
    bignum_of_wordlist [sum_s17; sum_s18; sum_s19; sum_s20; sum_s21] +
    val(w:int64) * p_256 =
    2 EXP 320 * bitval carry_s21 + m`
  ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `sum_s21:int64 = word_neg(word(bitval(m < val w * p_256))) /\
    (carry_s21 /\ ~carry_s13 <=> m < val(w:int64) * p_256)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(w:int64) * p_256 <= m + p_256`;
        `m < val(w:int64) * p_256 + p_256`] THEN
      REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      FIRST_ASSUM(fun th -> SUBST1_TAC(MATCH_MP
        (MESON[REAL_OF_NUM_ADD; REAL_ARITH `a:real = b + x ==> x = a - b`]
       `a = b + x ==> &x:real = &a - &b`) th) THEN MP_TAC th) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      MAP_EVERY ASM_CASES_TAC [`carry_s13:bool`; `carry_s21:bool`] THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      TRY(DISCH_THEN(K ALL_TAC) THEN BOUNDER_TAC[]) THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0:real <= x /\ m < e ==> ~(e * &1 + x = e * &0 + m)`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      SUBST1_TAC(ARITH_RULE `320 = 64 * 5`) THEN
      EXPAND_TAC "m" THEN MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_P256_EXEC [22;24;25;27] (22--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[bignum_of_wordlist] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(w:int64)`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b <=> m < val(w:int64) * p_256` THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC
   `2 EXP 320 * bitval carry_s13 +
    bignum_of_wordlist [sum_s17; sum_s18; sum_s19; sum_s20;
                        word_neg (word (bitval b))] +
    val(w:int64) * p_256 =
    2 EXP 320 * bitval carry_s21 + m` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256; bignum_of_wordlist] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP
   (REAL_ARITH `a:real = b + x ==> x = a - b`)) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_P256_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc returnaddress.
      nonoverlapping (word pc,0xf8) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_p256_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = n MOD p_256)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MOD_P256_EXEC BIGNUM_MOD_P256_CORRECT);;
