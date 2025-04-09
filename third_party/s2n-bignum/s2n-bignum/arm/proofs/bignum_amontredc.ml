(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Almost-Montgomery reduction of arbitrary bignum.                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_amontredc.o";;
 ****)

let bignum_amontredc_mc =
  define_assert_from_elf "bignum_amontredc_mc" "arm/generic/bignum_amontredc.o"
[
  0xb4000980;       (* arm_CBZ X0 (word 304) *)
  0xf940008d;       (* arm_LDR X13 X4 (Immediate_Offset (word 0)) *)
  0xd37ef5a6;       (* arm_LSL X6 X13 (rvalue (word 2)) *)
  0xcb0601a6;       (* arm_SUB X6 X13 X6 *)
  0xd27f00c6;       (* arm_EOR X6 X6 (rvalue (word 2)) *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0x9b061da7;       (* arm_MADD X7 X13 X6 X7 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0x9b0618e6;       (* arm_MADD X6 X7 X6 X6 *)
  0x9b087d07;       (* arm_MUL X7 X8 X8 *)
  0x9b061906;       (* arm_MADD X6 X8 X6 X6 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0x9b0618e6;       (* arm_MADD X6 X7 X6 X6 *)
  0x9b061906;       (* arm_MADD X6 X8 X6 X6 *)
  0xeb00005f;       (* arm_CMP X2 X0 *)
  0x9a822008;       (* arm_CSEL X8 X0 X2 Condition_CS *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xb4000108;       (* arm_CBZ X8 (word 32) *)
  0xf867786d;       (* arm_LDR X13 X3 (Shiftreg_Offset X7 3) *)
  0xf827782d;       (* arm_STR X13 X1 (Shiftreg_Offset X7 3) *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0xeb0800ff;       (* arm_CMP X7 X8 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xeb0000ff;       (* arm_CMP X7 X0 *)
  0x540000a2;       (* arm_BCS (word 20) *)
  0xf827783f;       (* arm_STR XZR X1 (Shiftreg_Offset X7 3) *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0xeb0000ff;       (* arm_CMP X7 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xb40005c5;       (* arm_CBZ X5 (word 184) *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xf940002b;       (* arm_LDR X11 X1 (Immediate_Offset (word 0)) *)
  0x9b067d69;       (* arm_MUL X9 X11 X6 *)
  0xf940008d;       (* arm_LDR X13 X4 (Immediate_Offset (word 0)) *)
  0x9b0d7d2c;       (* arm_MUL X12 X9 X13 *)
  0x9bcd7d2a;       (* arm_UMULH X10 X9 X13 *)
  0xab0c016b;       (* arm_ADDS X11 X11 X12 *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xd100040d;       (* arm_SUB X13 X0 (rvalue (word 1)) *)
  0xb40001ad;       (* arm_CBZ X13 (word 52) *)
  0xf868788d;       (* arm_LDR X13 X4 (Shiftreg_Offset X8 3) *)
  0xf868782b;       (* arm_LDR X11 X1 (Shiftreg_Offset X8 3) *)
  0x9b0d7d2c;       (* arm_MUL X12 X9 X13 *)
  0xba0a016b;       (* arm_ADCS X11 X11 X10 *)
  0x9bcd7d2a;       (* arm_UMULH X10 X9 X13 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0c016b;       (* arm_ADDS X11 X11 X12 *)
  0xd100050c;       (* arm_SUB X12 X8 (rvalue (word 1)) *)
  0xf82c782b;       (* arm_STR X11 X1 (Shiftreg_Offset X12 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xcb00010d;       (* arm_SUB X13 X8 X0 *)
  0xb5fffead;       (* arm_CBNZ X13 (word 2097108) *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0x8b070108;       (* arm_ADD X8 X8 X7 *)
  0xeb02011f;       (* arm_CMP X8 X2 *)
  0x54000082;       (* arm_BCS (word 16) *)
  0xf868786d;       (* arm_LDR X13 X3 (Shiftreg_Offset X8 3) *)
  0xab0d014a;       (* arm_ADDS X10 X10 X13 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xd1000408;       (* arm_SUB X8 X0 (rvalue (word 1)) *)
  0xf828782a;       (* arm_STR X10 X1 (Shiftreg_Offset X8 3) *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0xeb0500ff;       (* arm_CMP X7 X5 *)
  0x54fffbe3;       (* arm_BCC (word 2097020) *)
  0xcb0e03ee;       (* arm_NEG X14 X14 *)
  0xeb1f03e8;       (* arm_NEGS X8 XZR *)
  0xf868782d;       (* arm_LDR X13 X1 (Shiftreg_Offset X8 3) *)
  0xf868788b;       (* arm_LDR X11 X4 (Shiftreg_Offset X8 3) *)
  0x8a0e016b;       (* arm_AND X11 X11 X14 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xf828782d;       (* arm_STR X13 X1 (Shiftreg_Offset X8 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xcb00010d;       (* arm_SUB X13 X8 X0 *)
  0xb5ffff2d;       (* arm_CBNZ X13 (word 2097124) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_AMONTREDC_EXEC = ARM_MK_EXEC_RULE bignum_amontredc_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** This actually works mod 32 but if anything this is more convenient ***)

let WORD_NEGMODINV_SEED_LEMMA_16 = prove
 (`!a x:int64.
        ODD a /\
        word_xor (word_sub (word a) (word_shl (word a) 2)) (word 2) = x
        ==> (a * val x + 1 == 0) (mod 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONG; MOD_0] THEN
  TRANS_TAC EQ_TRANS
   `(val(word a:int64) MOD 16 * val(x:int64) MOD 16 + 1) MOD 16` THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    REWRITE_TAC[VAL_MOD; NUMSEG_LT; ARITH_EQ; ARITH]] THEN
  SUBGOAL_THEN `bit 0 (word a:int64)` MP_TAC THENL
   [ASM_REWRITE_TAC[BIT_LSB_WORD];
    EXPAND_TAC "x" THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 1 (word a:int64)`;`bit 2 (word a:int64)`;`bit 3 (word a:int64)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_AMONTREDC_CORRECT = time prove
 (`!k z r x m p a n pc.
        nonoverlapping (word pc,0x134) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
        val p < 2 EXP 61 /\ val r < 2 EXP 61
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_amontredc_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k; z; r; x; m; p] s /\
                  bignum_from_memory (x,val r) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = word(pc + 0x130) /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        inverse_mod n (2 EXP (64 * val p)) *
                        lowdigits a (val k + val p)) (mod n)))
             (MAYCHANGE [PC; X6; X7; X8; X9; X10; X11; X12; X13; X14] ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `nx:num` THEN X_GEN_TAC `x:int64` THEN
  X_GEN_TAC `m:int64` THEN W64_GEN_TAC `p:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  BIGNUM_TERMRANGE_TAC `nx:num` `a:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ODD];
    ALL_TAC] THEN

  (*** Initial word-level modular inverse ***)

  ENSURES_SEQUENCE_TAC `pc + 0x38`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word nx /\
        read X3 s = x /\
        read X4 s = m /\
        read X5 s = word p /\
        bignum_from_memory (x,nx) s = a /\
        bignum_from_memory (m,k) s = n /\
        (ODD n ==> (n * val(read X6 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `bignum_from_memory(m,k) s0 = highdigits n 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC LAND_CONV[BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC] THEN
    ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--5) THEN
    SUBGOAL_THEN `ODD n ==> (n * val (read X6 s5) + 1 == 0) (mod 16)`
    MP_TAC THENL [ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16]; ALL_TAC] THEN
    REABBREV_TAC `x0 = read X6 s5` THEN DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (6--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:num` `\s. val(read X6 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64]] THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  VAL_INT64_TAC `w:num` THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_1)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Initialization of the output buffer ***)

  ENSURES_SEQUENCE_TAC `pc + 0x78`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word nx /\
        read X3 s = x /\
        read X4 s = m /\
        read X5 s = word p /\
        bignum_from_memory (word_add x (word (8 * k)),nx - k) s =
        highdigits a k /\
        bignum_from_memory (m,k) s = n /\
        read X6 s = word w /\
        bignum_from_memory (z,k) s = lowdigits a k /\
        read X14 s = word 0` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `nx = 0` THENL
     [UNDISCH_THEN `nx = 0` SUBST_ALL_TAC THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
      ENSURES_WHILE_UP_TAC `k:num` `pc + 0x64` `pc + 0x6c`
       `\i s. read X0 s = word k /\
              read X1 s = z /\
              read X2 s = word 0 /\
              read X3 s = x /\
              read X4 s = m /\
              read X5 s = word p /\
              bignum_from_memory (m,k) s = n /\
              read X6 s = word w /\
              read X7 s = word i /\
              bignum_from_memory (z,i) s = 0` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--4) THEN
        ASM_REWRITE_TAC[LE; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
        ARITH_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--2);
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--3) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[LOWDIGITS_TRIVIAL] THEN
        REWRITE_TAC[LE; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; SUB_0] THEN
        REWRITE_TAC[HIGHDIGITS_TRIVIAL]];
      ALL_TAC] THEN

    (*** Copyloop ***)

    ENSURES_WHILE_UP_TAC `MIN k nx` `pc + 0x48` `pc + 0x54`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = word nx /\
            read X3 s = x /\
            read X4 s = m /\
            read X5 s = word p /\
            bignum_from_memory (m,k) s = n /\
            read X6 s = word w /\
            read X7 s = word i /\
            read X8 s = word(MIN k nx) /\
            bignum_from_memory(word_add x (word(8 * i)),nx - i) s =
            highdigits a i /\
            bignum_from_memory (z,i) s = lowdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `MIN a b = 0 <=> a = 0 \/ b = 0`];
      ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--4) THEN
      MATCH_MP_TAC(TAUT `q /\ (q ==> p) /\ r ==> p /\ q /\ r`) THEN
      CONJ_TAC THENL [REWRITE_TAC[MIN] THEN MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      DISCH_THEN SUBST1_TAC THEN VAL_INT64_TAC `MIN k nx` THEN
      ASM_REWRITE_TAC[ARITH_RULE `MIN a b = 0 <=> a = 0 \/ b = 0`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `i:num < nx /\ i < k` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      VAL_INT64_TAC `MIN k nx` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    (*** Now consider the cases again ***)

    ASM_CASES_TAC `k:num <= nx` THENL
     [ASM_SIMP_TAC[ARITH_RULE `k <= nx ==> MIN k nx = k`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
      ASM_SIMP_TAC[ARITH_RULE `nx < k ==> MIN k nx = nx`]] THEN

    (*** Padloop following copyloop ***)

    ENSURES_WHILE_AUP_TAC `nx:num` `k:num` `pc + 0x64` `pc + 0x6c`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = word nx /\
            read X3 s = x /\
            read X4 s = m /\
            read X5 s = word p /\
            bignum_from_memory (m,k) s = n /\
            read X6 s = word w /\
            read X7 s = word i /\
            bignum_from_memory (z,i) s = lowdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--4) THEN
      ASM_REWRITE_TAC[GSYM NOT_LT];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      SIMP_TAC[VAL_WORD_0; LOWDIGITS_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
      MATCH_MP_TAC(NUM_RING `d = 0 ==> a = e * d + a`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num <= i` THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--2);
      ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--3) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_SIMP_TAC[ARITH_RULE `nx < k ==> nx - k = 0`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC HIGHDIGITS_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num < k` THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Another semi-degenerate case p = 0, where we're done after init ***)

  ASM_CASES_TAC `p = 0` THENL
   [UNDISCH_THEN `p = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC [1] THEN DISCH_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; INVERSE_MOD_1; EXP; ADD_CLAUSES; CONG_REFL];
    ALL_TAC] THEN

  (*** Setup of the main loop, and corrective ending ***)

  ENSURES_WHILE_UP_TAC `p:num` `pc + 0x80` `pc + 0x100`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = word nx /\
          read X3 s = x /\
          read X4 s = m /\
          read X5 s = word p /\
          read X6 s = word w /\
          read X7 s = word i /\
          bignum_from_memory (m,k) s = n /\
          bignum_from_memory(word_add x (word(8 * (k + i))),nx - (k + i)) s =
          highdigits a (k + i) /\
          ?q r. q < 2 EXP (64 * i) /\ r < 2 EXP (64 * i) /\
                2 EXP (64 * i) *
                (2 EXP (64 * k) * val(read X14 s) +
                 bignum_from_memory(z,k) s) +
                r =
                q * n + lowdigits a (k + i) /\
                (ODD n ==> r = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_0] THEN
    REPEAT(EXISTS_TAC `0`) THEN ARITH_TAC;

    ALL_TAC; (*** This is the main loop invariant: save for later ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** This is the corrective subtraction part.... ***)

    GHOST_INTRO_TAC `cout:num` `\s. val(read X14 s)` THEN
    GHOST_INTRO_TAC `mm:num` `bignum_from_memory(z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `mm:num` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `cout < 2` MP_TAC THENL
     [SUBGOAL_THEN `q * n + lowdigits a (k + p) < 2 EXP (64 * (k + p)) * 2`
      MP_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x < e /\ y < e ==> x + y < e * 2`) THEN
        REWRITE_TAC[LOWDIGITS_BOUND] THEN
        REWRITE_TAC[ARITH_RULE `64 * (k + p) = 64 * p + 64 * k`] THEN
        ASM_SIMP_TAC[LT_MULT2; EXP_ADD];
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
        REWRITE_TAC[ARITH_RULE `64 * k + 64 * p = 64 * (p + k)`] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `a + b:num < c ==> a < c`)) THEN
        REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
        REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
      GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT]] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:bool` SUBST_ALL_TAC) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN
    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x110` `pc + 0x128`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X4 s = m /\
            read X14 s = word_neg(word(bitval c)) /\
            read X8 s = word i /\
            bignum_from_memory (word_add z (word(8 * i)),k - i) s =
            highdigits mm i /\
            bignum_from_memory (word_add m (word(8 * i)),k - i) s =
            highdigits n i /\
            &(bignum_from_memory(z,i) s):real =
            &2 pow (64 * i) * &(bitval(~read CF s)) +
            &(lowdigits mm i) - &(bitval c) * &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB_LZERO; SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BITVAL_CLAUSES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [4] (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                  LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
      REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
               BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      DISCH_TAC THEN UNDISCH_TAC `ODD n ==> r = 0` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])] THEN
   FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `e * x:num = q * n + ab
      ==> (i * e == 1) (mod n) /\ (y == x) (mod n)
          ==> (y == i * ab) (mod n)`)) THEN
   ASM_REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
   REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
   MATCH_MP_TAC(INTEGER_RULE
    `x = (e - n) * c + m ==> (x:int == e * c + m) (mod n)`) THEN
   MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow (64 * k)` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC(INT_ARITH
      `&0 <= x /\ x < e /\ &0 <= y /\ y < e ==> abs(x - y:int) < e`) THEN
     ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; LT_IMP_LE; LE_0] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
     UNDISCH_TAC
      `2 EXP (64 * p) * (2 EXP (64 * k) * bitval c + mm) =
      q * n + lowdigits a (k + p)` THEN
     ASM_CASES_TAC `c:bool` THEN
     ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; BITVAL_CLAUSES] THEN
     ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> ((e - n) + m < e <=> m < n)`] THEN
     DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
      `e * (d + m):num = qn + ab ==> ab < e * d ==> e * m < qn`)) THEN
     REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM EXP_ADD)] THEN
     REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; LOWDIGITS_BOUND] THEN
     REWRITE_TAC[GSYM NOT_LE; CONTRAPOS_THM] THEN
     ASM_SIMP_TAC[LE_MULT2; LT_IMP_LE];
     REWRITE_TAC[INTEGER_RULE
      `(z:int == (e - n) * c + m) (mod e) <=> (z + n * c == m) (mod e)`] THEN
     REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
     REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
     ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; LOWDIGITS_SELF] THEN
     REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC] THEN
     REWRITE_TAC[REAL_FIELD
      `(&2 pow n * x + y) / &2 pow n = x + y / &2 pow n`] THEN
     REAL_INTEGER_TAC]] THEN

  (*** Start on the main outer loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cout:num` `\s. val(read X14 s)` THEN
  GHOST_INTRO_TAC `z1:num` `bignum_from_memory(z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  (*** The initial prelude of the Montgomery reduction ***)

  ABBREV_TAC `q0 = (w * z1) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xa0`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word nx /\
        read X3 s = x /\
        read X4 s = m /\
        read X5 s = word p /\
        read X6 s = word w /\
        read X7 s = word i /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (word_add x (word (8 * (k + i))),nx - (k + i)) s =
        highdigits a (k + i) /\
        read X14 s = word cout /\
        bignum_from_memory (z,k) s = z1 /\
        read X9 s = word q0 /\
        read X8 s = word 1 /\
        read X13 s = word(k - 1) /\
        2 EXP 64 * (bitval(read CF s) + val(read X10 s)) + val(read X11 s) =
        q0 * bigdigit n 0 + bigdigit z1 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(m,k) s0 = highdigits n 0 /\
      bignum_from_memory(z,k) s0 = highdigits z1 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [4;6] (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[ADD_CLAUSES; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Break at "montend" to share the end reasoning ***)

  GHOST_INTRO_TAC `r0:num` `\s. val(read X11 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_SEQUENCE_TAC `pc + 0xd4`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word nx /\
        read X3 s = x /\
        read X4 s = m /\
        read X5 s = word p /\
        read X6 s = word w /\
        read X7 s = word i /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (word_add x (word (8 * (k + i))),nx - (k + i)) s =
        highdigits a (k + i) /\
        read X14 s = word cout /\
        read X9 s = word q0 /\
        read X8 s = word k /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read X10 s)) +
        2 EXP 64 * bignum_from_memory (z,k - 1) s +
        r0 =
        lowdigits z1 k + q0 * lowdigits n k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0xa4` `pc + 0xcc`
     `\j s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = word nx /\
            read X3 s = x /\
            read X4 s = m /\
            read X5 s = word p /\
            read X6 s = word w /\
            read X7 s = word i /\
            bignum_from_memory (m,k) s = n /\
            bignum_from_memory
             (word_add x (word (8 * (k + i))),nx - (k + i)) s =
            highdigits a (k + i) /\
            read X14 s = word cout /\
            read X9 s = word q0 /\
            read X8 s = word j /\
            bignum_from_memory(word_add z (word (8 * j)),k - j) s =
            highdigits z1 j /\
            bignum_from_memory(word_add m (word (8 * j)),k - j) s =
            highdigits n j /\
            2 EXP (64 * j) * (bitval(read CF s) + val(read X10 s)) +
            2 EXP 64 * bignum_from_memory(z,j-1) s + r0 =
            lowdigits z1 j + q0 * lowdigits n j` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[GSYM highdigits; BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_1] THEN ARITH_TAC;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`j:num`; `j - 1`] THEN
      SUBGOAL_THEN `word_sub (word j) (word 1):int64 = word(j - 1)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X10` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - j:num`; `a:num`; `j:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      UNDISCH_THEN `val(word q0:int64) = q0` (K ALL_TAC) THEN
      SUBGOAL_THEN `nonoverlapping (word_add z (word (8 * (j - 1))):int64,8)
                                   (word_add x (word (8 * (k + i))),
                                    8 * (nx - (k + i)))`
      MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
       [ASM_CASES_TAC `nx - (k + i) = 0` THEN
        ASM_SIMP_TAC[MULT_CLAUSES; NONOVERLAPPING_MODULO_TRIVIAL] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SUB_EQ_0; NOT_LE]) THEN
        FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
         [ALL_TAC;
          GEN_REWRITE_TAC LAND_CONV [NONOVERLAPPING_MODULO_SYM] THEN
          MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
              NONOVERLAPPING_MODULO_SUBREGIONS) THEN
          CONJ_TAC THEN CONTAINED_TAC] THEN
        SUBGOAL_THEN
         `word_add z (word (8 * (k + i))):int64 =
          word_add (word_add z (word(8 * (j - 1))))
                   (word(8 + 8 * ((k + i) - j)))`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
          NONOVERLAPPING_TAC];
        DISCH_TAC] THEN
      ABBREV_TAC `j' = j - 1` THEN
      SUBGOAL_THEN `j = j' + 1` SUBST_ALL_TAC THENL
       [EXPAND_TAC "j'" THEN UNDISCH_TAC `1 <= j` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(j' + 1) + 1 = j' + 2`]) THEN
      REWRITE_TAC[ARITH_RULE `(j' + 1) + 1 = j' + 2`] THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [3;4;6;7] (1--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(n + 2) - 1 = n + 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `j' + 2 = (j' + 1) + 1` MP_TAC THENL
       [ARITH_TAC; DISCH_THEN SUBST_ALL_TAC] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `(e * d1 + d0) + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (j + 1) = 64 * j + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
         [TAUT `p /\ q /\ r /\ s <=> p /\ r /\ q /\ s`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`j:num`; `j - 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]];

    ALL_TAC] THEN

  SUBGOAL_THEN `cout < 2` MP_TAC THENL
   [SUBGOAL_THEN `q * n + lowdigits a (k + i) < 2 EXP (64 * (k + i)) * 2`
    MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x < e /\ y < e ==> x + y < e * 2`) THEN
      REWRITE_TAC[LOWDIGITS_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (k + p) = 64 * p + 64 * k`] THEN
      ASM_SIMP_TAC[LT_MULT2; EXP_ADD];
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ARITH_RULE `64 * k + 64 * p = 64 * (p + k)`] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `a + b:num < c ==> a < c`)) THEN
      REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `tc:bool` SUBST_ALL_TAC)] THEN

  (*** Just case split over the "off the end" and share remainder ***)

  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read X10` THEN
  VAL_INT64_TAC `k - 1` THEN
  SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`];
    ALL_TAC] THEN
  VAL_INT64_TAC `k + i:num` THEN
  MP_TAC(WORD_RULE `word_add (word k) (word i):int64 = word(k + i)`) THEN
  DISCH_TAC THEN

  ASM_CASES_TAC `nx:num <= k + i` THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [1] (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `nx <= k + i ==> nx - (k + i + 1) = 0`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC SYM_CONV THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
       MATCH_MP_TAC HIGHDIGITS_ZERO THEN
       TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num <= k + i` THEN
      ARITH_TAC;
      ALL_TAC];

    SUBGOAL_THEN `nonoverlapping (word_add z (word (8 * (k - 1))):int64,8)
                                 (word_add x (word (8 * (k + i))),
                                  8 * (nx - (k + i)))`
    MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
       [ALL_TAC;
        GEN_REWRITE_TAC LAND_CONV [NONOVERLAPPING_MODULO_SYM] THEN
        MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
            NONOVERLAPPING_MODULO_SUBREGIONS) THEN
        CONJ_TAC THEN CONTAINED_TAC] THEN
      SUBGOAL_THEN
       `word_add z (word (8 * (k + i))):int64 =
        word_add (word_add z (word(8 * (k - 1))))
                 (word(8 + 8 * ((k + i) - k)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        NONOVERLAPPING_TAC];
      DISCH_TAC] THEN

    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0] THEN
    REWRITE_TAC[ARITH_RULE `n - (k + i) - 1 = n - (k + i + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `(k + i) + 1 = k + i + 1`] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [1;7;8] (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]] THEN

  (MAP_EVERY EXISTS_TAC
    [`2 EXP (64 * i) * q0 + q`;
     `2 EXP (64 * i) * r0 + r`] THEN
   GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
    [REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
     CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `q1 < e /\ q0 < ee /\ (q1 < e ==> (q1 + 1) * ee <= e * ee)
       ==> ee * q1 + q0 < ee * e`) THEN
     ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
     ASM_REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [ALL_TAC;
     DISCH_THEN(fun th ->
       REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th))) THEN
     ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     ASM_REWRITE_TAC[EXP_LT_0; ARITH_EQ] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
      `ee * x + e * y + r = z
       ==> e divides ee /\ (z == 0) (mod e)
           ==> (r == 0) (mod e)`)) THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
       UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
       UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM)] THEN
     REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
     REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
      `(n * w + 1 == 0) (mod e) ==> (z + (w * z) * n == 0) (mod e)`) THEN
     ASM_REWRITE_TAC[]] THEN
   SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
    [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
   ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
   REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
   REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
   SUBGOAL_THEN `(i + 1) + (k - 1) = i + k` SUBST1_TAC THENL
    [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES] THEN
   REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE `k + i + 1 = (k + i) + 1`]) THEN
  REWRITE_TAC[ARITH_RULE `64 * (k + i) = 64 * k + 64 * i`; EXP_ADD] THENL
   [REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
    SUBGOAL_THEN `bigdigit a (k + i) = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC BIGDIGIT_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num <= k + i` THEN
      ARITH_TAC;
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_BITVAL; ADD_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC REAL_RING;

    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_BITVAL; ADD_CLAUSES;
                 BIGDIGIT_BOUND] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC REAL_RING]);;

let BIGNUM_AMONTREDC_SUBROUTINE_CORRECT = time prove
 (`!k z r x m p a n pc returnaddress.
        nonoverlapping (word pc,0x134) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
        val p < 2 EXP 61 /\ val r < 2 EXP 61
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_amontredc_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; r; x; m; p] s /\
                  bignum_from_memory (x,val r) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        inverse_mod n (2 EXP (64 * val p)) *
                        lowdigits a (val k + val p)) (mod n)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_AMONTREDC_EXEC BIGNUM_AMONTREDC_CORRECT);;
