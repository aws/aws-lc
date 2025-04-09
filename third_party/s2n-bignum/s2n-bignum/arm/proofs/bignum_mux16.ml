(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 16-way multiplexing for k-length bignums.                                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_mux16.o";;
 ****)

let bignum_mux16_mc =
  define_assert_from_elf "bignum_mux16_mc" "arm/generic/bignum_mux16.o"
[
  0xab1f0007;       (* arm_ADDS X7 X0 XZR *)
  0x540008a0;       (* arm_BEQ (word 276) *)
  0x9b007c63;       (* arm_MUL X3 X3 X0 *)
  0xf9400044;       (* arm_LDR X4 X2 (Immediate_Offset (word 0)) *)
  0xaa0003e6;       (* arm_MOV X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf8667845;       (* arm_LDR X5 X2 (Shiftreg_Offset X6 3) *)
  0xeb0300df;       (* arm_CMP X6 X3 *)
  0x9a8400a4;       (* arm_CSEL X4 X5 X4 Condition_EQ *)
  0x8b0000c6;       (* arm_ADD X6 X6 X0 *)
  0xf9000024;       (* arm_STR X4 X1 (Immediate_Offset (word 0)) *)
  0x91002021;       (* arm_ADD X1 X1 (rvalue (word 8)) *)
  0x91002042;       (* arm_ADD X2 X2 (rvalue (word 8)) *)
  0xf10004e7;       (* arm_SUBS X7 X7 (rvalue (word 1)) *)
  0x54fff7c1;       (* arm_BNE (word 2096888) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUX16_EXEC = ARM_MK_EXEC_RULE bignum_mux16_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUX16_CORRECT = prove
 (`!k z xs i n pc.
     nonoverlapping (word pc,0x11c) (z,8 * val k) /\
     nonoverlapping (xs,8 * 16 * val k) (z,8 * val k)
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mux16_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [k; z; xs; i] s /\
                (!j. j < 16
                     ==> bignum_from_memory
                          (word_add xs (word(8 * val k * j)),val k) s = n j))
           (\s. read PC s = word (pc + 0x118) /\
                (val i < 16 ==> bignum_from_memory (z,val k) s = n (val i)))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`] THEN
  W64_GEN_TAC `i:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num->num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  STRIP_TAC THEN

  (*** We explicitly expand out the 16-fold stuff in many places here.  ***)
  (*** This is tolerable for 16 but still clumsy. It would be better    ***)
  (*** to have the simulation machinery handle bounded quantifiers, but ***)
  (*** currently the automation showing state components are maintained ***)
  (*** (e.g. READ_OVER_WRITE_ORTHOGONAL_TAC) only allows free subterms. ***)
  (*** It would not be hard to fix this, but for now we work around it. ***)

  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    REWRITE_TAC[ARITH_RULE `0 = x <=> x = 0`] THEN
    ARM_SIM_TAC BIGNUM_MUX16_EXEC (1--2) THEN
    SPEC_TAC(`i:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN

  (*** Get bounds on the individual bignums being selected ***)

  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`)
   (map (fun i -> vsubst[mk_small_numeral i,`i:num`] `(n:num->num) i`)
        (0--15)) THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0xc` `pc + 0x114`
   `\j s. (read X0 s = word k /\
           read X1 s = word_add z (word(8 * j)) /\
           read X2 s = word_add x (word(8 * j)) /\
           read X3 s = word(k * i) /\
           read X7 s = word(k - j) /\
           (!l. l < 16
                ==> bignum_from_memory
                     (word_add (word_add x (word (8 * k * l)))
                               (word(8 * j)),k - j) s =
                    highdigits (n l) j) /\
           (i < 16 ==> bignum_from_memory(z,j) s = lowdigits (n i) j)) /\
          (read ZF s <=> j = k)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    ARM_SIM_TAC BIGNUM_MUX16_EXEC (1--3) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; WORD_ADD_0]) THEN
    REWRITE_TAC[SUB_0; MULT_CLAUSES; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0; LOWDIGITS_0] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC; (*** This is the main loop invariant ***)
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    ARM_SIM_TAC BIGNUM_MUX16_EXEC [1];
    ARM_SIM_TAC BIGNUM_MUX16_EXEC [1] THEN ASM_SIMP_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN
    UNDISCH_TAC `i:num < 16` THEN SPEC_TAC(`i:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN ASM_REWRITE_TAC[]] THEN

  (*** Start to tackle the main loop invariant ***)

  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add x (word(8 * m))) (word(8 * n)) =
    word_add x (word(8 * (m + n)))`] THEN
  CONV_TAC((RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV) EXPAND_CASES_CONV) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  (*** First show that the next digit is the thing we expect before we
   *** write back. In order to avoid fiddling round too much with the
   *** normalization of addresses during simulation we use VSTEPS instead
   *** of STEPS and then normalize afterwards.
   ***)

  ARM_VSTEPS_TAC BIGNUM_MUX16_EXEC (1--62) THEN
  SUBGOAL_THEN `i < 16 ==> read X4 s62 = word(bigdigit (n(i:num)) j)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN
    REWRITE_TAC[ARITH_RULE `k + k = k * 2 /\ k + k * a = k * (a + 1)`] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[MESON[MULT_CLAUSES]
     `word k :int64 = word(k * i) <=> word(k * 1) :int64 = word(k * i)`] THEN
    SUBGOAL_THEN
     `!j. j < 16 ==> (word(k * j):int64 = word(k * i) <=> j = i)
`   MP_TAC THENL
     [DISCARD_OLDSTATE_TAC "s62" THEN DISCARD_STATE_TAC "s62" THEN
      X_GEN_TAC `d:num` THEN DISCH_TAC THEN
      TRANS_TAC EQ_TRANS `k * d:num = k * i` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[EQ_MULT_LCANCEL]] THEN
      REWRITE_TAC[GSYM VAL_EQ] THEN
      BINOP_TAC THEN REWRITE_TAC[VAL_WORD_EQ_EQ] THEN
      REWRITE_TAC[DIMINDEX_64] THEN TRANS_TAC LT_TRANS `k * 16` THEN
      REWRITE_TAC[LT_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
    REWRITE_TAC[VAL_WORD] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[WORD_MOD_SIZE] THEN REWRITE_TAC[ARITH_RULE
     `8 * j + 8 * k * d = 8 * (k * d + j)`] THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `8 * j + 8 * k = 8 * (k * 1 + j)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(ARITH_RULE `8 * j  = 8 * (k * 0 + j)`) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i < 16` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    DISCARD_OLDSTATE_TAC "s62" THEN ABBREV_TAC `nexd = read X4 s62`] THEN

  (*** Now the writeback and tail part of the loop ***)

  ARM_STEPS_TAC BIGNUM_MUX16_EXEC (63--66) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    CONV_TAC WORD_RULE;
    REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[VAL_WORD_BIGDIGIT; LOWDIGITS_CLAUSES] THEN ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `j < k ==> (j + 1 = k <=> k - j = 1)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_EQ] THEN
    MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `k < 2 EXP 64` THEN ARITH_TAC]);;

let BIGNUM_MUX16_SUBROUTINE_CORRECT = prove
 (`!k z xs i n pc returnaddress.
     nonoverlapping (word pc,0x11c) (z,8 * val k) /\
     nonoverlapping (xs,8 * 16 * val k) (z,8 * val k)
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mux16_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [k; z; xs; i] s /\
                (!j. j < 16
                     ==> bignum_from_memory
                          (word_add xs (word(8 * val k * j)),val k) s = n j))
           (\s. read PC s = returnaddress /\
                (val i < 16 ==> bignum_from_memory (z,val k) s = n (val i)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MUX16_EXEC BIGNUM_MUX16_CORRECT);;
