(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Creation of a power-of-2 bignum using the input word as the index.        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_pow2.o";;
 ****)

let bignum_pow2_mc =
  define_assert_from_elf "bignum_pow2_mc" "arm/generic/bignum_pow2.o"
[
  0xb4000160;       (* arm_CBZ X0 (word 44) *)
  0xd2800023;       (* arm_MOV X3 (rvalue (word 1)) *)
  0x9ac22063;       (* arm_LSL X3 X3 X2 *)
  0xd346fc42;       (* arm_LSR X2 X2 (rvalue (word 6)) *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xeb02009f;       (* arm_CMP X4 X2 *)
  0x9a9f0065;       (* arm_CSEL X5 X3 XZR Condition_EQ *)
  0xf8247825;       (* arm_STR X5 X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffff63;       (* arm_BCC (word 2097132) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_POW2_EXEC = ARM_MK_EXEC_RULE bignum_pow2_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_POW2_CORRECT = prove
 (`!k z n pc.
        nonoverlapping (word pc,0x30) (z,8 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_pow2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k;z;n] s)
             (\s. read PC s = word(pc + 0x2c) /\
                  bignum_from_memory (z,val k) s =
                  lowdigits (2 EXP (val n)) (val k))
             (MAYCHANGE [PC; X2; X3; X4; X5] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** The trivial case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_POW2_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0];
    ALL_TAC] THEN

  (*** Main loop setup ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x14` `pc + 0x24`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = word(n DIV 64) /\
          read X3 s = word(2 EXP (n MOD 64)) /\
          read X4 s = word i /\
          bignum_from_memory(z,i) s = lowdigits (2 EXP n) i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_POW2_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
    ASM_REWRITE_TAC[word_ushr; word_jshl; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[word_shl; VAL_WORD_1; MULT_CLAUSES];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_POW2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ARM_SIM_TAC BIGNUM_POW2_EXEC (1--2)] THEN

  (*** Main loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; LOWDIGITS_CLAUSES] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_POW2_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  VAL_INT64_TAC `n DIV 64` THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `2 EXP n = 2 EXP (64 * n DIV 64 + n MOD 64)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ARITH_TAC; REWRITE_TAC[EXP_ADD; bigdigit]] THEN
  CONV_TAC SYM_CONV THEN
  ASM_CASES_TAC `n DIV 64 = i` THEN ASM_REWRITE_TAC[] THENL
   [SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[LT_EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(a = b) ==> a < b \/ b < a`))
  THENL
   [MATCH_MP_TAC(MESON[MOD_0] `n = 0 ==> n MOD p = 0`) THEN
    SIMP_TAC[DIV_EQ_0; GSYM EXP_ADD; EXP_EQ_0; ARITH_EQ; LT_EXP] THEN
    UNDISCH_TAC `n DIV 64 < i` THEN ARITH_TAC;
    SIMP_TAC[DIV_MOD; DIV_EQ_0; ARITH_EQ; EXP_EQ_0] THEN
    MATCH_MP_TAC(ARITH_RULE `m = 0 /\ ~(n = 0) ==> m < n`) THEN
    REWRITE_TAC[GSYM EXP_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM DIVIDES_MOD] THEN MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
    UNDISCH_TAC `i < n DIV 64` THEN ARITH_TAC]);;

let BIGNUM_POW2_SUBROUTINE_CORRECT = prove
 (`!k z n pc returnaddress.
        nonoverlapping (word pc,0x30) (z,8 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_pow2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;n] s)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,val k) s =
                  lowdigits (2 EXP (val n)) (val k))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_POW2_EXEC BIGNUM_POW2_CORRECT);;
