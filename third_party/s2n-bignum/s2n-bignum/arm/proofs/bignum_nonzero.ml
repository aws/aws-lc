(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Deduce if a bignum is nonzero.                                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_nonzero.o";;
 ****)

let bignum_nonzero_mc = define_assert_from_elf "bignum_nonzero_mc"
  "arm/generic/bignum_nonzero.o"
[
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xb40000e0;       (* arm_CBZ X0 (word 28) *)
  0xd1000400;       (* arm_SUB X0 X0 (rvalue (word 1)) *)
  0xf8607822;       (* arm_LDR X2 X1 (Shiftreg_Offset X0 3) *)
  0xaa020063;       (* arm_ORR X3 X3 X2 *)
  0xb5ffffa0;       (* arm_CBNZ X0 (word 2097140) *)
  0xeb1f007f;       (* arm_CMP X3 XZR *)
  0x9a9f07e0;       (* arm_CSET X0 Condition_NE *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_NONZERO_EXEC = ARM_MK_EXEC_RULE bignum_nonzero_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_NONZERO_CORRECT = prove
 (`!k a x pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_nonzero_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s'. read PC s' = word (pc + 0x20) /\
                C_RETURN s' = if ~(x = 0) then word 1 else word 0)
          (MAYCHANGE [PC; X0; X2; X3] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_NONZERO_EXEC] THEN
  BIGNUM_RANGE_TAC "k" "x" THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC (1--2);
    ALL_TAC] THEN

  ENSURES_WHILE_DOWN_TAC `k:num` `pc + 0x08` `pc + 0x14`
   `\i s. bignum_from_memory (a,i) s = lowdigits x i /\
          read X1 s = a /\
          read X0 s = word i /\
          (read X3 s = word 0 <=> highdigits x i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO] THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC (1--2);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `d:int64` `read X3` THEN ASSUME_TAC
     (WORD_RULE `word_sub (word (i + 1)) (word 1):int64 = word i`) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC (1--3) THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [HIGHDIGITS_STEP] THEN
    ASM_REWRITE_TAC[WORD_OR_EQ_0; ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_0; VAL_WORD_BIGDIGIT; CONJ_ACI];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC [1];
    GHOST_INTRO_TAC `d:int64` `read X3` THEN
    ARM_SIM_TAC BIGNUM_NONZERO_EXEC (1--3) THEN
    ASM_REWRITE_TAC[VAL_WORD_0; VAL_EQ_0; COND_SWAP; HIGHDIGITS_0]]);;

let BIGNUM_NONZERO_SUBROUTINE_CORRECT = prove
 (`!k a x pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_nonzero_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s'. read PC s' = returnaddress /\
                C_RETURN s' = if ~(x = 0) then word 1 else word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_NONZERO_EXEC BIGNUM_NONZERO_CORRECT);;
