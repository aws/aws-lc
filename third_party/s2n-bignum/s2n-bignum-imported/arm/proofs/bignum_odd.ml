(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Deduce if a bignum is odd or even.                                        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_odd.o";;
 ****)

let bignum_odd_mc = define_assert_from_elf "bignum_odd_mc" "arm/generic/bignum_odd.o"
[
  0xb4000060;       (* arm_CBZ X0 (word 12) *)
  0xf9400020;       (* arm_LDR X0 X1 (Immediate_Offset (word 0)) *)
  0x92400000;       (* arm_AND X0 X0 (rvalue (word 1)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_ODD_EXEC = ARM_MK_EXEC_RULE bignum_odd_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_ODD_CORRECT = prove
 (`!k a x pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_odd_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s. read PC s = word (pc + 12) /\
               C_RETURN s = if ODD x then word 1 else word 0)
          (MAYCHANGE [PC; X0] ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a1:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[ENSURES_TRIVIAL; ODD] THEN
    ARM_SIM_TAC BIGNUM_ODD_EXEC [1] THEN REWRITE_TAC[ARITH];
    ENSURES_INIT_TAC "s0" THEN EXPAND_TAC "x" THEN
    ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
    ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ODD_EXP; ARITH_ODD; ARITH_EQ] THEN
    ABBREV_TAC `d = read (memory :> bytes64 a1) s0` THEN
    ARM_STEPS_TAC BIGNUM_ODD_EXEC (1--3) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_AND_1; BIT_LSB]]);;

let BIGNUM_ODD_SUBROUTINE_CORRECT = prove
 (`!k a x pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_odd_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s. read PC s = returnaddress /\
                C_RETURN s = if ODD x then word 1 else word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_ODD_EXEC BIGNUM_ODD_CORRECT);;
