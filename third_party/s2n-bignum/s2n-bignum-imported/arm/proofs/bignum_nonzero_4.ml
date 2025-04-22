(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Deduce if a 256-bit bignum is nonzero.                                    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p256/bignum_nonzero_4.o";;
 ****)

let bignum_nonzero_4_mc =
  define_assert_from_elf "bignum_nonzero_4_mc" "arm/p256/bignum_nonzero_4.o"
[
  0xa9400801;       (* arm_LDP X1 X2 X0 (Immediate_Offset (iword (&0))) *)
  0xaa020021;       (* arm_ORR X1 X1 X2 *)
  0xa9410803;       (* arm_LDP X3 X2 X0 (Immediate_Offset (iword (&16))) *)
  0xaa020063;       (* arm_ORR X3 X3 X2 *)
  0xaa030021;       (* arm_ORR X1 X1 X3 *)
  0xeb1f003f;       (* arm_CMP X1 XZR *)
  0x9a9f07e0;       (* arm_CSET X0 Condition_NE *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_NONZERO_4_EXEC = ARM_MK_EXEC_RULE bignum_nonzero_4_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_NONZERO_4_CORRECT = prove
 (`!x n pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_nonzero_4_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [x] s /\
               bignum_from_memory(x,4) s = n)
          (\s. read PC s = word(pc + 0x1c) /\
               C_RETURN s = if ~(n = 0) then word 1 else word 0)
          (MAYCHANGE [PC; X0; X1; X2; X3] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  ARM_STEPS_TAC BIGNUM_NONZERO_4_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[ADD_EQ_0; VAL_EQ_0; WORD_OR_EQ_0] THEN
  REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ; VAL_EQ_0] THEN
  REWRITE_TAC[CONJ_ACI; COND_SWAP]);;

let BIGNUM_NONZERO_4_SUBROUTINE_CORRECT = prove
 (`!x n pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_nonzero_4_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [x] s /\
               bignum_from_memory(x,4) s = n)
          (\s. read PC s = returnaddress /\
               C_RETURN s = if ~(n = 0) then word 1 else word 0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_NONZERO_4_EXEC BIGNUM_NONZERO_4_CORRECT);;
