(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplexing (selection, if-then-else) for 4-digit (256-bit) bignums.     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p256/bignum_mux_4.o";;
 ****)

let bignum_mux_4_mc =
  define_assert_from_elf "bignum_mux_4_mc" "arm/p256/bignum_mux_4.o"
[
  0xf100001f;       (* arm_CMP X0 (rvalue (word 0)) *)
  0xf9400044;       (* arm_LDR X4 X2 (Immediate_Offset (word 0)) *)
  0xf9400060;       (* arm_LDR X0 X3 (Immediate_Offset (word 0)) *)
  0x9a801084;       (* arm_CSEL X4 X4 X0 Condition_NE *)
  0xf9000024;       (* arm_STR X4 X1 (Immediate_Offset (word 0)) *)
  0xf9400444;       (* arm_LDR X4 X2 (Immediate_Offset (word 8)) *)
  0xf9400460;       (* arm_LDR X0 X3 (Immediate_Offset (word 8)) *)
  0x9a801084;       (* arm_CSEL X4 X4 X0 Condition_NE *)
  0xf9000424;       (* arm_STR X4 X1 (Immediate_Offset (word 8)) *)
  0xf9400844;       (* arm_LDR X4 X2 (Immediate_Offset (word 16)) *)
  0xf9400860;       (* arm_LDR X0 X3 (Immediate_Offset (word 16)) *)
  0x9a801084;       (* arm_CSEL X4 X4 X0 Condition_NE *)
  0xf9000824;       (* arm_STR X4 X1 (Immediate_Offset (word 16)) *)
  0xf9400c44;       (* arm_LDR X4 X2 (Immediate_Offset (word 24)) *)
  0xf9400c60;       (* arm_LDR X0 X3 (Immediate_Offset (word 24)) *)
  0x9a801084;       (* arm_CSEL X4 X4 X0 Condition_NE *)
  0xf9000c24;       (* arm_STR X4 X1 (Immediate_Offset (word 24)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUX_4_EXEC = ARM_MK_EXEC_RULE bignum_mux_4_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MUX_4_CORRECT = prove
 (`!p z x y m n pc.
     nonoverlapping (word pc,0x48) (z,8 * 4) /\
     (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
     (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n)
           (\s. read PC s = word (pc + 0x44) /\
                bignum_from_memory (z,4) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE [PC; X0; X4] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`p:int64`; `z:int64`; `x:int64`; `y:int64`;
    `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN
  ARM_STEPS_TAC BIGNUM_MUX_4_EXEC (1--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let BIGNUM_MUX_4_SUBROUTINE_CORRECT = prove
 (`!p z x y m n pc returnaddress.
     nonoverlapping (word pc,0x48) (z,8 * 4) /\
     (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4)) /\
     (y = z \/ nonoverlapping (y,8 * 4) (z,8 * 4))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mux_4_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [p; z; x; y] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s =
                  if ~(p = word 0) then m else n)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MUX_4_EXEC BIGNUM_MUX_4_CORRECT);;
