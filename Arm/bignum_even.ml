(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Deduce if a bignum is even or odd.                                        *)
(* ========================================================================= *)

(**** print_literal_from_elf "Arm/bignum_even.o";;
 ****)

let bignum_even_mc = define_assert_from_elf "bignum_even_mc" "Arm/bignum_even.o"
[
  0xb4000060;       (* arm_CBZ X0 (word 12) *)
  0xf9400020;       (* arm_LDR X0 X1 (Immediate_Offset (word 0)) *)
  0x92400000;       (* arm_AND X0 X0 (rvalue (word 1)) *)
  0xd2400000;       (* arm_EOR X0 X0 (rvalue (word 1)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_EVEN_EXEC = ARM_MK_EXEC_RULE bignum_even_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_EVEN_CORRECT = prove
 (`!k a x pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_even_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s. read PC s = word (pc + 16) /\
               C_RETURN s = if EVEN x then word 1 else word 0)
          (MAYCHANGE [PC; X0])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a1:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[ENSURES_TRIVIAL; EVEN] THEN
    ARM_SIM_TAC BIGNUM_EVEN_EXEC (1--2);
    ENSURES_INIT_TAC "s0" THEN EXPAND_TAC "x" THEN
    ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
    ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; EVEN_EXP; ARITH_EVEN; ARITH_EQ] THEN
    ABBREV_TAC `d = read (memory :> bytes64 a1) s0` THEN
    ARM_STEPS_TAC BIGNUM_EVEN_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_AND_1; BIT_LSB; GSYM NOT_ODD; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV]);;

let BIGNUM_EVEN_SUBROUTINE_CORRECT = prove
 (`!k a x pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) bignum_even_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [k;a] s /\
               bignum_from_memory(a,val k) s = x)
          (\s. read PC s = returnaddress /\
               C_RETURN s = if EVEN x then word 1 else word 0)
          (MAYCHANGE [PC; X0])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_EVEN_EXEC BIGNUM_EVEN_CORRECT);;
