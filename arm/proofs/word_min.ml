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
(* Finding minimum of two 64-bit words.                                      *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/generic/word_min.o";;
 ****)

let word_min_mc = define_assert_from_elf "word_min_mc" "arm/generic/word_min.o"
[
  0xeb01001f;       (* arm_CMP X0 X1 *)
  0x9a813000;       (* arm_CSEL X0 X0 X1 Condition_CC *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let WORD_MIN_EXEC = ARM_MK_EXEC_RULE word_min_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_MIN_CORRECT = prove
 (`!a b pc.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_min_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [a; b] s)
          (\s. read PC s = word(pc + 0x8) /\
               C_RETURN s = word_umin a b)
          (MAYCHANGE [PC; X0] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `b:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  ARM_SIM_TAC WORD_MIN_EXEC (1--2) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMIN] THEN ASM_ARITH_TAC);;

let WORD_MIN_SUBROUTINE_CORRECT = prove
 (`!a b pc returnaddress.
        ensures arm
          (\s. aligned_bytes_loaded s (word pc) word_min_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [a; b] s)
          (\s. read PC s = returnaddress /\
               C_RETURN s = word_umin a b)
          (MAYCHANGE [PC; X0] ,,
           MAYCHANGE SOME_FLAGS)`,
  ARM_ADD_RETURN_NOSTACK_TAC WORD_MIN_EXEC WORD_MIN_CORRECT);;
