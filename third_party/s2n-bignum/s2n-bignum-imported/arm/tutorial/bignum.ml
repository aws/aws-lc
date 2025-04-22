(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  An example that shows how to describe big numbers in a specification.
******************************************************************************)

needs "arm/proofs/base.ml";;

(* Let's prove that the following program

   0:   a9400c02        ldp     x2, x3, [x0]
   4:   a9401424        ldp     x4, x5, [x1]
   8:   eb04005f        cmp     x2, x4
   c:   540000a1        b.ne    20 <bb_false>  // b.any
  10:   eb05007f        cmp     x3, x5
  14:   54000061        b.ne    20 <bb_false>  // b.any
  18:   d2800020        mov     x0, #0x1
  1c:   d65f03c0        ret

0000000000000020 <bb_false>:
  20:   aa1f03e0        mov     x0, xzr
  24:   d65f03c0        ret

  .. returns 1 to x0 if a pair of 16-byte integers at buffer x0 and x1
  are equal, 0 otherwise.
  Since this example uses 128 bit integers, we will use 'bignum_from_memory'
  which will state that reading a memory buffer of a specified word number will
  return some large natural number.
*)
let bignum_mc = define_assert_from_elf "bignum_mc" "arm/tutorial/bignum.o" [
  0xa9400c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9401424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xeb04005f;       (* arm_CMP X2 X4 *)
  0x540000a1;       (* arm_BNE (word 20) *)
  0xeb05007f;       (* arm_CMP X3 X5 *)
  0x54000061;       (* arm_BNE (word 12) *)
  0xd2800020;       (* arm_MOV X0 (rvalue (word 1)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(*
You can get the above OCaml list data structure from
`print_literal_from_elf "<.o file>"` or
`save_literal_from_elf "<out.txt>" "<.o file>"`.
*)

(* ARM_MK_EXEC_RULE decodes the byte sequence into conjunction of
  equalities between the bytes and instructions. *)
let EXEC = ARM_MK_EXEC_RULE bignum_mc;;

let BIGNUM_SPEC = prove(
  `forall pc retpc loc0 loc1 a b.
  ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) bignum_mc /\
         read PC s = word pc /\
         read X30 s = word retpc /\
         read X0 s = word loc0 /\
         read X1 s = word loc1 /\
         // Read 2 words (=128bits) at loc0. It is equivalent to num a.
         // Alternatively, this kind of condition can be written using
         // bignum_of_wordlist which takes a list of 64-bit words.
         bignum_from_memory (word loc0,2) s = a /\
         // Read 2 words (=128bits) at loc1. It is equivalent to num b.
         bignum_from_memory (word loc1,2) s = b
         )
    // Postcondition
    (\s. read PC s = word retpc /\
         read X0 s = word (if a = b then 1 else 0))
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [PC;X0;X2;X3;X4;X5] ,, MAYCHANGE SOME_FLAGS ,,
     MAYCHANGE [events])`,

  REPEAT STRIP_TAC THEN
  (* Convert 'bignum_from_memory' into 'memory :> bytes (..)'.
     Also, expand SOME_FLAGS *)
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;SOME_FLAGS] THEN
  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN
  (* Split the memory :> bytes .. into a pair of memory :> bytes64.
     This is necessary to successfully encode the symbolic result of ldps. *)
  BIGNUM_DIGITIZE_TAC "a_" `read (memory :> bytes (word loc0,8 * 2)) s0` THEN
  BIGNUM_DIGITIZE_TAC "b_" `read (memory :> bytes (word loc1,8 * 2)) s0` THEN

  (* Symbolically run two ldp instructions *)
  ARM_STEPS_TAC EXEC (1--2) THEN
  (* Until first 'bne' *)
  ARM_STEPS_TAC EXEC (3--4) THEN

  (* Recognize the if condition and create two subgoals . *)
  FIRST_X_ASSUM MP_TAC THEN
  COND_CASES_TAC THENL [
    (* The low 64 bits of a and b are different. *)
    STRIP_TAC THEN
    ARM_STEPS_TAC EXEC (5--6) THEN
    (* Returned; Finalize symbolic execution. *)
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* From `~(val (word_sub a_0 b_0) = 0)` and `val a_0 + 2 EXP 64 * val a_1 = a`,
       and `val b_0 + 2 EXP 64 * val b_1 = b`,
       prove `~(a = b)`. *)
    SUBGOAL_THEN `~(a:num = b)` (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXPAND_TAC ["a";"b"] THEN
    (* VAL_WORD_SUB_EQ_0: |- !x y. val (word_sub x y) = 0 <=> val x = val y) *)
    RULE_ASSUM_TAC (REWRITE_RULE [VAL_WORD_SUB_EQ_0]) THEN
    (* EQ_DIVMOD: |- !p m n. m DIV p = n DIV p /\ m MOD p = n MOD p <=> m = n *)
    ONCE_REWRITE_TAC[SPEC `2 EXP 64` (GSYM EQ_DIVMOD)] THEN
    (* The first '.. DIV .. = .. DIV ..' part is irelevant. *)
    MATCH_MP_TAC (TAUT (`~Q ==> ~(P /\ Q)`)) THEN
    (* Simplfy! *)
    SIMP_TAC[MOD_MULT_ADD;VAL_BOUND_64;ARITH_RULE`~(2 EXP 64 = 0)`] THEN
    ASM_SIMP_TAC[MOD_LT;VAL_BOUND_64];

    ALL_TAC
  ] THEN

  (* The low 64 bits of a and b are equivalent. *)
  (* Until the second 'bne' *)
  STRIP_TAC THEN
  ARM_STEPS_TAC EXEC (5--6) THEN

  (* Recognize the if condition and create two subgoals . *)
  FIRST_X_ASSUM MP_TAC THEN
  COND_CASES_TAC THENL [
    (* The high 64 bits of a and b are different. *)
    STRIP_TAC THEN
    ARM_STEPS_TAC EXEC (7--8) THEN
    (* Returned; Finalize symbolic execution. *)
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* Proof pattern is similar to the first branch case *)
    SUBGOAL_THEN `~(a:num = b)` (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXPAND_TAC ["a";"b"] THEN
    (* VAL_WORD_SUB_EQ_0: |- !x y. val (word_sub x y) = 0 <=> val x = val y) *)
    RULE_ASSUM_TAC (REWRITE_RULE [VAL_WORD_SUB_EQ_0]) THEN
    (* EQ_DIVMOD: |- !p m n. m DIV p = n DIV p /\ m MOD p = n MOD p <=> m = n *)
    ONCE_REWRITE_TAC[SPEC `2 EXP 64` (GSYM EQ_DIVMOD)] THEN
    (* The second '.. MOD .. = .. MOD ..' part is irelevant. *)
    MATCH_MP_TAC (TAUT (`~P ==> ~(P /\ Q)`)) THEN
    (* Simplfy! *)
    SIMP_TAC[DIV_MULT_ADD;VAL_BOUND_64;ARITH_RULE`~(2 EXP 64 = 0)`] THEN
    ASM_SIMP_TAC[DIV_LT;VAL_BOUND_64;ADD_CLAUSES];

    ALL_TAC
  ] THEN

  (* Both limbs are equivalent! *)
  STRIP_TAC THEN
  ARM_STEPS_TAC EXEC (7--8) THEN
  (* Try to prove the postcondition and frame as much as possible *)
  ENSURES_FINAL_STATE_TAC THEN
  (* Use ASM_REWRITE_TAC[] to rewrite the goal using equalities in assumptions. *)
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:num = b)` (fun th -> REWRITE_TAC[th]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [VAL_WORD_SUB_EQ_0]) THEN
  ASM_ARITH_TAC);;
