(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove a property of a simple program by splitting into two sequential
  chunks with an intermediate assertion.
******************************************************************************)

(* Please copy this file to the root directory of s2n-bignum, then
   follow the instructions. *)

needs "arm/proofs/base.ml";;

(* Given a program
   0:   8b000021        add     x1, x1, x0
   4:   8b000042        add     x2, x2, x0
   8:   d2800043        mov     x3, #0x2
   c:   9b037c21        mul     x1, x1, x3

  Let's prove that x1 in the final state is (x1 + x0) * 2.
  As done in "simple.ml", this can be done using symbolic execution. However,
  in this file, we will try a slightly different approach:
  (1) The program will be splitted into two smaller programs:

  First prog:
   0:   8b000021        add     x1, x1, x0
   4:   8b000042        add     x2, x2, x0

  Second prog:
   8:   d2800043        mov     x3, #0x2
   c:   9b037c21        mul     x1, x1, x3

  (2) Each program will have its 'ensures' predicate specifying the pre and
      postcondition. The postcondition of the first program will be equivalent to
      the second one.
  (3) By proving the two 'ensures' predicate, the specification of whole
      program can be proven.
*)

let sequence_mc = new_definition `sequence_mc = [
    word 0x21; word 0x00; word 0x00; word 0x8b; // add x2, x1, x0
    word 0x42; word 0x00; word 0x00; word 0x8b; // add x2, x2, x0
    word 0x43; word 0x00; word 0x80; word 0xd2; // mov x3, #0x2
    word 0x21; word 0x7c; word 0x03; word 0x9b  // mul x1, x1, x3
  ]:((8)word)list`;;

let EXEC = ARM_MK_EXEC_RULE sequence_mc;;

let sequence_SPEC = prove(
  `forall pc a b.
  ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) sequence_mc /\
         read PC s = word pc /\
         read X0 s = word a /\
         read X1 s = word b /\
         read X2 s = word c)
    // Postcondition
    (\s. read PC s = word (pc+16) /\
         read X1 s = word ((a + b) * 2))
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [PC;X1;X2;X3])`,
  (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN

  (* Use ENSURES_SEQUENCE_TAC to split the program into two chunks:
     [pc, pc+8) and [pc+8, pc+16). The second argument of the tactic
     `\s. read X1 s = word (a + b)` is a lambda function stating the
     intermediate state at pc+8.
     The result of this tactic will be a conjunction of two ensures,
     the left clause of which is a spec of the first chunk and the
     right clause is the right one. *)
  ENSURES_SEQUENCE_TAC
    `pc + 8`
    `\s. read X1 s = word (a + b)` THEN

  (* Split the conjunction and create two subgoals. *)
  CONJ_TAC THENL [
    (* The first subgoal. *)
    (* Now we can use the symbolic execution tactics introduced in "simple.ml". *)
    (* Start symbolic execution with state 's0' *)
    ENSURES_INIT_TAC "s0" THEN
    (* Symbolically run two instructions *)
    ARM_STEPS_TAC EXEC (1--2) THEN
    (* Try to prove the postcondition and frame as much as possible *)
    ENSURES_FINAL_STATE_TAC THEN
    (* Use ASM_REWRITE_TAC[] to rewrite the goal using equalities in assumptions. *)
    ASM_REWRITE_TAC[] THEN
    (* Prove: `word_add (word b) (word a) = word (a + b)` *)
    CONV_TAC WORD_RULE;

    (* The second subgoal *)
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    (* Prove: `word (0 + val (word (a + b)) * 2) = word ((a + b) * 2)` *)
    CONV_TAC WORD_RULE;
  ]);;
