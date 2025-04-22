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

needs "x86/proofs/base.ml";;

(* Given a program
  0:   48 01 c3                add    %rax,%rbx
  3:   48 01 c1                add    %rax,%rcx
  6:   48 c7 c2 02 00 00 00    mov    $0x2,%rdx
  d:   48 0f af da             imul   %rdx,%rbx

  Let's prove that rbx in the final state is (rax(input) + rbx(input)) * 2.
  As done in "simple.ml", this can be done using symbolic execution. However,
  in this file, we will try a slightly different approach:
  (1) The program will be splitted into two smaller programs:

  First prog:
  0:   48 01 c3                add    %rax,%rbx
  3:   48 01 c1                add    %rax,%rcx

  Second prog:
  6:   48 c7 c2 02 00 00 00    mov    $0x2,%rdx
  d:   48 0f af da             imul   %rdx,%rbx

  (2) Each program will have its 'ensures' predicate specifying the pre and
      postcondition. The postcondition of the first program will be equivalent to
      the second one.
  (3) By proving the two 'ensures' predicate, the specification of whole
      program can be proven.
*)

let sequence_mc = new_definition `sequence_mc = [
    word 0x48; word 0x01; word 0xc3;
    word 0x48; word 0x01; word 0xc1;
    word 0x48; word 0xc7; word 0xc2; word 0x02; word 0x00; word 0x00; word 0x00;
    word 0x48; word 0x0f; word 0xaf; word 0xda
  ]:((8)word)list`;;

let EXEC = X86_MK_EXEC_RULE sequence_mc;;

let sequence_SPEC = prove(
  `forall pc a b.
  ensures x86
    // Precondition
    (\s. bytes_loaded s (word pc) sequence_mc /\
         read RIP s = word pc /\
         read RAX s = word a /\
         read RBX s = word b /\
         read RCX s = word c)
    // Postcondition
    (\s. read RIP s = word (pc+0x11) /\
         read RBX s = word ((a + b) * 2))
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [RIP;RBX;RCX;RDX] ,, MAYCHANGE SOME_FLAGS)`,
  (* ENSURES_FINAL_STATE_TAC does not understand SOME_FLAGS in MAYCHANGE. Let's
     unfold this in advance. *)
  REWRITE_TAC [SOME_FLAGS] THEN
  (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN

  (* Use ENSURES_SEQUENCE_TAC to split the program into two chunks:
     [pc, pc+6) and [pc+6, pc+12). The second argument of the tactic
     `\s. read RBX s = word (a + b)` is a lambda function stating the
     intermediate state at pc+6.
     The result of this tactic will be a conjunction of two ensures,
     the left clause of which is a spec of the first chunk and the
     right clause is the right one. *)
  ENSURES_SEQUENCE_TAC
    `pc + 6`
    `\s. read RBX s = word (a + b)` THEN

  (* Split the conjunction and create two subgoals. *)
  CONJ_TAC THENL [
    (* The first subgoal. *)
    (* Now we can use the symbolic execution tactics introduced in "simple.ml". *)
    (* Start symbolic execution with state 's0' *)
    ENSURES_INIT_TAC "s0" THEN
    (* Symbolically run two instructions *)
    X86_STEPS_TAC EXEC (1--2) THEN
    (* Try to prove the postcondition and frame as much as possible *)
    ENSURES_FINAL_STATE_TAC THEN
    (* Use ASM_REWRITE_TAC[] to rewrite the goal using equalities in assumptions. *)
    ASM_REWRITE_TAC[] THEN
    (* Prove: `word_add (word b) (word a) = word (a + b)` *)
    CONV_TAC WORD_RULE;

    (* The second subgoal *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    (* Prove: `word (0 + val (word (a + b)) * 2) = word ((a + b) * 2)` *)
    CONV_TAC WORD_RULE;
  ]);;
