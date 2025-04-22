(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove a property of a simple program that has a conditional branch.
******************************************************************************)

needs "arm/proofs/base.ml";;

(* The following program
  0:   eb02003f        cmp     x1, x2
  4:   54000068        b.hi    10 <BB2>
  8:   aa0203e0        mov     x0, x2
  c:   d65f03c0        ret

0000000000000010 <BB2>:
  10:   aa0103e0        mov     x0, x1
  14:   d65f03c0        ret

  .. copies max(x1,x2) to x0 and returns to the caller.
  Let's prove this property.
*)

let branch_mc = new_definition `branch_mc = [
    word 0x3f; word 0x00; word 0x02; word 0xeb; // cmp     x1, x2
    word 0x68; word 0x00; word 0x00; word 0x54; // b.hi    10 <BB2>

    word 0xe0; word 0x03; word 0x02; word 0xaa; // mov     x0, x2
    word 0xc0; word 0x03; word 0x5f; word 0xd6; // ret

  // BB2:
    word 0xe0; word 0x03; word 0x01; word 0xaa; // mov     x0, x1
    word 0xc0; word 0x03; word 0x5f; word 0xd6  // ret
  ]:((8)word)list`;;

let EXEC = ARM_MK_EXEC_RULE branch_mc;;

let branch_SPEC = prove(
  `forall pc pcret a b.
  ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) branch_mc /\
         read X30 s = word pcret /\
         read PC s = word pc /\
         read X1 s = word a /\
         read X2 s = word b)
    // Postcondition
    (\s. read PC s = word pcret /\
         read X0 s = word_umax (word a) (word b))
    // Registers (and memory locations) that may change after execution.
    // ',,' is composition of relations.
    (MAYCHANGE [PC;X0] ,, MAYCHANGE SOME_FLAGS ,,
     // Branch instructions raise observable microarchitectural events!
     MAYCHANGE [events])`,
  (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN
  (* ENSURES_FINAL_STATE_TAC does not understand SOME_FLAGS in MAYCHANGE. Let's
     unfold this in advance. *)
  REWRITE_TAC [SOME_FLAGS] THEN

  (* Let's do symbolic execution until it hits the branch instruction. *)
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--2) THEN

  (* The PC has the following symbolic expression:
    `read PC s2 =
      (if val (word b) <= val (word a) /\
          ~(val (word_sub (word a) (word b)) = 0)
       then word (pc + 16)
       else word (pc + 8))`
    Let's do case analysis on the condition of this if expression.

    First, move this assumption to the antecendent of the goal so the goal
    becomes:
      (read PC s2 = ...) ==> eventually arm ...
  *)
  FIRST_X_ASSUM MP_TAC THEN

  (* Recognize the if condition and create two subgoals . *)
  COND_CASES_TAC THENL [
    (** Case 1: if the branch was taken! **)
    (* Let's name the hypothesis first. *)
    POP_ASSUM (LABEL_TAC "Hcond") THEN
    DISCH_TAC THEN

    (* Do symbolic execution on the remaining two insts. *)
    ARM_STEPS_TAC EXEC (3--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN

    (* The remaining goal is `word a = word (MAX a b).` *)
    REMOVE_THEN "Hcond" MP_TAC THEN
    (* WORD_UMAX: `!x y. word_umax x y = (if val x <= val y then y else x)`
       VAL_WORD_SUB_EQ_0: `!x y. val (word_sub x y) = 0 <=> val x = val y` *)
    REWRITE_TAC[WORD_UMAX;VAL_WORD_SUB_EQ_0] THEN
    (* Let ARITH_TAC deal with reasoning on relational equations. *)
    ARITH_TAC;


    (** Case 2: if the branch was not taken! **)
    (* Let's name the hypothesis first. *)
    POP_ASSUM (LABEL_TAC "Hcond") THEN
    DISCH_TAC THEN

    (* Do symbolic execution on the remaining two insts. *)
    ARM_STEPS_TAC EXEC (3--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN

    (* The remaining goal is `word b = word (MAX a b).` *)
    REMOVE_THEN "Hcond" MP_TAC THEN
    (* WORD_UMAX: `!x y. word_umax x y = (if val x <= val y then y else x)`
       VAL_WORD_SUB_EQ_0: `!x y. val (word_sub x y) = 0 <=> val x = val y` *)
    REWRITE_TAC[WORD_UMAX;VAL_WORD_SUB_EQ_0] THEN
    (* Let ARITH_TAC deal with reasoning on relational equations. *)
    ARITH_TAC;
  ]);;
