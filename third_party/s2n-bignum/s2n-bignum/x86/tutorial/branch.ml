(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove a property of a simple program that has a conditional branch.
******************************************************************************)

needs "x86/proofs/base.ml";;

(* The following program
  0000000000000000 <BB2-0x9>:
    0:   48 39 cb                cmp    %rcx,%rbx
    3:   77 04                   ja     9 <BB2>
    5:   48 89 c8                mov    %rcx,%rax
    8:   c3                      retq

  0000000000000009 <BB2>:
    9:   48 89 d8                mov    %rbx,%rax
    c:   c3                      retq

  .. copies max(rbx,rcx) to rax and returns to the caller.
  Let's prove this property.
*)

let branch_mc = new_definition `branch_mc = [
    word 0x48; word 0x39; word 0xcb;
    word 0x77; word 0x04;
    word 0x48; word 0x89; word 0xc8;
    word 0xc3;

    word 0x48; word 0x89; word 0xd8;
    word 0xc3
  ]:((8)word)list`;;

let EXEC = X86_MK_EXEC_RULE branch_mc;;

let branch_SPEC = prove(
  `forall pc a b stackpointer returnaddress.
  ensures x86
    // Precondition
    (\s. bytes_loaded s (word pc) branch_mc /\
         read RIP s = word pc /\
         read RSP s = stackpointer /\
         read (memory :> bytes64 stackpointer) s = returnaddress /\
         read RBX s = word a /\
         read RCX s = word b)
    // Postcondition
    (\s. read RIP s = returnaddress /\
         read RSP s = word_add stackpointer (word 8) /\
         read RAX s = word_umax (word a) (word b))
    // Registers (and memory locations) that may change after execution.
    // ',,' is composition of relations.
    (MAYCHANGE [RSP;RIP;RAX] ,, MAYCHANGE SOME_FLAGS)`,
  (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN
  (* ENSURES_FINAL_STATE_TAC does not understand SOME_FLAGS in MAYCHANGE. Let's
     unfold this in advance. *)
  REWRITE_TAC [SOME_FLAGS] THEN

  (* Let's do symbolic execution until it hits the branch instruction. *)
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC EXEC (1--2) THEN

  (* The PC has the following symbolic expression:
    `read RIP s2 =
      (if ~(val (word a) < val (word b) \/
            val (word_sub (word a) (word b)) = 0)
       then word (pc + 9)
       else word (pc + 5))`
    Let's do case analysis on the condition of this if expression.

    First, move this assumption to the antecendent of the goal so the goal
    becomes:
      (read RIP s2 = ...) ==> eventually x86 ...
  *)
  FIRST_X_ASSUM MP_TAC THEN

  (* Recognize the if condition and create two subgoals . *)
  COND_CASES_TAC THENL [
    (** Case 1: if the branch was taken! **)
    (* Let's name the hypothesis first. *)
    POP_ASSUM (LABEL_TAC "Hcond") THEN
    DISCH_TAC THEN

    (* Do symbolic execution on the remaining two insts. *)
    X86_STEPS_TAC EXEC (3--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN

    (* The remaining goal is `word a = word (MAX a b).` *)
    REMOVE_THEN "Hcond" MP_TAC THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN
    REWRITE_TAC[NOT_LT;LE_LT] THEN
    (* WORD_UMAX: `!x y. word_umax x y = (if val x <= val y then y else x)`
       VAL_WORD_SUB_EQ_0: `!x y. val (word_sub x y) = 0 <=> val x = val y` *)
    REWRITE_TAC[VAL_WORD_SUB_EQ_0;WORD_UMAX] THEN
    (* Let ARITH_TAC deal with reasoning on relational equations. *)
    ARITH_TAC;


    (** Case 2: if the branch was not taken! **)
    (* Let's name the hypothesis first. *)
    POP_ASSUM (LABEL_TAC "Hcond") THEN
    DISCH_TAC THEN

    (* Do symbolic execution on the remaining two insts. *)
    X86_STEPS_TAC EXEC (3--4) THEN
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
