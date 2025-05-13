(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove a property of a simple program that has a loop.
******************************************************************************)

needs "arm/proofs/base.ml";;

(* The following program
   0:   aa1f03e1        mov     x1, xzr
   4:   aa1f03e0        mov     x0, xzr

0000000000000008 <loop>:
   8:   91000421        add     x1, x1, #0x1
   c:   91000800        add     x0, x0, #0x2
  10:   f100283f        cmp     x1, #0xa
  14:   54ffffa1        b.ne    8 <loop>  // b.any
  18:   d65f03c0        ret

  increments x0 until its value is 20.
  Let's prove that this function returns 20.
*)
let loop_mc = new_definition `loop_mc = [
  word 0xe1; word 0x03; word 0x1f; word 0xaa; // mov     x1, xzr
  word 0xe0; word 0x03; word 0x1f; word 0xaa; // mov     x0, xzr

// loop:
  word 0x21; word 0x04; word 0x00; word 0x91; // add     x1, x1, #0x1
  word 0x00; word 0x08; word 0x00; word 0x91; // add     x0, x0, #0x2
  word 0x3f; word 0x28; word 0x00; word 0xf1; // cmp     x1, #0xa
  word 0xa1; word 0xff; word 0xff; word 0x54; // b.ne    8 <loop>
  word 0xc0; word 0x03; word 0x5f; word 0xd6  // ret
]:((8)word)list`;;

let EXEC = ARM_MK_EXEC_RULE loop_mc;;

let loop_SPEC = prove(
  `forall pc retpc.
  ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) loop_mc /\
         read PC s = word pc /\
         read X30 s = word retpc)
    // Postcondition
    (\s. read PC s = word retpc /\
         read X0 s = word 20)
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [PC;X0;X1] ,, MAYCHANGE SOME_FLAGS ,,
     // Branch instructions raise observable microarchitectural events!
     MAYCHANGE [events])`,
  (* Unravel ARM flag registers! *)
  REWRITE_TAC[SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN

  (* ENSURES_WHILE_PAUP_TAC is one of several tactics for declaring a hoare triple of a loop.
     PAUP means:
     - "P": The loop ends with a flag-setting instruction such as 'cmp' or 'adds'.
            'read ZF s <=> i = 10' in the below statement relates the flag with
            the loop counter.
     - "A": The loop counter starts from variable 'a', In this tactic, this is 0.
            Actually, when a = 0, you can also use ENSURES_WHILE_PUP_TAC.
     - "UP": The counter goes up. *)
  ENSURES_WHILE_PAUP_TAC
    `0` (* counter begin number *)
    `10` (* counter end number *)
    `pc + 8` (* loop body start PC *)
    `pc + 0x14` (* loop backedge branch PC *)
    `\i s. // loop invariant at the end of the loop
           (read X1 s = word i /\ read X0 s = word (i*2) /\ read X30 s = word retpc) /\
           // loop backedge condition
           (read ZF s <=> i = 10)` THEN
  REPEAT CONJ_TAC THENL [
    (* counter begin < counter end *)
    ARITH_TAC;

    (* entrance to the loop *)
    (* Let's use ARM_SIM_TAC which is ENSURES_INIT_TAC + ARM_STEPS_TAC +
       ENSURES_FINAL_STATE_TAC + some post-processing. *)
    ARM_SIM_TAC EXEC (1--2) THEN
    CONV_TAC WORD_RULE;

    (* The loop body. let's prove this later. *)
    (* If you are interactively exploring this proof, try `r 1;;`. *)
    ALL_TAC;

    (* Prove that backedge is taken if i != 10. *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC EXEC [1];

    (* Loop exit to the end of the program *)
    ARM_SIM_TAC EXEC (1--2) THEN
    (* word (10*2) = word 20 *)
    CONV_TAC WORD_RULE
  ] THEN

  (* The loop body *)
  REPEAT STRIP_TAC THEN
  ARM_SIM_TAC EXEC (1--3) THEN
  REPEAT CONJ_TAC THENL [
    (* `word_add (word i) (word 1) = word (i + 1)` *)
    CONV_TAC WORD_RULE;

    (* `word_add (word (i * 2)) (word 2) = word ((i + 1) * 2)` *)
    CONV_TAC WORD_RULE;

    (* `val (word_add (word i) (word 18446744073709551607)) = 0 <=> i + 1 = 10` *)
    (* This goal is slightly complicated to prove using automatic solvers.
       Let's manually attack this. *)
    (* Yes, we also have 'WORD_BLAST' that works like bit-blasting. *)
    REWRITE_TAC [WORD_BLAST `word_add x (word 18446744073709551607):int64 =
                             word_sub x (word 9)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
    (* Rewrite all '_ MOD 2 EXP 64' to '_' because they are known to be less
       than 2 EXP 64. *)
    IMP_REWRITE_TAC[MOD_LT; ARITH_RULE`9 < 2 EXP 64`] THEN
    CONJ_TAC THEN (* will create two arithmetic subgoals. *)
    (* both goals can be solved using ASM_ARITH_TAC. *)
    ASM_ARITH_TAC
  ]);;
