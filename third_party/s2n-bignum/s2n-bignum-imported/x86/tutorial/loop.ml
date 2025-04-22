(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove a property of a simple program that has a loop.
******************************************************************************)

needs "x86/proofs/base.ml";;

(* The following program
   0:   48 c7 c3 00 00 00 00    mov    $0x0,%rbx
   7:   48 c7 c0 00 00 00 00    mov    $0x0,%rax

000000000000000e <loop>:
   e:   48 83 c3 01             add    $0x1,%rbx
  12:   48 83 c0 02             add    $0x2,%rax
  16:   48 83 fb 0a             cmp    $0xa,%rbx
  1a:   75 f2                   jne    e <loop>
  1c:   c3                      retq

  increments rax until its value is 20.
  Let's prove that this function returns 20.
*)
let loop_mc = new_definition `loop_mc = [
  word 0x48; word 0xc7; word 0xc3; word 0x00; word 0x00; word 0x00; word 0x00;
  word 0x48; word 0xc7; word 0xc0; word 0x00; word 0x00; word 0x00; word 0x00;

// loop:
  word 0x48; word 0x83; word 0xc3; word 0x01;
  word 0x48; word 0x83; word 0xc0; word 0x02;
  word 0x48; word 0x83; word 0xfb; word 0x0a;
  word 0x75; word 0xf2;
  word 0xc3
]:((8)word)list`;;

let EXEC = X86_MK_EXEC_RULE loop_mc;;

let loop_SPEC = prove(
  `forall pc stackpointer returnaddress.
  ensures x86
    // Precondition
    (\s. bytes_loaded s (word pc) loop_mc /\
         read RIP s = word pc /\
         read RSP s = stackpointer /\
         read (memory :> bytes64 stackpointer) s = returnaddress)
    // Postcondition
    (\s. read RIP s = returnaddress /\
         read RSP s = word_add stackpointer (word 8) /\
         read RAX s = word 20)
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [RSP;RIP;RAX;RBX] ,, MAYCHANGE SOME_FLAGS)`,
  (* Unfold flag registers! *)
  REWRITE_TAC[SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN

  (* ENSURES_WHILE_PAUP_TAC is one of several tactics for declaring a hoare triple of a loop.
     PAUP means:
     - "P": The loop ends with a flag-setting instruction such as 'cmp' or 'add'.
            'read ZF s <=> i = 10' in the below statement relates the flag with
            the loop counter.
     - "A": The loop counter starts from variable 'a', In this tactic, this is 0.
            Actually, when a = 0, you can also use ENSURES_WHILE_PUP_TAC.
     - "UP": The counter goes up. *)
  ENSURES_WHILE_PAUP_TAC
    `0` (* counter begin number *)
    `10` (* counter end number *)
    `pc + 0xe` (* loop body start PC *)
    `pc + 0x1a` (* loop backedge branch PC *)
    `\i s. // loop invariant at the end of the loop
           (read RBX s = word i /\ read RAX s = word (i*2) /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress) /\
           // loop backedge condition
           (read ZF s <=> i = 10)` THEN
  REPEAT CONJ_TAC THENL [
    (* counter begin < counter end *)
    ARITH_TAC;

    (* entrance to the loop *)
    (* Let's use X86_SIM_TAC which is ENSURES_INIT_TAC + X86_STEPS_TAC +
       ENSURES_FINAL_STATE_TAC + some post-processing. *)
    X86_SIM_TAC EXEC (1--2) THEN
    CONV_TAC WORD_RULE;

    (* The loop body. let's prove this later. *)
    (* If you are interactively exploring this proof, try `r 1;;`. *)
    ALL_TAC;

    (* Prove that backedge is taken if i != 10. *)
    REPEAT STRIP_TAC THEN
    X86_SIM_TAC EXEC [1];

    (* Loop exit to the end of the program *)
    X86_SIM_TAC EXEC (1--2) THEN
    (* word (10*2) = word 20 *)
    CONV_TAC WORD_RULE
  ] THEN

  (* The loop body *)
  REPEAT STRIP_TAC THEN
  X86_SIM_TAC EXEC (1--3) THEN
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
    CONJ_TAC THENL [ (* will create two arithmetic subgoals. *)
      UNDISCH_TAC `i < 10` THEN ARITH_TAC;
      ARITH_TAC
    ]
  ]);;
