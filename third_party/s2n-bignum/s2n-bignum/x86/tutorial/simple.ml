(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Proving a simple property about program 'simple.S'
******************************************************************************)

(* Please copy this file to the root directory of s2n-bignum, then
   follow the instructions. *)

needs "x86/proofs/base.ml";;

(* Let's prove a simple property of the following program:

    0:   48 01 c3                add    %rax,%rbx
    3:   48 29 c3                sub    %rax,%rbx

  Let's start with defining a byte sequence of a program 'simple.S'
*)
let simple_mc = new_definition `simple_mc = [
    word 0x48; word 0x01; word 0xc3;
    word 0x48; word 0x29; word 0xc3
  ]:((8)word)list`;;

(* Or, you can read .o file and store the byte list as follows:
let simple_mc = define_assert_from_elf "simple_mc" "x86/tutorial/simple.o"
[
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x29; 0xc3         (* SUB (% rbx) (% rax) *)
];;

You can get the above OCaml list data structure from
`print_literal_from_elf "<.o file>"` or `save_literal_from_elf "<out.txt>"
"<.o file>"`.
*)

(* X86_MK_EXEC_RULE decodes the byte sequence into conjunction of
  equalities between the bytes and instructions. *)
let EXEC = X86_MK_EXEC_RULE simple_mc;;

(*
  In s2n-bignum, a specification (ensures) has three components:
  1. precondition: assume that a program starts from some program state satisfying the critera
  2. postcondition: the program must reach to a program state satisfying the criteria
  3. frame: the start program state and end program state must satisfy this relation
     (e.g., this program only changes callee-save register)
  In this file,
  1. precondition is:
    - the 'simple' binary is loaded at some location in memory, say 'pc'
    - the x86 program counter register, RIP, has value pc
    - the x86 register RAX has a symbolic value a and RBX has a symbolic value b
  2. postcondition is:
    - the x86 program counter RIP, has value pc+6
      (meaning that two instructions have been executed)
    - the x86 register RBX has value b
  3. frame is:
    - the register values of RIP, RBX and flags might have been changed

  If you are using the VSCode plugin of HOL Light, you can ctrl+click
  (cmd+click for Mac) to jump to definitions.
*)
let SIMPLE_SPEC = prove(
  `forall pc a b.
  ensures x86
    // Precondition
    (\s. // bytes_loaded states that a byte sequence 'simple_mc'
         // is loaded at memory location 'pc' in the state 's'.
         bytes_loaded s (word pc) simple_mc /\
         // 'word' is a bit-vector type in HOL Light.
         // 'word a' means it is a bit-vector whose numeral (:num type)
         // is 'a'. Its bit-width is inferred as 64 bits here, but it can
         // be manually annotated as (word a:(64)word).
         read RIP s = word pc /\
         read RAX s = word a /\
         read RBX s = word b)
    // Postcondition
    (\s. read RIP s = word (pc+6) /\
         read RBX s = word b)
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [RIP;RBX] ,, MAYCHANGE SOME_FLAGS)`,

  (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN
  (* ENSURES_FINAL_STATE_TAC does not understand SOME_FLAGS in MAYCHANGE. Let's
     unfold this in advance. *)
  REWRITE_TAC [SOME_FLAGS] THEN
  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN

  (* Symbolically run two instructions *)
  X86_STEPS_TAC EXEC (1--2) THEN
  (* Try to prove the postcondition and frame as much as possible *)
  ENSURES_FINAL_STATE_TAC THEN

  (* Use ASM_REWRITE_TAC[] to rewrite the goal using equalities in assumptions. *)
  ASM_REWRITE_TAC[] THEN
  (* We need to prove this:
     `word_sub (word_add (word b) (word a)) (word a) = word b`
     Use an automated prover for words in HOL Light *)
  CONV_TAC WORD_RULE);;

(* Note that symbolic simulator will discard the output of instructions
   if its inputs do not have their symbolic expressions defined in assumption.
   To list which instructions are discarded by the simulation tactic.
   set:
    x86_print_log := true;;
   This flag will also print helpful informations that are useful. *)
