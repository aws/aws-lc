(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove a property of a simple program that reads from and writes to
  the memory.
******************************************************************************)

needs "x86/proofs/base.ml";;

(* The following program
  0:   48 8b 08                mov    (%rax),%rcx
  3:   48 8b 13                mov    (%rbx),%rdx
  6:   48 89 0b                mov    %rcx,(%rbx)
  9:   48 89 10                mov    %rdx,(%rax)

  .. swaps the two words at address rax and rbx, of rax and rbx do not alias.
  Let's prove this.
*)

let memory_mc = new_definition `memory_mc = [
  word 0x48; word 0x8b; word 0x08;
  word 0x48; word 0x8b; word 0x13;
  word 0x48; word 0x89; word 0x0b;
  word 0x48; word 0x89; word 0x10
]:((8)word)list`;;

let EXEC = X86_MK_EXEC_RULE memory_mc;;

let memory_SPEC = prove(
  `forall pc loc0 loc1 a b.
  // Assume that loc0 (=rax) and loc1(=rbx) do not overlap within 8 bytes.
  nonoverlapping (word loc0:int64, 8) (word loc1:int64, 8) /\
  // .. and the writing locations do not overlap with the loaded program.
  nonoverlapping (word loc0:int64, 8) (word pc:int64, LENGTH memory_mc) /\
  nonoverlapping (word loc1:int64, 8) (word pc:int64, LENGTH memory_mc)
  ==> ensures x86
    // Precondition
    (\s. bytes_loaded s (word pc) memory_mc /\
         read RIP s = word pc /\
         read RAX s = word loc0 /\
         read RBX s = word loc1 /\
         read (memory :> bytes64 (word loc0)) s = word a /\
         read (memory :> bytes64 (word loc1)) s = word b)
    // Postcondition
    (\s. read RIP s = word (pc + 12) /\
         read (memory :> bytes64 (word loc0)) s = word b /\
         read (memory :> bytes64 (word loc1)) s = word a)
    // Registers (and memory locations) that may change after execution.
    // ',,' is composition of relations.
    (MAYCHANGE [RIP;RCX;RDX] ,,
     // The memory locations may change. Record this.
     MAYCHANGE [memory :> bytes64 (word loc0); memory :> bytes64 (word loc1)])`,

  (* Convert 'nonoverlapping' into 'nonoverlapping_modulo' and rewrite 'LENGTH memory_mc'
     with the concrete number. *)
  REWRITE_TAC[NONOVERLAPPING_CLAUSES;fst EXEC] THEN
  (* Strips the assumption and outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN

  (* Let's do symbolic execution until it hits the branch instruction. *)
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC EXEC (1--4) THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* If the written nonoverlapping condition is not sufficient, existing assumptions
   on memory loads may be erased after simulating store instructions.
   To print which instructions are erased, set
     components_print_log := true;;
*)
