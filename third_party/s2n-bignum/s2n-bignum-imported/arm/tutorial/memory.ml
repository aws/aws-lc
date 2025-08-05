(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove a property of a simple program that reads from and writes to
  the memory.
******************************************************************************)

needs "arm/proofs/base.ml";;

(* The following program
  0:   f9400002        ldr     x2, [x0]
  4:   f9400023        ldr     x3, [x1]
  8:   f9000022        str     x2, [x1]
  c:   f9000003        str     x3, [x0]

  .. swaps the two words at address x0 and x1, of x0 and x1 do not alias.
  Let's prove this.
*)

let memory_mc = new_definition `memory_mc = [
  word 0x02; word 0x00; word 0x40; word 0xf9; // ldr     x2, [x0]
  word 0x23; word 0x00; word 0x40; word 0xf9; // ldr     x3, [x1]
  word 0x22; word 0x00; word 0x00; word 0xf9; // str     x2, [x1]
  word 0x03; word 0x00; word 0x00; word 0xf9  // str     x3, [x0]
]:((8)word)list`;;

let EXEC = ARM_MK_EXEC_RULE memory_mc;;

let memory_SPEC = prove(
  `forall pc loc0 loc1 a b.
  // Assume that loc0 (=x0) and loc1(=x1) do not overlap within 8 bytes.
  nonoverlapping (word loc0:int64, 8) (word loc1:int64, 8) /\
  // .. and the writing locations do not overlap with the loaded program.
  nonoverlapping (word loc0:int64, 8) (word pc:int64, LENGTH memory_mc) /\
  nonoverlapping (word loc1:int64, 8) (word pc:int64, LENGTH memory_mc)
  ==> ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) memory_mc /\
         read PC s = word pc /\
         read X0 s = word loc0 /\
         read X1 s = word loc1 /\
         read (memory :> bytes64 (word loc0)) s = word a /\
         read (memory :> bytes64 (word loc1)) s = word b)
    // Postcondition
    (\s. read PC s = word (pc + 16) /\
         read (memory :> bytes64 (word loc0)) s = word b /\
         read (memory :> bytes64 (word loc1)) s = word a)
    // Registers (and memory locations) that may change after execution.
    // ',,' is composition of relations.
    (MAYCHANGE [PC;X2;X3] ,,
     // The memory locations may change. Record this.
     MAYCHANGE [memory :> bytes64 (word loc0); memory :> bytes64 (word loc1)] ,,
     // Memory instructions raise observable microarchitectural events!
     MAYCHANGE [events])`,

  (* Rewrite 'LENGTH memory_mc' with the concrete number. *)
  REWRITE_TAC[fst EXEC] THEN
  (* Strips the assumption and outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN

  (* Let's do symbolic execution until it hits the branch instruction. *)
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--4) THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* If the written nonoverlapping condition is not sufficient, existing assumptions
   on memory loads may be erased after simulating store instructions.
   To print which instructions are erased, set
     components_print_log := true;;
*)
