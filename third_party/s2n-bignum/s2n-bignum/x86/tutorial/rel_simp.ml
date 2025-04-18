(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
        An example that proves equivalence of two straight-line codes.
******************************************************************************)

(* Please copy this file to the root directory of
   s2n-bignum, then follow the instructions. *)

needs "x86/proofs/equiv.ml";;

(* Prove that given RAX and RBX are equal, their final results are also equal. *)

let simp1_mc = define_assert_from_elf "simp1_mc" "x86/tutorial/rel_simp.o"
[
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0x83; 0xc0; 0x01   (* ADD (% rax) (Imm8 (word 1)) *)
];;
let SIMP1_EXEC_LENGTH, SIMP1_EXEC_DECODE = X86_MK_EXEC_RULE simp1_mc;;
let SIMP1_EXEC = SIMP1_EXEC_LENGTH, SIMP1_EXEC_DECODE;;

let simp2_mc = define_assert_from_elf "simp2_mc" "x86/tutorial/rel_simp2.o"
[
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0xc7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Imm32 (word 1)) *)
  0x48; 0x01; 0xc8         (* ADD (% rax) (% rcx) *)
];;
let SIMP2_EXEC_LENGTH, SIMP2_EXEC_DECODE = X86_MK_EXEC_RULE simp2_mc;;
let SIMP2_EXEC = SIMP2_EXEC_LENGTH, SIMP2_EXEC_DECODE;;


(* A definition of 'equivalent states' that is sufficient to prove the correctness
   of SIMP2 using that of SIMP1. *)
let simp_equiv_states = new_definition
  `!s1 s2. (simp_equiv_states:(x86state#x86state)->bool) (s1,s2) <=>
    mk_equiv_regs [RAX;RBX] (s1,s2)`;;


(* For relational reasoning, we use predicates and tactics that are slightly
   different from those for unary reasoning. *)

(* Proving the equivalence between SIMP1 and SIMP2 w.r.t. simp_equiv_states*)
let SIMP1_SIMP2_EQUIV = prove(`forall pc pc2.
  // Relational hoare triple.
  ensures2 x86
    // Precondition
    (\(s,s2).
        bytes_loaded s (word pc) simp1_mc /\
        read RIP s = word pc /\
        bytes_loaded s2 (word pc2) simp2_mc /\
        read RIP s2 = word pc2 /\
        simp_equiv_states (s,s2))
    // Postcondition
    (\(s,s2).
        read RIP s = word (pc + LENGTH simp1_mc) /\
        read RIP s2 = word (pc2 + LENGTH simp2_mc) /\
        simp_equiv_states (s,s2))
    // State components that may change in the two programs.
    (\(s,s2) (s',s2').
      (MAYCHANGE [RIP;RAX] ,, MAYCHANGE SOME_FLAGS) s s' /\
      (MAYCHANGE [RIP;RAX;RCX] ,, MAYCHANGE SOME_FLAGS) s2 s2')
    // The number of small steps of the 'left' program and 'right' program.
    // 'ensures2' needs the number of small steps taken to reach at the
    // postcondition. Similarly, 'ensures_n' is a unary predicate similar to
    // 'ensures' but takes the number of steps too. 'ensures_n' will not
    // appear in this example.
    (\s. 2) (\s. 3)`,
  REWRITE_TAC[SOME_FLAGS;SIMP1_EXEC_LENGTH;SIMP2_EXEC_LENGTH] THEN
  REWRITE_TAC[simp_equiv_states;mk_equiv_regs] THEN
  REPEAT STRIP_TAC THEN

  (* Start symbolic execution of the two programs! The left program's initial
     state is named as s0, and the right is s0'. *)
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  REPEAT_N 2 (* # of vars in simp_equiv_states *) (FIRST_X_ASSUM CHOOSE_TAC) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN

  (* Symbolically execute the left program only. *)
  X86_N_STUTTER_LEFT_TAC SIMP1_EXEC [1;2] THEN
  (* Symbolically execute the right program only. "'" is the suffix of the
     state name. *)
  X86_N_STUTTER_RIGHT_TAC SIMP2_EXEC [1;2;3] "'" THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    CONJ_TAC THEN (HINT_EXISTS_REFL_TAC THEN REWRITE_TAC[]);

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;
