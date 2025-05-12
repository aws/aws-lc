(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
        An example that proves equivalence of two straight-line codes.
******************************************************************************)

(* Please copy this file to the root directory of
   s2n-bignum, then follow the instructions. *)

needs "arm/proofs/equiv.ml";;

(* Prove that given x0 and x1 are equal, their final results are also equal. *)

let simp_mc = define_assert_from_elf "simp_mc" "arm/tutorial/rel_simp.o" [
  0x91000400;       (* arm_ADD X0 X0 (rvalue (word 1)) *)
  0x91000821;       (* arm_ADD X1 X1 (rvalue (word 2)) *)
  0x91000c00        (* arm_ADD X0 X0 (rvalue (word 3)) *)
];;

let simp2_mc = define_assert_from_elf "simp2_mc" "arm/tutorial/rel_simp2.o" [
  0x91001000;       (* arm_ADD X0 X0 (rvalue (word 4)) *)
  0x91000821        (* arm_ADD X1 X1 (rvalue (word 2)) *)
];;

let SIMP_EXEC = ARM_MK_EXEC_RULE simp_mc;;
let SIMP2_EXEC = ARM_MK_EXEC_RULE simp2_mc;;

(* For relational reasoning, we use predicates and tactics that are slightly
   different from those for unary reasoning. *)

let SIMP_EQUIV = prove(
  `forall pc1 pc2 a b.
    // Relational hoare triple.
    ensures2 arm
      // Precondition
      (\(s1,s2). aligned_bytes_loaded s1 (word pc1) simp_mc /\
                  read PC s1 = word pc1 /\
                  aligned_bytes_loaded s2 (word pc2) simp2_mc /\
                  read PC s2 = word pc2 /\
                  // X0 and X1 start equal.
                  read X0 s1 = a /\ read X0 s2 = a /\
                  read X1 s1 = b /\ read X1 s2 = b)
      // Postcondition
      (\(s1,s2). aligned_bytes_loaded s1 (word pc1) simp_mc /\
                  read PC s1 = word (pc1 + 12) /\
                  aligned_bytes_loaded s2 (word pc2) simp2_mc /\
                  read PC s2 = word (pc2 + 8) /\
                  // They finish with an equal value.
                  (?k. read X0 s1 = k /\ read X0 s2 = k) /\
                  (?k2. read X1 s1 = k2 /\ read X1 s2 = k2))
      // State components that may change.
      (\(s1,s2) (s1',s2').
        // PC,X0,X1 may change in the left program
        MAYCHANGE [PC;X0;X1] s1 s1' /\
        // .. and in the right program as well.
        MAYCHANGE [PC;X0;X1] s2 s2')
      // The number of small steps of the 'left' program and 'right' program.
      // 'ensures2' needs the number of small steps taken to reach at the
      // postcondition. Similarly, 'ensures_n' is a unary predicate similar to
      // 'ensures' but takes the number of steps too. 'ensures_n' will not
      // appear in this example.
      (\s. 3) (\s. 2)`,

  REPEAT STRIP_TAC THEN
  (* Start symbolic execution of the two programs! The left program's initial
     state is named as s0, and the right is s0'. *)
  ENSURES2_INIT_TAC "s0" "s0'" THEN

  (* Symbolically execute the left program only. *)
  ARM_N_STUTTER_LEFT_TAC SIMP_EXEC (1--3) None THEN
  (* Symbolically execute the right program only. "'" is the suffix of the
     state name. *)
  ARM_N_STUTTER_RIGHT_TAC SIMP2_EXEC (1--2) "'" None THEN

  (* Let's prove the postcondition. *)
  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  CONJ_TAC THENL [
    (* ((?k. word_add a (word 4) = k)
       Actually, simplification procedure in symbolic execution tactic already
       folded 'word_add (word_add a (word 1)) (word 3)' into
       'word_add a (word 4)'. *)
    (* META_EXISTS_TAC is somewhat similar to eexists in Coq. *)
    CONJ_TAC THENL [
      META_EXISTS_TAC THEN UNIFY_REFL_TAC;
      META_EXISTS_TAC THEN UNIFY_REFL_TAC;
    ];

    (* Maychange pair *)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;
