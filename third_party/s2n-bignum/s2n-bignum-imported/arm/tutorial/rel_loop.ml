(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
              An example that proves equivalence of two loops.
******************************************************************************)

needs "arm/proofs/equiv.ml";;

(* Prove that these two loops are equivalent in the sense that the results of
   two X2 are same. *)

let loop_mc = define_assert_from_elf "loop_mc" "arm/tutorial/rel_loop.o" [
  0x91000842;       (* arm_ADD X2 X2 (rvalue (word 2)) *)
  0x91000400;       (* arm_ADD X0 X0 (rvalue (word 1)) *)
  0xeb01001f;       (* arm_CMP X0 X1 *)
  0x54ffffa1        (* arm_BNE (word 2097140) *)
];;

let loop2_mc = define_assert_from_elf "loop2_mc" "arm/tutorial/rel_loop2.o" [
  0x91000442;       (* arm_ADD X2 X2 (rvalue (word 1)) *)
  0x91000442;       (* arm_ADD X2 X2 (rvalue (word 1)) *)
  0x91000400;       (* arm_ADD X0 X0 (rvalue (word 1)) *)
  0xeb01001f;       (* arm_CMP X0 X1 *)
  0x54ffff81        (* arm_BNE (word 2097136) *)
];;

let LOOP_EXEC = ARM_MK_EXEC_RULE loop_mc;;
let LOOP2_EXEC = ARM_MK_EXEC_RULE loop2_mc;;

(* For relational reasoning, we use predicates and tactics that are slightly
   different from those for unary reasoning. *)

let LOOP_EQUIV = prove(
  `forall pc1 pc2 n.
    n > 0 /\ n < 2 EXP 64 ==>
    // Relational hoare triple.
    ensures2 arm
      // Precondition
      (\(s1,s2). aligned_bytes_loaded s1 (word pc1) loop_mc /\
                  read PC s1 = word pc1 /\
                  aligned_bytes_loaded s2 (word pc2) loop2_mc /\
                  read PC s2 = word pc2 /\
                  // X0 is the induction variable and X1 is n.
                  (read X0 s1 = word 0 /\ read X0 s2 = word 0 /\
                  read X1 s1 = word n /\ read X1 s2 = word n /\
                  // X2 must start equal.
                  (?k. read X2 s1 = k /\ read X2 s2 = k)))
      // Postcondition
      (\(s1,s2). aligned_bytes_loaded s1 (word pc1) loop_mc /\
                  read PC s1 = word (pc1 + 12) /\
                  aligned_bytes_loaded s2 (word pc2) loop2_mc /\
                  read PC s2 = word (pc2 + 16) /\
                  // They finish with an equal value.
                  (?k. read X2 s1 = k /\ read X2 s2 = k))
      // State components that may change.
      (\(s1,s2) (s1',s2').
        (MAYCHANGE [PC;X0;X2] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s1 s1' /\
        (MAYCHANGE [PC;X0;X2] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]) s2 s2')
      // The number of small steps of the 'left' program and 'right' program.
      (\s. 4 * n - 1) (\s. 5 * n - 1)`,

  REPEAT STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN
  (* Look at the definition of ENSURES2_WHILE_PAUP_TAC in arm/proofs/equiv.ml
     to understand the meanings of arguments. *)
  ENSURES2_WHILE_PAUP_TAC `0:num` `n:num` `pc1:num` `pc1+12` `pc2:num` `pc2+16`
    `\(i:num) s1 s2.
        read X0 s1 = word i /\ read X0 s2 = word i /\
        read X1 s1 = word n /\ read X1 s2 = word n /\
        (?k. read X2 s1 = k /\ read X2 s2 = k)`
    `\(i:num) s. read ZF s <=> (word i:int64) = word n`
    `\(i:num) s. read ZF s <=> (word i:int64) = word n`
    `\(i:num). 3`
    `\(i:num). 4`
    `0` `0` `0` `0` `1` `1` THEN
  REPEAT CONJ_TAC THENL [
    (* # loop itrs > 0 *)
    ASM_ARITH_TAC;

    (* pre *)
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN
    MONOTONE_MAYCHANGE_CONJ_TAC;

    (* now the main loop! *)
    REPEAT STRIP_TAC THEN
    (* Start symbolic execution of two programs. *)
    ENSURES2_INIT_TAC "s0" "s0'" THEN

    FIRST_X_ASSUM (MP_TAC o (check (is_exists o concl))) THEN
    STRIP_TAC THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN

    (* Symbolically execute the left program only. *)
    ARM_N_STUTTER_LEFT_TAC LOOP_EXEC (1--3) None THEN
    (* Symbolically execute the right program only. *)
    ARM_N_STUTTER_RIGHT_TAC LOOP2_EXEC (1--4) "'" None THEN
    (* Let's prove the postcondition. *)
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_ADD] THEN

    CONJ_TAC THENL [
      CONJ_TAC THENL [
        META_EXISTS_TAC THEN UNIFY_REFL_TAC;
        REWRITE_TAC[VAL_EQ_0] THEN CONV_TAC WORD_RULE;
      ];

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* backedge *)
    REPEAT STRIP_TAC THEN
    ENSURES2_INIT_TAC "s0" "s0'" THEN
    UNDISCH_TAC `?k. read X2 s0 = k /\ read X2 s0' = k` THEN
    STRIP_TAC THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN

    ARM_N_STUTTER_LEFT_TAC LOOP_EXEC (1--1) None THEN
    ARM_N_STUTTER_RIGHT_TAC LOOP2_EXEC (1--1) "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_ADD] THEN

    SUBGOAL_THEN `(word i:int64 = word n) <=> F` SUBST_ALL_TAC THENL [
      REWRITE_TAC[WORD_EQ;CONG;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC;

      ALL_TAC
    ] THEN
    REWRITE_TAC[] THEN
    CONJ_TAC THENL [

      META_EXISTS_TAC THEN UNIFY_REFL_TAC;

      MONOTONE_MAYCHANGE_CONJ_TAC
    ];

    (* postcond *)
    MATCH_MP_TAC ENSURES2_TRIVIAL THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN MONOTONE_MAYCHANGE_CONJ_TAC;

    (* counter 1 *)
    REWRITE_TAC[NSUM_CONST_NUMSEG] THEN ASM_ARITH_TAC;

    (* counter 2 *)
    REWRITE_TAC[NSUM_CONST_NUMSEG] THEN ASM_ARITH_TAC;
  ]);;
