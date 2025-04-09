(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
              An example that proves the equivalence of
              two implementations of 128x128->256-bit squaring.
******************************************************************************)

needs "arm/proofs/equiv.ml";;
(* neon_helper.ml has lemmas and tactics that are useful to prove programs
   manipulating SIMD registers. *)
needs "arm/proofs/neon_helper.ml";;

(* This is a realistic (and a bit 'dirty') example that shows how equivalence
   of vectorization is proven using relational reasoning.
   It is always welcome to clean this proof further. *)

let veceq_mc = define_assert_from_elf "veceq_mc" "arm/tutorial/rel_veceq.o" [
  0xa9402c2a;       (* arm_LDP X10 X11 X1 (Immediate_Offset (iword (&0))) *)
  0x9b0a7d54;       (* arm_MUL X20 X10 X10 *)
  0x9bca7d4c;       (* arm_UMULH X12 X10 X10 *)
  0x9b0b7d4d;       (* arm_MUL X13 X10 X11 *)
  0x9bcb7d4e;       (* arm_UMULH X14 X10 X11 *)
  0x9b0b7d6f;       (* arm_MUL X15 X11 X11 *)
  0x9bcb7d70;       (* arm_UMULH X16 X11 X11 *)
  0xab0d019b;       (* arm_ADDS X27 X12 X13 *)
  0xba0e01fc;       (* arm_ADCS X28 X15 X14 *)
  0x9a1f021d;       (* arm_ADC X29 X16 XZR *)
  0xab0d0375;       (* arm_ADDS X21 X27 X13 *)
  0xba0e0396;       (* arm_ADCS X22 X28 X14 *)
  0x9a1f03b7        (* arm_ADC X23 X29 XZR *)
];;

let VECEQ_EXEC = ARM_MK_EXEC_RULE veceq_mc;;

let veceq2_mc = define_assert_from_elf "veceq2_mc" "arm/tutorial/rel_veceq2.o" [
  0xa9403c29;       (* arm_LDP X9 X15 X1 (Immediate_Offset (iword (&0))) *)
  0x3dc0003e;       (* arm_LDR Q30 X1 (Immediate_Offset (word 0)) *)
  0x2ebec3c0;       (* arm_UMULL_VEC Q0 Q30 Q30 32 *)
  0x6ebec3c2;       (* arm_UMULL2_VEC Q2 Q30 Q30 32 *)
  0x0ea12bd8;       (* arm_XTN Q24 Q30 32 *)
  0x4e9e5bde;       (* arm_UZP2 Q30 Q30 Q30 32 *)
  0x2eb8c3de;       (* arm_UMULL_VEC Q30 Q30 Q24 32 *)
  0x4e083c07;       (* arm_UMOV X7 Q0 0 8 *)
  0x4e183c0e;       (* arm_UMOV X14 Q0 1 8 *)
  0x4e083c53;       (* arm_UMOV X19 Q2 0 8 *)
  0x4e183c56;       (* arm_UMOV X22 Q2 1 8 *)
  0x4e083fc4;       (* arm_UMOV X4 Q30 0 8 *)
  0x4e183fcc;       (* arm_UMOV X12 Q30 1 8 *)
  0xab0484f5;       (* arm_ADDS X21 X7 (Shiftedreg X4 LSL 33) *)
  0xd35ffc84;       (* arm_LSR X4 X4 31 *)
  0x9a0401ce;       (* arm_ADC X14 X14 X4 *)
  0xab0c8673;       (* arm_ADDS X19 X19 (Shiftedreg X12 LSL 33) *)
  0xd35ffd84;       (* arm_LSR X4 X12 31 *)
  0x9a0402d6;       (* arm_ADC X22 X22 X4 *)
  0x9b0f7d24;       (* arm_MUL X4 X9 X15 *)
  0x9bcf7d2c;       (* arm_UMULH X12 X9 X15 *)
  0xab0405d8;       (* arm_ADDS X24 X14 (Shiftedreg X4 LSL 1) *)
  0x93c4fd84;       (* arm_EXTR X4 X12 X4 63 *)
  0xba040273;       (* arm_ADCS X19 X19 X4 *)
  0xd37ffd84;       (* arm_LSR X4 X12 63 *)
  0x9a0402c4        (* arm_ADC X4 X22 X4 *)
];;

let VECEQ2_EXEC = ARM_MK_EXEC_RULE veceq2_mc;;


(* Define the equivalence of input states and output states. *)

let equiv_input_states = new_definition
  `forall s1 s1' x.
    (equiv_input_states:(armstate#armstate)->int64->bool) (s1,s1') x <=>
    (read X1 s1 = x /\ read X1 s1' = x /\
     exists a. bignum_from_memory (x,2) s1 = a /\
         bignum_from_memory (x,2) s1' = a)`;;

let equiv_output_states = new_definition
  `forall s1 s1'.
    (equiv_output_states:(armstate#armstate)->bool) (s1,s1') <=>
    (exists a. read X20 s1 = a /\ read X21 s1' = a /\
     (exists b. read X21 s1 = b /\ read X24 s1' = b /\
      (exists c. read X22 s1 = c /\ read X19 s1' = c /\
       (exists d. read X23 s1 = d /\ read X4 s1' = d))))`;;


(* Define the equivalence statement which is ensures2 predicate.
   Please look at the definition of mk_equiv_statement_simple for full
   definitions of its parameters. *)

let equiv_goal1 = mk_equiv_statement_simple
    `T` (* assumption such as nonoverlapping; nothing here, so simply T. *)
    equiv_input_states
    equiv_output_states
    veceq_mc
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X20;X21;X22;X23;X27;X28;X29]`
    veceq2_mc
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X19;X21;X22;X24]`;;

(* 'actions' is a list of line diffs between the two assembly files (textual
    form). This isn't important in this example, but to understand when
    it is useful you might want to look at proofs in s2n-bignum that use
    EQUIV_STEPS_TAC. *)
let actions = [
  ("replace",0,13,0,26)
];;

(* After every small step, simplify the symbolic expression using
   a new custom rewrite rule that is WORD_BITMANIP_SIMP_LEMMAS. *)
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS]]
  @ (!extra_word_CONV);;


let VECTORIZE_SQR_EQUIV = prove(equiv_goal1,

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    fst VECEQ_EXEC; fst VECEQ2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC equiv_input_states THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Symbolically simulate each program, to the last instructions. *)
  EQUIV_STEPS_TAC actions VECEQ_EXEC VECEQ2_EXEC THEN

  (* For some reason, using this additional RULE_ASSUME_TAC was necessary...
     Adding these rules to extra_word_CONV didn't work. Yes, this is a 'dirty'
     part of the current status (= manual rewrites are sometimes necessary).
     Also, these rewrite rules (WORD_SQR128_DIGIT0, ...) are not succinct.
     Would be great if their proofs are shorter at least. *)
  RULE_ASSUM_TAC (REWRITE_RULE[WORD_SQR128_DIGIT0;
                       WORD_SQR128_DIGIT1;WORD_SQR128_DIGIT2;
                       WORD_SQR128_DIGIT3]) THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (* Prove the equivalence! *)
    ASM_REWRITE_TAC[equiv_output_states;mk_equiv_regs;mk_equiv_bool_regs] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;
