(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
        An example that proves equivalence of two straight-line codes
                      whose instructions are shuffled.
******************************************************************************)

(* Please copy this file to the root directory of
   s2n-bignum, then follow the instructions. *)

needs "arm/proofs/equiv.ml";;

(* This example will define & prove the equivalence of two programs
   whose instructions are reordered, using ARM_N_STEPS_AND_ABBREV_TAC and
   ARM_N_STEPS_AND_REWRITE_TAC.
   These tactics receive the mapping between the lines of instructions
   of the two programs (which is an OCaml integer list).
   ARM_N_STEPS_AND_ABBREV_TAC symbolically simulates the "left" program,
   introduces abbreviations of the output symbolic expressions of each
   instruction, and stores it to an OCaml reference variable.
   ARM_N_STEPS_AND_REWRITE_TAC symbolically simulates the "right" program,
   finds the right abbreviation expression according to the line-number
   mapping information, and rewrites the output expressions using the matched
   abbreviation. *)

let mc = define_assert_from_elf "mc" "arm/tutorial/rel_reordertac.o" [
  0xf940000a;       (* arm_LDR X10 X0 (Immediate_Offset (word 0)) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xf900002a;       (* arm_STR X10 X1 (Immediate_Offset (word 0)) *)
  0xf940040a;       (* arm_LDR X10 X0 (Immediate_Offset (word 8)) *)
  0x9100094a;       (* arm_ADD X10 X10 (rvalue (word 2)) *)
  0xf900042a        (* arm_STR X10 X1 (Immediate_Offset (word 8)) *)
];;

(* Note that the used registers are different between mc and mc2
   (X10 vs. X10,X11). This is fine since the tactics can smartly
   map the registers.
   Also, this reordering is correct only of [X0, X0+16) is disjoint with
   [X1, X1+16). We will have this as an assumption in the equivalence
   goal. *)
let mc2 = define_assert_from_elf "mc2" "arm/tutorial/rel_reordertac2.o" [
  0xf940000a;       (* arm_LDR X10 X0 (Immediate_Offset (word 0)) *)
  0xf940040b;       (* arm_LDR X11 X0 (Immediate_Offset (word 8)) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0x9100096b;       (* arm_ADD X11 X11 (rvalue (word 2)) *)
  0xf900002a;       (* arm_STR X10 X1 (Immediate_Offset (word 0)) *)
  0xf900042b        (* arm_STR X11 X1 (Immediate_Offset (word 8)) *)
];;

let EXEC = ARM_MK_EXEC_RULE mc;;
let EXEC2 = ARM_MK_EXEC_RULE mc2;;

(* Define the equality between the input states. *)
let eqin = new_definition
  `forall s1 s1' inbuf outbuf.
    (eqin:(armstate#armstate)->int64->int64->bool) (s1,s1') inbuf outbuf <=>
     (// The values of buffer pointers, X0 and X1.
      // Their values are symbolically defined as inbuf and outbuf.
      // outbuf is also used for the nonoverlapping precondition between
      // the output buffer and the program bytecode.
      read X0 s1 = inbuf /\
      read X0 s1' = inbuf /\
      read X1 s1 = outbuf /\
      read X1 s1' = outbuf /\
      // The equal buffer contents at the input buffer. '2' stands for 2 words
      // (and 1 word is 8 bytes, hence 2*8=16 bytes)
      (exists n.
        bignum_from_memory (inbuf,2) s1 = n /\
        bignum_from_memory (inbuf,2) s1' = n))`;;

(* Define the equality between the output states. *)
let eqout = new_definition
  `forall s1 s1' inbuf outbuf.
    (eqout:(armstate#armstate)->int64->int64->bool) (s1,s1') inbuf outbuf <=>
     (read X0 s1 = inbuf /\
      read X0 s1' = inbuf /\
      read X1 s1 = outbuf /\
      read X1 s1' = outbuf /\
      (exists n.
        bignum_from_memory (inbuf,2) s1 = n /\
        bignum_from_memory (inbuf,2) s1' = n) /\
      (exists n.
        bignum_from_memory (outbuf,2) s1 = n /\
        bignum_from_memory (outbuf,2) s1' = n))`;;

(* Now, build the program equivalence statement using
   'mk_equiv_statement_simple'.
   Its first argument states the assumption that will appear at
   LHS of '<assumption> ==> ensures2 ..(equiv statement)..'.

   If it fails, please try `arm_print_log := true`. *)
let equiv_goal = mk_equiv_statement_simple
  `ALL (nonoverlapping (outbuf,16)) [
    (word pc:int64, LENGTH mc);
    (word pc2:int64, LENGTH mc2);
    (inbuf:int64, 16)
  ]`
  eqin  (* Input state equivalence *)
  eqout (* Output state equivalence *)
  mc    (* First program machine code *)
  `MAYCHANGE [PC; X10] ,, MAYCHANGE [memory :> bytes (outbuf, 16)] ,, MAYCHANGE [events]`
  mc2   (* Second program machine code *)
  `MAYCHANGE [PC; X10; X11] ,, MAYCHANGE [memory :> bytes (outbuf, 16)] ,, MAYCHANGE [events]`;;

(* equiv_goal is:
  `forall pc pc2 inbuf outbuf.
       ALL (nonoverlapping (outbuf,16))
       [word pc,LENGTH mc; word pc2,LENGTH mc2; inbuf,16]
       ==> ensures2 arm
           (\(s,s2).
                aligned_bytes_loaded s (word pc) mc /\
                read PC s = word pc /\
                aligned_bytes_loaded s2 (word pc2) mc2 /\
                read PC s2 = word pc2 /\
                eqin (s,s2) inbuf outbuf)
           (\(s,s2).
                aligned_bytes_loaded s (word pc) mc /\
                read PC s = word (pc + 24) /\
                aligned_bytes_loaded s2 (word pc2) mc2 /\
                read PC s2 = word (pc2 + 24) /\
                eqout (s,s2) inbuf outbuf)
           (\(s,s2) (s',s2').
                (MAYCHANGE [PC; X10] ,,
                 MAYCHANGE [memory :> bytes (outbuf,16)] ,,
                 MAYCHANGE [events])
                s
                s' /\
                (MAYCHANGE [PC; X10; X11] ,,
                 MAYCHANGE [memory :> bytes (outbuf,16)] ,,
                 MAYCHANGE [events])
                s2
                s2')
           (\s. 6)
           (\s. 6)`
*)

(* Line numbers from the second program (mc2) to the first program (mc1). *)
let inst_map = [1;4;2;5;3;6];;

(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

(* Now, let's prove the program equivalence. *)
let EQUIV = prove(equiv_goal,

  (* Rewrite ALL and LENGTH * *)
  REWRITE_TAC[ALL; fst EXEC; fst EXEC2] THEN
  REPEAT STRIP_TAC THEN

  (** Initialize **)
  EQUIV_INITIATE_TAC eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC EXEC  (1--(List.length inst_map))
      state_to_abbrevs None THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC EXEC2 (1--(List.length inst_map))
      inst_map state_to_abbrevs None THEN

  (* Running the statements above step by step will raise an error
     message saying that the tactic is not VALID. You can temporarily
     disable the message by redefining 'e' as follows:

     let e tac = refine(by(tac));;

     The whole proof ("prove(...)") will still run okay.
  *)

  REPEAT_N 2 ENSURES_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  (* This tactic below is typically fixed and probably you will want to reuse. :) *)
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[eqout;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (outbuf,2) s`] THEN
    REPEAT CONJ_TAC THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;
