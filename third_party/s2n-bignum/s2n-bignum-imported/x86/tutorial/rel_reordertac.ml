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

needs "x86/proofs/equiv.ml";;

(* This example will define & prove the equivalence of two programs
   whose instructions are reordered, using X86_N_STEPS_AND_ABBREV_TAC and
   X86_N_STEPS_AND_REWRITE_TAC.
   These tactics receive the mapping between the lines of instructions
   of the two programs (which is an OCaml integer list).
   X86_N_STEPS_AND_ABBREV_TAC symbolically simulates the "left" program,
   introduces abbreviations of the output symbolic expressions of each
   instruction, and stores it to an OCaml reference variable.
   X86_N_STEPS_AND_REWRITE_TAC symbolically simulates the "right" program,
   finds the right abbreviation expression according to the line-number
   mapping information, and rewrites the output expressions using the matched
   abbreviation. *)

let mc = define_assert_from_elf "mc" "x86/tutorial/rel_reordertac.o" [
  0x48; 0x8b; 0x38;        (* MOV (% rdi) (Memop Quadword (%% (rax,0))) *)
  0x48; 0x83; 0xc7; 0x01;  (* ADD (% rdi) (Imm8 (word 1)) *)
  0x48; 0x89; 0x3b;        (* MOV (Memop Quadword (%% (rbx,0))) (% rdi) *)
  0x48; 0x8b; 0x78; 0x08;  (* MOV (% rdi) (Memop Quadword (%% (rax,8))) *)
  0x48; 0x83; 0xc7; 0x02;  (* ADD (% rdi) (Imm8 (word 2)) *)
  0x48; 0x89; 0x7b; 0x08   (* MOV (Memop Quadword (%% (rbx,8))) (% rdi) *)
];;

(* Note that the used registers are different between mc and mc2
   (RDI vs. R8,R9). This is fine since the tactics can smartly
   map the registers.
   Also, this reordering is correct only of [RAX, RAX+16) is disjoint with
   [RBX, RBX+16). We will have this as an assumption in the equivalence
   goal. *)
let mc2 = define_assert_from_elf "mc2" "x86/tutorial/rel_reordertac2.o" [
  0x4c; 0x8b; 0x00;        (* MOV (% r8) (Memop Quadword (%% (rax,0))) *)
  0x4c; 0x8b; 0x48; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rax,8))) *)
  0x49; 0x83; 0xc0; 0x01;  (* ADD (% r8) (Imm8 (word 1)) *)
  0x49; 0x83; 0xc1; 0x02;  (* ADD (% r9) (Imm8 (word 2)) *)
  0x4c; 0x89; 0x03;        (* MOV (Memop Quadword (%% (rbx,0))) (% r8) *)
  0x4c; 0x89; 0x4b; 0x08   (* MOV (Memop Quadword (%% (rbx,8))) (% r9) *)
];;

let EXEC = X86_MK_EXEC_RULE mc;;
let EXEC2 = X86_MK_EXEC_RULE mc2;;

(* Define the equality between the input states. *)
let eqin = new_definition
  `forall s1 s1' inbuf outbuf.
    (eqin:(x86state#x86state)->int64->int64->bool) (s1,s1') inbuf outbuf <=>
     (// The values of buffer pointers, RAX and RBX.
      // Their values are symbolically defined as inbuf and outbuf.
      // outbuf is also used for the nonoverlapping precondition between
      // the output buffer and the program bytecode.
      read RAX s1 = inbuf /\
      read RAX s1' = inbuf /\
      read RBX s1 = outbuf /\
      read RBX s1' = outbuf /\
      // The equal buffer contents at the input buffer. '2' stands for 2 words
      // (and 1 word is 8 bytes, hence 2*8=16 bytes)
      (exists n.
        bignum_from_memory (inbuf,2) s1 = n /\
        bignum_from_memory (inbuf,2) s1' = n))`;;

(* Define the equality between the output states. *)
let eqout = new_definition
  `forall s1 s1' inbuf outbuf.
    (eqout:(x86state#x86state)->int64->int64->bool) (s1,s1') inbuf outbuf <=>
     (read RAX s1 = inbuf /\
      read RAX s1' = inbuf /\
      read RBX s1 = outbuf /\
      read RBX s1' = outbuf /\
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
  mc EXEC   (* First program machine code *)
  `MAYCHANGE [RIP; RDI] ,, MAYCHANGE [memory :> bytes (outbuf, 16)] ,,
   MAYCHANGE SOME_FLAGS`
  mc2 EXEC2  (* Second program machine code *)
  `MAYCHANGE [RIP; R8; R9] ,, MAYCHANGE [memory :> bytes (outbuf, 16)] ,,
   MAYCHANGE SOME_FLAGS`;;

(* equiv_goal is:
  `forall pc pc2 inbuf outbuf.
       ALL (nonoverlapping (outbuf,16))
       [word pc,LENGTH mc; word pc2,LENGTH mc2; inbuf,16]
       ==> ensures2 x86
           (\(s,s2).
                bytes_loaded s (word pc) mc /\
                read RIP s = word pc /\
                bytes_loaded s2 (word pc2) mc2 /\
                read RIP s2 = word pc2 /\
                eqin (s,s2) inbuf outbuf)
           (\(s,s2).
                bytes_loaded s (word pc) mc /\
                read RIP s = word (pc + 22) /\
                bytes_loaded s2 (word pc2) mc2 /\
                read RIP s2 = word (pc2 + 22) /\
                eqout (s,s2) inbuf outbuf)
           (\(s,s2) (s',s2').
                (MAYCHANGE [RIP; RDI] ,,
                 MAYCHANGE [memory :> bytes (outbuf,16)] ,,
                 MAYCHANGE SOME_FLAGS)
                s
                s' /\
                (MAYCHANGE [RIP; R8; R9] ,,
                 MAYCHANGE [memory :> bytes (outbuf,16)] ,,
                 MAYCHANGE SOME_FLAGS)
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

  (* Rewrite ALL, nonoverlapping, and LENGTH * *)
  REWRITE_TAC[ALL;NONOVERLAPPING_CLAUSES;SOME_FLAGS; fst EXEC; fst EXEC2] THEN
  REPEAT STRIP_TAC THEN

  (** Initialize **)
  EQUIV_INITIATE_TAC eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Left *)
  X86_N_STEPS_AND_ABBREV_TAC EXEC  (1--(List.length inst_map))
      state_to_abbrevs None THEN

  (* Right *)
  X86_N_STEPS_AND_REWRITE_TAC EXEC2 (1--(List.length inst_map))
      inst_map state_to_abbrevs None THEN

  (* Running the statements above step by step will raise an error
     message saying that the tactic is not VALID. You can temporarily
     disable the message by redefining 'e' as follows:

     let e tac = refine(by(tac));;

     The whole proof ("prove(...)") will still run okay.
  *)

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
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