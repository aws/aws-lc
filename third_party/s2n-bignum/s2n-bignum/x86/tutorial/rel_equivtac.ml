(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
        An example that proves equivalence of two straight-line codes
                  accessing memory using EQUIV_STEPS_TAC.
******************************************************************************)

(* Please copy this file to the root directory of
   s2n-bignum, then follow the instructions. *)

needs "x86/proofs/equiv.ml";;

(* This example will define & prove the equivalence of two programs
   using EQUIV_STEPS_TAC.
   This tactic is useful if two programs are supposed to have many
   equivalent parts. EQUIV_STEPS_TAC receives 'actions', which is an
   OCaml list stating which lines are equivalent and which lines are diverging.
   This 'actions' can be generated from, say, syntactic diff of
   two assembly programs. s2n-bignum also has tools/gen-actions.py
   which runs the `diff` linux tool on two assembly files. *)

let mc = define_assert_from_elf "mc" "x86/tutorial/rel_equivtac.o" [
  0x48; 0x8b; 0x38;        (* MOV (% rdi) (Memop Quadword (%% (rax,0))) *)
  0x48; 0x8b; 0x70; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rax,8))) *)
  0x48; 0x83; 0xc7; 0x01;  (* ADD (% rdi) (Imm8 (word 1)) *)
  0x48; 0x0f; 0xaf; 0xf7;  (* IMUL (% rsi) (% rdi) *)
  0x48; 0x89; 0x33         (* MOV (Memop Quadword (%% (rbx,0))) (% rsi) *)
];;

(* Note that the used registers are different between mc and mc2
   (rsi,rdi vs. r8,r9). This is fine since EQUIV_STEPS_TAC
   can smartly map differently used registers. *)
let mc2 = define_assert_from_elf "mc2" "x86/tutorial/rel_equivtac2.o" [
  0x4c; 0x8b; 0x00;        (* MOV (% r8) (Memop Quadword (%% (rax,0))) *)
  0x4c; 0x8b; 0x48; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rax,8))) *)
  0x4d; 0x0f; 0xaf; 0xc1;  (* IMUL (% r8) (% r9) *)
  0x4d; 0x01; 0xc8;        (* ADD (% r8) (% r9) *)
  0x4c; 0x89; 0x03         (* MOV (Memop Quadword (%% (rbx,0))) (% r8) *)
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
  `forall s1 s1' outbuf.
    (eqout:(x86state#x86state)->int64->bool) (s1,s1') outbuf <=>
     (read RBX s1 = outbuf /\
      read RBX s1' = outbuf /\
      (exists n.
        bignum_from_memory (outbuf,1) s1 = n /\
        bignum_from_memory (outbuf,1) s1' = n))`;;

(* Now, build the program equivalence statement using
   'mk_equiv_statement_simple'.
   Its first argument states the assumption that will appear at
   LHS of '<assumption> ==> ensures2 ..(equiv statement)..'.

   If it fails, please try `x86_print_log := true`. *)
let equiv_goal = mk_equiv_statement_simple
  `ALL (nonoverlapping (outbuf,8)) [
    (word pc:int64, LENGTH mc);
    (word pc2:int64, LENGTH mc2)
  ]`
  eqin  (* Input state equivalence *)
  eqout (* Output state equivalence *)
  mc EXEC  (* First program machine code *)
  `MAYCHANGE [RIP; RSI; RDI] ,, MAYCHANGE [memory :> bytes (outbuf, 8)] ,,
   MAYCHANGE SOME_FLAGS`
  mc2 EXEC2 (* Second program machine code *)
  `MAYCHANGE [RIP; R8; R9] ,, MAYCHANGE [memory :> bytes (outbuf, 8)] ,,
   MAYCHANGE SOME_FLAGS`;;

(* equiv_goal is:
  `forall pc pc2 inbuf outbuf.
       ALL (nonoverlapping (outbuf,8))
       [word pc,LENGTH mc; word pc2,LENGTH mc2]
       ==> ensures2 x86
           (\(s,s2).
                bytes_loaded s (word pc) mc /\
                read RIP s = word pc /\
                bytes_loaded s2 (word pc2) mc2 /\
                read RIP s2 = word pc2 /\
                eqin (s,s2) inbuf outbuf)
           (\(s,s2).
                bytes_loaded s (word pc) mc /\
                read RIP s = word (pc + 18) /\
                bytes_loaded s2 (word pc2) mc2 /\
                read RIP s2 = word (pc2 + 17) /\
                eqout (s,s2) outbuf)
           (\(s,s2) (s',s2').
                (MAYCHANGE [RIP; RSI; RDI] ,,
                 MAYCHANGE [memory :> bytes (outbuf,8)])
                s
                s' /\
                (MAYCHANGE [RIP; R8; R9] ,,
                 MAYCHANGE [memory :> bytes (outbuf,8)])
                s2
                s2')
           (\s. 5)
           (\s. 5)`
*)

(* Now, let's prove the program equivalence. *)
let EQUIV = prove(equiv_goal,

  (* Rewrite SOME_FLAGS, ALL, nonoverlapping, and LENGTH * *)
  REWRITE_TAC[SOME_FLAGS; ALL;NONOVERLAPPING_CLAUSES;
              fst EXEC; fst EXEC2] THEN
  REPEAT STRIP_TAC THEN

  (** Initialize **)
  EQUIV_INITIATE_TAC eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Do symbolic simulations on the two programs using EQUIV_STEPS_TAC.
     As explained before, the action is an OCaml list.
     Each item describes:
     - ("equal",begin line number of program 1 (start from 0),
                end line number of program 1 (not inclusive),
                begin line number of program 2,
                end line number of program 2)
       : means that these instructions in program 1 and program 2 must
         yield sysmbolically equivalent output. Therefore, EQUIV_STEPS_TAC
         uses a lock-step simulation for these.
         If the symbolic outputs of the matching instructions are not having
         equal expression, it will print an error message.
         Actually, it tries to solve a simple bit-vector equality such as
           'x * (y + 1) = x * y + x',
         and can succeed. This is exactly the example case here.
     - ("replace",beign line number of program 1,
                  end line number of program 1 (not inclusive),
                  begin line number of program 2,
                  end line number of program 2)
       : means that these instructions in program 1 and 2 differ.
         EQUIV_STEPS_TAC uses stuttering simulations for each program.
  *)
  EQUIV_STEPS_TAC [
    ("equal",0,2,0,2);
    ("replace",2,4,2,4);
    ("equal",4,5,4,5)
  ] EXEC EXEC2 THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  (* This tactic below is typically fixed and probably you will want to reuse. :) *)
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[eqout;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (outbuf,1) s`] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

(*
    If the EQUIV_STEPS_TAC fails to prove that instructions that are supposed
    to be equivalent according to actions are yielding equal output expressions,
    it will print a message like this:

    X86_LOCKSTEP_TAC (4,4)
    Running left...
    Running right...
    1 basis elements and 0 critical pairs
            - Error: WORD_RULE could not prove
              `<word expression (program 2)> = <word expression (program 1)>`

    If you are certain that these expressions must be equal, you can improve
    `extra_word_CONV` of symbolic simulator by adding a custom word equation
    to extra_word_CONV.

    ```
    let org_convs = !extra_word_CONV;;
    extra_word_CONV := (GEN_REWRITE_CONV I [<your_word_thm>])::org_convs;;
    ```
*)