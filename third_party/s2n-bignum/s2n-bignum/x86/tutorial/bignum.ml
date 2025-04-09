(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  An example that shows how to describe big numbers in a specification.
******************************************************************************)

needs "x86/proofs/base.ml";;

(* Let's prove that the following program

0000000000000000 <bb_false-0x20>:
   0:   48 8b 08                mov    (%rax),%rcx
   3:   48 8b 50 08             mov    0x8(%rax),%rdx
   7:   48 8b 33                mov    (%rbx),%rsi
   a:   48 8b 7b 08             mov    0x8(%rbx),%rdi
   e:   48 39 f1                cmp    %rsi,%rcx
  11:   75 0d                   jne    20 <bb_false>
  13:   48 39 fa                cmp    %rdi,%rdx
  16:   75 08                   jne    20 <bb_false>
  18:   48 c7 c0 01 00 00 00    mov    $0x1,%rax
  1f:   c3                      retq

0000000000000020 <bb_false>:
  20:   48 c7 c0 00 00 00 00    mov    $0x0,%rax
  27:   c3                      retq

  .. returns 1 to rax if a pair of 16-byte integers at buffer rax and rbx
  are equal, 0 otherwise.
  Since this example uses 128 bit integers, we will use 'bignum_from_memory'
  which will state that reading a memory buffer of a specified word number will
  return some large natural number.
*)
let bignum_mc = define_assert_from_elf "bignum_mc" "x86/tutorial/bignum.o" [
  0x48; 0x8b; 0x08;        (* MOV (% rcx) (Memop Quadword (%% (rax,0))) *)
  0x48; 0x8b; 0x50; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rax,8))) *)
  0x48; 0x8b; 0x33;        (* MOV (% rsi) (Memop Quadword (%% (rbx,0))) *)
  0x48; 0x8b; 0x7b; 0x08;  (* MOV (% rdi) (Memop Quadword (%% (rbx,8))) *)
  0x48; 0x39; 0xf1;        (* CMP (% rcx) (% rsi) *)
  0x75; 0x0d;              (* JNE (Imm8 (word 13)) *)
  0x48; 0x39; 0xfa;        (* CMP (% rdx) (% rdi) *)
  0x75; 0x08;              (* JNE (Imm8 (word 8)) *)
  0x48; 0xc7; 0xc0; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 1)) *)
  0xc3;                    (* RET *)
  0x48; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 0)) *)
  0xc3                     (* RET *)
];;

(*
You can get the above OCaml list data structure from
`print_literal_from_elf "<.o file>"` or
`save_literal_from_elf "<out.txt>" "<.o file>"`.
*)

(* X86_MK_EXEC_RULE decodes the byte sequence into conjunction of
  equalities between the bytes and instructions. *)
let EXEC = X86_MK_EXEC_RULE bignum_mc;;

let BIGNUM_SPEC = prove(
  `forall pc loc0 loc1 a b stackpointer returnaddress.
  ensures x86
    // Precondition
    (\s. bytes_loaded s (word pc) bignum_mc /\
         read RIP s = word pc /\
         read RSP s = stackpointer /\
         read (memory :> bytes64 stackpointer) s = returnaddress /\
         read RAX s = word loc0 /\
         read RBX s = word loc1 /\
         // Read 2 words (=128bits) at loc0. It is equivalent to num a.
         // Alternatively, this kind of condition can be written using
         // bignum_of_wordlist which takes a list of 64-bit words.
         bignum_from_memory (word loc0,2) s = a /\
         // Read 2 words (=128bits) at loc1. It is equivalent to num b.
         bignum_from_memory (word loc1,2) s = b
         )
    // Postcondition
    (\s. read RIP s = returnaddress /\
         read RSP s = word_add stackpointer (word 8) /\
         read RAX s = word (if a = b then 1 else 0))
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [RSP;RIP;RAX;RCX;RDX;RDI;RSI] ,, MAYCHANGE SOME_FLAGS)`,

  REPEAT STRIP_TAC THEN
  (* Convert 'bignum_from_memory' into 'memory :> bytes (..)'.
     Also, expand SOME_FLAGS *)
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;SOME_FLAGS] THEN
  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN
  (* Split the memory :> bytes .. into a pair of memory :> bytes64.
     This is necessary to successfully encode the symbolic result of movs. *)
  BIGNUM_DIGITIZE_TAC "a_" `read (memory :> bytes (word loc0,8 * 2)) s0` THEN
  BIGNUM_DIGITIZE_TAC "b_" `read (memory :> bytes (word loc1,8 * 2)) s0` THEN

  (* Symbolically run two ldp instructions *)
  X86_STEPS_TAC EXEC (1--4) THEN
  (* Until first 'bne' *)
  X86_STEPS_TAC EXEC (5--6) THEN

  (* Recognize the if condition and create two subgoals . *)
  FIRST_X_ASSUM MP_TAC THEN
  COND_CASES_TAC THENL [
    (* The low 64 bits of a and b are different. *)
    STRIP_TAC THEN
    X86_STEPS_TAC EXEC (7--8) THEN
    (* Returned; Finalize symbolic execution. *)
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* From `~(val (word_sub a_0 b_0) = 0)` and `val a_0 + 2 EXP 64 * val a_1 = a`,
       and `val b_0 + 2 EXP 64 * val b_1 = b`,
       prove `~(a = b)`. *)
    SUBGOAL_THEN `~(a:num = b)` (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXPAND_TAC ["a";"b"] THEN
    (* VAL_WORD_SUB_EQ_0: |- !x y. val (word_sub x y) = 0 <=> val x = val y) *)
    RULE_ASSUM_TAC (REWRITE_RULE [VAL_WORD_SUB_EQ_0]) THEN
    (* EQ_DIVMOD: |- !p m n. m DIV p = n DIV p /\ m MOD p = n MOD p <=> m = n *)
    ONCE_REWRITE_TAC[SPEC `2 EXP 64` (GSYM EQ_DIVMOD)] THEN
    (* The first '.. DIV .. = .. DIV ..' part is irelevant. *)
    MATCH_MP_TAC (TAUT (`~Q ==> ~(P /\ Q)`)) THEN
    (* Simplfy! *)
    SIMP_TAC[MOD_MULT_ADD;VAL_BOUND_64;ARITH_RULE`~(2 EXP 64 = 0)`] THEN
    ASM_SIMP_TAC[MOD_LT;VAL_BOUND_64];

    ALL_TAC
  ] THEN

  (* The low 64 bits of a and b are equivalent. *)
  (* Until the second 'bne' *)
  STRIP_TAC THEN
  X86_STEPS_TAC EXEC (7--8) THEN

  (* Recognize the if condition and create two subgoals . *)
  FIRST_X_ASSUM MP_TAC THEN
  COND_CASES_TAC THENL [
    (* The high 64 bits of a and b are different. *)
    STRIP_TAC THEN
    X86_STEPS_TAC EXEC (9--10) THEN
    (* Returned; Finalize symbolic execution. *)
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* Proof pattern is similar to the first branch case *)
    SUBGOAL_THEN `~(a:num = b)` (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXPAND_TAC ["a";"b"] THEN
    (* VAL_WORD_SUB_EQ_0: |- !x y. val (word_sub x y) = 0 <=> val x = val y) *)
    RULE_ASSUM_TAC (REWRITE_RULE [VAL_WORD_SUB_EQ_0]) THEN
    (* EQ_DIVMOD: |- !p m n. m DIV p = n DIV p /\ m MOD p = n MOD p <=> m = n *)
    ONCE_REWRITE_TAC[SPEC `2 EXP 64` (GSYM EQ_DIVMOD)] THEN
    (* The second '.. MOD .. = .. MOD ..' part is irelevant. *)
    MATCH_MP_TAC (TAUT (`~P ==> ~(P /\ Q)`)) THEN
    (* Simplfy! *)
    SIMP_TAC[DIV_MULT_ADD;VAL_BOUND_64;ARITH_RULE`~(2 EXP 64 = 0)`] THEN
    ASM_SIMP_TAC[DIV_LT;VAL_BOUND_64;ADD_CLAUSES];

    ALL_TAC
  ] THEN

  (* Both limbs are equivalent! *)
  STRIP_TAC THEN
  X86_STEPS_TAC EXEC (9--10) THEN
  (* Try to prove the postcondition and frame as much as possible *)
  ENSURES_FINAL_STATE_TAC THEN
  (* Use ASM_REWRITE_TAC[] to rewrite the goal using equalities in assumptions. *)
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:num = b)` (fun th -> REWRITE_TAC[th]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [VAL_WORD_SUB_EQ_0]) THEN
  MAP_EVERY EXPAND_TAC ["a";"b"] THEN
  MAP_EVERY UNDISCH_TAC [`val (a_0:int64) = val (b_0:int64)`;`val (a_1:int64) = val (b_1:int64)`] THEN
  ARITH_TAC);;
