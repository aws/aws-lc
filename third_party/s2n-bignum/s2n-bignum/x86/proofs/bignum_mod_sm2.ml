(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo p_sm2, the field characteristic for CC curve SM2.        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/sm2/bignum_mod_sm2.o";;
 ****)

let bignum_mod_sm2_mc =
  define_assert_from_elf "bignum_mod_sm2_mc" "x86/sm2/bignum_mod_sm2.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x48; 0x83; 0xfe; 0x04;  (* CMP (% rsi) (Imm8 (word 4)) *)
  0x0f; 0x82; 0xf9; 0x00; 0x00; 0x00;
                           (* JB (Imm32 (word 249)) *)
  0x48; 0x83; 0xee; 0x04;  (* SUB (% rsi) (Imm8 (word 4)) *)
  0x4c; 0x8b; 0x5c; 0xf2; 0x18;
                           (* MOV (% r11) (Memop Quadword (%%%% (rdx,3,rsi,&24))) *)
  0x4c; 0x8b; 0x54; 0xf2; 0x10;
                           (* MOV (% r10) (Memop Quadword (%%%% (rdx,3,rsi,&16))) *)
  0x4c; 0x8b; 0x4c; 0xf2; 0x08;
                           (* MOV (% r9) (Memop Quadword (%%%% (rdx,3,rsi,&8))) *)
  0x4c; 0x8b; 0x04; 0xf2;  (* MOV (% r8) (Memop Quadword (%%% (rdx,3,rsi))) *)
  0x49; 0x83; 0xe8; 0xff;  (* SUB (% r8) (Imm8 (word 255)) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rbx) (Imm64 (word 18446744069414584320)) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x48; 0xb9; 0xff; 0xff; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584319)) *)
  0x49; 0x83; 0xda; 0xff;  (* SBB (% r10) (Imm8 (word 255)) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0x21; 0xc1;        (* AND (% rcx) (% rax) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x0f; 0x84; 0x8f; 0x00; 0x00; 0x00;
                           (* JE (Imm32 (word 143)) *)
  0x4d; 0x89; 0xd4;        (* MOV (% r12) (% r10) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x4d; 0x01; 0xdc;        (* ADD (% r12) (% r11) *)
  0x4c; 0x11; 0xd9;        (* ADC (% rcx) (% r11) *)
  0x49; 0xc1; 0xec; 0x20;  (* SHR (% r12) (Imm8 (word 32)) *)
  0x4d; 0x01; 0xdc;        (* ADD (% r12) (% r11) *)
  0x49; 0xc1; 0xec; 0x20;  (* SHR (% r12) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x64; 0xf2; 0xf8;
                           (* MOV (% r12) (Memop Quadword (%%%% (rdx,3,rsi,-- &8))) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x48; 0xc1; 0xeb; 0x20;  (* SHR (% rbx) (Imm8 (word 32)) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x48; 0x29; 0xc8;        (* SUB (% rax) (% rcx) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xcb;        (* SUB (% r11) (% rcx) *)
  0x49; 0x01; 0xcc;        (* ADD (% r12) (% rcx) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rbx) (Imm64 (word 18446744069414584320)) *)
  0x4c; 0x21; 0xdb;        (* AND (% rbx) (% r11) *)
  0x48; 0xb9; 0xff; 0xff; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584319)) *)
  0x4c; 0x21; 0xd9;        (* AND (% rcx) (% r11) *)
  0x4d; 0x01; 0xdc;        (* ADD (% r12) (% r11) *)
  0x49; 0x11; 0xd8;        (* ADC (% r8) (% rbx) *)
  0x4d; 0x11; 0xd9;        (* ADC (% r9) (% r11) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x4d; 0x89; 0xca;        (* MOV (% r10) (% r9) *)
  0x4d; 0x89; 0xc1;        (* MOV (% r9) (% r8) *)
  0x4d; 0x89; 0xe0;        (* MOV (% r8) (% r12) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x0f; 0x85; 0x71; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967153)) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3;                    (* RET *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x74; 0xdc;              (* JE (Imm8 (word 220)) *)
  0x4c; 0x8b; 0x02;        (* MOV (% r8) (Memop Quadword (%% (rdx,0))) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x74; 0xd4;              (* JE (Imm8 (word 212)) *)
  0x4c; 0x8b; 0x4a; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rdx,8))) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x74; 0xcb;              (* JE (Imm8 (word 203)) *)
  0x4c; 0x8b; 0x52; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rdx,16))) *)
  0xeb; 0xc5               (* JMP (Imm8 (word 197)) *)
];;

let bignum_mod_sm2_tmc = define_trimmed "bignum_mod_sm2_tmc" bignum_mod_sm2_mc;;

let BIGNUM_MOD_SM2_EXEC = X86_MK_EXEC_RULE bignum_mod_sm2_tmc;;

(* ------------------------------------------------------------------------- *)
(* Common tactic for slightly different standard and Windows variants.       *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let sm2longredlemma = prove
 (`!n. n < 2 EXP 64 * p_sm2
       ==> let q = MIN
                   ((n DIV 2 EXP 192 + (1 + 2 EXP 32) *
                     n DIV 2 EXP 256 + 2 EXP 64) DIV (2 EXP 64))
                   (2 EXP 64 - 1) in
          q < 2 EXP 64 /\
          q * p_sm2 <= n + p_sm2 /\
          n < q * p_sm2 + p_sm2`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC);;

let tac execth offset =
  X_GEN_TAC `z:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Case split over the k < 4 case, which is a different path ***)

  ASM_CASES_TAC `k < 4` THENL
   [SUBGOAL_THEN `n MOD p_sm2 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP (64 * 3)` THEN
      ASM_REWRITE_TAC[LE_EXP; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
   BIGNUM_DIGITIZE_TAC "n_" `read(memory :> bytes(x,8 * 4)) s0` THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `k < 4 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`)) THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
   EXPAND_TAC "n" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
   ASM_REWRITE_TAC[] THENL
    [X86_STEPS_TAC execth (1--12);
     X86_STEPS_TAC execth (1--15);
     X86_STEPS_TAC execth (1--18);
     X86_STEPS_TAC execth (1--20)] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
   ARITH_TAC;
   FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN

  (*** Initial 4-digit modulus ***)

  ENSURES_SEQUENCE_TAC (offset 0x5b)
   `\s. bignum_from_memory(x,k) s = n /\
        read RDI s = z /\
        read RDX s = x /\
        read RSI s = word(k - 4) /\
        bignum_of_wordlist[read R8 s; read R9 s; read R10 s; read R11 s] =
        (highdigits n (k - 4)) MOD p_sm2` THEN
  CONJ_TAC THENL
   [ABBREV_TAC `j = k - 4` THEN VAL_INT64_TAC `j:num` THEN
    SUBGOAL_THEN `word_sub (word k) (word 4):int64 = word j` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `k - 4 = j`)) THEN
      REWRITE_TAC[WORD_SUB] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[highdigits] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_DIV] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    SUBST1_TAC(SYM(ASSUME `k - 4 = j`)) THEN
    ASM_SIMP_TAC[ARITH_RULE `4 <= k ==> k - (k - 4) = 4`] THEN
    ABBREV_TAC `m = bignum_from_memory(word_add x (word (8 * j)),4) s0` THEN
    SUBGOAL_THEN `m < 2 EXP (64 * 4)` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV)) THEN
    BIGNUM_DIGITIZE_TAC "m_"
     `read (memory :> bytes (word_add x (word(8 * j)),8 * 4)) s0` THEN
    X86_ACCSTEPS_TAC execth [8;10;12;13] (1--13) THEN
    SUBGOAL_THEN `carry_s13 <=> m < p_sm2` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_BITVAL_NOT] THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    X86_ACCSTEPS_TAC execth (17--20) (14--20) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`64 * 4`; `if m < p_sm2 then &m:real else &(m - p_sm2)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      ALL_TAC;
      REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MOD_CASES THEN UNDISCH_TAC `m < 2 EXP (64 * 4)` THEN
      REWRITE_TAC[p_sm2] THEN ARITH_TAC] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    EXPAND_TAC "m" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Finish off the k = 4 case which is now just the writeback ***)

  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o MATCH_MP (ARITH_RULE
   `4 <= k ==> k = 4 \/ 4 < k`))
  THENL
   [GHOST_INTRO_TAC `d0:int64` `read R8` THEN
    GHOST_INTRO_TAC `d1:int64` `read R9` THEN
    GHOST_INTRO_TAC `d2:int64` `read R10` THEN
    GHOST_INTRO_TAC `d3:int64` `read R11` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `0 < k - 4 /\ ~(k - 4 = 0)` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Setup of loop invariant ***)

  ENSURES_WHILE_PDOWN_TAC `k - 4` (offset 0x64) (offset 0xed)
   `\i s. (bignum_from_memory(x,k) s = n /\
           read RDI s = z /\
           read RDX s = x /\
           read RSI s = word i /\
           bignum_of_wordlist[read R8 s; read R9 s; read R10 s; read R11 s] =
           (highdigits n i) MOD p_sm2) /\
          (read ZF s <=> i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [VAL_INT64_TAC `k - 4` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `d0:int64` `read R8` THEN
    GHOST_INTRO_TAC `d1:int64` `read R9` THEN
    GHOST_INTRO_TAC `d2:int64` `read R10` THEN
    GHOST_INTRO_TAC `d3:int64` `read R11` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN

  (*** Mathematics of main loop with decomposition and quotient estimate ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `m1:int64` `read R8` THEN
  GHOST_INTRO_TAC `m2:int64` `read R9` THEN
  GHOST_INTRO_TAC `m3:int64` `read R10` THEN
  GHOST_INTRO_TAC `m4:int64` `read R11` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m0:int64 = word(bigdigit n i)` THEN
  ABBREV_TAC `m = bignum_of_wordlist[m0; m1; m2; m3; m4]` THEN
  SUBGOAL_THEN `m < 2 EXP 64 * p_sm2` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MP_TAC(SPEC `m0:int64` VAL_BOUND_64) THEN
    ASM_REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `highdigits n i MOD p_sm2 = m MOD p_sm2` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
    EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    EXPAND_TAC "m0" THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` sm2longredlemma) THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN STRIP_TAC THEN

  (*** The computation of the quotient estimate q ***)

  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_ACCSTEPS_TAC execth [3;4;6;8] (1--8) THEN
  SUBGOAL_THEN
   `2 EXP 64 * bitval(read CF s8) + val(read RCX s8) =
    (m DIV 2 EXP 192 + (1 + 2 EXP 32) * m DIV 2 EXP 256 + 2 EXP 64)
    DIV 2 EXP 64`
  MP_TAC THENL
   [EXPAND_TAC "m" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `m < 2 EXP 64 * p_sm2 ==> m DIV 2 EXP 256 <= p_sm2 DIV 2 EXP 192`)) THEN
    EXPAND_TAC "m" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_sm2] THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
    ACCUMULATOR_ASSUM_LIST(fun ths -> ASSUM_LIST (fun thc ->
      MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE thc ths)))) THEN
    REWRITE_TAC[VAL_WORD_USHR; REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  X86_STEPS_TAC execth [9] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word q:int64` o MATCH_MP (MESON[]
   `!q. read RCX s = q' ==> q' = q ==> read RCX s = q`)) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `2 EXP 64 * bitval carry_s8 + val(sum_s8:int64) <= 2 EXP 64`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `m < 2 EXP 64 * p_sm2` THEN
      REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "q" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (funpow 3 RAND_CONV o LAND_CONV) [SYM th]) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    BOOL_CASES_TAC `carry_s8:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    SIMP_TAC[VAL_BOUND_64; WORD_VAL; WORD_SUB_0; ARITH_RULE
     `n < 2 EXP 64 ==> MIN n (2 EXP 64 - 1) = n`] THEN
    SIMP_TAC[ARITH_RULE `a + b <= a <=> b = 0`; VAL_EQ_0] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    DISCH_TAC THEN VAL_INT64_TAC `q:num`] THEN

  (*** The next digit in the current state ***)

  VAL_INT64_TAC `i + 1` THEN
  ASSUME_TAC(SPEC `i:num` WORD_INDEX_WRAP) THEN
  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `x:int64`; `s9:x86state`; `i:num`]
        BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word:num->int64` o SYM) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN DISCH_TAC THEN

  (*** A bit of fiddle to make the accumulation tactics work ***)

  ABBREV_TAC `w:int64 = word q` THEN
  UNDISCH_THEN `val(w:int64) = q` (SUBST_ALL_TAC o SYM) THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC o end_itlist CONJ) THEN

  (*** Basic subtraction to get low part and top mask ***)

  X86_ACCSTEPS_TAC execth (10--24) (10--24) THEN
  MP_TAC(ISPECL
   [`sum_s24:int64`;
    `&(bignum_of_wordlist[sum_s20; sum_s21; sum_s22; sum_s23]):real`;
    `256`; `m:num`; `val(w:int64) * p_sm2`] MASK_AND_VALUE_FROM_CARRY_LT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(w:int64) * p_sm2 <= m + p_sm2`;
        `m < val(w:int64) * p_sm2 + p_sm2`] THEN
      REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV)] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REPEAT(MATCH_MP_TAC INTEGER_ADD THEN CONJ_TAC) THEN
    TRY REAL_INTEGER_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC] THEN

  (*** Final correction ***)

  X86_ACCSTEPS_TAC execth (29--32) (25--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(w:int64)`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b <=> m < val(w:int64) * p_sm2` THEN
  REWRITE_TAC[REAL_ARITH
   `m - s - (w - b) * n:real = (m - w * n) + (b * n - s)`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[REAL_ADD_RID]
   `x = (if p then y + z else y) ==> x = y + (if p then z else &0)`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `x:real = y + z <=> y = x - z`] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness of standard ABI version.                                      *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MOD_SM2_CORRECT = time prove
 (`!z k x n pc.
      nonoverlapping (word pc,0x12e) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_sm2_tmc /\
                read RIP s = word(pc + 0x3) /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = word (pc + 0x102) /\
                bignum_from_memory (z,4) s = n MOD p_sm2)
          (MAYCHANGE [RIP; RSI; RAX; RDX; RCX; RBX; R8; R9; R10; R11; R12] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  tac BIGNUM_MOD_SM2_EXEC (curry mk_comb `(+) (pc:num)` o mk_small_numeral));;

let BIGNUM_MOD_SM2_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 16),24) (z,32) /\
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,LENGTH bignum_mod_sm2_tmc); (x, 8 * val k)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_sm2_tmc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_sm2_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD p_sm2)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                 memory :> bytes(word_sub stackpointer (word 16),16)])`,
  X86_ADD_RETURN_STACK_TAC BIGNUM_MOD_SM2_EXEC BIGNUM_MOD_SM2_CORRECT
   `[RBX; R12]` 16);;

let BIGNUM_MOD_SM2_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 16),24) (z,32) /\
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,LENGTH bignum_mod_sm2_mc); (x, 8 * val k)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_sm2_mc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_sm2_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD p_sm2)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                 memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_SM2_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mod_sm2_windows_mc = define_from_elf
   "bignum_mod_sm2_windows_mc" "x86/sm2/bignum_mod_sm2.obj";;

let bignum_mod_sm2_windows_tmc = define_trimmed "bignum_mod_sm2_windows_tmc" bignum_mod_sm2_windows_mc;;

let BIGNUM_MOD_SM2_WINDOWS_CORRECT = time prove
 (`!z k x n pc.
      nonoverlapping (word pc,0x13b) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_sm2_windows_tmc /\
                read RIP s = word(pc + 0xe) /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = word (pc + 0x10d) /\
                bignum_from_memory (z,4) s = n MOD p_sm2)
          (MAYCHANGE [RIP; RSI; RAX; RDX; RCX; RBX; R8; R9; R10; R11; R12] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  tac (X86_MK_EXEC_RULE bignum_mod_sm2_windows_tmc)
      (curry mk_comb `(+) (pc:num)` o mk_small_numeral o (fun n -> n+11)));;

let BIGNUM_MOD_SM2_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 32),40) (z,32) /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),32))
          [(word pc,LENGTH bignum_mod_sm2_windows_tmc); (x, 8 * val k)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_sm2_windows_tmc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_sm2_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD p_sm2)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                 memory :> bytes(word_sub stackpointer (word 32),32)])`,
  GEN_X86_ADD_RETURN_STACK_TAC (X86_MK_EXEC_RULE bignum_mod_sm2_windows_tmc)
    BIGNUM_MOD_SM2_WINDOWS_CORRECT
    `[RDI; RSI; RBX; R12]` 32 (7,5));;

let BIGNUM_MOD_SM2_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 32),40) (z,32) /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),32))
          [(word pc,LENGTH bignum_mod_sm2_windows_mc); (x, 8 * val k)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_sm2_windows_mc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_sm2_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD p_sm2)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                 memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_SM2_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

