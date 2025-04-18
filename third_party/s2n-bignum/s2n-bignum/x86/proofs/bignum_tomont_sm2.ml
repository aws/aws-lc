(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 4-word (256-bit) bignum to Montgomery form modulo p_sm2.  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/sm2/bignum_tomont_sm2.o";;
 ****)

let bignum_tomont_sm2_mc =
  define_assert_from_elf "bignum_tomont_sm2_mc" "x86/sm2/bignum_tomont_sm2.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x83; 0xe8; 0xff;  (* SUB (% r8) (Imm8 (word 255)) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584320)) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x48; 0xba; 0xff; 0xff; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584319)) *)
  0x49; 0x83; 0xda; 0xff;  (* SBB (% r10) (Imm8 (word 255)) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x21; 0xc1;        (* AND (% rcx) (% rax) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xd9;        (* ADD (% rcx) (% r11) *)
  0x4c; 0x11; 0xd8;        (* ADC (% rax) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd9;        (* ADD (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0xc1; 0xe1; 0x20;  (* SHL (% rcx) (Imm8 (word 32)) *)
  0x48; 0xc1; 0xea; 0x20;  (* SHR (% rdx) (Imm8 (word 32)) *)
  0x49; 0x01; 0xca;        (* ADD (% r10) (% rcx) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x29; 0xc1;        (* SUB (% rcx) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584320)) *)
  0x4c; 0x21; 0xd9;        (* AND (% rcx) (% r11) *)
  0x48; 0xba; 0xff; 0xff; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584319)) *)
  0x4c; 0x21; 0xda;        (* AND (% rdx) (% r11) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x4d; 0x11; 0xd9;        (* ADC (% r9) (% r11) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xd1;        (* ADD (% rcx) (% r10) *)
  0x4c; 0x11; 0xd0;        (* ADC (% rax) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xd1;        (* ADD (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0xc1; 0xe1; 0x20;  (* SHL (% rcx) (Imm8 (word 32)) *)
  0x48; 0xc1; 0xea; 0x20;  (* SHR (% rdx) (Imm8 (word 32)) *)
  0x49; 0x01; 0xc9;        (* ADD (% r9) (% rcx) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x29; 0xc1;        (* SUB (% rcx) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x01; 0xcb;        (* ADD (% r11) (% rcx) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584320)) *)
  0x4c; 0x21; 0xd1;        (* AND (% rcx) (% r10) *)
  0x48; 0xba; 0xff; 0xff; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584319)) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4d; 0x11; 0xd0;        (* ADC (% r8) (% r10) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x89; 0xc2;        (* MOV (% r10) (% rax) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xc9;        (* ADD (% rcx) (% r9) *)
  0x4c; 0x11; 0xc8;        (* ADC (% rax) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc9;        (* ADD (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0xc1; 0xe1; 0x20;  (* SHL (% rcx) (Imm8 (word 32)) *)
  0x48; 0xc1; 0xea; 0x20;  (* SHR (% rdx) (Imm8 (word 32)) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x29; 0xc1;        (* SUB (% rcx) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x01; 0xca;        (* ADD (% r10) (% rcx) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584320)) *)
  0x4c; 0x21; 0xc9;        (* AND (% rcx) (% r9) *)
  0x48; 0xba; 0xff; 0xff; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584319)) *)
  0x4c; 0x21; 0xca;        (* AND (% rdx) (% r9) *)
  0x4c; 0x01; 0xc8;        (* ADD (% rax) (% r9) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x4d; 0x11; 0xcb;        (* ADC (% r11) (% r9) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xc1;        (* ADD (% rcx) (% r8) *)
  0x4c; 0x11; 0xc0;        (* ADC (% rax) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x4c; 0x01; 0xc1;        (* ADD (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0xc1; 0xe1; 0x20;  (* SHL (% rcx) (Imm8 (word 32)) *)
  0x48; 0xc1; 0xea; 0x20;  (* SHR (% rdx) (Imm8 (word 32)) *)
  0x49; 0x01; 0xcb;        (* ADD (% r11) (% rcx) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x48; 0x29; 0xc1;        (* SUB (% rcx) (% rax) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x01; 0xc9;        (* ADD (% r9) (% rcx) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584320)) *)
  0x4c; 0x21; 0xc1;        (* AND (% rcx) (% r8) *)
  0x48; 0xba; 0xff; 0xff; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584319)) *)
  0x4c; 0x21; 0xc2;        (* AND (% rdx) (% r8) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x4d; 0x11; 0xc2;        (* ADC (% r10) (% r8) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_tomont_sm2_tmc = define_trimmed "bignum_tomont_sm2_tmc" bignum_tomont_sm2_mc;;

let BIGNUM_TOMONT_SM2_EXEC = X86_MK_CORE_EXEC_RULE bignum_tomont_sm2_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
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

let BIGNUM_TOMONT_SM2_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x227) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_tomont_sm2_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0x226) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_sm2)
             (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10; R11] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initial reduction of the input mod p_sm2 ***)

  BIGNUM_TERMRANGE_TAC `4` `a:num` THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  X86_ACCSTEPS_TAC BIGNUM_TOMONT_SM2_EXEC [5;7;9;10] (1--10) THEN
  SUBGOAL_THEN `carry_s10 <=> a < p_sm2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC BIGNUM_TOMONT_SM2_EXEC (14--17) (11--17) THEN
  ABBREV_TAC `a1 = bignum_of_wordlist
   [read R8 s17; read R9 s17; read R10 s17; read R11 s17]` THEN
  SUBGOAL_THEN `a1 = a MOD p_sm2` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`64 * 4`; `if a < p_sm2 then &a:real else &(a - p_sm2)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      ALL_TAC;
      REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MOD_CASES THEN UNDISCH_TAC `a < 2 EXP (64 * 4)` THEN
      REWRITE_TAC[p_sm2] THEN ARITH_TAC] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    POP_ASSUM MP_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`read RDI s17 = z`; `read RIP s17 = word (pc + 70)`] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read Xnn s = y`] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num` o concl))) THEN
    DISCH_TAC THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(2 EXP 256 * a) MOD p_sm2 = (2 EXP 256 * a MOD p_sm2) MOD p_sm2`
  SUBST1_TAC THENL [CONV_TAC MOD_DOWN_CONV THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a MOD p_sm2 < p_sm2` MP_TAC THENL
   [REWRITE_TAC[p_sm2] THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`a MOD p_sm2`,`a:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`x_0 = read R8 s17`; `x_1 = read R9 s17`; `x_2 = read R10 s17`;
    `x_3 = read R11 s17`] THEN
  DISCH_TAC THEN

  (*** Break down the goal into 4 steps at the outset ***)

  SUBGOAL_THEN
   `(2 EXP 256 * a) MOD p_sm2 =
    (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * (2 EXP 64 * a)
     MOD p_sm2) MOD p_sm2) MOD p_sm2) MOD p_sm2`
  SUBST1_TAC THENL
   [CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Main 4-fold iteration of the same tactic ***)

  REPLICATE_TAC 4
 (
  SUBGOAL_THEN `2 EXP 64 * a < 2 EXP 64 * p_sm2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  ABBREV_TAC `m = 2 EXP 64 * a` THEN

  (*** The computation of the quotient estimate q ***)

  MP_TAC(SPEC `m:num` sm2longredlemma) THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN STRIP_TAC THEN
  X86_ACCSTEPS_TAC BIGNUM_TOMONT_SM2_EXEC [20;21;23;25] (18--25) THEN
  SUBGOAL_THEN
   `2 EXP 64 * bitval carry_s25 + val(sum_s25:int64) =
    (m DIV 2 EXP 192 + (1 + 2 EXP 32) * m DIV 2 EXP 256 + 2 EXP 64)
    DIV 2 EXP 64`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m";"a"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_ZAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `m < 2 EXP 64 * p_sm2 ==> m DIV 2 EXP 256 <= p_sm2 DIV 2 EXP 192`)) THEN
    MAP_EVERY EXPAND_TAC ["m";"a"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_ZAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_sm2] THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
    ACCUMULATOR_ASSUM_LIST(fun ths -> ASSUM_LIST (fun thc ->
      MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE thc ths)))) THEN
    REWRITE_TAC[VAL_WORD_USHR; REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  X86_STEPS_TAC BIGNUM_TOMONT_SM2_EXEC [26] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word q:int64` o MATCH_MP (MESON[]
   `!q. read RAX s = q' ==> q' = q ==> read RAX s = q`)) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `2 EXP 64 * bitval carry_s25 + val(sum_s25:int64) <= 2 EXP 64`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `m < 2 EXP 64 * p_sm2` THEN
      REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "q" THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (funpow 3 RAND_CONV o LAND_CONV) [SYM th]) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    BOOL_CASES_TAC `carry_s25:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    SIMP_TAC[VAL_BOUND_64; WORD_VAL; WORD_SUB_0; ARITH_RULE
     `n < 2 EXP 64 ==> MIN n (2 EXP 64 - 1) = n`] THEN
    SIMP_TAC[ARITH_RULE `a + b <= a <=> b = 0`; VAL_EQ_0] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    DISCH_TAC THEN VAL_INT64_TAC `q:num`] THEN

  (*** A bit of fiddle to make the accumulation tactics work ***)

  ABBREV_TAC `w:int64 = word q` THEN
  UNDISCH_THEN `val(w:int64) = q` (SUBST_ALL_TAC o SYM) THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC o end_itlist CONJ) THEN

  (*** Main subtraction of q * p_sm2 ***)

  X86_ACCSTEPS_TAC BIGNUM_TOMONT_SM2_EXEC (27--39) (27--39) THEN
  MP_TAC(ISPECL
   [`sum_s39:int64`;
    `&(bignum_of_wordlist[w; sum_s36; sum_s37; sum_s38]):real`;
    `256`; `m:num`; `val(w:int64) * p_sm2`] MASK_AND_VALUE_FROM_CARRY_LT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(w:int64) * p_sm2 <= m + p_sm2`;
        `m < val(w:int64) * p_sm2 + p_sm2`] THEN
      REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV)] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["m"; "a"] THEN
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

  X86_ACCSTEPS_TAC BIGNUM_TOMONT_SM2_EXEC (44--47) (40--47) THEN
  ABBREV_TAC `m' = bignum_of_wordlist[sum_s44; sum_s45; sum_s46; sum_s47]` THEN
  SUBGOAL_THEN `m MOD p_sm2 < p_sm2` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; p_sm2; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `m MOD p_sm2 = m'` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
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
    MAP_EVERY EXPAND_TAC ["m"; "m'"; "a"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Absorb one more move (register shuffle or first writeback ***)

  X86_STEPS_TAC BIGNUM_TOMONT_SM2_EXEC [48] THEN

  (*** Reset all the variables to match the initial expectations ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `w:int64`) o concl)) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue w) s = y`] THEN

  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`s48:x86state`,`s17:x86state`) THEN
  SPEC_TAC(`sum_s44:int64`,`x_0:int64`) THEN
  SPEC_TAC(`sum_s45:int64`,`x_1:int64`) THEN
  SPEC_TAC(`sum_s46:int64`,`x_2:int64`) THEN
  SPEC_TAC(`sum_s47:int64`,`x_3:int64`) THEN
  SPEC_TAC(`m':num`,`a:num`) THEN REPEAT STRIP_TAC) THEN

  (*** Final writeback is all that is left ***)

  X86_STEPS_TAC BIGNUM_TOMONT_SM2_EXEC (49--51) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[]);;

let BIGNUM_TOMONT_SM2_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_tomont_sm2_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_sm2_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_sm2)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC
    bignum_tomont_sm2_tmc BIGNUM_TOMONT_SM2_CORRECT);;

let BIGNUM_TOMONT_SM2_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_tomont_sm2_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_sm2_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_sm2)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOMONT_SM2_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_tomont_sm2_windows_mc = define_from_elf
   "bignum_tomont_sm2_windows_mc" "x86/sm2/bignum_tomont_sm2.obj";;

let bignum_tomont_sm2_windows_tmc = define_trimmed "bignum_tomont_sm2_windows_tmc" bignum_tomont_sm2_windows_mc;;

let BIGNUM_TOMONT_SM2_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_tomont_sm2_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_sm2_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_sm2_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_sm2)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_tomont_sm2_windows_tmc
    bignum_tomont_sm2_tmc BIGNUM_TOMONT_SM2_CORRECT);;

let BIGNUM_TOMONT_SM2_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_tomont_sm2_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_sm2_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_sm2_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_sm2)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOMONT_SM2_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

