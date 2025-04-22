(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery multiplication modulo p_sm2 using using traditional x86 muls.  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/sm2/bignum_montmul_sm2_alt.o";;
 ****)

let bignum_montmul_sm2_alt_mc =
  define_assert_from_elf "bignum_montmul_sm2_alt_mc" "x86/sm2/bignum_montmul_sm2_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4d; 0x11; 0xe4;        (* ADC (% r12) (% r12) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4d; 0x11; 0xed;        (* ADC (% r13) (% r13) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x21;        (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x49; 0x83; 0xd5; 0x00;  (* ADC (% r13) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xf6;        (* ADC (% r14) (% r14) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x08;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x10;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,16))) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xf7; 0x61; 0x18;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,24))) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc1;        (* MOV (% rcx) (% r8) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc0;        (* SUB (% rax) (% r8) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x49; 0x19; 0xd8;        (* SBB (% r8) (% rbx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xc9;        (* MOV (% rcx) (% r9) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xc8;        (* SUB (% rax) (% r9) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x49; 0x19; 0xcb;        (* SBB (% r11) (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x4c; 0x89; 0xd0;        (* MOV (% rax) (% r10) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd1;        (* MOV (% rcx) (% r10) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x19; 0xc8;        (* SBB (% r8) (% rcx) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x4c; 0x29; 0xd8;        (* SUB (% rax) (% r11) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x11; 0xc0;        (* ADC (% rax) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x01; 0xe1;        (* ADD (% rcx) (% r12) *)
  0x4c; 0x8d; 0x5a; 0x01;  (* LEA (% r11) (%% (rdx,1)) *)
  0x4c; 0x11; 0xea;        (* ADC (% rdx) (% r13) *)
  0x4c; 0x8d; 0x43; 0xff;  (* LEA (% r8) (%% (rbx,18446744073709551615)) *)
  0x4c; 0x11; 0xf3;        (* ADC (% rbx) (% r14) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x49; 0x11; 0xc0;        (* ADC (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xe1;  (* CMOVB (% r12) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xea;  (* CMOVB (% r13) (% rdx) *)
  0x4c; 0x0f; 0x42; 0xf3;  (* CMOVB (% r14) (% rbx) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4c; 0x89; 0x77; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r15) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_montmul_sm2_alt_tmc = define_trimmed "bignum_montmul_sm2_alt_tmc" bignum_montmul_sm2_alt_mc;;

let BIGNUM_MONTMUL_SM2_ALT_EXEC = X86_MK_CORE_EXEC_RULE bignum_montmul_sm2_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let BIGNUM_MONTMUL_SM2_ALT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,0x21e) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_montmul_sm2_alt_tmc) /\
                  read RIP s = word(pc + 0x09) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = word (pc + 0x214) /\
                  (a * b <= 2 EXP 256 * p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a * b) MOD p_sm2))
             (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 256 * p_sm2  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 256 * p_sm2` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_MONTMUL_SM2_ALT_EXEC (1--156)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,4) s0` THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  MAP_EVERY (fun n ->
    X86_STEPS_TAC BIGNUM_MONTMUL_SM2_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n)))
   (1--137) THEN
  X86_STEPS_TAC BIGNUM_MONTMUL_SM2_ALT_EXEC [138] THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s134; sum_s135; sum_s136; sum_s137; word(bitval carry_s137)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_sm2 /\ (2 EXP 256 * t == a * b) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC BIGNUM_MONTMUL_SM2_ALT_EXEC
   [142;144;146;147;148] (139--156) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_sm2` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_sm2 then &t:real else &t - &p_sm2`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    REWRITE_TAC[p_sm2] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN `carry_s148 <=> p_sm2 <= t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTMUL_SM2_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_montmul_sm2_alt_tmc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montmul_sm2_alt_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montmul_sm2_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a * b <= 2 EXP 256 * p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a * b) MOD p_sm2))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 40),40)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_montmul_sm2_alt_tmc BIGNUM_MONTMUL_SM2_ALT_CORRECT
   `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_MONTMUL_SM2_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_montmul_sm2_alt_mc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montmul_sm2_alt_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montmul_sm2_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a * b <= 2 EXP 256 * p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a * b) MOD p_sm2))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 40),40)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTMUL_SM2_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 256 bits, may then not be fully reduced mod p_sm2.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTMUL_SM2_ALT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,0x21e) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_montmul_sm2_alt_tmc) /\
                  read RIP s = word(pc + 0x09) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = word (pc + 0x214) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_sm2 (2 EXP 256) * a * b) (mod p_sm2))
             (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,4) s0` THEN

  (*** Simulate the core pre-reduced result accumulation ***)

  MAP_EVERY (fun n ->
    X86_STEPS_TAC BIGNUM_MONTMUL_SM2_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_sub x (word_neg y):int64 = word_add x y`]) THEN
    TRY(ACCUMULATE_ARITH_TAC("s"^string_of_int n)))
   (1--137) THEN
  X86_STEPS_TAC BIGNUM_MONTMUL_SM2_ALT_EXEC [138] THEN
  ABBREV_TAC
   `t = bignum_of_wordlist
          [sum_s134; sum_s135; sum_s136; sum_s137; word(bitval carry_s137)]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 256 + p_sm2 /\ (2 EXP 256 * t == a * b) (mod p_sm2)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `2 EXP 256 * t <= (2 EXP 256 - 1) EXP 2 + (2 EXP 256 - 1) * p
        ==> t < 2 EXP 256 + p`) THEN
      REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_sm2; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC BIGNUM_MONTMUL_SM2_ALT_EXEC
   [142;144;146;147;148] (139--156) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == ab) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * ab) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_sm2] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `carry_s148 <=> p_sm2 <= t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `320` THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[p_sm2; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_BITVAL] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  MATCH_MP_TAC(NUMBER_RULE `!b:num. x + b * p = y ==> (x == y) (mod p)`) THEN
  EXISTS_TAC `bitval(p_sm2 <= t)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b:real = c <=> c - b = a`] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 EXP 256 + p_sm2` THEN
    REWRITE_TAC[bitval; p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BITVAL_CLAUSES; p_sm2] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTMUL_SM2_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_montmul_sm2_alt_tmc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montmul_sm2_alt_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montmul_sm2_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_sm2 (2 EXP 256) * a * b) (mod p_sm2))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 40),40)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_montmul_sm2_alt_tmc BIGNUM_AMONTMUL_SM2_ALT_CORRECT
   `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_AMONTMUL_SM2_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_montmul_sm2_alt_mc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montmul_sm2_alt_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montmul_sm2_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_sm2 (2 EXP 256) * a * b) (mod p_sm2))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 40),40)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_AMONTMUL_SM2_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_montmul_sm2_alt_windows_mc = define_from_elf
   "bignum_montmul_sm2_alt_windows_mc" "x86/sm2/bignum_montmul_sm2_alt.obj";;

let bignum_montmul_sm2_alt_windows_tmc = define_trimmed "bignum_montmul_sm2_alt_windows_tmc" bignum_montmul_sm2_alt_windows_mc;;

let BIGNUM_MONTMUL_SM2_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_montmul_sm2_alt_windows_tmc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montmul_sm2_alt_windows_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montmul_sm2_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a * b <= 2 EXP 256 * p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a * b) MOD p_sm2))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 56),56)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_montmul_sm2_alt_windows_tmc bignum_montmul_sm2_alt_tmc
   BIGNUM_MONTMUL_SM2_ALT_CORRECT `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_MONTMUL_SM2_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_montmul_sm2_alt_windows_mc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montmul_sm2_alt_windows_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montmul_sm2_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a * b <= 2 EXP 256 * p_sm2
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_sm2 (2 EXP 256) * a * b) MOD p_sm2))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 56),56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTMUL_SM2_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

let BIGNUM_AMONTMUL_SM2_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_montmul_sm2_alt_windows_tmc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montmul_sm2_alt_windows_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montmul_sm2_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_sm2 (2 EXP 256) * a * b) (mod p_sm2))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 56),56)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_montmul_sm2_alt_windows_tmc bignum_montmul_sm2_alt_tmc
   BIGNUM_AMONTMUL_SM2_ALT_CORRECT `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_AMONTMUL_SM2_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_montmul_sm2_alt_windows_mc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montmul_sm2_alt_windows_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montmul_sm2_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = a /\
                  bignum_from_memory (y,4) s = b)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (bignum_from_memory (z,4) s ==
                   inverse_mod p_sm2 (2 EXP 256) * a * b) (mod p_sm2))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 56),56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_AMONTMUL_SM2_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

