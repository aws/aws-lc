(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 4-word (256-bit) bignum to Montgomery form modulo p_256.  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p256/bignum_tomont_p256.o";;
 ****)

let bignum_tomont_p256_mc =
  define_assert_from_elf "bignum_tomont_p256_mc" "x86/p256/bignum_tomont_p256.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0xba; 0x03; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 3)) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x0e;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xf3; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% rcx) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% rcx) *)
  0xc4; 0x62; 0xf3; 0xf6; 0x5e; 0x10;
                           (* MULX4 (% r11,% rcx) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADCX (% r10) (% rcx) *)
  0xc4; 0x62; 0xf3; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% rcx) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADCX (% r11) (% rcx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe5;
                           (* ADCX (% r12) (% r13) *)
  0x48; 0xba; 0xff; 0xff; 0xff; 0xff; 0xfb; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744056529682431)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x10;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x4d; 0x11; 0xf5;        (* ADC (% r13) (% r14) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xef;
                           (* ADCX (% r13) (% r15) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADOX (% r14) (% r15) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf7;
                           (* ADCX (% r14) (% r15) *)
  0x48; 0xc7; 0xc2; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm32 (word 4294967294)) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x10;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% r8) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADOX (% r15) (% r8) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf8;
                           (* ADCX (% r15) (% r8) *)
  0x48; 0xba; 0xfd; 0xff; 0xff; 0xff; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 21474836477)) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x0e;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x08;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x10;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,16))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x4e; 0x18;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADCX (% r8) (% r9) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcb;
                           (* MULX4 (% rcx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcb;
                           (* MULX4 (% rcx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% r9) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADCX (% r8) (% r9) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0xb9; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xc7; 0xc0; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967294)) *)
  0x4c; 0x29; 0xe0;        (* SUB (% rax) (% r12) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x4c; 0x19; 0xe8;        (* SBB (% rax) (% r13) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x4c; 0x19; 0xf0;        (* SBB (% rax) (% r14) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x4c; 0x19; 0xf8;        (* SBB (% rax) (% r15) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x4c; 0x19; 0xc0;        (* SBB (% rax) (% r8) *)
  0x48; 0x21; 0xc2;        (* AND (% rdx) (% rax) *)
  0x48; 0x21; 0xc1;        (* AND (% rcx) (% rax) *)
  0x49; 0x29; 0xc4;        (* SUB (% r12) (% rax) *)
  0x49; 0x19; 0xd5;        (* SBB (% r13) (% rdx) *)
  0x49; 0x83; 0xde; 0x00;  (* SBB (% r14) (Imm8 (word 0)) *)
  0x49; 0x19; 0xcf;        (* SBB (% r15) (% rcx) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4c; 0x89; 0x77; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r15) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0xc3                     (* RET *)
];;

let bignum_tomont_p256_tmc = define_trimmed "bignum_tomont_p256_tmc" bignum_tomont_p256_mc;;

let BIGNUM_TOMONT_P256_EXEC = X86_MK_CORE_EXEC_RULE bignum_tomont_p256_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let BIGNUM_TOMONT_P256_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x299) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_tomont_p256_tmc) /\
                  read RIP s = word(pc + 0x08) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0x290) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_256)
             (MAYCHANGE [RIP; RAX; RCX; RDX;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  X86_ACCSTEPS_TAC BIGNUM_TOMONT_P256_EXEC (1--95) (1--95) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist [sum_s84; sum_s88; sum_s91; sum_s93; sum_s95]` THEN
  ABBREV_TAC `r = (2 EXP 256 EXP 2) MOD p_256` THEN
  POP_ASSUM(ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV o REWRITE_RULE[p_256]) THEN
  SUBGOAL_THEN
   `t < 2 * p_256 /\ (2 EXP 256 * t == a * r) (mod p_256)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
        `!ab. ab <= 2 EXP 256 * p /\
              2 EXP 256 * t < ab + 2 EXP 256 * p
              ==> t < 2 * p`) THEN
      EXISTS_TAC `a * r:num` THEN
      MAP_EVERY EXPAND_TAC ["a"; "r"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "r"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  X86_ACCSTEPS_TAC BIGNUM_TOMONT_P256_EXEC (96--107) (96--107) THEN
  SUBGOAL_THEN
  `sum_s107:int64 = word_neg(word(bitval(p_256 <= t))) /\
   (carry_s107 <=> p_256 <= t)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [SUBGOAL_THEN `p_256 <= t <=> p_256 - 1 < t` SUBST1_TAC THENL
     [REWRITE_TAC[p_256] THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `t < 2 * p_256` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      EXPAND_TAC "t" THEN
      REWRITE_TAC[p_256; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  X86_ACCSTEPS_TAC BIGNUM_TOMONT_P256_EXEC (108--117) (108--117) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t:num == a * r) (mod p)
        ==> coprime(p,e) /\ (e * e == r) (mod p)
            ==> (t == e * a) (mod p)`)) THEN
    REWRITE_TAC[COPRIME_REXP; COPRIME_2; CONG] THEN EXPAND_TAC "r" THEN
    REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  ASM_SIMP_TAC[MOD_CASES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 * p_256` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_TOMONT_P256_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 32),40) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_tomont_p256_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p256_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p256_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_256)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  X86_PROMOTE_RETURN_STACK_TAC
    bignum_tomont_p256_tmc BIGNUM_TOMONT_P256_CORRECT
    `[R12; R13; R14; R15]` 32);;

let BIGNUM_TOMONT_P256_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 32),40) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_tomont_p256_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p256_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p256_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_256)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOMONT_P256_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_tomont_p256_windows_mc = define_from_elf
   "bignum_tomont_p256_windows_mc" "x86/p256/bignum_tomont_p256.obj";;

let bignum_tomont_p256_windows_tmc = define_trimmed "bignum_tomont_p256_windows_tmc" bignum_tomont_p256_windows_mc;;

let BIGNUM_TOMONT_P256_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_tomont_p256_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p256_windows_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p256_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_256)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    bignum_tomont_p256_windows_tmc bignum_tomont_p256_tmc
    BIGNUM_TOMONT_P256_CORRECT `[R12; R13; R14; R15]` 32);;

let BIGNUM_TOMONT_P256_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_tomont_p256_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_tomont_p256_windows_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_tomont_p256_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (2 EXP 256 * a) MOD p_256)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOMONT_P256_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

