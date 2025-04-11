(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Division and remainder of bignum by a single (nonzero) word.              *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_cdiv.o";;
 ****)

let bignum_cdiv_mc =
  define_assert_from_elf "bignum_cdiv_mc" "x86/generic/bignum_cdiv.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0x89; 0xca;        (* MOV (% r10) (% rcx) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x4d; 0x85; 0xc9;        (* TEST (% r9) (% r9) *)
  0x0f; 0x84; 0x5d; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 349)) *)
  0x49; 0x0f; 0xbd; 0xc8;  (* BSR (% rcx) (% r8) *)
  0x48; 0x83; 0xf1; 0x3f;  (* XOR (% rcx) (Imm8 (word 63)) *)
  0x49; 0xd3; 0xe0;        (* SHL (% r8) (% cl) *)
  0x4d; 0x89; 0xc7;        (* MOV (% r15) (% r8) *)
  0x49; 0xbb; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x01; 0x00;
                           (* MOV (% r11) (Imm64 (word 562949953421311)) *)
  0x49; 0xc1; 0xef; 0x10;  (* SHR (% r15) (Imm8 (word 16)) *)
  0x4d; 0x31; 0xfb;        (* XOR (% r11) (% r15) *)
  0x49; 0xff; 0xc7;        (* INC (% r15) *)
  0x49; 0xc1; 0xeb; 0x20;  (* SHR (% r11) (Imm8 (word 32)) *)
  0x4c; 0x89; 0xfa;        (* MOV (% rdx) (% r15) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xc1; 0xe8; 0x31;  (* SHR (% rax) (Imm8 (word 49)) *)
  0x48; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% rax) *)
  0x48; 0xc1; 0xea; 0x22;  (* SHR (% rdx) (Imm8 (word 34)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x48; 0x0d; 0x00; 0x00; 0x00; 0x40;
                           (* OR (% rax) (Imm32 (word 1073741824)) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x48; 0xc1; 0xe8; 0x1e;  (* SHR (% rax) (Imm8 (word 30)) *)
  0x49; 0x0f; 0xaf; 0xc3;  (* IMUL (% rax) (% r11) *)
  0x49; 0xc1; 0xe3; 0x1e;  (* SHL (% r11) (Imm8 (word 30)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0xc1; 0xeb; 0x1e;  (* SHR (% r11) (Imm8 (word 30)) *)
  0x4c; 0x89; 0xfa;        (* MOV (% rdx) (% r15) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0xc1; 0xea; 0x18;  (* SHR (% rdx) (Imm8 (word 24)) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x49; 0xc1; 0xe3; 0x10;  (* SHL (% r11) (Imm8 (word 16)) *)
  0x48; 0xc1; 0xea; 0x18;  (* SHR (% rdx) (Imm8 (word 24)) *)
  0x49; 0x01; 0xd3;        (* ADD (% r11) (% rdx) *)
  0x4c; 0x89; 0xfa;        (* MOV (% rdx) (% r15) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0xc1; 0xea; 0x20;  (* SHR (% rdx) (Imm8 (word 32)) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x49; 0xc1; 0xe3; 0x1f;  (* SHL (% r11) (Imm8 (word 31)) *)
  0x48; 0xc1; 0xea; 0x11;  (* SHR (% rdx) (Imm8 (word 17)) *)
  0x49; 0x01; 0xd3;        (* ADD (% r11) (% rdx) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0x48; 0x0f; 0xac; 0xd0; 0x3c;
                           (* SHRD (% rax) (% rdx) (Imm8 (word 60)) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0xc1; 0xea; 0x21;  (* SHR (% rdx) (Imm8 (word 33)) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x49; 0xd1; 0xe3;        (* SHL (% r11) (Imm8 (word 1)) *)
  0x48; 0xc1; 0xe8; 0x21;  (* SHR (% rax) (Imm8 (word 33)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x83; 0xc3; 0x01;  (* ADD (% r11) (Imm8 (word 1)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0x4c; 0x01; 0xc2;        (* ADD (% rdx) (% r8) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4d; 0x89; 0xc7;        (* MOV (% r15) (% r8) *)
  0x4d; 0x0f; 0xaf; 0xfb;  (* IMUL (% r15) (% r11) *)
  0x49; 0xf7; 0xdf;        (* NEG (% r15) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x49; 0xf7; 0xe7;        (* MUL2 (% rdx,% rax) (% r15) *)
  0x49; 0x03; 0x44; 0xda; 0xf8;
                           (* ADD (% rax) (Memop Quadword (%%%% (r10,3,rbx,-- &8))) *)
  0x4c; 0x11; 0xf2;        (* ADC (% rdx) (% r14) *)
  0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x4c; 0x21; 0xf8;        (* AND (% rax) (% r15) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0xff; 0xcb;        (* DEC (% rbx) *)
  0x75; 0xdd;              (* JNE (Imm8 (word 221)) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x48; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% rdx) *)
  0x48; 0x01; 0xda;        (* ADD (% rdx) (% rbx) *)
  0x4d; 0x19; 0xff;        (* SBB (% r15) (% r15) *)
  0x4d; 0x21; 0xc7;        (* AND (% r15) (% r8) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x4c; 0x01; 0xfa;        (* ADD (% rdx) (% r15) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x49; 0x29; 0xc6;        (* SUB (% r14) (% rax) *)
  0x48; 0x19; 0xd3;        (* SBB (% rbx) (% rdx) *)
  0x4d; 0x0f; 0x45; 0xf8;  (* CMOVNE (% r15) (% r8) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x4d; 0x29; 0xfe;        (* SUB (% r14) (% r15) *)
  0x48; 0x19; 0xc3;        (* SBB (% rbx) (% rax) *)
  0x49; 0x0f; 0x45; 0xc0;  (* CMOVNE (% rax) (% r8) *)
  0x49; 0x29; 0xc6;        (* SUB (% r14) (% rax) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x4c; 0x01; 0xf2;        (* ADD (% rdx) (% r14) *)
  0x48; 0xd1; 0xda;        (* RCR (% rdx) (Imm8 (word 1)) *)
  0x49; 0xd3; 0xe8;        (* SHR (% r8) (% cl) *)
  0x48; 0x83; 0xf1; 0x3f;  (* XOR (% rcx) (Imm8 (word 63)) *)
  0x48; 0xd3; 0xea;        (* SHR (% rdx) (% cl) *)
  0x49; 0x0f; 0xaf; 0xd0;  (* IMUL (% rdx) (% r8) *)
  0x49; 0x29; 0xd6;        (* SUB (% r14) (% rdx) *)
  0x4d; 0x89; 0xf7;        (* MOV (% r15) (% r14) *)
  0x4d; 0x29; 0xc6;        (* SUB (% r14) (% r8) *)
  0x4d; 0x0f; 0x43; 0xfe;  (* CMOVAE (% r15) (% r14) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x0f; 0x84; 0xbd; 0x00; 0x00; 0x00;
                           (* JE (Imm32 (word 189)) *)
  0x49; 0x0f; 0xbc; 0xc8;  (* BSF (% rcx) (% r8) *)
  0x49; 0xd3; 0xe8;        (* SHR (% r8) (% cl) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x4d; 0x89; 0xc3;        (* MOV (% r11) (% r8) *)
  0x48; 0xc1; 0xe0; 0x02;  (* SHL (% rax) (Imm8 (word 2)) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x49; 0x83; 0xf3; 0x02;  (* XOR (% r11) (Imm8 (word 2)) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 2)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x48; 0x83; 0xc0; 0x01;  (* ADD (% rax) (Imm8 (word 1)) *)
  0x4c; 0x0f; 0xaf; 0xda;  (* IMUL (% r11) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% rax) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x4c; 0x0f; 0xaf; 0xda;  (* IMUL (% r11) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% rax) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x4c; 0x0f; 0xaf; 0xda;  (* IMUL (% r11) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% rax) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x4c; 0x0f; 0xaf; 0xda;  (* IMUL (% r11) (% rdx) *)
  0x4d; 0x89; 0xfc;        (* MOV (% r12) (% r15) *)
  0x49; 0xd3; 0xec;        (* SHR (% r12) (% cl) *)
  0x4d; 0x89; 0xc5;        (* MOV (% r13) (% r8) *)
  0x4d; 0x29; 0xe5;        (* SUB (% r13) (% r12) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x4d; 0x85; 0xc9;        (* TEST (% r9) (% r9) *)
  0x74; 0x0a;              (* JE (Imm8 (word 10)) *)
  0x4d; 0x8b; 0x22;        (* MOV (% r12) (Memop Quadword (%% (r10,0))) *)
  0x49; 0x83; 0xc2; 0x08;  (* ADD (% r10) (Imm8 (word 8)) *)
  0x49; 0xff; 0xc9;        (* DEC (% r9) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x4c; 0x39; 0xcb;        (* CMP (% rbx) (% r9) *)
  0x73; 0x04;              (* JAE (Imm8 (word 4)) *)
  0x4d; 0x8b; 0x34; 0xda;  (* MOV (% r14) (Memop Quadword (%%% (r10,3,rbx))) *)
  0x4d; 0x0f; 0xad; 0xf4;  (* SHRD (% r12) (% r14) (% cl) *)
  0x4d; 0x01; 0xec;        (* ADD (% r12) (% r13) *)
  0x4d; 0x19; 0xed;        (* SBB (% r13) (% r13) *)
  0x49; 0xf7; 0xdd;        (* NEG (% r13) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x49; 0x0f; 0xaf; 0xc4;  (* IMUL (% rax) (% r12) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x89; 0x04; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x4c; 0x01; 0xe0;        (* ADD (% rax) (% r12) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x89; 0xf4;        (* MOV (% r12) (% r14) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xc2;              (* JB (Imm8 (word 194)) *)
  0x4c; 0x89; 0xf8;        (* MOV (% rax) (% r15) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_cdiv_tmc = define_trimmed "bignum_cdiv_tmc" bignum_cdiv_mc;;

let BIGNUM_CDIV_EXEC = X86_MK_CORE_EXEC_RULE bignum_cdiv_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_NEG_MUL_MNEG_LEMMA = prove
 (`!a b:int64.
        word_neg(word_mul a b) = iword(&0 - ival a * ival b)`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_MADD_LEMMA = prove
 (`!a b:int64.
        word_mul a b = word(0 + val a * val b)`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_MUL_MADD_LEMMA = prove
 (`!a b c:int64.
        word_add a (word_mul b c) = word(val a + val b * val c)`,
  CONV_TAC WORD_RULE);;

(*** This actually works mod 32 but if anything this is more convenient ***)

let WORD_NEGMODINV_SEED_LEMMA_16 = prove
 (`!a x:int64.
        ODD a /\
        word_xor (word_sub (word a) (word_shl (word a) 2)) (word 2) = x
        ==> (a * val x + 1 == 0) (mod 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONG; MOD_0] THEN
  TRANS_TAC EQ_TRANS
   `(val(word a:int64) MOD 16 * val(x:int64) MOD 16 + 1) MOD 16` THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    REWRITE_TAC[VAL_MOD; NUMSEG_LT; ARITH_EQ; ARITH]] THEN
  SUBGOAL_THEN `bit 0 (word a:int64)` MP_TAC THENL
   [ASM_REWRITE_TAC[BIT_LSB_WORD];
    EXPAND_TAC "x" THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 1 (word a:int64)`;`bit 2 (word a:int64)`;`bit 3 (word a:int64)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_CDIV_CORRECT = prove
 (`!k z n x m a pc.
        nonoverlapping (word pc,0x24f) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cdiv_tmc) /\
                  read RIP s = word(pc + 0x9) /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = word(pc + 0x245) /\
                  (~(val m = 0)
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k) /\
                       C_RETURN s = word(a MOD val m)))
             (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10; R11;
                         RBX; R12; R13; R14; R15] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN W64_GEN_TAC `n:num` THEN
  X_GEN_TAC `x:int64` THEN W64_GEN_TAC `m:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN

  (*** Initial parameter move ***)

  ENSURES_SEQUENCE_TAC `pc + 0xf`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R9 s = word n /\
        read R10 s = x /\
        read R8 s = word m /\
        bignum_from_memory (x,n) s = a` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_CDIV_EXEC (1--2); ALL_TAC] THEN

  (*** Split the proof into two main parts, modulus and quotient ***)

  ENSURES_SEQUENCE_TAC `pc + 0x17c`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R9 s = word n /\
        read R10 s = x /\
        read R8 s = word m /\
        bignum_from_memory (x,n) s = a /\
        (~(m = 0) ==> read R15 s = word(a MOD m))` THEN
  CONJ_TAC THENL
   [(*** Factor away irrelevancies from modulus computation ***)

    SUBGOAL_THEN
     `ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST bignum_cdiv_tmc) /\
            read RIP s = word (pc + 0xf) /\
            read R9 s = word n /\
            read R10 s = x /\
            read R8 s = word m /\
            bignum_from_memory (x,n) s = a)
       (\s. read RIP s = word (pc + 0x17c) /\
            read R8 s = word m /\
            (~(m = 0) ==> read R15 s = word(a MOD m)))
       (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R11; RBX; R12; R13; R14; R15] ,,
        MAYCHANGE [CF; PF; AF; ZF; SF; OF])`
    MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_THEN(fun th ->
        ENSURES_INIT_TAC "s0" THEN MP_TAC th THEN
        X86_BIGSTEP_TAC BIGNUM_CDIV_EXEC "s1") THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

    (*** Rename n -> k to allow even easier reuse of bignum_cmod proof ***)

    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `k:num` o concl))) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    SPEC_TAC(`n:num`,`k:num`) THEN REPEAT STRIP_TAC THEN

    (*** Now essentially a copy of the bignum_cmod proof ***)

    (*** Degenerate case when output size is zero ***)

    ASM_CASES_TAC `k = 0` THENL
     [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
      X86_SIM_TAC BIGNUM_CDIV_EXEC (1--4) THEN REWRITE_TAC[MOD_0];
      ALL_TAC] THEN

    (*** Introduce the scaled n = 2^e * m which is used for a while ***)

    ABBREV_TAC `e = word_clz(word m:int64)` THEN
    MP_TAC(ISPEC `word m:int64` WORD_CLZ_LE_DIMINDEX) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN VAL_INT64_TAC `e:num` THEN

    ABBREV_TAC `n = 2 EXP e * m` THEN
    SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["n"; "m"] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND_CLZ] THEN
      ASM_REWRITE_TAC[LE_REFL];
      VAL_INT64_TAC `n:num`] THEN

    ENSURES_SEQUENCE_TAC `pc + 0x26`
     `\s. read R9 s = word k /\
          read R10 s = x /\
          read R8 s = word n /\
          (~(m = 0) ==> read RCX s = word e) /\
          read R14 s = word 0 /\
          bignum_from_memory(x,k) s = a` THEN
    CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_CDIV_EXEC (1--6) THEN ASM_REWRITE_TAC[word_jshl] THEN
      ASM_CASES_TAC `m = 0` THENL
       [UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
        ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0]] THEN
      ASM_REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      ASM_REWRITE_TAC[word_shl] THEN
      SUBGOAL_THEN `e < dimindex(:64)` MP_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `word_clz (word m:int64) = e`)) THEN
          REWRITE_TAC[WORD_CLZ_LT_DIMINDEX] THEN
          ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0];
        REWRITE_TAC[DIMINDEX_64]] THEN
      UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
      SPEC_TAC(`e:num`,`e:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN

    (*** Now the effective clone of word_recip ***)

    ENSURES_SEQUENCE_TAC `pc + 0xec`
     `\s. read R9 s = word k /\
          read R10 s = x /\
          read R8 s = word n /\
          (~(m = 0) ==> read RCX s = word e) /\
          read R14 s = word 0 /\
          bignum_from_memory(x,k) s = a /\
          (~(m = 0)
           ==> &2 pow 64 + &(val(read R11 s)) < &2 pow 128 / &n /\
               &2 pow 128 / &n <= &2 pow 64 + &(val(read R11 s)) + &1)` THEN
    CONJ_TAC THENL
     [(*** Start by globalizing the nonzero assumption ***)

      ASM_CASES_TAC `m = 0` THENL
       [X86_ACCSIM_TAC BIGNUM_CDIV_EXEC (1--53) (1--53);
        ASM_REWRITE_TAC[]] THEN

      (*** Discard irrelevancies that are unchanged ***)

      SUBGOAL_THEN
       `ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST bignum_cdiv_tmc) /\
              read RIP s = word (pc + 0x26) /\
              read R8 s = word n)
         (\s. read RIP s = word (pc + 0xec) /\
              &2 pow 64 + &(val (read R11 s)) < &2 pow 128 / &n /\
              &2 pow 128 / &n <= &2 pow 64 + &(val (read R11 s)) + &1)
         (MAYCHANGE [RIP; RAX; RDX; R11; R15] ,,
          MAYCHANGE [CF; PF; AF; ZF; SF; OF])`
      MP_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_THEN(fun th ->
          ENSURES_INIT_TAC "s0" THEN MP_TAC th THEN
          X86_BIGSTEP_TAC BIGNUM_CDIV_EXEC "s1") THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

      (*** Replace word n with a to allow easy copy of word_recip proof ***)

      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      SPEC_TAC(`a:num`,`aa:num`) THEN REPEAT STRIP_TAC THEN
      ABBREV_TAC `a:int64 = word n` THEN
      UNDISCH_THEN `val(a:int64) = n` (SUBST_ALL_TAC o SYM) THEN
      SUBGOAL_THEN `bit (dimindex(:64) - 1) (a:int64)` MP_TAC THENL
       [REWRITE_TAC[MSB_VAL] THEN
        UNDISCH_THEN `2 EXP e * m = val(a:int64)` (SUBST1_TAC o SYM) THEN
        MP_TAC(ISPECL [`word m:int64`; `word_clz(word m:int64) + 1`]
           VAL_BOUND_CLZ) THEN
        REWRITE_TAC[ARITH_RULE `~(a + 1 <= a)`] THEN
        ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN
        REWRITE_TAC[DIMINDEX_64; EXP_ADD] THEN ARITH_TAC;
        REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`]] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN

      (*** Now segue into a copy of the word_recip proof ***)

      ENSURES_INIT_TAC "s0" THEN

      (*** Handle the special case a = 2^63 explicitly ***)

      ASM_CASES_TAC `a:int64 = word(2 EXP 63)` THENL
       [UNDISCH_THEN `a:int64 = word(2 EXP 63)` SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
        X86_STEPS_TAC BIGNUM_CDIV_EXEC (1--53) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN

      (*** Establish initial range of the input ***)

      SUBGOAL_THEN
       `(&2:real) pow 63 + &1 <= &(val(a:int64)) /\
        &(val(a:int64)):real <= &2 pow 64 - &1`
      STRIP_ASSUME_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV THEN MP_TAC(ISPEC `a:int64` MSB_VAL) THEN
        MP_TAC(SPEC `a:int64` VAL_BOUND_64) THEN
        REWRITE_TAC[DIMINDEX_64; REAL_OF_NUM_LE] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM VAL_EQ]) THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC;
        ALL_TAC] THEN

      (*** Initial switch to a shorter b, initial approximation x = z0 ***)

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (1--3) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t3:int64`; `e3:real`] THEN
      STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [4] THEN
      MP_TAC(ISPECL [`49`; `t3:int64`] WORD_SUB_MASK_WORD) THEN
      CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM BOUNDER_TAC[];
        DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SUB) THEN
      CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t4:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [5] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
      ASM_REWRITE_TAC[VAL_WORD_1] THEN
      ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:int64`
       (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
      SUBGOAL_THEN
       `&2 pow 47 + &1 <= &(val(b:int64)) /\ &(val(b:int64)) <= &2 pow 48`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN
        POP_ASSUM(SUBST1_TAC o SYM) THEN ASM BOUNDER_TAC[];
        ALL_TAC] THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [6] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`z0:int64`; `e6:real`] THEN
      ASM_REWRITE_TAC[REAL_ARITH
       `&562949953421311 - x = &2 pow 49 - (x + &1)`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
       (STRIP_ASSUME_TAC o GSYM)) THEN

      SUBGOAL_THEN
       `&2 pow 15 <= &(val(z0:int64)) /\
        &(val(z0:int64)) <= &2 pow 16 + &2 pow 15 - &1`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN
        POP_ASSUM(SUBST1_TAC o SYM) THEN ASM BOUNDER_TAC[];
        ALL_TAC] THEN

      SUBGOAL_THEN
       `&2 pow 64 - &2 pow 62 - &2 pow 48 <=
        &(val(b:int64)) * &(val(z0:int64)) /\
        &(val(b:int64)) * &(val(z0:int64)) <= &2 pow 64`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
         (PAT_CONV `\z:real. l <= b * z /\ b * z <= u`) [SYM th]) THEN
        REWRITE_TAC[REAL_ARITH
         `b * ((&2 pow 49 - b) / &2 pow 32 - e) =
          &2 pow 64 - (&2 pow 48 - b) pow 2 / &2 pow 32 - b * e`] THEN
        ASM PURE_BOUNDER_TAC[];
        ALL_TAC] THEN

      (*** Computation of initial error d0 ***)

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (7--9) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_MUL_MNEG_LEMMA]) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MNEG) THEN
      ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d0:int64`
       (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
      W(fun (asl,w) -> FIRST_ASSUM
        (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

      (*** Accumulation of the polynomial giving z1 ***)

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (10--11) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t11:int64`; `e11:real`] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [12] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t12:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [13] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t13:int64`; `e13:real`] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [14] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD o
        GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SYM]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t14:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [15] THEN
      MP_TAC(ISPECL [`t12:int64`; `word 1073741824:int64`] WORD_ADD_OR) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[WORD_AND_EQ_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
        REWRITE_TAC[SET_RULE `DISJOINT s {a} <=> ~(a IN s)`] THEN
        REWRITE_TAC[IN_BITS_OF_WORD; BIT_VAL] THEN
        MATCH_MP_TAC(MESON[ODD; DIV_LT] `a < n ==> ~ODD(a DIV n)`) THEN
        ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
        DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
      DISCH_THEN(X_CHOOSE_THEN `t15:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [16] THEN
      FIRST_X_ASSUM(ASSUME_TAC o
        GEN_REWRITE_RULE RAND_CONV [WORD_MUL_SYM]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t16:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [17] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t17:int64`; `e17:real`] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (18--19) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t19:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [20] THEN
      FIRST_X_ASSUM(ASSUME_TAC o
       GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [WORD_MUL_SYM]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_MUL_MADD_LEMMA]) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MADD) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t20:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [21] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`z1:int64`; `e21:real`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (STRIP_ASSUME_TAC o GSYM)) THEN

      (*** Accuracy of z1 then bounds on z1 and tidying up ***)

      SUBGOAL_THEN
       `&2 pow 64 - (&2 pow 54 + &2 pow 50) <=
        &(val(b:int64)) * &(val(z1:int64)) /\
        &(val(b:int64)) * &(val(z1:int64)) <= &2 pow 64`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[REAL_ARITH
         `b * ((a * z + z * c) / &2 pow 30 - e:real) =
          (b * z) * (a + c) / &2 pow 30 - b * e`] THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
           `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
          ASM BOUNDER_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[REAL_ARITH `(x * x + x') * (x * x + a):real =
            a * x' + a * x * x + x' * x * x + x * x * x * x`] THEN
        REWRITE_TAC[REAL_ARITH
         `bz * (&2 pow 30 + x / &2 pow 30 - e) / &2 pow 30 - be <= u <=>
          bz * (&2 pow 60 + x) <=
          &2 pow 60 * (u + be + bz * e / &2 pow 30)`] THEN
        REWRITE_TAC[REAL_ARITH
         `(x - d) * (y - e):real = x * y - (d * y + e * (x - d)) /\
          (x - d) + (y - e):real = (x + y) - (d + e) /\
          &c * (x - y) = (&c * x - &c * y)`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `bz * (&2 pow 60 + x) <= &2 pow 124 /\ &0 <= u /\ &0 <= bz * y
          ==> bz * (&2 pow 60 + x - y) <= &2 pow 60 * (&2 pow 64 + u)`) THEN
        REPEAT CONJ_TAC THENL
         [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
           `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
          ASM BOUNDER_TAC[];
          ASM BOUNDER_TAC[];
          SUBGOAL_THEN
           `&(val(t11:int64)) <= &2 pow 15 /\ &(val(t13:int64)) <= &2 pow 30`
          STRIP_ASSUME_TAC THENL
           [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM BOUNDER_TAC[];
            ALL_TAC] THEN
          MAP_EVERY (C UNDISCH_THEN (SUBST_ALL_TAC o SYM))
           [`&(val(t11:int64)) = &(val(d0:int64)) / &2 pow 49 - e11`;
            `&(val(t13:int64)) = &(val(d0:int64)) / &2 pow 34 - e13`] THEN
          ASM BOUNDER_TAC[]];
        ALL_TAC] THEN

      SUBGOAL_THEN
       `&2 pow 15 <= &(val(z1:int64)) /\ &(val(z1:int64)) <= &130945`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THENL
         [ALL_TAC; ASM BOUNDER_TAC[]] THEN
        REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
        REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
         `&(val x) = a ==> a = &(val x)`))) THEN
        ASM BOUNDER_TAC[];
        DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

      (*** First Newton step ***)

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (22--24) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_MUL_MNEG_LEMMA]) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MNEG) THEN
      ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d1:int64`
       (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
      W(fun (asl,w) -> FIRST_ASSUM
         (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [25] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t25:int64`; `e25:real`] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [26] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t26:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [27] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t27:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [28] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t28:int64`; `e28:real`] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [29] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
      DISCH_THEN(X_CHOOSE_THEN `z2:int64`
       (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN

      SUBGOAL_THEN
       `&2 pow 80 - &5 / &4 * &2 pow 60
        <= &(val(b:int64)) * &(val(z2:int64)) /\
        &(val(b:int64)) * &(val(z2:int64)) <= &2 pow 80`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[REAL_ARITH
         `b * (z * d - e):real = (b * z) * d - b * e`] THEN
        FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
           `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
        CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[REAL_ARITH
         `(&2 pow 64 - d) * (&2 pow 16 + (d / &2 pow 24 - e) / &2 pow 24) =
          (&2 pow 128 - d pow 2) / &2 pow 48 -
          (&2 pow 64 - d) * e / &2 pow 24`] THEN
        CONV_TAC(funpow 3 LAND_CONV REAL_POLY_CONV) THEN
        ASM PURE_BOUNDER_TAC[];
        ALL_TAC] THEN

      SUBGOAL_THEN
       `&2 pow 31 <= &(val(z2:int64)) /\ &(val(z2:int64)) <= &2 pow 33 - &1`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN SHARPEN_INEQ_TAC THENL
         [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
          REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
          REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
           `&(val x) = a ==> a = &(val x)`))) THEN
          ASM BOUNDER_TAC[];
          MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
          EXISTS_TAC `&(val(b:int64))` THEN
          CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
          GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN ASM PURE_BOUNDER_TAC[]];
        DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

      (*** Second Newton step ***)

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (30--32) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_MUL_MNEG_LEMMA]) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_IWORD) THEN
      DISCH_THEN(MP_TAC o SPEC
       `&2 pow 80 - &(val(b:int64)) * &(val(z2:int64)):int`) THEN
      REWRITE_TAC[int_le; int_lt; int_sub_th; int_mul_th;
                    int_pow_th; int_of_num_th] THEN
      ANTS_TAC THENL
       [REPEAT(CONJ_TAC THENL [ASM PURE_BOUNDER_TAC[]; ALL_TAC]) THEN
        MATCH_MP_TAC(INTEGER_RULE
         `e divides n /\ (b == b') (mod e) /\ (z == z') (mod e)
          ==> (&0 - b * z:int == n - b' * z') (mod e)`) THEN
        REWRITE_TAC[REWRITE_RULE[DIMINDEX_64]
         (INST_TYPE [`:64`,`:N`]IVAL_VAL_CONG)] THEN
        MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d2:int64`
       (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
      W(fun (asl,w) -> FIRST_ASSUM
        (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [33] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t33:int64`; `e33:real`] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [34] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t34:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [35] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t35:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [36] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t36:int64`; `e36:real`] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [37] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
      ASM_REWRITE_TAC[REAL_ARITH
       `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(b:int64))` THEN
        CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[REAL_ARITH
         `b * (z * d - e):real = (b * z) * d - b * e`] THEN
        FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
           `&2 pow 80 - b * z = d ==> b * z:real = &2 pow 80 - d`)) THEN
        GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN
        ASM BOUNDER_TAC[];
        ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
      DISCH_THEN(X_CHOOSE_THEN `z3:int64`
       (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN

      SUBGOAL_THEN
       `&2 pow 111 - &201 / &128 * &2 pow 71
        <= &(val(b:int64)) * &(val(z3:int64)) /\
        &(val(b:int64)) * &(val(z3:int64)) <= &2 pow 111`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[REAL_ARITH
         `b * (z * d - e):real = (b * z) * d - b * e`] THEN
        FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
           `&2 pow 80 - b * z = d ==> b * z:real = &2 pow 80 - d`)) THEN
        CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[REAL_ARITH
         `(&2 pow 80 - d) * (&2 pow 31 + (d / &2 pow 32 - e) / &2 pow 17) =
          (&2 pow 160 - d pow 2) / &2 pow 49 -
          (&2 pow 80 - d) * e / &2 pow 17`] THEN
        CONV_TAC(funpow 3 LAND_CONV REAL_POLY_CONV) THEN
        ASM PURE_BOUNDER_TAC[];
        ALL_TAC] THEN

      SUBGOAL_THEN
       `&2 pow 62 <= &(val(z3:int64)) /\ &(val(z3:int64)) <= &2 pow 64 - &1`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
        SHARPEN_INEQ_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
        REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
         `&(val x) = a ==> a = &(val x)`))) THEN
        ASM BOUNDER_TAC[];
        DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

      (*** Transfer accuracy to original input a, throw away facts about b ***)

      SUBGOAL_THEN
       `&2 pow 127 - &2 pow 88 + &1 <= &(val(a:int64)) * &(val(z3:int64)) /\
        &(val(a:int64)) * &(val(z3:int64)) <= &2 pow 127`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
         `a / &2 pow 16 - e + &1 = b ==> a = &2 pow 16 * (b + e - &1)`)) THEN
       REWRITE_TAC[REAL_ARITH
        `(c * (b + x)) * z:real = c * (b * z + x * z)`] THEN
       CONJ_TAC THEN ASM PURE_BOUNDER_TAC[];
       REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
        (vfree_in `b:int64` o concl)))] THEN

      (*** Observe this, which implies the result is not exact ***)

      SUBGOAL_THEN `!w p. ~(val(a:int64) * w = 2 EXP p)` ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ_ALT] PRIME_POWER_MULT)) THEN
        REWRITE_TAC[PRIME_2] THEN STRIP_TAC THEN
        SUBGOAL_THEN `2 EXP 63 < val(a:int64) /\ val a < 2 EXP 64` MP_TAC THENL
         [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
          ASM_REWRITE_TAC[LT_EXP] THEN ARITH_TAC];
        ALL_TAC] THEN

      (*** The full-sized Newton step ***)

      X86_ACCSTEPS_TAC BIGNUM_CDIV_EXEC [39] (38--40) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (41--42) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t42:int64`; `e42:real`] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [43] THEN
      REABBREV_TAC `bf = read RAX s43` THEN

      SUBGOAL_THEN
       `?e. &0 <= e /\ e <= &1 /\
            &(val(bf:int64)):real =
            (&2 pow 127 - &(val(a:int64)) * &(val(z3:int64))) / &2 pow 60 - e`
      (X_CHOOSE_THEN `e32:real` STRIP_ASSUME_TAC) THENL
       [MP_TAC(SPEC `&2 pow 127 - &(val(a:int64)) * &(val(z3:int64)):real`
              INTEGER_POS) THEN
        ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
        ANTS_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_TAC `d3:num`) THEN
        SUBGOAL_THEN `&d3:real <= &2 pow 88 - &1` ASSUME_TAC THENL
         [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
          ASM BOUNDER_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `d3 < 2 EXP 88` ASSUME_TAC THENL
         [ASM BOUNDER_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `1 <= d3` ASSUME_TAC THENL
         [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
          FIRST_X_ASSUM(fun th ->
            GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
          REWRITE_TAC[REAL_OF_NUM_CLAUSES; REAL_SUB_0] THEN
          DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[GSYM int_of_num_th] THEN
        SUBGOAL_THEN `&(val(bf:int64)):int = &((d3 - 1) DIV 2 EXP 60)`
        SUBST1_TAC THENL
         [EXPAND_TAC "bf" THEN
          SIMP_TAC[GSYM WORD_SUBWORD_NOT; GSYM WORD_JOIN_NOT;
                   DIMINDEX_64; DIMINDEX_128; ARITH] THEN
          SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; DIMINDEX_128;
                   ARITH_LE; ARITH_LT] THEN
          REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM;
                      GSYM INT_OF_NUM_DIV; INT_VAL_WORD_NOT; DIMINDEX_64] THEN
          REWRITE_TAC[INT_ARITH
            `e * (e - &1 - h) + e - &1 - l:int = e * e - &1 - (e * h + l)`] THEN
          SIMP_TAC[INT_DIV_REM; INT_POS; INT_POW_LE; GSYM INT_POW_ADD] THEN
          CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
          ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
          FIRST_ASSUM(MP_TAC o check (is_eq o concl)) THEN
          REWRITE_TAC[IMP_IMP; REAL_EQ_SUB_RADD] THEN
          GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [REAL_OF_NUM_CLAUSES] THEN
          GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
           [GSYM INT_OF_NUM_CLAUSES] THEN
          REWRITE_TAC[GSYM INT_EQ_SUB_RADD] THEN DISCH_THEN(fun th ->
            REWRITE_TAC[th; INT_ARITH
            `&2 pow 128 - &1 - x:int =
             (&2 pow 127 - &1) + &2 pow 127 - x`]) THEN
          SUBGOAL_THEN `(&2 pow 127 - &1 + &d3) rem &2 pow 124 = &(d3 - 1)`
          SUBST1_TAC THENL
           [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
            MATCH_MP_TAC INT_REM_UNIQ THEN
            EXISTS_TAC `&8:int` THEN CONJ_TAC THENL
             [INT_ARITH_TAC; ALL_TAC] THEN
            REWRITE_TAC[INT_SUB_LE; INT_LT_SUB_RADD] THEN
            REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_ABS_NUM] THEN
            REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
            REWRITE_TAC[INT_OF_NUM_DIV; INT_OF_NUM_CLAUSES] THEN ARITH_TAC];
          ASM_REWRITE_TAC[int_of_num_th]] THEN
        EXISTS_TAC `&((d3 - 1) MOD 2 EXP 60 + 1):real / &2 pow 60` THEN
        SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
         [SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
          REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
          ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LE_1] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [44] THEN
      FIRST_X_ASSUM(ASSUME_TAC o
        GEN_REWRITE_RULE RAND_CONV [WORD_MUL_SYM]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM PURE_BOUNDER_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t44:int64` STRIP_ASSUME_TAC) THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (45--46) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t46:int64`; `e46:real`] THEN STRIP_TAC THEN

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [47] THEN

      (*** Analysis of provisional result w before the final truncation ***)

      ABBREV_TAC `w = 2 * val(z3:int64) + val(t46:int64)` THEN
      SUBGOAL_THEN
       `&2 pow 128 - &2 pow 62 <= &(val(a:int64)) * &w + &(val a) /\
        &(val(a:int64)) * &w <= &2 pow 128`
      STRIP_ASSUME_TAC THENL
       [ABBREV_TAC `d3 = &2 pow 127 - &(val(a:int64)) * &(val(z3:int64))` THEN
        SUBGOAL_THEN `&0 <= d3 /\ d3:real <= &2 pow 88 - &1`
        STRIP_ASSUME_TAC THENL
         [EXPAND_TAC "d3" THEN ASM PURE_BOUNDER_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "w" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        ASM_REWRITE_TAC[REAL_ARITH
         `a * (&2 * z + ((z / &2 pow 33 - d) * c) / &2 pow 33 - f):real =
          (a * z) * (&2 + c / &2 pow 66) - d * c * a / &2 pow 33 - a * f`] THEN
        FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
           `&2 pow 127 - a * z = d ==> a * z:real = &2 pow 127 - d`)) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH
           `&0 <= a * (&1 - e) /\ l <= b - c
            ==> l:real <= b - c - a * e + a`) THEN
          CONJ_TAC THENL [ASM PURE_BOUNDER_TAC[]; ASM BOUNDER_TAC[]];
          REWRITE_TAC[REAL_ARITH
           `(&2 pow 127 - d) * (&2 + (d / &2 pow 60 - e) / &2 pow 66) =
            (&2 pow 254 - d pow 2) / &2 pow 126 -
            (&2 pow 127 - d) * e / &2 pow 66`] THEN
          SUBST1_TAC(SYM(ASSUME
           `&(val(bf:int64)) = d3 / &2 pow 60 - e32`)) THEN
          ASM PURE_BOUNDER_TAC[]];
        ALL_TAC] THEN

      (*** Now the computed result with implicit 1 bit ***)

      ABBREV_TAC `z:int64 = word_add (word_shl z3 1) t46` THEN
      SUBGOAL_THEN `&w:real = (&2 pow 64) + &(val(z:int64))`
      SUBST_ALL_TAC THENL
       [EXPAND_TAC "z" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL] THEN
        REWRITE_TAC[DIMINDEX_64; EXP_1] THEN CONV_TAC MOD_DOWN_CONV THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `2 EXP 64 <= w /\ w < 2 * 2 EXP 64` MP_TAC THENL
         [REWRITE_TAC[GSYM REAL_OF_NUM_LT; ARITH_RULE `a <= b <=> a < b + 1`];
          SIMP_TAC[GSYM NOT_LE; MOD_CASES; GSYM REAL_OF_NUM_SUB] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THEN
        (MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
         EXISTS_TAC `&(val(a:int64))` THEN
         CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC])
        THENL
         [REWRITE_TAC[REAL_ARITH `a * (w + &1):real = a * w + a`] THEN
          TRANS_TAC REAL_LTE_TRANS `&2 pow 128 - &2 pow 62`;
          TRANS_TAC REAL_LET_TRANS `&2 pow 128`] THEN
        ASM_REWRITE_TAC[] THEN ASM BOUNDER_TAC[];
        ALL_TAC] THEN

      (*** In this non-trivial case the increment does not wrap ***)

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (48--50) THEN
      REABBREV_TAC `z' = read R11 s50` THEN
      SUBGOAL_THEN `&(val(z':int64)):real = &(val(z:int64)) + &1`
      ASSUME_TAC THENL
       [EXPAND_TAC "z'" THEN
        SUBGOAL_THEN `val(z:int64) + 1 < 2 EXP 64` MP_TAC THENL
         [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES];
          SIMP_TAC[GSYM NOT_LT; BITVAL_CLAUSES; ADD_CLAUSES] THEN
          SIMP_TAC[WORD_SUB_0; VAL_WORD_ADD_CASES;
                   DIMINDEX_64; VAL_WORD_1] THEN
          REWRITE_TAC[REAL_OF_NUM_CLAUSES]] THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&2 pow 63 + &1) * (&2 pow 64 + z) <= &2 pow 128
          ==> z + &1 < &2 pow 64`) THEN
        TRANS_TAC REAL_LE_TRANS
         `&(val(a:int64)) * (&2 pow 64 + &(val(z:int64)))` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN ASM BOUNDER_TAC[];
        ALL_TAC] THEN

      (*** The final bounds check and selection ***)

      X86_STEPS_TAC BIGNUM_CDIV_EXEC (51--53) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ;
                   REAL_ARITH `&2 pow 63 + &1 <= a ==> &0 < a`] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; ADD_CLAUSES] THEN
      SIMP_TAC[DIMINDEX_64; DIMINDEX_128; MOD_LT; VAL_BOUND_64; LT_MULT2;
               ARITH_RULE `a < 2 EXP 64 * 2 EXP 64
                           ==> a DIV 2 EXP 64 < 2 EXP 64 /\ a < 2 EXP 128`;
               ARITH_RULE `2 EXP 64 <= h DIV 2 EXP 64 + a <=>
                           2 EXP 128 <= 2 EXP 64 * a + h`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LT_LE] THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bitval] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0] THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1; DIMINDEX_64] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REAL_ARITH_TAC;

      GHOST_INTRO_TAC `w:int64` `read R11` THEN
      GLOBALIZE_PRECONDITION_TAC] THEN

    (*** The main loop resulting in a 128-bit modular equivalent ***)

    ENSURES_WHILE_PDOWN_TAC `k:num` `pc + 0xfb` `pc + 0x11c`
     `\i s. (read R9 s = word k /\
             read R10 s = x /\
             read R8 s = word n /\
             (~(m = 0) ==> read RCX s = word e) /\
             read R11 s = w /\
             read RBX s = word i /\
             (~(m = 0) ==> (val(read R15 s) == 2 EXP 128) (mod m)) /\
             (~(m = 0) ==> (bignum_of_wordlist[read R14 s; read RDX s] ==
                            highdigits a i) (mod m)) /\
             bignum_from_memory(x,i) s = lowdigits a i) /\
            (read ZF s <=> i = 0)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_CDIV_EXEC (1--5) THEN
      ASM_SIMP_TAC[bignum_of_wordlist; LOWDIGITS_SELF; VAL_WORD_0] THEN
      ASM_SIMP_TAC[HIGHDIGITS_ZERO; ADD_CLAUSES; MULT_CLAUSES; CONG_REFL] THEN
      DISCH_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
       [UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ;
                     REAL_OF_NUM_LT; LE_1] THEN
        REPEAT STRIP_TAC] THEN
      REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC INT_CONG_TRANS THEN
      EXISTS_TAC `&2 pow 128 - (&2 pow 64 + &(val(w:int64))) * &n:int` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INT_EQ_IMP_CONG;
        UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC NUMBER_RULE] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 64` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(INT_ARITH
         `&0 <= x /\ x:int < p /\ &0 <= y /\ y < p ==> abs(x - y) < p`) THEN
        REWRITE_TAC[INT_LE_SUB_LADD; INT_LT_SUB_RADD] THEN
        REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_POS;
                    VAL_BOUND_64; ADD_CLAUSES] THEN
        ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC(REAL_ARITH
         `a:real <= (e + w + &1) * n /\ n < e ==> a < e + (e + w) * n`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES];
        MATCH_MP_TAC(INTEGER_RULE
         `e divides ee /\ (a == --(w * n)) (mod e)
          ==> (a:int == ee - (e + w) * n) (mod e)`) THEN
        SIMP_TAC[INT_DIVIDES_POW_LE_IMP; ARITH_LE; ARITH_LT] THEN
        W(MP_TAC o PART_MATCH (lhand o rator) INT_CONG_WORD_NEG o
          lhand o rator o snd) THEN
        REWRITE_TAC[DIMINDEX_64] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
        REWRITE_TAC[VAL_WORD_MUL; GSYM INT_OF_NUM_CLAUSES; DIMINDEX_64;
                    GSYM INT_OF_NUM_REM; VAL_WORD; GSYM INT_REM_EQ] THEN
        CONV_TAC INT_REM_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        INT_ARITH_TAC];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
      ASM_CASES_TAC `m = 0` THENL
       [X86_SIM_TAC BIGNUM_CDIV_EXEC (1--10) THEN
        VAL_INT64_TAC `i + 1` THEN ASM_REWRITE_TAC[VAL_WORD_1] THEN
        CONJ_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC ARITH_RULE];
        ASM_REWRITE_TAC[]] THEN
      GHOST_INTRO_TAC `r:int64` `read R15` THEN
      GHOST_INTRO_TAC `h:int64` `read RDX` THEN
      GHOST_INTRO_TAC `l:int64` `read R14` THEN
      MP_TAC(WORD_RULE `word_sub (word(i + 1)) (word 1):int64 = word i`) THEN
      DISCH_TAC THEN VAL_INT64_TAC `i + 1` THEN
      ASSUME_TAC(SPEC `i:num` WORD_INDEX_WRAP) THEN
      X86_ACCSIM_TAC BIGNUM_CDIV_EXEC [2;3;4;8;9] (1--10) THEN
      MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC
       `bignum_of_wordlist[word(bigdigit a i); l] +
        val(r:int64) * val(h:int64)` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
         `(a == h) (mod m)
          ==> (e * a + b == x) (mod m)
              ==> (x == e * h + b) (mod m)`)) THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_CONV) THEN
        REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN MATCH_MP_TAC(NUMBER_RULE
         `(r == e EXP 2) (mod m)
          ==> (e * (l + e * h) + d == (d + e * l) + r * h) (mod m)`) THEN
        ASM_REWRITE_TAC[ARITH_RULE `2 EXP 64 EXP 2 = 2 EXP 128`]] THEN
      ABBREV_TAC `z:num = bignum_of_wordlist[word(bigdigit a i); l] +
                          val(r:int64) * val(h:int64)` THEN
      ASM_REWRITE_TAC[REAL_CONGRUENCE; REAL_OF_NUM_EQ] THEN
      SUBGOAL_THEN
       `&(bignum_of_wordlist [sum_s8; sum_s9]):real =
        if &z < &2 pow 128 then &z else &z - (&2 pow 128 - &(val(r:int64)))`
      SUBST1_TAC THENL
       [ALL_TAC;
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO;
           INTEGER_CLOSED; REAL_ARITH `z - (a - b) - z:real = b - a`] THEN
        UNDISCH_TAC `(val(r:int64) == 2 EXP 128) (mod m)` THEN
        ASM_REWRITE_TAC[REAL_CONGRUENCE; REAL_OF_NUM_EQ] THEN
        REWRITE_TAC[real_div; GSYM REAL_OF_NUM_CLAUSES]] THEN
      MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
      CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
      CONJ_TAC THENL
       [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "z" THEN POP_ASSUM_LIST(K ALL_TAC) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&z:real < &2 pow 128 <=> ~carry_s4` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_REAL_LT THEN
        EXISTS_TAC `128` THEN
        ACCUMULATOR_POP_ASSUM_LIST
         (MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        EXPAND_TAC "z" THEN
        REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        EXPAND_TAC "z" THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        REWRITE_TAC[COND_SWAP; WORD_AND_MASK] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_CDIV_EXEC [1];
      ALL_TAC] THEN

    (*** Globalize the nonzeroness for the rest of the proofs ***)

    ASM_CASES_TAC `m = 0` THENL
     [GHOST_INTRO_TAC `e':int64` `read RCX` THEN
      X86_SIM_TAC BIGNUM_CDIV_EXEC (1--31) THEN
      UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; WORD_USHR_0];
      ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
      [UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
       ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ];
       ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ;
                    REAL_OF_NUM_LT; LE_1] THEN
       STRIP_TAC] THEN

    (*** Reduction from 128 bits to 64 bits ***)

    ASM_SIMP_TAC[HIGHDIGITS_0; LOWDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x155`
     `\s. read R8 s = word n /\
          read RCX s = word e /\
          read R11 s = w /\
          (val(read R14 s) == a) (mod m)` THEN
    CONJ_TAC THENL
     [GHOST_INTRO_TAC `h:int64` `read RDX` THEN
      GHOST_INTRO_TAC `l:int64` `read R14` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

      (*** Initial quotient multiple ***)

      ABBREV_TAC
       `q = ((2 EXP 64 + val(w:int64)) * val(h:int64)) DIV 2 EXP 64` THEN
      UNDISCH_THEN `val(word n:int64) = n` (K ALL_TAC) THEN
      X86_ACCSTEPS_TAC BIGNUM_CDIV_EXEC [4;5;9;10;12;13] (1--13) THEN
      SUBGOAL_THEN
       `&(bignum_of_wordlist[sum_s12; sum_s13]) =
        &(bignum_of_wordlist [l; h]) - &q * &n`
      MP_TAC THENL
       [EXPAND_TAC "q" THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
        MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
        CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_DIV; bignum_of_wordlist; REAL_ADD_RID;
                      GSYM REAL_OF_NUM_CLAUSES; REAL_MUL_RZERO] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0 <= l /\ &0 <= m * n /\ q * n:real <= h
             ==> &0 <= (l + h) - (q - m) * n`) THEN
          SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LE_DIV; REAL_POW_LE] THEN
          REWRITE_TAC[REAL_ARITH
           `(x * h) / &2 pow 64 * n <= &2 pow 64 * h <=>
            (x * n) * h <= &2 pow 128 * h`] THEN
          ASM_SIMP_TAC[REAL_LE_RMUL; REAL_LT_IMP_LE; REAL_POS];
          MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x:real < n ==> x - y < n`) THEN
          SIMP_TAC[REAL_POS; REAL_LE_MUL] THEN BOUNDER_TAC[];
          SIMP_TAC[RIGHT_ADD_DISTRIB; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ]] THEN
        UNDISCH_THEN
         `&2 pow 64 * &(val(mulhi_s4:int64)) + &(val(mullo_s4:int64)) =
          &(val(w:int64)) * &(val(h:int64))`
         (MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
        DISCH_THEN(MP_TAC o AP_TERM `\x. x DIV 2 EXP 64`) THEN
        SIMP_TAC[DIV_MULT_ADD; DIV_LT; VAL_BOUND_64; EXP_EQ_0; ARITH_EQ] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ADD_CLAUSES] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BITVAL_CLAUSES; VAL_WORD_0] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
        ALL_TAC] THEN
      ABBREV_TAC `z0 = bignum_of_wordlist [sum_s12; sum_s13]` THEN
      DISCH_THEN(ASSUME_TAC o SYM) THEN
      ABBREV_TAC
       `zf0 <=>
        val(word_sub h (word_add sum_s10
           (word(bitval carry_s12))):int64) = 0` THEN
      SUBGOAL_THEN `zf0 <=> z0 < 2 EXP 64` SUBST_ALL_TAC THENL
       [TRANS_TAC EQ_TRANS `val (sum_s13:int64) = 0` THEN CONJ_TAC THENL
         [ALL_TAC;
          REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (~p ==> ~q)`] THEN
          EXPAND_TAC "z0" THEN SIMP_TAC[bignum_of_wordlist] THEN
          CONJ_TAC THENL [DISCH_TAC THEN BOUNDER_TAC[]; ARITH_TAC]] THEN
        EXPAND_TAC "zf0" THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[WORD_RULE `word_sub x y = z <=> word_add y z = x`] THEN
        REWRITE_TAC[GSYM VAL_CONG; VAL_WORD_ADD; VAL_WORD_BITVAL; CONG] THEN
        REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
         `--e * c + s = h - i - j ==> (i + j) + s = e * c + h`)) THEN
        SIMP_TAC[REAL_OF_NUM_CLAUSES; MOD_MULT_ADD];
        ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
      SUBGOAL_THEN `z0 < 2 EXP 64 + 2 * n` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        EXPAND_TAC "q" THEN
        SIMP_TAC[RIGHT_ADD_DISTRIB; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        REWRITE_TAC[REAL_OF_NUM_DIV; REAL_MUL_RZERO; REAL_ADD_RID] THEN
        MATCH_MP_TAC(REAL_ARITH
         `l:real < e /\ m * n <= &1 * n /\
          eh <= (h + q + &1) * n
          ==> (l + eh) - (h + q - m) * n < e + &2 * n`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REPEAT CONJ_TAC THENL
         [BOUNDER_TAC[];
          MATCH_MP_TAC REAL_LE_RMUL THEN
          SIMP_TAC[REAL_POS; REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
          REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[REAL_ARITH
         `e * h <= (h + (w * h) / a + &1) * n <=>
          h * (e - (&1 + w / a) * n) <= n`] THEN
        TRANS_TAC REAL_LE_TRANS `&(val(h:int64)) * &n / &2 pow 64` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN
          UNDISCH_TAC
           `&2 pow 128 <= (&2 pow 64 + &(val(w:int64)) + &1) * &n` THEN
          REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ARITH
           `h * n / &2 pow 64 <= n <=> h * n <= &2 pow 64 * n`] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN
          REWRITE_TAC[REAL_POS] THEN BOUNDER_TAC[]];
        ALL_TAC] THEN

      (*** First correction ***)

      X86_ACCSTEPS_TAC BIGNUM_CDIV_EXEC [16;17] (14--17) THEN
      SUBGOAL_THEN
       `&(bignum_of_wordlist[sum_s16; sum_s17]) =
        if 2 EXP 64 <= z0 then &z0 - &n else &z0`
      MP_TAC THENL
       [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
        MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
        CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]] THEN
        CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`z0 < 2 EXP 64 + 2 * n`; `n < 2 EXP 64`] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        EXPAND_TAC "z0" THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        COND_CASES_TAC THEN
        ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BITVAL_CLAUSES; VAL_WORD_0] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
        ALL_TAC] THEN
      ABBREV_TAC `z1 = bignum_of_wordlist [sum_s16; sum_s17]` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(ASSUME_TAC o SYM) THEN
      ABBREV_TAC
       `zf1 <=>
        val(word_sub sum_s13 (word (bitval carry_s16)):int64) = 0` THEN
      SUBGOAL_THEN `zf1 <=> z1 < 2 EXP 64` SUBST_ALL_TAC THENL
       [TRANS_TAC EQ_TRANS `val (sum_s17:int64) = 0` THEN CONJ_TAC THENL
         [ALL_TAC;
          REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (~p ==> ~q)`] THEN
          EXPAND_TAC "z1" THEN SIMP_TAC[bignum_of_wordlist] THEN
          CONJ_TAC THENL [DISCH_TAC THEN BOUNDER_TAC[]; ARITH_TAC]] THEN
        EXPAND_TAC "zf1" THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[WORD_RULE `word_sub x y = z <=> word_add z y = x`] THEN
        REWRITE_TAC[GSYM VAL_CONG; ADD_CLAUSES; VAL_WORD_ADD; VAL_WORD_BITVAL;
                    CONG; DIMINDEX_64] THEN
        CONV_TAC MOD_DOWN_CONV THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
         `--e * c + s = h - i ==> s + i = e * c + h`)) THEN
        SIMP_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_BITVAL; MOD_MULT_ADD];
        ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
      SUBGOAL_THEN `z0 < 2 EXP 64 + 2 * n` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        EXPAND_TAC "q" THEN
        SIMP_TAC[RIGHT_ADD_DISTRIB; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        REWRITE_TAC[REAL_OF_NUM_DIV; REAL_MUL_RZERO; REAL_ADD_RID] THEN
        MATCH_MP_TAC(REAL_ARITH
         `l:real < e /\ m * n <= &1 * n /\
          eh <= (h + q + &1) * n
          ==> (l + eh) - (h + q - m) * n < e + &2 * n`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REPEAT CONJ_TAC THENL
         [BOUNDER_TAC[];
          MATCH_MP_TAC REAL_LE_RMUL THEN
          SIMP_TAC[REAL_POS; REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
          REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[REAL_ARITH
         `e * h <= (h + (w * h) / a + &1) * n <=>
          h * (e - (&1 + w / a) * n) <= n`] THEN
        TRANS_TAC REAL_LE_TRANS `&(val(h:int64)) * &n / &2 pow 64` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN
          UNDISCH_TAC
           `&2 pow 128 <= (&2 pow 64 + &(val(w:int64)) + &1) * &n` THEN
          REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ARITH
           `h * n / &2 pow 64 <= n <=> h * n <= &2 pow 64 * n`] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN
          REWRITE_TAC[REAL_POS] THEN BOUNDER_TAC[]];
        ALL_TAC] THEN

      (*** Second correction ***)

      X86_STEPS_TAC BIGNUM_CDIV_EXEC [18;19] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `z0:num` THEN CONJ_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC `&(bignum_of_wordlist [l; h]) - &q * &n:real = &z0` THEN
        REWRITE_TAC[REAL_EQ_SUB_RADD] THEN
        UNDISCH_TAC `(bignum_of_wordlist[l; h] == a) (mod m)` THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
        UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
        CONV_TAC NUMBER_RULE] THEN
      MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `z1:num` THEN CONJ_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC
         `(if &2 pow 64 <= &z0 then &z0 - &n:real else &z0) = &z1` THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN COND_CASES_TAC THEN
        REWRITE_TAC[REAL_EQ_SUB_RADD] THEN
        REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
        UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
        CONV_TAC NUMBER_RULE] THEN
      MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC `if 2 EXP 64 <= z1 then z1 - n else z1` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EQ_IMP_CONG THEN
        MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
        REWRITE_TAC[VAL_BOUND_64] THEN CONJ_TAC THENL
         [REWRITE_TAC[COND_RAND; COND_RATOR] THEN
          REWRITE_TAC[ARITH_RULE
           `z - n:num < 2 EXP 64 <=> z < n + 2 EXP 64`] THEN
          UNDISCH_TAC `z0 < 2 EXP 64 + 2 * n` THEN
          UNDISCH_TAC `n < 2 EXP 64` THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
          UNDISCH_TAC
           `(if &2 pow 64 <= &z0 then &z0 - &n:real else &z0) = &z1` THEN
          REAL_ARITH_TAC;
          EXPAND_TAC "z1" THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
          REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES;
                      WORD_SUB_0]
          THENL [ALL_TAC; CONV_TAC NUMBER_RULE] THEN
          DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP (ARITH_RULE
           `a <= b ==> !n. n < a ==> n <= b`)) THEN
          ASM_SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB] THEN
          DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[INT_VAL_WORD_SUB_CASES] THEN
          ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
          COND_CASES_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
          CONV_TAC INTEGER_RULE];
        COND_CASES_TAC THEN REWRITE_TAC[CONG_REFL] THEN
        SUBGOAL_THEN `n:num <= z1` MP_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`n < 2 EXP 64`; `2 EXP 64 <= z1`] THEN
          ARITH_TAC;
          SIMP_TAC[num_congruent; GSYM INT_OF_NUM_SUB]] THEN
        UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE];
      ALL_TAC] THEN

    (*** The final one-word reciprocal multiplication ***)

    GHOST_INTRO_TAC `z:int64` `read R14` THEN
    ABBREV_TAC
     `q = ((2 EXP 64 + val(w:int64)) * val(z:int64)) DIV 2 EXP (128 - e)` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_ACCSTEPS_TAC BIGNUM_CDIV_EXEC [2;3] (1--7) THEN
    MP_TAC(ISPEC `word m:int64` WORD_CLZ_LT_DIMINDEX) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM VAL_EQ] THEN
    ASM_REWRITE_TAC[VAL_WORD_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `val(word(e MOD 256):byte) MOD 64 = e /\
      val(word(val(word_xor (word e:int64) (word 63)) MOD 256):byte) MOD 64 =
      63 - e`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [UNDISCH_TAC `e < 64` THEN SPEC_TAC(`e:num`,`e:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      ALL_TAC] THEN
    SUBGOAL_THEN `word_ushr (word n:int64) e = word m` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[word_ushr] THEN
      UNDISCH_THEN `2 EXP e * m = n` (SUBST1_TAC o SYM) THEN
      SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_ushr
        (word_subword (word_ror
          ((word_join:1 word->int64->((1,64)finite_sum)word)
              (word (bitval carry_s3)) sum_s3) 1)
        (0,64)) (63 - e):int64 =
      word q`
    SUBST_ALL_TAC THENL
     [SIMP_TAC[word_ushr; VAL_WORD_SUBWORD; VAL_WORD_JOIN; VAL_WORD_ROR;
               DIMINDEX_64; DIMINDEX_1; ARITH_LE; ARITH_LT;
               DIMINDEX_FINITE_SUM; ARITH_ADD; ARITH_SUC; VAL_WORD_BITVAL] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN; EXP_1; EXP; DIV_1] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
      REWRITE_TAC[EXP_1; ARITH_RULE `65 - 1 = 64`] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN
      SIMP_TAC[MOD_LT; BITVAL_BOUND; VAL_BOUND_64; DIV_DIV; ARITH_RULE
       `c <= 1 /\ s < 2 EXP 64
        ==> 2 EXP 64 * c + s < 2 EXP 65 /\
            (2 EXP 64 * c + s) DIV 2 < 2 EXP 64`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
      ASM_REWRITE_TAC[] THEN
      AP_TERM_TAC THEN EXPAND_TAC "q" THEN
      REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
      SUBGOAL_THEN `128 - e = 64 + SUC(63 - e)` SUBST1_TAC THENL
       [UNDISCH_TAC `e < 64` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[RIGHT_ADD_DISTRIB; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
      ASM_REWRITE_TAC[ARITH_RULE `a + z:num = z + b <=> a = b`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      SIMP_TAC[DIV_LT; VAL_BOUND_64; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[ADD_CLAUSES];
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
    SUBGOAL_THEN `q * m:num <= val(z:int64)` ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= m * n /\ (n * q) * inv e <= z ==> (q / e - m) * n <= z`) THEN
      SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LE_DIV; REAL_LE_MUL] THEN
      SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POS; REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH_EQ;
                   ARITH_RULE `e <= 64 ==> e <= 128`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(m * ww) * e:real = (e * m) * ww`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `q < 2 EXP 64 /\ q * m < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `!z. q * m <= z /\ z < e /\ q * 1 <= q * m
            ==> q < e /\ q * m < e`) THEN
      EXISTS_TAC `val(z:int64)` THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL; VAL_BOUND_64] THEN ASM_SIMP_TAC[LE_1];
      ALL_TAC] THEN
    X86_STEPS_TAC BIGNUM_CDIV_EXEC (8--9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    REABBREV_TAC `z' = read R14 s9` THEN
    SUBGOAL_THEN
     `val(z':int64) < 2 * m /\ a MOD m = val(z':int64) MOD m`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THENL
     [SUBGOAL_THEN `val(z':int64) = val(z:int64) - q * m` SUBST1_TAC THENL
      [EXPAND_TAC "z'" THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
       ASM_SIMP_TAC[GSYM WORD_MUL; VAL_WORD_EQ; DIMINDEX_64];
       ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `q * m <= a /\ a < (q + 2) * m ==> a - q * m < 2 * m`) THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "q" THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
        MATCH_MP_TAC(REAL_ARITH
         `m * n <= &1 * n /\ z < (q + &1) * n
          ==> z:real < (q - m + &2) * n`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_LT_POW2] THEN
          REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
          SIMP_TAC[MOD_LT_EQ; LT_IMP_LE; EXP_EQ_0; ARITH_EQ];
          ASM_SIMP_TAC[REAL_POS; REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH_EQ;
                       ARITH_RULE `e <= 64 ==> e <= 128`] THEN
          REWRITE_TAC[REAL_FIELD
           `(wz / (&2 pow d / &2 pow e) + &1) * m =
            (wz / &2 pow d + &1 / &2 pow e) * (&2 pow e * m)`] THEN
          ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
          REWRITE_TAC[REAL_ARITH `z < ((ww * z) / &2 pow 128 + e) * n <=>
                         z * (&2 pow 128 - ww * n) < &2 pow 128 * e * n`] THEN
          TRANS_TAC REAL_LET_TRANS `&(val(z:int64)) * &n` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
          ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1] THEN
          TRANS_TAC REAL_LTE_TRANS `(&2:real) pow 64` THEN
          SIMP_TAC[REAL_OF_NUM_CLAUSES; VAL_BOUND_64] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; real_div; REAL_MUL_LID] THEN
          ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
          REWRITE_TAC[GSYM REAL_POW_ADD] THEN
          MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
          UNDISCH_TAC `e <= 64` THEN ARITH_TAC];
        UNDISCH_TAC `(val(z:int64) == a) (mod m)` THEN
        ASM_REWRITE_TAC[GSYM CONG; num_congruent] THEN
        ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE];
      ASM_SIMP_TAC[MOD_CASES]] THEN
    X86_STEPS_TAC BIGNUM_CDIV_EXEC (10--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0] THEN
    ASM_REWRITE_TAC[WORD_SUB; WORD_VAL];

    ALL_TAC] THEN

  (*** Degenerate case when output size is zero ***)

  ASM_CASES_TAC `k = 0` THENL
   [ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    X86_SIM_TAC BIGNUM_CDIV_EXEC (1--3) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Introduce the initial decomposition into m = 2^e * m', replace m ***)

  ABBREV_TAC `e = index 2 m` THEN
  SUBGOAL_THEN `e < 64` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC INDEX_LT THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    VAL_INT64_TAC `e:num`] THEN

  MP_TAC(SPECL [`m:num`; `2`] INDEX_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; ARITH_EQ; DIVIDES_2; NOT_EVEN] THEN
  X_GEN_TAC `m':num` THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`m':num`,`m:num`) THEN X_GEN_TAC `m:num` THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN

  SUBGOAL_THEN `m < 2 EXP 64` ASSUME_TAC THENL
   [TRANS_TAC LET_TRANS `2 EXP e * m` THEN
    ASM_REWRITE_TAC[ARITH_RULE `m <= e * m <=> 1 * m <= e * m`] THEN
    SIMP_TAC[LE_MULT_RCANCEL; LE_1; EXP_EQ_0; ARITH_EQ];
    VAL_INT64_TAC `m:num`] THEN

  (*** Verify the initial breakdown computation ***)

  ENSURES_SEQUENCE_TAC `pc + 0x18c`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R9 s = word n /\
        read R10 s = x /\
        bignum_from_memory (x,n) s = a /\
        read R8 s = word m /\
        (~(m = 0) ==> read RCX s = word e) /\
        (~(m = 0) ==> read R15 s = word (a MOD (2 EXP e * m)))` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_CDIV_EXEC (1--4) THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; WORD_USHR_0] THEN
    ASM_REWRITE_TAC[WORD_CTZ_INDEX; GSYM VAL_EQ_0; MULT_EQ_0;
                    EXP_EQ_0; ARITH_EQ; MOD_64_CLAUSES; MOD_LT] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR] THEN
    ASM_SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ; MOD_LT];
    ALL_TAC] THEN

  (*** The negated modular inverse computation ****)

  ENSURES_SEQUENCE_TAC `pc + 0x1e4`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R9 s = word n /\
        read R10 s = x /\
        bignum_from_memory (x,n) s = a /\
        read R8 s = word m /\
        (~(m = 0) ==> read R15 s = word (a MOD (2 EXP e * m))) /\
        (~(m = 0) ==> read RCX s = word e) /\
        (~(m = 0) ==> (m * val(read R11 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_CDIV_EXEC (1--23) THEN
    DISCH_TAC THEN UNDISCH_TAC `m = 0 \/ ODD m` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MP_TAC(SPEC `m:num` WORD_NEGMODINV_SEED_LEMMA_16) THEN
    ASM_REWRITE_TAC[FORALL_UNWIND_THM1] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; CONG; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `16 = 2 EXP 4`) THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 2 EXP 4 EXP 16`) THEN
    SPEC_TAC(`2 EXP 4`,`p:num`) THEN CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:int64` `read R11` THEN GLOBALIZE_PRECONDITION_TAC] THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x204` `pc + 0x23d`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read R9 s = word(if n = 0 then 0 else n - 1) /\
          read R10 s = (if n = 0 then x else word_add x (word 8)) /\
          read R8 s = word m /\
          (~(m = 0) ==> read R15 s = word (a MOD (2 EXP e * m))) /\
          (~(m = 0) ==> read RCX s = word e) /\
          read R11 s = w /\
          read RBX s = word i /\
          (~(m = 0) ==> read R12 s = word(bigdigit a i)) /\
          bignum_from_memory(word_add x (word (8 * i)),MIN n (k + 1) - i) s =
          highdigits (lowdigits a (k + 1)) i /\
          (~(m = 0)
           ==> &(lowdigits (a DIV 2 EXP e) i) +
               (&2 pow (64 * i) - &(bignum_from_memory(z,i) s)) * &m:real =
               &2 pow (64 * i) * &(val(read R13 s)) +
               &((a DIV 2 EXP e) MOD m))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
      GHOST_INTRO_TAC `ee:int64` `read RCX` THEN
      GHOST_INTRO_TAC `rr:int64` `read R15` THEN
      X86_SIM_TAC BIGNUM_CDIV_EXEC (1--8) THEN
      ASM_SIMP_TAC[ARITH_RULE `MIN 0 n = 0`; LOWDIGITS_0; SUB_0] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; DIV_0; BIGDIGIT_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL;
                  LOWDIGITS_TRIVIAL; HIGHDIGITS_0] THEN
      ASM_REWRITE_TAC[MOD_0; WORD_USHR_0; WORD_SUB_0] THEN
      REWRITE_TAC[LOWDIGITS_0; MULT_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    GHOST_INTRO_TAC `ee:int64` `read RCX` THEN
    GHOST_INTRO_TAC `rr:int64` `read R15` THEN
    REWRITE_TAC[HIGHDIGITS_0; MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    REWRITE_TAC[GSYM LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `read (memory :> bytes64 x) s0 = word(bigdigit a 0)`
    ASSUME_TAC THENL
     [EXPAND_TAC "a" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      ASM_SIMP_TAC[LE_1; MULT_CLAUSES; WORD_ADD_0; WORD_VAL];
      ALL_TAC] THEN
    X86_STEPS_TAC BIGNUM_CDIV_EXEC (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; LE] THEN
    ASM_SIMP_TAC[WORD_SUB; LE_1; word_jushr; DIMINDEX_64; MOD_LT] THEN
    REWRITE_TAC[word_ushr; VAL_WORD_BIGDIGIT] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
    ASM_SIMP_TAC[MOD_64_CLAUSES; MOD_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `a MOD (2 EXP e * m) < 2 EXP dimindex(:64)` MP_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o lhand) MOD_LT_EQ o lhand o snd) THEN
      ASM_REWRITE_TAC[DIMINDEX_64; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
      ASM_SIMP_TAC[LT_IMP_LE];
      SIMP_TAC[VAL_WORD_EQ] THEN
      REWRITE_TAC[GSYM DIV_MOD; DIMINDEX_64] THEN DISCH_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_ADD_LID] THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
    SUBGOAL_THEN `(a DIV 2 EXP e) MOD m < 2 EXP dimindex(:64)` MP_TAC THENL
     [TRANS_TAC LET_TRANS `m:num` THEN
      ASM_SIMP_TAC[LT_IMP_LE; MOD_LT_EQ; DIMINDEX_64];
      ASM_SIMP_TAC[VAL_WORD_EQ; LT_IMP_LE; MOD_LT_EQ;
                   GSYM REAL_OF_NUM_SUB] THEN
      REAL_ARITH_TAC];

    ALL_TAC; (*** The main loop invariant ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_CDIV_EXEC (1--2);

    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THENL
     [X86_SIM_TAC BIGNUM_CDIV_EXEC (1--3);
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
      UNDISCH_TAC `m = 0 \/ ODD m` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC] THEN
    GHOST_INTRO_TAC `c:int64` `read R13` THEN
    GHOST_INTRO_TAC `q:num` `bignum_from_memory (z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `q:num` THEN
    X86_SIM_TAC BIGNUM_CDIV_EXEC (1--3) THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * k)` THEN
    ASM_REWRITE_TAC[LOWDIGITS_BOUND] THEN
    MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2] THEN
    MATCH_MP_TAC CONG_ADD_RCANCEL THEN EXISTS_TAC `(a DIV 2 EXP e) MOD m` THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `lowdigits (a DIV 2 EXP e) k` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN FIRST_ASSUM(SUBST1_TAC o
        MATCH_MP(REAL_ARITH
         `l + (e - q) * m:real = e * c + r
          ==> (m * q + r) - l = e * (m - c)`)) THEN
      REWRITE_TAC[REAL_FIELD `(&2 pow e * a) / &2 pow e = a`] THEN
      REAL_INTEGER_TAC;
      REWRITE_TAC[CONG; lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[GSYM DIV_DIV] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      ASM_SIMP_TAC[GSYM DIVIDES_DIV_MULT; DIVIDES_DIVIDES_DIV_IMP] THEN
      REWRITE_TAC[DIVISION_SIMP]]] THEN

  (*** Start tackling the main loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `c:int64` `read R13` THEN
  GHOST_INTRO_TAC `q:num` `bignum_from_memory (z,i)` THEN
  BIGNUM_TERMRANGE_TAC `i:num` `q:num` THEN GLOBALIZE_PRECONDITION_TAC THEN

  (*** The optional load depending on whether i < n ***)

  ENSURES_SEQUENCE_TAC `pc + 0x210`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R9 s = word(if n = 0 then 0 else n - 1) /\
        read R10 s = (if n = 0 then x else word_add x (word 8)) /\
        read R8 s = word m /\
        (~(m = 0) ==> read R15 s = word (a MOD (2 EXP e * m))) /\
        (~(m = 0) ==> read RCX s = word e) /\
        read R11 s = w /\
        read RBX s = word i /\
        (~(m = 0) ==> read R12 s = word(bigdigit a i)) /\
        bignum_from_memory(word_add x (word (8 * i)),MIN n (k + 1) - i) s =
        highdigits (lowdigits a (k + 1)) i /\
        read R13 s = c /\
        bignum_from_memory (z,i) s = q /\
        read R14 s = word(bigdigit a (i + 1))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `val(word(if n = 0 then 0 else n - 1):int64) <= i <=>
                  ~(i + 1 < n)`
    MP_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; LT; LE_0] THEN
      ASM_SIMP_TAC[WORD_SUB; LE_1; VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
      UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN

    ASM_CASES_TAC `i + 1 < n` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read (memory :> bytes64(word_add x (word(8 + 8 * i)))) s0 =
        word(bigdigit (highdigits (lowdigits a (k + 1)) i) 1)`
      MP_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_SIMP_TAC[ARITH_RULE
         `i + 1 < n /\ i < k ==> 1 < MIN n (k + 1) - i`] THEN
        REWRITE_TAC[WORD_VAL] THEN AP_THM_TAC THEN
        REPLICATE_TAC 3 AP_TERM_TAC THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[BIGDIGIT_HIGHDIGITS; BIGDIGIT_LOWDIGITS] THEN
        ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `~(n = 0)`
       (fun th -> REWRITE_TAC[th] THEN
                  RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
       [UNDISCH_TAC `i + 1 < n` THEN ARITH_TAC; ALL_TAC] THEN
      X86_STEPS_TAC BIGNUM_CDIV_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      X86_SIM_TAC BIGNUM_CDIV_EXEC (1--3) THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BIGDIGIT_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
      UNDISCH_TAC `~(i + 1 < n)` THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Now the main Montgomery part ***)

  GHOST_INTRO_TAC `d:int64` `read R12` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS_ALT] THEN
  REWRITE_TAC[ARITH_RULE `n - i - 1 = n - (i + 1)`] THEN
  SUBGOAL_THEN
   `nonoverlapping (word_add z (word (8 * i):int64),8)
            (word_add x (word (8 * (i + 1))),8 * (MIN n (k + 1) - (i + 1)))`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [ASM_CASES_TAC `i + 1 < MIN n (k + 1)` THENL
     [NONOVERLAPPING_TAC;
      ASM_SIMP_TAC[ARITH_RULE `~(i < n) ==> 8 * (n - i) = 0`] THEN
      REWRITE_TAC[nonoverlapping_modulo; LT]];
    DISCH_TAC] THEN
  UNDISCH_THEN `val(word m:int64) = m` (K ALL_TAC) THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THENL
   [X86_SIM_TAC BIGNUM_CDIV_EXEC (1--14) THEN REWRITE_TAC[WORD_ADD];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  UNDISCH_TAC `m = 0 \/ ODD m` THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  X86_ACCSIM_TAC BIGNUM_CDIV_EXEC [2;10;11;12] (1--14) THEN
  ASM_REWRITE_TAC
   [REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES] BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL] THEN
  ASM_SIMP_TAC[MOD_64_CLAUSES; MOD_LT; GSYM WORD_BIGDIGIT_DIV; LT_IMP_LE] THEN
  ASM_SIMP_TAC[VAL_WORD_BIGDIGIT; VAL_WORD_EQ; DIMINDEX_64;
               WORD_NEG_NEG; VAL_WORD_BITVAL] THEN
  REWRITE_TAC[REAL_ARITH `e - &1 - (e - &1 - x):real = x`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * (i + 1) + 64`; `&0:real`] THEN
  REWRITE_TAC[REAL_POW_ADD; INTEGER_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= l /\ &0 <= q * m /\ &0 <= e * m /\
      q * m < e * m /\ l + e * m < e * &2 pow 64
      ==> &0 <= l + (e - q) * m /\ l + (e - q) * m < e * &2 pow 64`) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN BOUNDER_TAC[];
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1] THEN
      REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= ee * v /\ q < ee ==> q + ee * (e - &1 - v) < ee * e`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN EXPAND_TAC "q" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
      MATCH_MP_TAC(REAL_ARITH
       `l < e /\ e * (m + &1) <= e * &2 pow 64
        ==> l + e * m < e * &2 pow 64`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; LOWDIGITS_BOUND] THEN
      REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m + 1 <= 2 EXP 64 <=> m < 2 EXP 64`]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[LE_0] THEN MATCH_MP_TAC(ARITH_RULE
     `e * s <= e * (2 EXP 64 - 1) /\ r < e ==> e * s + r < e * 2 EXP 64`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[VAL_BOUND_64; ARITH_RULE `a < n ==> a <= n - 1`] THEN
    TRANS_TAC LTE_TRANS `m:num` THEN ASM_REWRITE_TAC[MOD_LT_EQ] THEN
    TRANS_TAC LE_TRANS `2 EXP 64` THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `l + q * m:real = e * c + r ==> l = (e * c + r) - q * m`)) THEN
  REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  REWRITE_TAC[REAL_INV_MUL; real_div] THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  REWRITE_TAC[REAL_ARITH
   `x * inv(&2 pow e) = inv(&2 pow e) * x /\
    x * inv(&2 pow e) * y = inv(&2 pow e) * x * y`] THEN
  REWRITE_TAC[REAL_ARITH
   `x * &2 pow e = &2 pow e * x /\ x * &2 pow e * y = &2 pow e * x * y`] THEN
  REWRITE_TAC[REAL_FIELD `&2 pow e * inv(&2 pow e) * x = x`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `e * h + l = &(bigdigit a i) + c ==> &(bigdigit a i) = e * h + l - c`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `&2 pow 64 * b + s = x ==> s = x - &2 pow 64 * b`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `&2 pow 64 * b + s = x + y
    ==> (&2 pow 64 * b + s = x + y ==> s = &0)
        ==> y = &2 pow 64 * b - x`)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 64 * c + s = x ==> s = x - &2 pow 64 * c`)) THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
      `e * c + s:real = qm - e * h + t ==> e * (c + h) + s = qm + t`)) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
    SIMP_TAC[DIMINDEX_64; MOD_MULT_ADD; VAL_WORD_MUL; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `(w * s) * m + s = (m * w + 1) * s`] THEN
    SIMP_TAC[MOD_LT; VAL_BOUND_64] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM DIVIDES_MOD] THEN
    UNDISCH_TAC `(m * val(w:int64) + 1 == 0) (mod (2 EXP 64))` THEN
    SPEC_TAC(`2 EXP 64`,`p:num`) THEN CONV_TAC NUMBER_RULE;
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 64 * b + s = x ==> s = x - &2 pow 64 * b`)) THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN REAL_INTEGER_TAC]);;

let BIGNUM_CDIV_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z n x m a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_cdiv_tmc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cdiv_tmc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cdiv_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (~(val m = 0)
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k) /\
                       C_RETURN s = word(a MOD val m)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                       memory :> bytes(word_sub stackpointer (word 40),40)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_cdiv_tmc BIGNUM_CDIV_CORRECT
    `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_CDIV_SUBROUTINE_CORRECT = prove
 (`!k z n x m a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 40),48) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
            [(word pc,LENGTH bignum_cdiv_mc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cdiv_mc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cdiv_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (~(val m = 0)
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k) /\
                       C_RETURN s = word(a MOD val m)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                       memory :> bytes(word_sub stackpointer (word 40),40)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CDIV_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cdiv_windows_mc = define_from_elf
   "bignum_cdiv_windows_mc" "x86/generic/bignum_cdiv.obj";;

let bignum_cdiv_windows_tmc = define_trimmed "bignum_cdiv_windows_tmc" bignum_cdiv_windows_mc;;

let BIGNUM_CDIV_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n x m a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_cdiv_windows_tmc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cdiv_windows_tmc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cdiv_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (~(val m = 0)
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k) /\
                       WINDOWS_C_RETURN s = word(a MOD val m)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                       memory :> bytes(word_sub stackpointer (word 56),56)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_cdiv_windows_tmc bignum_cdiv_tmc
    BIGNUM_CDIV_CORRECT `[RBX; R12; R13; R14; R15]` 40);;

let BIGNUM_CDIV_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n x m a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 56),64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_cdiv_windows_mc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cdiv_windows_mc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cdiv_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (~(val m = 0)
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k) /\
                       WINDOWS_C_RETURN s = word(a MOD val m)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                       memory :> bytes(word_sub stackpointer (word 56),56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CDIV_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

