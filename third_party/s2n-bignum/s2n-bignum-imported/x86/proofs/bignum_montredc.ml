(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery reduction of arbitrary bignum.                                 *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_montredc.o";;
 ****)

let bignum_montredc_mc =
  define_assert_from_elf "bignum_montredc_mc" "x86/generic/bignum_montredc.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x83; 0xec; 0x08;  (* SUB (% rsp) (Imm8 (word 8)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x0f; 0x84; 0x57; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 343)) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x49; 0xc1; 0xe6; 0x02;  (* SHL (% r14) (Imm8 (word 2)) *)
  0x4c; 0x29; 0xf3;        (* SUB (% rbx) (% r14) *)
  0x48; 0x83; 0xf3; 0x02;  (* XOR (% rbx) (Imm8 (word 2)) *)
  0x49; 0x89; 0xde;        (* MOV (% r14) (% rbx) *)
  0x4c; 0x0f; 0xaf; 0xf0;  (* IMUL (% r14) (% rax) *)
  0xb8; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 2)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x49; 0x83; 0xc6; 0x01;  (* ADD (% r14) (Imm8 (word 1)) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x4d; 0x0f; 0xaf; 0xf6;  (* IMUL (% r14) (% r14) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x4d; 0x0f; 0xaf; 0xf6;  (* IMUL (% r14) (% r14) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x4d; 0x0f; 0xaf; 0xf6;  (* IMUL (% r14) (% r14) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x4c; 0x01; 0xf0;        (* ADD (% rax) (% r14) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x48; 0x89; 0x1c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rbx) *)
  0x48; 0x89; 0xfb;        (* MOV (% rbx) (% rdi) *)
  0x49; 0x39; 0xfa;        (* CMP (% r10) (% rdi) *)
  0x49; 0x0f; 0x42; 0xda;  (* CMOVB (% rbx) (% r10) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x85; 0xdb;        (* TEST (% rbx) (% rbx) *)
  0x74; 0x18;              (* JE (Imm8 (word 24)) *)
  0x4a; 0x8b; 0x04; 0xf1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r14))) *)
  0x4a; 0x89; 0x04; 0xf6;  (* MOV (Memop Quadword (%%% (rsi,3,r14))) (% rax) *)
  0x49; 0xff; 0xc6;        (* INC (% r14) *)
  0x49; 0x39; 0xde;        (* CMP (% r14) (% rbx) *)
  0x72; 0xf0;              (* JB (Imm8 (word 240)) *)
  0x49; 0x39; 0xfe;        (* CMP (% r14) (% rdi) *)
  0x73; 0x0f;              (* JAE (Imm8 (word 15)) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x4a; 0x89; 0x1c; 0xf6;  (* MOV (Memop Quadword (%%% (rsi,3,r14))) (% rbx) *)
  0x49; 0xff; 0xc6;        (* INC (% r14) *)
  0x49; 0x39; 0xfe;        (* CMP (% r14) (% rdi) *)
  0x72; 0xf4;              (* JB (Imm8 (word 244)) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x4d; 0x85; 0xc9;        (* TEST (% r9) (% r9) *)
  0x74; 0x78;              (* JE (Imm8 (word 120)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x4c; 0x8b; 0x26;        (* MOV (% r12) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x2c; 0x24;  (* MOV (% rbp) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x0f; 0xaf; 0xec;  (* IMUL (% rbp) (% r12) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x01; 0xe0;        (* ADD (% rax) (% r12) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0xbb; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 1)) *)
  0x49; 0x89; 0xfd;        (* MOV (% r13) (% rdi) *)
  0x49; 0xff; 0xcd;        (* DEC (% r13) *)
  0x74; 0x24;              (* JE (Imm8 (word 36)) *)
  0x4c; 0x13; 0x1c; 0xde;  (* ADC (% r11) (Memop Quadword (%%% (rsi,3,rbx))) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x49; 0x8b; 0x04; 0xd8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,rbx))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x44; 0xde; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rbx,-- &8))) (% rax) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x49; 0xff; 0xcd;        (* DEC (% r13) *)
  0x75; 0xdc;              (* JNE (Imm8 (word 220)) *)
  0x4d; 0x11; 0xfb;        (* ADC (% r11) (% r15) *)
  0x41; 0xbf; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r15d) (Imm32 (word 0)) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x4c; 0x01; 0xf3;        (* ADD (% rbx) (% r14) *)
  0x4c; 0x39; 0xd3;        (* CMP (% rbx) (% r10) *)
  0x73; 0x0b;              (* JAE (Imm8 (word 11)) *)
  0x48; 0x8b; 0x04; 0xd9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,rbx))) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5c; 0xfe; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rdi,-- &8))) (% r11) *)
  0x49; 0xff; 0xc6;        (* INC (% r14) *)
  0x4d; 0x39; 0xce;        (* CMP (% r14) (% r9) *)
  0x72; 0x8b;              (* JB (Imm8 (word 139)) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x89; 0xfa;        (* MOV (% r10) (% rdi) *)
  0x48; 0x8b; 0x04; 0xde;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,rbx))) *)
  0x49; 0x1b; 0x04; 0xd8;  (* SBB (% rax) (Memop Quadword (%%% (r8,3,rbx))) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x49; 0xff; 0xca;        (* DEC (% r10) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0x49; 0x83; 0xdf; 0x00;  (* SBB (% r15) (Imm8 (word 0)) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x48; 0xf7; 0xd5;        (* NOT (% rbp) *)
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x8b; 0x04; 0xd8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,rbx))) *)
  0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
  0x49; 0xf7; 0xdc;        (* NEG (% r12) *)
  0x48; 0x19; 0x04; 0xde;  (* SBB (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xe7;              (* JB (Imm8 (word 231)) *)
  0x48; 0x83; 0xc4; 0x08;  (* ADD (% rsp) (Imm8 (word 8)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_montredc_tmc = define_trimmed "bignum_montredc_tmc" bignum_montredc_mc;;

let BIGNUM_MONTREDC_EXEC = X86_MK_CORE_EXEC_RULE bignum_montredc_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

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

let BIGNUM_MONTREDC_CORRECT = time prove
 (`!k z r x m p a n pc stackpointer.
        ALL (nonoverlapping (stackpointer,8))
            [(word pc,0x17d); (x,8 * val r); (m,8 * val k); (z,8 * val k)] /\
        ALL (nonoverlapping (z,8 * val k)) [(word pc,0x17d); (m,8 * val k)] /\
        (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
        val p < 2 EXP 61 /\ val r < 2 EXP 61
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_montredc_tmc) /\
                  read RIP s = word(pc + 0xe) /\
                  read RSP s = stackpointer /\
                  C_ARGUMENTS [k; z; r; x; m; p] s /\
                  bignum_from_memory (x,val r) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = word(pc + 0x16e) /\
                  (ODD n /\
                   lowdigits a (val k + val p) <= 2 EXP (64 * val p) * n
                   ==> bignum_from_memory (z,val k) s =
                       (inverse_mod n (2 EXP (64 * val p)) *
                        lowdigits a (val k + val p)) MOD n))
             (MAYCHANGE [RIP; RAX; RBX; RBP; RDX;
                         R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(stackpointer,8)] ,,
              MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `nx:num` THEN X_GEN_TAC `x:int64` THEN
  X_GEN_TAC `m:int64` THEN W64_GEN_TAC `p:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  X_GEN_TAC `stackpointer:int64` THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  BIGNUM_TERMRANGE_TAC `nx:num` `a:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ODD];
    ALL_TAC] THEN

  (*** Initial word-level modular inverse ***)

  ENSURES_SEQUENCE_TAC `pc + 0x75`
   `\s. read RSP s = stackpointer /\
        read RDI s = word k /\
        read RSI s = z /\
        read R10 s = word nx /\
        read RCX s = x /\
        read R8 s = m /\
        read R9 s = word p /\
        bignum_from_memory (x,nx) s = a /\
        bignum_from_memory (m,k) s = n /\
        (ODD n ==> (n * val(read RBX s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `bignum_from_memory(m,k) s0 = highdigits n 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC LAND_CONV[BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC] THEN
    X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--9) THEN
    SUBGOAL_THEN `ODD n ==> (n * val (read RBX s9) + 1 == 0) (mod 16)`
    MP_TAC THENL [ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16]; ALL_TAC] THEN
    REABBREV_TAC `x0 = read RBX s9` THEN DISCH_TAC THEN
    X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (10--27) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:num` `\s. val(read RBX s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64]] THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  VAL_INT64_TAC `w:num` THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_1)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Initialization of the output buffer ***)

  ENSURES_SEQUENCE_TAC `pc + 0xb2`
   `\s. read RSP s = stackpointer /\
        read RDI s = word k /\
        read RSI s = z /\
        read R10 s = word nx /\
        read RCX s = x /\
        read R8 s = m /\
        read R9 s = word p /\
        bignum_from_memory (word_add x (word (8 * k)),nx - k) s =
        highdigits a k /\
        bignum_from_memory (m,k) s = n /\
        read (memory :> bytes64 stackpointer) s = word w /\
        bignum_from_memory (z,k) s = lowdigits a k /\
        read R15 s = word 0` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `nx = 0` THENL
     [UNDISCH_THEN `nx = 0` SUBST_ALL_TAC THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
      ENSURES_WHILE_UP_TAC `k:num` `pc + 0xa3` `pc + 0xaa`
       `\i s. read RSP s = stackpointer /\
              read RDI s = word k /\
              read RSI s = z /\
              read R10 s = word 0 /\
              read RCX s = x /\
              read R8 s = m /\
              read R9 s = word p /\
              bignum_from_memory (m,k) s = n /\
              read (memory :> bytes64 stackpointer) s = word w /\
              read R14 s = word i /\
              read RBX s = word 0 /\
              bignum_from_memory (z,i) s = 0` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--7) THEN
        ASM_SIMP_TAC[LE_1; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
        ARITH_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--2);
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--3) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[LOWDIGITS_TRIVIAL] THEN
        REWRITE_TAC[LE; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; SUB_0] THEN
        REWRITE_TAC[HIGHDIGITS_TRIVIAL]];
      ALL_TAC] THEN

    (*** Copyloop ***)

    ENSURES_WHILE_UP_TAC `MIN k nx` `pc + 0x8b` `pc + 0x96`
     `\i s. read RSP s = stackpointer /\
            read RDI s = word k /\
            read RSI s = z /\
            read R10 s = word nx /\
            read RCX s = x /\
            read R8 s = m /\
            read R9 s = word p /\
            bignum_from_memory (m,k) s = n /\
            read (memory :> bytes64 stackpointer) s = word w /\
            read R14 s = word i /\
            read RBX s = word(MIN k nx) /\
            bignum_from_memory(word_add x (word(8 * i)),nx - i) s =
            highdigits a i /\
            bignum_from_memory (z,i) s = lowdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `MIN a b = 0 <=> a = 0 \/ b = 0`];
      X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--7) THEN
      MATCH_MP_TAC(TAUT `q /\ (q ==> p) /\ r ==> p /\ q /\ r`) THEN
      CONJ_TAC THENL [REWRITE_TAC[MIN] THEN MESON_TAC[NOT_LT]; ALL_TAC] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      DISCH_THEN SUBST1_TAC THEN VAL_INT64_TAC `MIN k nx` THEN
      ASM_REWRITE_TAC[ARITH_RULE `MIN a b = 0 <=> a = 0 \/ b = 0`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `i:num < nx /\ i < k` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
      VAL_INT64_TAC `MIN k nx` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    (*** Now consider the cases again ***)

    ASM_CASES_TAC `k:num <= nx` THENL
     [ASM_SIMP_TAC[ARITH_RULE `k <= nx ==> MIN k nx = k`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
      ASM_SIMP_TAC[ARITH_RULE `nx < k ==> MIN k nx = nx`]] THEN

    (*** Padloop following copyloop ***)

    ENSURES_WHILE_AUP_TAC `nx:num` `k:num` `pc + 0xa3` `pc + 0xaa`
     `\i s. read RSP s = stackpointer /\
            read RDI s = word k /\
            read RSI s = z /\
            read R10 s = word nx /\
            read RCX s = x /\
            read R8 s = m /\
            read R9 s = word p /\
            bignum_from_memory (m,k) s = n /\
            read (memory :> bytes64 stackpointer) s = word w /\
            read R14 s = word i /\
            read RBX s = word 0 /\
            bignum_from_memory (z,i) s = lowdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--5);
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      SIMP_TAC[VAL_WORD_0; LOWDIGITS_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
      MATCH_MP_TAC(NUM_RING `d = 0 ==> a = e * d + a`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num <= i` THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--2);
      X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--3) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_SIMP_TAC[ARITH_RULE `nx < k ==> nx - k = 0`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC HIGHDIGITS_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num < k` THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Break at "corrective" to share degenerate cases, corrective ending ***)

  ENSURES_SEQUENCE_TAC `pc + 0x12f`
   `\s. read RSP s = stackpointer /\
        read RDI s = word k /\
        read RSI s = z /\
        read R8 s = m /\
        bignum_from_memory (m,k) s = n /\
        ?q r.
           q < 2 EXP (64 * p) /\
           r < 2 EXP (64 * p) /\
           2 EXP (64 * p) *
           (2 EXP (64 * k) * val(read R15 s) + bignum_from_memory(z,k) s) + r =
           q * n + lowdigits a (k + p) /\
           (ODD n ==> r = 0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `cout:num` `\s. val(read R15 s)` THEN
    GHOST_INTRO_TAC `mm:num` `bignum_from_memory(z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `mm:num` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `cout < 2` MP_TAC THENL
     [SUBGOAL_THEN `q * n + lowdigits a (k + p) < 2 EXP (64 * (k + p)) * 2`
      MP_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x < e /\ y < e ==> x + y < e * 2`) THEN
        REWRITE_TAC[LOWDIGITS_BOUND] THEN
        REWRITE_TAC[ARITH_RULE `64 * (k + p) = 64 * p + 64 * k`] THEN
        ASM_SIMP_TAC[LT_MULT2; EXP_ADD];
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
        REWRITE_TAC[ARITH_RULE `64 * k + 64 * p = 64 * (p + k)`] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `a + b:num < c ==> a < c`)) THEN
        REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
        REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
      GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT]] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:bool` SUBST_ALL_TAC) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN

    (*** Comparison operation "cmploop" ***)

    ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x135` `pc + 0x143`
    `\i s. (read RDI s = word k /\
            read RSI s = z /\
            read R8 s = m /\
            bignum_from_memory (z,k) s = mm /\
            bignum_from_memory (m,k) s = n /\
            read RBX s = word i /\
            read R10 s = word(k - i) /\
            read R15 s = word(bitval c0) /\
            bignum_from_memory (word_add z (word(8 * i)),k - i) s =
            highdigits mm i /\
            bignum_from_memory (word_add m (word(8 * i)),k - i) s =
            highdigits n i /\
            (read CF s <=> lowdigits mm i < lowdigits n i)) /\
           (read ZF s <=> i = k)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; LT_REFL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_ADD] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES];
       REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
       VAL_INT64_TAC `k - i:num` THEN
       ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1] THEN ARITH_TAC] THEN
     SIMP_TAC[LEXICOGRAPHIC_LT; LOWDIGITS_BOUND] THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN ARITH_TAC;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MONTREDC_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

     (*** Corrective subtraction "corrloop" ***)

    ABBREV_TAC `c <=> n <= 2 EXP (64 * k) * bitval c0 + mm` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x155` `pc + 0x169`
     `\i s. read RDI s = word k /\
            read RSI s = z /\
            read R8 s = m /\
            read RBP s = word_neg(word(bitval c)) /\
            read RBX s = word i /\
            val(word_neg(read R12 s)) <= 1 /\
            bignum_from_memory (word_add z (word(8 * i)),k - i) s =
            highdigits mm i /\
            bignum_from_memory (word_add m (word(8 * i)),k - i) s =
            highdigits n i /\
            &(bignum_from_memory(z,i) s):real =
            &2 pow (64 * i) * &(val(word_neg(read R12 s))) +
            &(lowdigits mm i) - &(bitval c) * &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB_LZERO; SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BITVAL_CLAUSES; WORD_NEG_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0; VAL_WORD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0; LE_0] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_SUB_REFL] THEN
      REWRITE_TAC[WORD_NOT_MASK] THEN EXPAND_TAC "c" THEN
      REPLICATE_TAC 3 AP_TERM_TAC THEN REWRITE_TAC[NOT_LT; ADD_CLAUSES] THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN BOOL_CASES_TAC `c0:bool` THEN
      REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
      ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> n <= e + m`; BITVAL_BOUND] THEN
      REWRITE_TAC[CONJUNCT1 LE; BITVAL_EQ_0; NOT_LT];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read R12 s))` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
       GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
      REWRITE_TAC[VAL_EQ_BITVAL] THEN
      REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_MONTREDC_EXEC [4] (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[WORD_NEG_NEG; VAL_WORD_BITVAL; BITVAL_BOUND] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                  LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
      REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
               BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_SELF] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      STRIP_TAC THEN UNDISCH_TAC `ODD n ==> r = 0` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (MESON[ODD] `ODD n ==> ~(n = 0)`)) THEN
    TRANS_TAC EQ_TRANS `(2 EXP (64 * k) * bitval c0 + mm) MOD n` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND; LE_0];
        REWRITE_TAC[INTEGER_CLOSED; REAL_POS]] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN TRANS_TAC LT_TRANS `n:num` THEN
        ASM_REWRITE_TAC[MOD_LT_EQ];
        ALL_TAC] THEN
      MP_TAC(SPECL [`2 EXP (64 * k) * bitval c0 + mm`; `n:num`]
        MOD_CASES) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC(MESON[LT_MULT_LCANCEL]
         `!e. ~(e = 0) /\ e * a < e * b ==> a < b`) THEN
        EXISTS_TAC `2 EXP (64 * p)` THEN
        ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
        MATCH_MP_TAC(ARITH_RULE
         `q * n < e * n /\ aa <= e * n ==> q * n + aa < e * 2 * n`) THEN
        ASM_REWRITE_TAC[LT_MULT_RCANCEL];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
      SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_CASES_TAC `c:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
      REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN
      SIMP_TAC[REAL_MUL_LINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      REAL_INTEGER_TAC;
      REWRITE_TAC[GSYM CONG] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
         `e * x:num = q * n + ab
          ==> (i * e == 1) (mod n)
              ==> (x == i * ab) (mod n)`)) THEN
      ASM_REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2]]] THEN

  (*** Another semi-degenerate case p = 0 ***)

  ASM_CASES_TAC `p = 0` THENL
   [UNDISCH_THEN `p = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
    REPEAT(EXISTS_TAC `0`) THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_UP_TAC `p:num` `pc + 0xba` `pc + 0x12a`
   `\i s. read RSP s = stackpointer /\
          read RDI s = word k /\
          read RSI s = z /\
          read R10 s = word nx /\
          read RCX s = x /\
          read R8 s = m /\
          read R9 s = word p /\
          read (memory :> bytes64 stackpointer) s = word w /\
          read R14 s = word i /\
          bignum_from_memory (m,k) s = n /\
          bignum_from_memory(word_add x (word(8 * (k + i))),nx - (k + i)) s =
          highdigits a (k + i) /\
          ?q r. q < 2 EXP (64 * i) /\ r < 2 EXP (64 * i) /\
                2 EXP (64 * i) *
                (2 EXP (64 * k) * val(read R15 s) +
                 bignum_from_memory(z,k) s) +
                r =
                q * n + lowdigits a (k + i) /\
                (ODD n ==> r = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--3) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_0] THEN
    REPEAT(EXISTS_TAC `0`) THEN ARITH_TAC;

    ALL_TAC; (*** This is the main loop invariant: save for later ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--2)] THEN

  (*** Start on the main outer loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cout:num` `\s. val(read R15 s)` THEN
  GHOST_INTRO_TAC `z1:num` `bignum_from_memory(z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  (*** The initial prelude of the Montgomery reduction ***)

  ABBREV_TAC `q0 = (w * z1) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xd9`
   `\s. read RSP s = stackpointer /\
        read RDI s = word k /\
        read RSI s = z /\
        read R10 s = word nx /\
        read RCX s = x /\
        read R8 s = m /\
        read R9 s = word p /\
        read (memory :> bytes64 stackpointer) s = word w /\
        read R14 s = word i /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (word_add x (word (8 * (k + i))),nx - (k + i)) s =
        highdigits a (k + i) /\
        read R15 s = word cout /\
        bignum_from_memory (z,k) s = z1 /\
        read RBP s = word q0 /\
        read RBX s = word 1 /\
        read R13 s = word k /\
        2 EXP 64 * (bitval(read CF s) + val(read R11 s)) + val(read RAX s) =
        q0 * bigdigit n 0 + bigdigit z1 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(m,k) s0 = highdigits n 0 /\
      bignum_from_memory(z,k) s0 = highdigits z1 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_MONTREDC_EXEC [5;6] (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM WORD_MUL] THEN ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[ADD_CLAUSES; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Break at "montend" to share the end reasoning ***)

  GHOST_INTRO_TAC `r0:num` `\s. val(read RAX s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_SEQUENCE_TAC `pc + 0x102`
   `\s. read RSP s = stackpointer /\
        read RDI s = word k /\
        read RSI s = z /\
        read R10 s = word nx /\
        read RCX s = x /\
        read R8 s = m /\
        read R9 s = word p /\
        read (memory :> bytes64 stackpointer) s = word w /\
        read R14 s = word i /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (word_add x (word (8 * (k + i))),nx - (k + i)) s =
        highdigits a (k + i) /\
        read R15 s = word cout /\
        read RBP s = word q0 /\
        read RBX s = word k /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read R11 s)) +
        2 EXP 64 * bignum_from_memory (z,k - 1) s +
        r0 =
        lowdigits z1 k + q0 * lowdigits n k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      X86_SIM_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_PAUP_TAC `1` `k:num` `pc + 0xde` `pc + 0x100`
     `\j s. (read RSP s = stackpointer /\
             read RDI s = word k /\
             read RSI s = z /\
             read R10 s = word nx /\
             read RCX s = x /\
             read R8 s = m /\
             read R9 s = word p /\
             read (memory :> bytes64 stackpointer) s = word w /\
             read R14 s = word i /\
             bignum_from_memory (m,k) s = n /\
             bignum_from_memory
              (word_add x (word (8 * (k + i))),nx - (k + i)) s =
             highdigits a (k + i) /\
             read R15 s = word cout /\
             read RBP s = word q0 /\
             read RBX s = word j /\
             read R13 s = word(k - j) /\
             bignum_from_memory(word_add z (word (8 * j)),k - j) s =
             highdigits z1 j /\
             bignum_from_memory(word_add m (word (8 * j)),k - j) s =
             highdigits n j /\
             2 EXP (64 * j) * (bitval(read CF s) + val(read R11 s)) +
             2 EXP 64 * bignum_from_memory(z,j-1) s + r0 =
             lowdigits z1 j + q0 * lowdigits n j) /\
            (read ZF s <=> j = k)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_MONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      ASM_REWRITE_TAC[VAL_WORD_1; ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[GSYM highdigits; BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_1] THEN ARITH_TAC;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`j:num`; `j - 1`] THEN
      SUBGOAL_THEN `word_sub (word j) (word 1):int64 = word(j - 1)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read R11` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - j:num`; `a:num`; `j:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      UNDISCH_THEN `val(word q0:int64) = q0` (K ALL_TAC) THEN
      SUBGOAL_THEN `nonoverlapping (word_add z (word (8 * (j - 1))):int64,8)
                                   (word_add x (word (8 * (k + i))),
                                    8 * (nx - (k + i)))`
      MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
       [ASM_CASES_TAC `nx - (k + i) = 0` THEN
        ASM_SIMP_TAC[MULT_CLAUSES; NONOVERLAPPING_MODULO_TRIVIAL] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SUB_EQ_0; NOT_LE]) THEN
        FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
         [ALL_TAC;
          GEN_REWRITE_TAC LAND_CONV [NONOVERLAPPING_MODULO_SYM] THEN
          MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
              NONOVERLAPPING_MODULO_SUBREGIONS) THEN
          CONJ_TAC THEN CONTAINED_TAC] THEN
        SUBGOAL_THEN
         `word_add z (word (8 * (k + i))):int64 =
          word_add (word_add z (word(8 * (j - 1))))
                   (word(8 + 8 * ((k + i) - j)))`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
          NONOVERLAPPING_TAC];
        DISCH_TAC] THEN
      ABBREV_TAC `j' = j - 1` THEN
      SUBGOAL_THEN `j = j' + 1` SUBST_ALL_TAC THENL
       [EXPAND_TAC "j'" THEN UNDISCH_TAC `1 <= j` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(j' + 1) + 1 = j' + 2`]) THEN
      REWRITE_TAC[ARITH_RULE `(j' + 1) + 1 = j' + 2`] THEN
      MP_TAC(SPEC `j':num` WORD_INDEX_WRAP) THEN DISCH_TAC THEN
      X86_ACCSTEPS_TAC BIGNUM_MONTREDC_EXEC [1;4] (1--5) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
       `word_sub x (word_neg y):int64 = word_add x y`]) THEN
      ACCUMULATE_ARITH_TAC "s5" THEN
      X86_ACCSTEPS_TAC BIGNUM_MONTREDC_EXEC [6] (6--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `k - (j + 2) = k - (j + 1) - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= k - (j + 1) <=> j + 1 < k`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        ASM_SIMP_TAC[ARITH_RULE
         `j + 1 < k ==> (j + 2 = k <=> k - (j + 2) = 0)`] THEN
        REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC WORD_EQ_0 THEN
        REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `k < 2 EXP 64` THEN
        ARITH_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(n + 2) - 1 = n + 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `j' + 2 = (j' + 1) + 1` MP_TAC THENL
       [ARITH_TAC; DISCH_THEN SUBST_ALL_TAC] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `(e * d1 + d0) + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
       [TAUT `p /\ q /\ r /\ s <=> p /\ s /\ q /\ r`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`j:num`; `j - 1`] THEN
      X86_SIM_TAC BIGNUM_MONTREDC_EXEC [1];

      X86_SIM_TAC BIGNUM_MONTREDC_EXEC [1]];

    ALL_TAC] THEN

  SUBGOAL_THEN `cout < 2` MP_TAC THENL
   [SUBGOAL_THEN `q * n + lowdigits a (k + i) < 2 EXP (64 * (k + i)) * 2`
    MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x < e /\ y < e ==> x + y < e * 2`) THEN
      REWRITE_TAC[LOWDIGITS_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (k + p) = 64 * p + 64 * k`] THEN
      ASM_SIMP_TAC[LT_MULT2; EXP_ADD];
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ARITH_RULE `64 * k + 64 * p = 64 * (p + k)`] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `a + b:num < c ==> a < c`)) THEN
      REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `tc:bool` SUBST_ALL_TAC)] THEN

  (*** Just case split over the "off the end" and share remainder ***)

  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read R11` THEN
  VAL_INT64_TAC `k - 1` THEN
  SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`];
    ALL_TAC] THEN
  VAL_INT64_TAC `k + i:num` THEN
  MP_TAC(WORD_RULE `word_add (word k) (word i):int64 = word(k + i)`) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `k - 1` WORD_INDEX_WRAP) THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1] THEN DISCH_TAC THEN

  ASM_CASES_TAC `nx:num <= k + i` THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_ACCSTEPS_TAC BIGNUM_MONTREDC_EXEC [1] (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `nx <= k + i ==> nx - (k + i + 1) = 0`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC SYM_CONV THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
       MATCH_MP_TAC HIGHDIGITS_ZERO THEN
       TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num <= k + i` THEN
      ARITH_TAC;
      ALL_TAC];

    SUBGOAL_THEN `nonoverlapping (word_add z (word (8 * (k - 1))):int64,8)
                                 (word_add x (word (8 * (k + i))),
                                  8 * (nx - (k + i)))`
    MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
       [ALL_TAC;
        GEN_REWRITE_TAC LAND_CONV [NONOVERLAPPING_MODULO_SYM] THEN
        MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
            NONOVERLAPPING_MODULO_SUBREGIONS) THEN
        CONJ_TAC THEN CONTAINED_TAC] THEN
      SUBGOAL_THEN
       `word_add z (word (8 * (k + i))):int64 =
        word_add (word_add z (word(8 * (k - 1))))
                 (word(8 + 8 * ((k + i) - k)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        NONOVERLAPPING_TAC];
      DISCH_TAC] THEN

    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0] THEN
    REWRITE_TAC[ARITH_RULE `n - (k + i) - 1 = n - (k + i + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `(k + i) + 1 = k + i + 1`] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    X86_ACCSTEPS_TAC BIGNUM_MONTREDC_EXEC [1;8;9] (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]] THEN

  (MAP_EVERY EXISTS_TAC
    [`2 EXP (64 * i) * q0 + q`;
     `2 EXP (64 * i) * r0 + r`] THEN
   GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
    [REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
     CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `q1 < e /\ q0 < ee /\ (q1 < e ==> (q1 + 1) * ee <= e * ee)
       ==> ee * q1 + q0 < ee * e`) THEN
     ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
     ASM_REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [ALL_TAC;
     DISCH_THEN(fun th ->
       REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th))) THEN
     ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     ASM_REWRITE_TAC[EXP_LT_0; ARITH_EQ] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
      `ee * x + e * y + r = z
       ==> e divides ee /\ (z == 0) (mod e)
           ==> (r == 0) (mod e)`)) THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
       UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
       UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM)] THEN
     REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
     REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
      `(n * w + 1 == 0) (mod e) ==> (z + (w * z) * n == 0) (mod e)`) THEN
     ASM_REWRITE_TAC[]] THEN
   SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
    [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
   ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
   REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
   REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
   SUBGOAL_THEN `(i + 1) + (k - 1) = i + k` SUBST1_TAC THENL
    [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES] THEN
   REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE `k + i + 1 = (k + i) + 1`]) THEN
  REWRITE_TAC[ARITH_RULE `64 * (k + i) = 64 * k + 64 * i`; EXP_ADD] THENL
   [REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
    SUBGOAL_THEN `bigdigit a (k + i) = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC BIGDIGIT_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num <= k + i` THEN
      ARITH_TAC;
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_BITVAL; ADD_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC REAL_RING;

    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_BITVAL; ADD_CLAUSES;
                 BIGDIGIT_BOUND] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC REAL_RING]);;

let BIGNUM_MONTREDC_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!k z r x m p a n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 56),64) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_montredc_tmc); (x,8 * val r); (m,8 * val k)] /\
        ALL (nonoverlapping (z,8 * val k)) [(word pc,LENGTH bignum_montredc_tmc); (m,8 * val k)] /\
        (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
        val p < 2 EXP 61 /\ val r < 2 EXP 61
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montredc_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; r; x; m; p] s /\
                  bignum_from_memory (x,val r) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD n /\
                   lowdigits a (val k + val p) <= 2 EXP (64 * val p) * n
                   ==> bignum_from_memory (z,val k) s =
                       (inverse_mod n (2 EXP (64 * val p)) *
                        lowdigits a (val k + val p)) MOD n))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                      memory :> bytes(word_sub stackpointer (word 56),56)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_montredc_tmc BIGNUM_MONTREDC_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 56);;

let BIGNUM_MONTREDC_SUBROUTINE_CORRECT = time prove
 (`!k z r x m p a n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 56),64) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,LENGTH bignum_montredc_mc); (x,8 * val r); (m,8 * val k)] /\
        ALL (nonoverlapping (z,8 * val k)) [(word pc,LENGTH bignum_montredc_mc); (m,8 * val k)] /\
        (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
        val p < 2 EXP 61 /\ val r < 2 EXP 61
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montredc_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; r; x; m; p] s /\
                  bignum_from_memory (x,val r) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD n /\
                   lowdigits a (val k + val p) <= 2 EXP (64 * val p) * n
                   ==> bignum_from_memory (z,val k) s =
                       (inverse_mod n (2 EXP (64 * val p)) *
                        lowdigits a (val k + val p)) MOD n))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                      memory :> bytes(word_sub stackpointer (word 56),56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTREDC_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_montredc_windows_mc = define_from_elf
   "bignum_montredc_windows_mc" "x86/generic/bignum_montredc.obj";;

let bignum_montredc_windows_tmc = define_trimmed "bignum_montredc_windows_tmc" bignum_montredc_windows_mc;;

let BIGNUM_MONTREDC_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z r x m p a n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 72),80) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 72),72))
            [(word pc,LENGTH bignum_montredc_windows_tmc); (x,8 * val r); (m,8 * val k)] /\
        ALL (nonoverlapping (z,8 * val k)) [(word pc,LENGTH bignum_montredc_windows_tmc); (m,8 * val k)] /\
        (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
        val p < 2 EXP 61 /\ val r < 2 EXP 61
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montredc_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; r; x; m; p] s /\
                  bignum_from_memory (x,val r) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD n /\
                   lowdigits a (val k + val p) <= 2 EXP (64 * val p) * n
                   ==> bignum_from_memory (z,val k) s =
                       (inverse_mod n (2 EXP (64 * val p)) *
                        lowdigits a (val k + val p)) MOD n))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                      memory :> bytes(word_sub stackpointer (word 72),72)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_montredc_windows_tmc bignum_montredc_tmc
   BIGNUM_MONTREDC_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 56);;

let BIGNUM_MONTREDC_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z r x m p a n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 72),80) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 72),72))
            [(word pc,LENGTH bignum_montredc_windows_mc); (x,8 * val r); (m,8 * val k)] /\
        ALL (nonoverlapping (z,8 * val k)) [(word pc,LENGTH bignum_montredc_windows_mc); (m,8 * val k)] /\
        (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
        val p < 2 EXP 61 /\ val r < 2 EXP 61
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montredc_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; r; x; m; p] s /\
                  bignum_from_memory (x,val r) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD n /\
                   lowdigits a (val k + val p) <= 2 EXP (64 * val p) * n
                   ==> bignum_from_memory (z,val k) s =
                       (inverse_mod n (2 EXP (64 * val p)) *
                        lowdigits a (val k + val p)) MOD n))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                      memory :> bytes(word_sub stackpointer (word 72),72)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTREDC_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

