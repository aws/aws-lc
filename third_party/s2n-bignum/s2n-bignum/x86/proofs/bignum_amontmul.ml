(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Almost-Montgomery multiplication of arbitrary bignums.                    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_amontmul.o";;
 ****)

let bignum_amontmul_mc =
  define_assert_from_elf "bignum_amontmul_mc" "x86/generic/bignum_amontmul.o"
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
  0x0f; 0x84; 0x38; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 312)) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xc1; 0xe2; 0x02;  (* SHL (% rdx) (Imm8 (word 2)) *)
  0x48; 0x29; 0xd3;        (* SUB (% rbx) (% rdx) *)
  0x48; 0x83; 0xf3; 0x02;  (* XOR (% rbx) (Imm8 (word 2)) *)
  0x48; 0x89; 0xda;        (* MOV (% rdx) (% rbx) *)
  0x48; 0x0f; 0xaf; 0xd0;  (* IMUL (% rdx) (% rax) *)
  0xb8; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 2)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0x83; 0xc2; 0x01;  (* ADD (% rdx) (Imm8 (word 1)) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% rdx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% rdx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% rdx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0x0f; 0xaf; 0xd8;  (* IMUL (% rbx) (% rax) *)
  0x48; 0x89; 0x1c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rbx) *)
  0x4d; 0x31; 0xed;        (* XOR (% r13) (% r13) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x4c; 0x89; 0x2c; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,rbx))) (% r13) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x48; 0x39; 0xfb;        (* CMP (% rbx) (% rdi) *)
  0x72; 0xf4;              (* JB (Imm8 (word 244)) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x4b; 0x8b; 0x2c; 0xe9;  (* MOV (% rbp) (Memop Quadword (%%% (r9,3,r13))) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xff;        (* XOR (% r15) (% r15) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x4c; 0x13; 0x14; 0xde;  (* ADC (% r10) (Memop Quadword (%%% (rsi,3,rbx))) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x48; 0x8b; 0x04; 0xd9;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,rbx))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x89; 0x04; 0xde;  (* MOV (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x75; 0xdd;              (* JNE (Imm8 (word 221)) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xff;        (* ADC (% r15) (% r15) *)
  0x4c; 0x8b; 0x1e;        (* MOV (% r11) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x2c; 0x24;  (* MOV (% rbp) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x0f; 0xaf; 0xeb;  (* IMUL (% rbp) (% r11) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0xbb; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 1)) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x74; 0x24;              (* JE (Imm8 (word 36)) *)
  0x4c; 0x13; 0x14; 0xde;  (* ADC (% r10) (Memop Quadword (%%% (rsi,3,rbx))) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
  0x49; 0x8b; 0x04; 0xd8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,rbx))) *)
  0x48; 0xf7; 0xe5;        (* MUL2 (% rdx,% rax) (% rbp) *)
  0x4c; 0x29; 0xda;        (* SUB (% rdx) (% r11) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x89; 0x44; 0xde; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rbx,-- &8))) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x48; 0xff; 0xc3;        (* INC (% rbx) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x75; 0xdc;              (* JNE (Imm8 (word 220)) *)
  0x4d; 0x11; 0xf2;        (* ADC (% r10) (% r14) *)
  0x49; 0x83; 0xd7; 0x00;  (* ADC (% r15) (Imm8 (word 0)) *)
  0x4d; 0x89; 0xfe;        (* MOV (% r14) (% r15) *)
  0x4c; 0x89; 0x54; 0xde; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rbx,-- &8))) (% r10) *)
  0x49; 0xff; 0xc5;        (* INC (% r13) *)
  0x49; 0x39; 0xfd;        (* CMP (% r13) (% rdi) *)
  0x0f; 0x82; 0x64; 0xff; 0xff; 0xff;
                           (* JB (Imm32 (word 4294967140)) *)
  0x48; 0x31; 0xed;        (* XOR (% rbp) (% rbp) *)
  0x4c; 0x29; 0xf5;        (* SUB (% rbp) (% r14) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x49; 0x8b; 0x04; 0xd8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,rbx))) *)
  0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
  0x49; 0xf7; 0xdb;        (* NEG (% r11) *)
  0x48; 0x19; 0x04; 0xde;  (* SBB (Memop Quadword (%%% (rsi,3,rbx))) (% rax) *)
  0x4d; 0x19; 0xdb;        (* SBB (% r11) (% r11) *)
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

let bignum_amontmul_tmc = define_trimmed "bignum_amontmul_tmc" bignum_amontmul_mc;;

let BIGNUM_AMONTMUL_EXEC = X86_MK_CORE_EXEC_RULE bignum_amontmul_tmc;;

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

let BIGNUM_AMONTMUL_CORRECT = time prove
 (`!k z x y m a b n pc stackpointer.
        nonoverlapping (z,8 * val k) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
          [(z,8 * val k); (stackpointer,8)]
          [(word pc,0x15e); (x,8 * val k); (y,8 * val k); (m,8 * val k)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_amontmul_tmc) /\
                read RIP s = word (pc + 0xe) /\
                read RSP s = stackpointer /\
                C_ARGUMENTS [k; z; x; y; m] s /\
                bignum_from_memory (x,val k) s = a /\
                bignum_from_memory (y,val k) s = b /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = word(pc + 0x14f) /\
                (ODD n
                 ==> (bignum_from_memory (z,val k) s ==
                      inverse_mod n (2 EXP (64 * val k)) * a * b) (mod n)))
           (MAYCHANGE [RIP; RAX; RBX; RBP; RDX; R9;
                       R10; R11; R12; R13; R14; R15] ,,
            MAYCHANGE [memory :> bytes(z,8 * val k);
                       memory :> bytes(stackpointer,8)] ,,
            MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `n:num`; `pc:num`] THEN
  X_GEN_TAC `stackpointer:int64` THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN STRIP_TAC THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`] THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ODD];
    ALL_TAC] THEN

  (*** Initial word-level modular inverse ***)

  ENSURES_SEQUENCE_TAC `pc + 0x75`
   `\s. read RSP s = stackpointer /\
        read RDI s = word k /\
        read RSI s = z /\
        read R9 s = x /\
        read RCX s = y /\
        read R8 s = m /\
        bignum_from_memory (x,k) s = a /\
        bignum_from_memory (y,k) s = b /\
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
    X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--9) THEN
    SUBGOAL_THEN `ODD n ==> (n * val (read RBX s9) + 1 == 0) (mod 16)`
    MP_TAC THENL [ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16]; ALL_TAC] THEN
    REABBREV_TAC `x0 = read RBX s9` THEN DISCH_TAC THEN
    X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (10--27) THEN
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

  (*** Setup of the main loop with zeroing and corrective start/end ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x8e` `pc + 0x121`
   `\i s. read RSP s = stackpointer /\
          read RDI s = word k /\
          read RSI s = z /\
          read R9 s = x /\
          read RCX s = y /\
          read R8 s = m /\
          read (memory :> bytes64 stackpointer) s = word w /\
          read R13 s = word i /\
          bignum_from_memory(word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          bignum_from_memory (y,k) s = b /\
          bignum_from_memory (m,k) s = n /\
          ?q r. q < 2 EXP (64 * i) /\ r < 2 EXP (64 * i) /\
                2 EXP (64 * i) *
                (2 EXP (64 * k) * val(read R14 s) +
                 bignum_from_memory(z,k) s) +
                r =
                q * n + lowdigits a i * b /\
                (ODD n ==> r = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `k:num` `pc + 0x7f` `pc + 0x86`
     `\i s. read RSP s = stackpointer /\
            read RDI s = word k /\
            read RSI s = z /\
            read R9 s = x /\
            read RCX s = y /\
            read R8 s = m /\
            read (memory :> bytes64 stackpointer) s = word w /\
            read RBX s = word i /\
            read R13 s = word 0 /\
            bignum_from_memory (x,k) s = a /\
            bignum_from_memory (y,k) s = b /\
            bignum_from_memory (m,k) s = n /\
            bignum_from_memory (z,i) s = 0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      X86_SIM_TAC BIGNUM_AMONTMUL_EXEC (1--3) THEN
      ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; LOWDIGITS_0; ADD_CLAUSES;
                      SUB_0; WORD_ADD_0; HIGHDIGITS_0] THEN
      REPEAT(EXISTS_TAC `0`) THEN ARITH_TAC];

    ALL_TAC; (*** This is the main loop invariant: save for later ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** This is the corrective subtraction part.... ***)

    GHOST_INTRO_TAC `cout:num` `\s. val(read R14 s)` THEN
    GHOST_INTRO_TAC `mm:num` `bignum_from_memory(z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `mm:num` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `cout < 2` MP_TAC THENL
     [SUBGOAL_THEN `q * n + a * b < 2 EXP (64 * k) EXP 2 * 2` MP_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `x < e * e /\ y < e * e ==> x + y < e EXP 2 * 2`) THEN
        ASM_SIMP_TAC[LT_MULT2];
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `e * (e * c + m) + r < e EXP 2 * 2
          ==> e EXP 2 * c < e EXP 2 * 2`)) THEN
        REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
      GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT]] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:bool` SUBST_ALL_TAC) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN
    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x136` `pc + 0x14a`
     `\i s. read RSP s = stackpointer /\
            read RDI s = word k /\
            read RSI s = z /\
            read R8 s = m /\
            read RBP s = word_neg(word(bitval c)) /\
            read RBX s = word i /\
            val(word_neg(read R11 s)) <= 1 /\
            bignum_from_memory (word_add z (word(8 * i)),k - i) s =
            highdigits mm i /\
            bignum_from_memory (word_add m (word(8 * i)),k - i) s =
            highdigits n i /\
            &(bignum_from_memory(z,i) s):real =
            &2 pow (64 * i) * &(val(word_neg(read R11 s))) +
            &(lowdigits mm i) - &(bitval c) * &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB_LZERO; SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BITVAL_CLAUSES; WORD_NEG_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0; VAL_WORD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0; LE_0] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read R11 s))` THEN
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
      X86_ACCSTEPS_TAC BIGNUM_AMONTMUL_EXEC [4] (1--6) THEN
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
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      DISCH_TAC THEN UNDISCH_TAC `ODD n ==> r = 0` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])] THEN
   FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `e * x:num = q * n + ab
      ==> (i * e == 1) (mod n) /\ (y == x) (mod n)
          ==> (y == i * ab) (mod n)`)) THEN
   ASM_REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
   REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
   MATCH_MP_TAC(INTEGER_RULE
    `x = (e - n) * c + m ==> (x:int == e * c + m) (mod n)`) THEN
   MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow (64 * k)` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC(INT_ARITH
      `&0 <= x /\ x < e /\ &0 <= y /\ y < e ==> abs(x - y:int) < e`) THEN
     ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; LT_IMP_LE; LE_0] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
     UNDISCH_TAC
      `2 EXP (64 * k) * (2 EXP (64 * k) * bitval c + mm) = q * n + a * b` THEN
     ASM_CASES_TAC `c:bool` THEN
     ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; BITVAL_CLAUSES] THEN
     ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> ((e - n) + m < e <=> m < n)`] THEN
     DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
      `e * (e + m):num = qn + ab ==> ab < e * e ==> e * m < qn`)) THEN
     ASM_SIMP_TAC[LT_MULT2] THEN REWRITE_TAC[GSYM NOT_LE; CONTRAPOS_THM] THEN
     ASM_SIMP_TAC[LE_MULT2; LT_IMP_LE];
     REWRITE_TAC[INTEGER_RULE
      `(z:int == (e - n) * c + m) (mod e) <=> (z + n * c == m) (mod e)`] THEN
     REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
     REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
     ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; LOWDIGITS_SELF] THEN
     REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC] THEN
     REWRITE_TAC[REAL_FIELD
      `(&2 pow n * x + y) / &2 pow n = x + y / &2 pow n`] THEN
     REAL_INTEGER_TAC]] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cout:num` `\s. val(read R14 s)` THEN
  GHOST_INTRO_TAC `z1:num` `bignum_from_memory(z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN

  (*** The multiply-add loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0xc7`
   `\s. read RSP s = stackpointer /\
        read RDI s = word k /\
        read RSI s = z /\
        read R9 s = x /\
        read RCX s = y /\
        read R8 s = m /\
        bignum_from_memory (y,k) s = b /\
        bignum_from_memory (m,k) s = n /\
        read (memory :> bytes64 stackpointer) s = word w /\
        read R13 s = word i /\
        bignum_from_memory (word_add x (word (8 * (i + 1))),k - (i + 1)) s =
        highdigits a (i + 1) /\
        ?c1 c0. c0 < 2 EXP 64 /\
                read R15 s = word(bitval c1) /\
                read R14 s = word c0 /\
                2 EXP (64 * k) * (2 EXP 64 * bitval c1 + c0) +
                bignum_from_memory (z,k) s =
                (2 EXP (64 * k) * cout + z1) + bigdigit a i * b` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x9e` `pc + 0xbf`
     `\j s. (read RSP s = stackpointer /\
             read RDI s = word k /\
             read RSI s = z /\
             read R9 s = x /\
             read RCX s = y /\
             read R8 s = m /\
             bignum_from_memory (y,k) s = b /\
             bignum_from_memory (m,k) s = n /\
             read (memory :> bytes64 stackpointer) s = word w /\
             read R14 s = word cout /\
             read R13 s = word i /\
             read RBP s = word(bigdigit a i) /\
             read RBX s = word j /\
             read R15 s = word 0 /\
             read R12 s = word(k - j) /\
             bignum_from_memory (word_add x (word (8 * (i + 1))),
                                 k - (i + 1)) s =
             highdigits a (i + 1) /\
             bignum_from_memory(word_add z (word (8 * j)),k - j) s =
             highdigits z1 j /\
             bignum_from_memory(word_add y (word (8 * j)),k - j) s =
             highdigits b j /\
             2 EXP (64 * j) * (bitval(read CF s) + val(read R10 s)) +
             bignum_from_memory(z,j) s =
             lowdigits z1 j + bigdigit a i * lowdigits b j) /\
            (read ZF s <=> j = k)` THEN

    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0] THEN
      REWRITE_TAC[LOWDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0; SUB_0];

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read R10` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - j:num`; `a:num`; `j:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTMUL_EXEC [1;4] (1--5) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
       `word_sub x (word_neg y):int64 = word_add x y`]) THEN
      ACCUMULATE_ARITH_TAC "s5" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTMUL_EXEC [6] (6--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC];
        VAL_INT64_TAC `k - (j + 1)` THEN ASM_REWRITE_TAC[] THEN
        SIMPLE_ARITH_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `e * d1 + d0 + c * (e * a1 + a0):num =
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

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hout:int64` `read R10` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTMUL_EXEC [2] (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`carry_s2:bool`; `val(sum_s2:int64)`] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; VAL_BOUND_64; WORD_VAL] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
      ONCE_REWRITE_TAC[REAL_ARITH
       `e * (c + h + b) + y:real = e * c + e * (b + h) + y`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Tidying up a bit ***)

  GHOST_INTRO_TAC `z2:num` `bignum_from_memory(z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z2:num` THEN
  GHOST_INTRO_TAC `g6:int64` `read R14` THEN
  GHOST_INTRO_TAC `g7:int64` `read R15` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c1:bool`
   (X_CHOOSE_THEN `c0:num` STRIP_ASSUME_TAC)) THEN
  UNDISCH_THEN `g6:int64 = word c0` SUBST_ALL_TAC THEN
  UNDISCH_THEN `g7:int64 = word(bitval c1)` SUBST_ALL_TAC THEN

  (*** The initial prelude of the Montgomery reduction ***)

  ABBREV_TAC `q0 = (w * z2) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xe6`
   `\s. read RSP s = stackpointer /\
        read RDI s = word k /\
        read RSI s = z /\
        read R9 s = x /\
        read RCX s = y /\
        read R8 s = m /\
        bignum_from_memory (y,k) s = b /\
        bignum_from_memory (m,k) s = n /\
        read (memory :> bytes64 stackpointer) s = word w /\
        read R13 s = word i /\
        bignum_from_memory (word_add x (word (8 * (i + 1))),k - (i + 1)) s =
        highdigits a (i + 1) /\
        bignum_from_memory (z,k) s = z2 /\
        read R14 s = word c0 /\
        read R15 s = word (bitval c1) /\
        read RBP s = word q0 /\
        read RBX s = word 1 /\
        read R12 s = word k /\
        2 EXP 64 * (bitval(read CF s) + val(read R10 s)) + val(read RAX s) =
        q0 * bigdigit n 0 + bigdigit z2 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(m,k) s0 = highdigits n 0 /\
      bignum_from_memory(z,k) s0 = highdigits z2 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_AMONTMUL_EXEC [5; 6] (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z2) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
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

  ENSURES_SEQUENCE_TAC `pc + 0x10f`
   `\s. read RSP s = stackpointer /\
        read RDI s = word k /\
        read RSI s = z /\
        read R9 s = x /\
        read RCX s = y /\
        read R8 s = m /\
        bignum_from_memory (y,k) s = b /\
        bignum_from_memory (m,k) s = n /\
        read (memory :> bytes64 stackpointer) s = word w /\
        read R14 s = word c0 /\
        read R15 s = word (bitval c1) /\
        read R13 s = word i /\
        read RBP s = word q0 /\
        read RBX s = word k /\
        bignum_from_memory (word_add x (word (8 * (i + 1))),k - (i + 1)) s =
        highdigits a (i + 1) /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read R10 s)) +
        2 EXP 64 * bignum_from_memory (z,k - 1) s +
        r0 =
        lowdigits z2 k + q0 * lowdigits n k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_PAUP_TAC `1` `k:num` `pc + 0xeb` `pc + 0x10d`
     `\j s. (read RSP s = stackpointer /\
             read RDI s = word k /\
             read RSI s = z /\
             read R9 s = x /\
             read RCX s = y /\
             read R8 s = m /\
             bignum_from_memory (y,k) s = b /\
             bignum_from_memory (m,k) s = n /\
             read (memory :> bytes64 stackpointer) s = word w /\
             read R14 s = word c0 /\
             read R15 s = word (bitval c1) /\
             read R13 s = word i /\
             read RBP s = word q0 /\
             read RBX s = word j /\
             read R12 s = word(k - j) /\
             bignum_from_memory (word_add x (word (8 * (i + 1))),
                                 k - (i + 1)) s =
             highdigits a (i + 1) /\
             bignum_from_memory(word_add z (word (8 * j)),k - j) s =
             highdigits z2 j /\
             bignum_from_memory(word_add m (word (8 * j)),k - j) s =
             highdigits n j /\
             2 EXP (64 * j) * (bitval(read CF s) + val(read R10 s)) +
             2 EXP 64 * bignum_from_memory(z,j-1) s + r0 =
             lowdigits z2 j + q0 * lowdigits n j) /\
            (read ZF s <=> j = k)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
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
      GHOST_INTRO_TAC `hin:int64` `read R10` THEN
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
      ABBREV_TAC `j' = j - 1` THEN
      SUBGOAL_THEN `j = j' + 1` SUBST_ALL_TAC THENL
       [EXPAND_TAC "j'" THEN UNDISCH_TAC `1 <= j` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(j' + 1) + 1 = j' + 2`]) THEN
      REWRITE_TAC[ARITH_RULE `(j' + 1) + 1 = j' + 2`] THEN
      MP_TAC(SPEC `j':num` WORD_INDEX_WRAP) THEN DISCH_TAC THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTMUL_EXEC [1;4] (1--5) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
       `word_sub x (word_neg y):int64 = word_add x y`]) THEN
      ACCUMULATE_ARITH_TAC "s5" THEN
      X86_ACCSTEPS_TAC BIGNUM_AMONTMUL_EXEC [6] (6--10) THEN
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
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_AMONTMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    ALL_TAC] THEN

  (*** The final digit write ****)

  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read R10` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  VAL_INT64_TAC `k - 1` THEN
  SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`];
    ALL_TAC] THEN
  MP_TAC(SPEC `k - 1` WORD_INDEX_WRAP) THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1] THEN DISCH_TAC THEN

  X86_ACCSTEPS_TAC BIGNUM_AMONTMUL_EXEC [1;2] (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN

  (*** The final mathematics of the outer loop invariant ***)

  MAP_EVERY EXISTS_TAC
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
   [SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    SUBGOAL_THEN `(i + 1) + (k - 1) = i + k` SUBST1_TAC THENL
     [UNDISCH_TAC `i:num < k` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES] THEN
    REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC REAL_RING;
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
      UNDISCH_THEN `(w * z2) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(n * w + 1 == 0) (mod e) ==> (z + (w * z) * n == 0) (mod e)`) THEN
    ASM_REWRITE_TAC[]]);;

let BIGNUM_AMONTMUL_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 56),64) /\
        ALLPAIRS nonoverlapping
          [(z,8 * val k); (word_sub stackpointer (word 56),56)]
          [(word pc,LENGTH bignum_amontmul_tmc); (x,8 * val k); (y,8 * val k); (m,8 * val k)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_amontmul_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [k; z; x; y; m] s /\
                bignum_from_memory (x,val k) s = a /\
                bignum_from_memory (y,val k) s = b /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (ODD n
                 ==> (bignum_from_memory (z,val k) s ==
                      inverse_mod n (2 EXP (64 * val k)) * a * b) (mod n)))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 56),56)])`,
  X86_PROMOTE_RETURN_STACK_TAC
    bignum_amontmul_tmc BIGNUM_AMONTMUL_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 56);;

let BIGNUM_AMONTMUL_SUBROUTINE_CORRECT = time prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 56),64) /\
        ALLPAIRS nonoverlapping
          [(z,8 * val k); (word_sub stackpointer (word 56),56)]
          [(word pc,LENGTH bignum_amontmul_mc); (x,8 * val k); (y,8 * val k); (m,8 * val k)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_amontmul_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [k; z; x; y; m] s /\
                bignum_from_memory (x,val k) s = a /\
                bignum_from_memory (y,val k) s = b /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (ODD n
                 ==> (bignum_from_memory (z,val k) s ==
                      inverse_mod n (2 EXP (64 * val k)) * a * b) (mod n)))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 56),56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_AMONTMUL_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_amontmul_windows_mc = define_from_elf
   "bignum_amontmul_windows_mc" "x86/generic/bignum_amontmul.obj";;

let bignum_amontmul_windows_tmc = define_trimmed "bignum_amontmul_windows_tmc" bignum_amontmul_windows_mc;;

let BIGNUM_AMONTMUL_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 72),80) /\
        ALLPAIRS nonoverlapping
          [(z,8 * val k); (word_sub stackpointer (word 72),72)]
          [(word pc,LENGTH bignum_amontmul_windows_tmc); (x,8 * val k); (y,8 * val k); (m,8 * val k)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_amontmul_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z; x; y; m] s /\
                bignum_from_memory (x,val k) s = a /\
                bignum_from_memory (y,val k) s = b /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (ODD n
                 ==> (bignum_from_memory (z,val k) s ==
                      inverse_mod n (2 EXP (64 * val k)) * a * b) (mod n)))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 72),72)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    bignum_amontmul_windows_tmc bignum_amontmul_tmc BIGNUM_AMONTMUL_CORRECT
    `[RBX; RBP; R12; R13; R14; R15]` 56);;

let BIGNUM_AMONTMUL_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 72),80) /\
        ALLPAIRS nonoverlapping
          [(z,8 * val k); (word_sub stackpointer (word 72),72)]
          [(word pc,LENGTH bignum_amontmul_windows_mc); (x,8 * val k); (y,8 * val k); (m,8 * val k)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_amontmul_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z; x; y; m] s /\
                bignum_from_memory (x,val k) s = a /\
                bignum_from_memory (y,val k) s = b /\
                bignum_from_memory (m,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (ODD n
                 ==> (bignum_from_memory (z,val k) s ==
                      inverse_mod n (2 EXP (64 * val k)) * a * b) (mod n)))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 72),72)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_AMONTMUL_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

