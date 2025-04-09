(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bignum negated modular inversion.                                         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_negmodinv.o";;
 ****)

let bignum_negmodinv_mc =
  define_assert_from_elf "bignum_negmodinv_mc" "x86/generic/bignum_negmodinv.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x0f; 0x84; 0x02; 0x01; 0x00; 0x00;
                           (* JE (Imm32 (word 258)) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x48; 0xc1; 0xe2; 0x02;  (* SHL (% rdx) (Imm8 (word 2)) *)
  0x49; 0x29; 0xd3;        (* SUB (% r11) (% rdx) *)
  0x49; 0x83; 0xf3; 0x02;  (* XOR (% r11) (Imm8 (word 2)) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x48; 0x0f; 0xaf; 0xd0;  (* IMUL (% rdx) (% rax) *)
  0xb8; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 2)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x48; 0x83; 0xc2; 0x01;  (* ADD (% rdx) (Imm8 (word 1)) *)
  0x4c; 0x0f; 0xaf; 0xd8;  (* IMUL (% r11) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% rdx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x4c; 0x0f; 0xaf; 0xd8;  (* IMUL (% r11) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% rdx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x4c; 0x0f; 0xaf; 0xd8;  (* IMUL (% r11) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% rdx) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x4c; 0x0f; 0xaf; 0xd8;  (* IMUL (% r11) (% rax) *)
  0x4c; 0x89; 0x1e;        (* MOV (Memop Quadword (%% (rsi,0))) (% r11) *)
  0x48; 0x83; 0xff; 0x01;  (* CMP (% rdi) (Imm8 (word 1)) *)
  0x0f; 0x84; 0x97; 0x00; 0x00; 0x00;
                           (* JE (Imm32 (word 151)) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0x48; 0x83; 0xc0; 0x01;  (* ADD (% rax) (Imm8 (word 1)) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x4a; 0x8b; 0x04; 0xc1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r8))) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4a; 0x89; 0x04; 0xc6;  (* MOV (Memop Quadword (%%% (rsi,3,r8))) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x49; 0x39; 0xf8;        (* CMP (% r8) (% rdi) *)
  0x72; 0xe3;              (* JB (Imm8 (word 227)) *)
  0x48; 0x83; 0xef; 0x02;  (* SUB (% rdi) (Imm8 (word 2)) *)
  0x74; 0x52;              (* JE (Imm8 (word 82)) *)
  0x48; 0x83; 0xc6; 0x08;  (* ADD (% rsi) (Imm8 (word 8)) *)
  0x4c; 0x8b; 0x16;        (* MOV (% r10) (Memop Quadword (%% (rsi,0))) *)
  0x4d; 0x89; 0xd9;        (* MOV (% r9) (% r11) *)
  0x4d; 0x0f; 0xaf; 0xca;  (* IMUL (% r9) (% r10) *)
  0x4c; 0x89; 0x0e;        (* MOV (Memop Quadword (%% (rsi,0))) (% r9) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x4e; 0x13; 0x14; 0xc6;  (* ADC (% r10) (Memop Quadword (%%% (rsi,3,r8))) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x4a; 0x8b; 0x04; 0xc1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r8))) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x4c; 0x01; 0xd0;        (* ADD (% rax) (% r10) *)
  0x4a; 0x89; 0x04; 0xc6;  (* MOV (Memop Quadword (%%% (rsi,3,r8))) (% rax) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x49; 0xff; 0xc0;        (* INC (% r8) *)
  0x49; 0xff; 0xcc;        (* DEC (% r12) *)
  0x75; 0xdd;              (* JNE (Imm8 (word 221)) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xae;              (* JNE (Imm8 (word 174)) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x49; 0x0f; 0xaf; 0xc3;  (* IMUL (% rax) (% r11) *)
  0x48; 0x89; 0x46; 0x08;  (* MOV (Memop Quadword (%% (rsi,8))) (% rax) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_negmodinv_tmc = define_trimmed "bignum_negmodinv_tmc" bignum_negmodinv_mc;;

let BIGNUM_NEGMODINV_EXEC = X86_MK_CORE_EXEC_RULE bignum_negmodinv_tmc;;

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

let BIGNUM_NEGMODINV_CORRECT = prove
 (`!k z x m pc.
        nonoverlapping (word pc,0x112) (z,8 * val k) /\
        nonoverlapping (x,8 * val k) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_negmodinv_tmc) /\
                  read RIP s = word (pc + 0x3) /\
                  C_ARGUMENTS [k; z; x] s /\
                  bignum_from_memory (x,val k) s = m)
             (\s. read RIP s = word(pc + 0x10e) /\
                  (ODD m
                   ==> (m * bignum_from_memory(z,val k) s + 1 == 0)
                       (mod (2 EXP (64 * val k)))))
             (MAYCHANGE [RIP; RDI; RSI; RAX; RDX; RCX; R8; R9; R10; R11;
                         RBX; R12] ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)] ,,
              MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `m:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--2) THEN REWRITE_TAC[ODD];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** Initial word-level modular inverse ***)

  ENSURES_SEQUENCE_TAC `pc + 0x6a`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read RCX s = x /\
        bignum_from_memory (x,k) s = m /\
        (ODD m ==> (m * val(read R11 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `bignum_from_memory(x,k) s0 = highdigits m 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC LAND_CONV[BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC] THEN
    X86_STEPS_TAC BIGNUM_NEGMODINV_EXEC (1--9) THEN
    SUBGOAL_THEN `ODD m ==> (m * val (read R11 s9) + 1 == 0) (mod 16)`
    MP_TAC THENL [ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16]; ALL_TAC] THEN
    REABBREV_TAC `x0 = read R11 s9` THEN DISCH_TAC THEN
    X86_STEPS_TAC BIGNUM_NEGMODINV_EXEC (10--27) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:num` `\s. val(read R11 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC] THEN

  (*** Handle the next degenerate case k = 1 ***)

  ASM_CASES_TAC `k = 1` THENL
   [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--3) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_SING] THEN
    ASM_SIMP_TAC[MULT_CLAUSES; VAL_WORD_EQ; DIMINDEX_64];
    ALL_TAC] THEN

  (*** The "initloop" doing the first multiplication setting up output ***)

  SUBGOAL_THEN `1 < k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0) /\ ~(k = 1)`]; ALL_TAC] THEN
  ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0x8d` `pc + 0xa5`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read RCX s = x /\
          read R11 s = word w /\
          bignum_from_memory(x,k) s = m /\
          bignum_from_memory(word_add x (word(8 * i)),k - i) s =
          highdigits m i /\
          read (memory :> bytes64 z) s = word w /\
          read R8 s = word i /\
          (ODD m
           ==> 2 EXP (64 * i) * val(read R10 s) +
               bignum_from_memory(z,i) s =
               (w * lowdigits m i + 1) + w)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `~(val (word_sub (word k) (word 1):int64) = 0)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_1]; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
   SUBGOAL_THEN `bignum_from_memory(x,k) s0 = highdigits m 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC LAND_CONV[BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_NEGMODINV_EXEC (6--8) (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; EQ_ADD_RCANCEL; LOWDIGITS_1] THEN
    SUBGOAL_THEN
     `2 EXP 64 * val(sum_s8:int64) + val(sum_s7:int64) =
      w * bigdigit m 0 + 1`
    MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64; LOWDIGITS_1] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE
     `(eh + l = m * w + 1 ==> l = 0)
      ==> eh + l = w * m + 1 ==> eh = w * m + 1`) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
    REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MOD_MULT_ADD; MULT_CLAUSES] THEN
    SIMP_TAC[MOD_LT; VAL_BOUND_64] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC(LAND_CONV MOD_DOWN_CONV) THEN REWRITE_TAC[GSYM CONG] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CONG]) THEN ASM_SIMP_TAC[MOD_0];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `hin:int64` `read R10` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    X86_ACCSIM_TAC BIGNUM_NEGMODINV_EXEC [2;3;4] (1--7) THEN
    REWRITE_TAC[GSYM WORD_ADD; LOWDIGITS_CLAUSES] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `(w * (e * d + l) + 1) + w = w * e * d + (w * l + 1) + w`] THEN
    REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    CONV_TAC REAL_RING;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--2);

    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** Handle the "finale" next to share the k = 2 and general cases ***)

  ENSURES_SEQUENCE_TAC `pc + 0x102`
   `\s. read RSI s = word_sub (word_add z (word (8 * (k - 1)))) (word 8) /\
        read R11 s = word w /\
        (ODD m
        ==> (bignum_from_memory (z,k - 1) s * (m + 1) + 1 ==
             bignum_from_memory (z,k) s)
            (mod (2 EXP (64 * k))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `bignum_from_memory (z,k) = bignum_from_memory (z,(k-1)+1)`
    SUBST1_TAC THENL [ASM_SIMP_TAC[SUB_ADD; LT_IMP_LE]; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    GHOST_INTRO_TAC `l:num` `bignum_from_memory (z,k - 1)` THEN
    GHOST_INTRO_TAC `h:int64`
     `read (memory :> bytes64 (word_add z (word (8 * (k - 1)))))` THEN
    ASSUME_TAC(WORD_RULE
     `!x:int64. word_add (word_sub x (word 8)) (word 8) = x`) THEN
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--3) THEN

    DISCH_THEN(fun th -> REPEAT(FIRST_X_ASSUM(MP_TAC o C MATCH_MP th))) THEN
    DISCH_TAC THEN MATCH_MP_TAC(NUMBER_RULE
     `!p. (m * v + h == 0) (mod p) /\ (p * d = e)
          ==> (l * (m + 1) + 1 == l + d * h) (mod e)
              ==> (m * (l + d * v) + 1 == 0) (mod e)`) THEN
    EXISTS_TAC `2 EXP 64` THEN REWRITE_TAC[GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 64 + 64 * (k - 1) = 64 * k`] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD; ADD_CLAUSES; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    UNDISCH_TAC `(m * w + 1 == 0) (mod (2 EXP 64))` THEN
    SPEC_TAC(`2 EXP 64`,`p:num`) THEN CONV_TAC NUMBER_RULE] THEN

  (*** Next degenerate case k = 2 ***)

  ASM_CASES_TAC `k = 2` THENL
   [UNDISCH_THEN `k = 2` SUBST_ALL_TAC THEN
    GHOST_INTRO_TAC `hin:int64` `read R10` THEN
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--4) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_SIMP_TAC[BIGNUM_FROM_MEMORY_SING; VAL_WORD_EQ; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[ARITH_RULE `w * (m + 1) + 1 = (w * m + 1) + w`] THEN
    REWRITE_TAC[CONG; MOD_MULT_ADD; BIGNUM_FROM_MEMORY_BYTES];
    ALL_TAC] THEN

  (*** Setup of the main loop "outerloop" ***)

  SUBGOAL_THEN `2 < k /\ 1 < k - 1` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_WHILE_PAUP_TAC `1` `k - 1` `pc + 0xb0` `pc + 0x100`
   `\i s. (read RDI s = word(k - 1 - i) /\
           read RSI s = word_sub (word_add z (word(8 * i))) (word 8) /\
           read RCX s = x /\
           read R11 s = word w /\
           bignum_from_memory (x,k) s = m /\
           (ODD m
            ==> (bignum_from_memory(z,i) s * (m + 1) + 1 ==
                 bignum_from_memory(z,k) s) (mod (2 EXP (64 * k))))) /\
           (read ZF s <=> i = k - 1)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`word k:int64`; `word k:int64`] VAL_WORD_SUB_EQ_0) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SING] THEN DISCH_TAC THEN
    GHOST_INTRO_TAC `hin:int64` `read R10` THEN
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC (1--4) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_VAL_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `k - 1 - 1 = k - 2`] THEN REWRITE_TAC[WORD_SUB] THEN
    ASM_SIMP_TAC[LT_IMP_LE] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
    ASM_REWRITE_TAC[ARITH_RULE `w * (m + 1) + 1 = (w * m + 1) + w`] THEN
    REWRITE_TAC[CONG; MOD_MULT_ADD];
    ALL_TAC; (*** The main outer loop invariant ***)
    REPEAT STRIP_TAC THEN X86_SIM_TAC BIGNUM_NEGMODINV_EXEC [1];
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC [1]] THEN

  (*** Now completely rebase/reindex to focus on relevant window i...k-1
   ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN

  MP_TAC(ISPECL [`z:int64`; `i:num`; `k - i:num`]
        BIGNUM_FROM_MEMORY_SPLIT) THEN
  ASM_SIMP_TAC[ARITH_RULE `i < k - 1 ==> i + k - i = k`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `z':int64 = word_add z (word (8 * i))` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  GHOST_INTRO_TAC `l:num` `bignum_from_memory (z,i)` THEN
  GHOST_INTRO_TAC `q:num` `bignum_from_memory (z',k - i)` THEN
  REWRITE_TAC[NUMBER_RULE
   `(l * (m + 1) + 1 == e * q + l) (mod p) <=>
    (l * m + 1 == e * q) (mod p)`] THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[WORD_RULE
   `word_sub (word_add z (word (8 * (i + 1)))) (word 8) =
    word_add z (word (8 * i))`] THEN

  REWRITE_TAC[ARITH_RULE `k - 1 - (i + 1) = k - i - 2`] THEN
  REWRITE_TAC[ARITH_RULE `k - 1 - i = k - i - 1`] THEN
  ABBREV_TAC `p:num = k - i` THEN

  ENSURES_SEQUENCE_TAC `pc + 0xb4`
   `\s. read RDI s = word (p - 1) /\
        read RSI s = z' /\
        read RCX s = x /\
        read R11 s = word w /\
        bignum_from_memory (x,k) s = m /\
        bignum_from_memory (x,p) s = lowdigits m p /\
        bignum_from_memory (z,i) s = l /\
        bignum_from_memory (z',p) s = q` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_NEGMODINV_EXEC [1] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[ARITH_RULE `MIN k (k - i) = k - i`];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (z',8 * p) (z:int64,8 * i) /\
    nonoverlapping (z',8 * p) (x,8 * p) /\
    nonoverlapping (z',8 * p) (x,8 * k) /\
    nonoverlapping (z',8 * p) (word pc,0x112)`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [RIP; RDI; RSI; RAX; RDX; RCX; R8; R9; R10; R11; RBX; R12] ,,
    MAYCHANGE [memory :> bytes (z',8 * p)] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xfd`
   `\s. read RDI s = word (p - 1) /\
        read RSI s = z' /\
        read RCX s = x /\
        read R11 s = word w /\
        bignum_from_memory (x,k) s = m /\
        bignum_from_memory (z,i) s = l /\
        (ODD m
         ==> ((l + 2 EXP (64 * i) * val(read (memory :> bytes64 z') s)) *
              (m + 1) + 1 ==
              2 EXP (64 * i) * bignum_from_memory (z',p) s + l)
             (mod (2 EXP (64 * k))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC [1] THEN
    REWRITE_TAC[ARITH_RULE `p - 2 = p - 1 - 1`] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WORD_SUB] THEN
    UNDISCH_THEN `k - i:num = p` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k - 1 ==> 1 <= k - i - 1`] THEN
    VAL_INT64_TAC `k - i - 1` THEN ASM_REWRITE_TAC[VAL_WORD_1] THEN
    UNDISCH_TAC `i < k - 1` THEN ARITH_TAC] THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_FORGET_COMPONENTS_TAC
    [`memory :> bytes (z,8 * i)`; `memory :> bytes (x,8 * k)`] THEN

  ASM_SIMP_TAC[NUMBER_RULE
   `(l * m + 1 == e * q) (mod d)
    ==> (((l + e * z) * (m + 1) + 1 == e * w + l) (mod d) <=>
         (e * (q + m * z + z) == e * w) (mod d))`] THEN
  SUBGOAL_THEN `2 EXP (64 * k) = 2 EXP (64 * i) * 2 EXP (64 * p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN EXPAND_TAC "p" THEN
    UNDISCH_TAC `i < k - 1` THEN ARITH_TAC;
    REWRITE_TAC[CONG_MULT_LCANCEL_ALL; EXP_EQ_0; ARITH_EQ]] THEN

  SUBGOAL_THEN
   `!q w z. (q + m * z + z == w) (mod (2 EXP (64 * p))) <=>
            (q + lowdigits m p * z + z == w) (mod (2 EXP (64 * p)))`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[lowdigits; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD m <=> ODD(lowdigits m p)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[lowdigits; ODD_MOD_POW2] THEN
    ASM_CASES_TAC `ODD m` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "p" THEN UNDISCH_TAC `i < k - 1` THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(m * w + 1 == 0) (mod (2 EXP 64)) <=>
    (lowdigits m p * w + 1 == 0) (mod (2 EXP 64))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE
     `(m == m') (mod e)
      ==> ((m * w + 1 == 0) (mod e) <=> (m' * w + 1 == 0) (mod e))`) THEN
    REWRITE_TAC[lowdigits; CONG; MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN EXPAND_TAC "p" THEN
    UNDISCH_TAC `i < k - 1` THEN ARITH_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `m' = lowdigits m p` THEN

  SUBGOAL_THEN `2 <= p /\ p < 2 EXP 61` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `z:int64` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `m:num` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `i:num` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `k:num` o concl))) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN

  SPEC_TAC(`m':num`,`m:num`) THEN SPEC_TAC(`z':int64`,`z:int64`) THEN
  SPEC_TAC(`p:num`,`k:num`) THEN SPEC_TAC(`q:num`,`a:num`) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`m:num`; `a:num`] THEN

  (*** Setup of innermost loop "innerloop" ****)

  ABBREV_TAC `v = (w * a) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `v < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN

  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP
   (ARITH_RULE `2 <= k ==> 1 < k /\ ~(k = 0)`)) THEN
  ENSURES_WHILE_PAUP_TAC `1` `k:num` `pc + 0xda` `pc + 0xfb`
   `\i s. (read RDI s = word (k - 1) /\
           read RSI s = z /\
           read RCX s = x /\
           read R11 s = word w /\
           bignum_from_memory(x,k) s = m /\
           read R9 s = word v /\
           read (memory :> bytes64 z) s = word v /\
           read R8 s = word i /\
           read R12 s = word(k - i) /\
           bignum_from_memory(word_add x (word(8 * i)),k - i) s =
           highdigits m i /\
           bignum_from_memory(word_add z (word(8 * i)),k - i) s =
           highdigits a i /\
           (ODD m
            ==> 2 EXP (64 * i) * (bitval(read CF s) + val(read R10 s)) +
                bignum_from_memory(z,i) s =
                lowdigits a i + lowdigits m i * v + v)) /\
          (read ZF s <=> i = k)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_SING] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(x,k) s0 = highdigits m 0 /\
      bignum_from_memory(z,k) s0 = highdigits a 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_NEGMODINV_EXEC (6--8) (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_MUL] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      EXPAND_TAC "v" THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REWRITE_TAC[WORD_EQ; CONG; GSYM LOWDIGITS_1; lowdigits] THEN
      REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES] THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[ODD] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; EQ_ADD_RCANCEL; ADD_ASSOC] THEN

    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; LOWDIGITS_1] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_0] THEN
    CONV_TAC(LAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ENTIRE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VAL_MOD_REFL] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o
      map (AP_TERM `\x. x MOD 2 EXP 64`) o CONJUNCTS) THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN EXPAND_TAC "v" THEN
    REWRITE_TAC[VAL_WORD; GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
    GEN_REWRITE_TAC RAND_CONV [SYM(NUM_REDUCE_CONV `0 MOD 2 EXP 64`)] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(m * w + 1 == 0) (mod e) ==> (m * w * a + a == 0) (mod e)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC; (*** The main loop invariant ***)
    REPEAT STRIP_TAC THEN
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC [1] THEN ASM_REWRITE_TAC[VAL_EQ_0];
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    GHOST_INTRO_TAC `cout:bool` `read CF` THEN
    GHOST_INTRO_TAC `hout:int64` `read R10` THEN
    X86_SIM_TAC BIGNUM_NEGMODINV_EXEC [1] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
    REWRITE_TAC[CONG; MOD_MULT_ADD]] THEN

  (*** Proof of the inner loop invariant, just a simple multiply-add ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read R10` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_ACCSTEPS_TAC BIGNUM_NEGMODINV_EXEC [1;4] (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub x (word_neg y):int64 = word_add x y`]) THEN
  ACCUMULATE_ARITH_TAC "s5" THEN
  X86_ACCSTEPS_TAC BIGNUM_NEGMODINV_EXEC [6] (6--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
    ALL_TAC;
    REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k ==> (i + 1 = k <=> k - i = 1)`] THEN
    MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC [`i:num < k`; `k < 2 EXP 61`] THEN ARITH_TAC] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  DISCH_THEN(fun th ->
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o GSYM o C MATCH_MP th))) THEN
  ASM_REWRITE_TAC[ARITH_RULE
   `(e * a' + a) + (e * m' + m) * v + v:num =
    e * (a' + m' * v) + (a + m * v + v)`] THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  GEN_REWRITE_TAC LAND_CONV
   [TAUT `p /\ q /\ r /\ s <=> p /\ s /\ q /\ r`] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING);;

let BIGNUM_NEGMODINV_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z x m pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_negmodinv_tmc);(x,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_negmodinv_tmc) (z,8 * val k) /\
        nonoverlapping (x,8 * val k) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_negmodinv_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; x] s /\
                  bignum_from_memory (x,val k) s = m)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD m
                   ==> (m * bignum_from_memory(z,val k) s + 1 == 0)
                       (mod (2 EXP (64 * val k)))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_negmodinv_tmc BIGNUM_NEGMODINV_CORRECT
    `[RBX; R12]` 16);;

let BIGNUM_NEGMODINV_SUBROUTINE_CORRECT = prove
 (`!k z x m pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_negmodinv_mc);(x,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_negmodinv_mc) (z,8 * val k) /\
        nonoverlapping (x,8 * val k) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_negmodinv_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; x] s /\
                  bignum_from_memory (x,val k) s = m)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD m
                   ==> (m * bignum_from_memory(z,val k) s + 1 == 0)
                       (mod (2 EXP (64 * val k)))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NEGMODINV_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_negmodinv_windows_mc = define_from_elf
   "bignum_negmodinv_windows_mc" "x86/generic/bignum_negmodinv.obj";;

let bignum_negmodinv_windows_tmc = define_trimmed "bignum_negmodinv_windows_tmc" bignum_negmodinv_windows_mc;;

let BIGNUM_NEGMODINV_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x m pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 32),40) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_negmodinv_windows_tmc);(x,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_negmodinv_windows_tmc) (z,8 * val k) /\
        nonoverlapping (x,8 * val k) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_negmodinv_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; x] s /\
                  bignum_from_memory (x,val k) s = m)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD m
                   ==> (m * bignum_from_memory(z,val k) s + 1 == 0)
                       (mod (2 EXP (64 * val k)))))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_negmodinv_windows_tmc bignum_negmodinv_tmc
    BIGNUM_NEGMODINV_CORRECT `[RBX; R12]` 16);;

let BIGNUM_NEGMODINV_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x m pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 32),40) (z,8 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_negmodinv_windows_mc);(x,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_negmodinv_windows_mc) (z,8 * val k) /\
        nonoverlapping (x,8 * val k) (z,8 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_negmodinv_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; x] s /\
                  bignum_from_memory (x,val k) s = m)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (ODD m
                   ==> (m * bignum_from_memory(z,val k) s + 1 == 0)
                       (mod (2 EXP (64 * val k)))))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NEGMODINV_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

