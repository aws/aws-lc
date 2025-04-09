(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum.                        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_emontredc.o";;
 ****)

let bignum_emontredc_mc =
  define_assert_from_elf "bignum_emontredc_mc" "x86/generic/bignum_emontredc.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x4d; 0x31; 0xf6;        (* XOR (% r14) (% r14) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x78;              (* JE (Imm8 (word 120)) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4c; 0x8b; 0x26;        (* MOV (% r12) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0xcb;        (* MOV (% rbx) (% rcx) *)
  0x49; 0x0f; 0xaf; 0xdc;  (* IMUL (% rbx) (% r12) *)
  0x49; 0x8b; 0x00;        (* MOV (% rax) (Memop Quadword (%% (r8,0))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x89; 0x1e;        (* MOV (Memop Quadword (%% (rsi,0))) (% rbx) *)
  0x4c; 0x01; 0xe0;        (* ADD (% rax) (% r12) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x41; 0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 1)) *)
  0x49; 0x89; 0xfd;        (* MOV (% r13) (% rdi) *)
  0x49; 0xff; 0xcd;        (* DEC (% r13) *)
  0x74; 0x23;              (* JE (Imm8 (word 35)) *)
  0x4e; 0x13; 0x1c; 0xd6;  (* ADC (% r11) (Memop Quadword (%%% (rsi,3,r10))) *)
  0x4d; 0x19; 0xe4;        (* SBB (% r12) (% r12) *)
  0x4b; 0x8b; 0x04; 0xd0;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,r10))) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x4c; 0x29; 0xe2;        (* SUB (% rdx) (% r12) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0xff; 0xcd;        (* DEC (% r13) *)
  0x75; 0xdd;              (* JNE (Imm8 (word 221)) *)
  0x4d; 0x11; 0xf3;        (* ADC (% r11) (% r14) *)
  0x41; 0xbe; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r14d) (Imm32 (word 0)) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x04; 0xfe;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,rdi))) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x04; 0xfe;  (* MOV (Memop Quadword (%%% (rsi,3,rdi))) (% rax) *)
  0x49; 0x83; 0xd6; 0x00;  (* ADC (% r14) (Imm8 (word 0)) *)
  0x48; 0x83; 0xc6; 0x08;  (* ADD (% rsi) (Imm8 (word 8)) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0x8e;              (* JB (Imm8 (word 142)) *)
  0x4c; 0x89; 0xf0;        (* MOV (% rax) (% r14) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_emontredc_tmc = define_trimmed "bignum_emontredc_tmc" bignum_emontredc_mc;;

let BIGNUM_EMONTREDC_EXEC = X86_MK_CORE_EXEC_RULE bignum_emontredc_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_EMONTREDC_CORRECT = time prove
 (`!k z m w a n pc.
        nonoverlapping (word pc,0x92) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_emontredc_tmc) /\
                  read RIP s = word(pc + 0x7) /\
                  C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = word(pc + 0x8a) /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
             (MAYCHANGE [RIP; RSI; RAX; RBX; RDX; R8; R9;
                         R10; R11; R12; R13; R14] ,,
              MAYCHANGE [memory :> bytes(z,8 * 2 * val k)] ,,
              MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`] THEN
  W64_GEN_TAC `w:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--4) THEN
    REWRITE_TAC[MULT_CLAUSES; CONG] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** The outer loop setup with start and end ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x15` `pc + 0x82`
   `\i s. read RDI s = word k /\
          read RSI s = word_add z (word(8 * i)) /\
          read R8 s = m /\
          read RCX s = word w /\
          bignum_from_memory (m,k) s = n /\
          read R9 s = word i /\
          bignum_from_memory(word_add z (word(8 * (k + i))),
                             2 * k - (k + i)) s =
          highdigits a (k + i) /\
          ?r. r < 2 EXP (64 * i) /\
              2 EXP (64 * i) *
              (2 EXP (64 * k) * val(read R14 s) +
               bignum_from_memory(word_add z (word(8 * i)),k) s) + r =
              bignum_from_memory(z,i) s * n + lowdigits a (k + i) /\
              ((n * w + 1 == 0) (mod (2 EXP 64)) ==> r = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:x86state`]
        HIGHDIGITS_BIGNUM_FROM_MEMORY) THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:x86state`]
        LOWDIGITS_BIGNUM_FROM_MEMORY) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `MIN (2 * k) k = k /\ 2 * k - k = k`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
    X86_STEPS_TAC BIGNUM_EMONTREDC_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `2 * k - k = k`] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; VAL_WORD_0; EXP] THEN
    EXISTS_TAC `0` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES; MULT_CLAUSES];
    ALL_TAC; (*** This is the main loop invariant: save for later ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--2);
    GHOST_INTRO_TAC `cout:int64` `read R14` THEN
    X86_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--3) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` MP_TAC) THEN
    ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM MULT_2] THEN REWRITE_TAC[MULT_SYM]] THEN

  (*** Start on the main outer loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cout:num` `\s. val(read R14 s)` THEN
  GHOST_INTRO_TAC `z1:num`
   `bignum_from_memory(word_add z (word (8 * i)),k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GHOST_INTRO_TAC `q:num` `bignum_from_memory (z,i)` THEN
  BIGNUM_TERMRANGE_TAC `i:num` `q:num` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN

  (*** The initial prelude of the Montgomery reduction ***)

  ABBREV_TAC `q0 = (w * z1) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  (*** Rebase some things at z' = z + 8 * i ***)

  ABBREV_TAC `z':int64 = word_add z (word (8 * i))` THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN

  SUBGOAL_THEN
   `word_add z (word (8 * (k + i))):int64 = word_add z' (word(8 * k)) /\
    word_add z (word (8 * (k + i + 1))) = word_add z' (word(8 * (k + 1))) /\
    word_add z (word (8 * (i + 1))):int64 = word_add z' (word(8 * 1))`
  (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
    [EXPAND_TAC "z'" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `n - (k + i + 1) = n - (k + i) - 1`] THEN
  REWRITE_TAC[ARITH_RULE `2 * k - (k + i) = 2 * k - i - k`] THEN

  ABBREV_TAC `p = 2 * k - i` THEN
  SUBGOAL_THEN `~(p = 0) /\ 0 < p /\ k < p` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN UNDISCH_TAC `i:num < k` THEN ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (z',8 * p) (z:int64,8 * i) /\
    nonoverlapping (z',8 * p) (m,8 * k) /\
    nonoverlapping (z',8 * p) (word pc,146)`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [RIP; RSI; RAX; RBX; RDX; R8; R9; R10; R11; R12; R13; R14] ,,
    MAYCHANGE [memory :> bytes (z',8 * p)] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x3a`
   `\s. read RDI s = word k /\
        read RSI s = z' /\
        read R8 s = m /\
        read RCX s = word w /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (z,i) s = q /\
        read R9 s = word i /\
        bignum_from_memory (word_add z' (word (8 * k)),p - k) s =
        highdigits a (k + i) /\
        read R14 s = word cout /\
        bignum_from_memory(word_add z' (word 8),k - 1) s = highdigits z1 1 /\
        read (memory :> bytes64 z') s = word q0 /\
        read R10 s = word 1 /\
        read RBX s = word q0 /\
        read R13 s = word(k - 1) /\
        (read ZF s <=> k = 1) /\
        ?r0. r0 < 2 EXP 64 /\
             2 EXP 64 * (bitval(read CF s) + val(read R11 s)) + r0 =
             q0 * bigdigit n 0 + bigdigit z1 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(m,k) s0 = highdigits n 0 /\
      bignum_from_memory(z',k) s0 = highdigits z1 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_EMONTREDC_EXEC [5;7] (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_1] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM WORD_MUL] THEN ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[ADD_CLAUSES; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
    EXISTS_TAC `val(sum_s7:int64)` THEN REWRITE_TAC[VAL_BOUND_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Break at "montend" to share the end reasoning ***)

  GHOST_INTRO_TAC `carin:bool` `read CF` THEN
  GHOST_INTRO_TAC `mulin:int64` `read R11` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r0:num` STRIP_ASSUME_TAC) THEN

  ENSURES_SEQUENCE_TAC `pc + 0x5f`
   `\s. read RDI s = word k /\
        read RSI s = z' /\
        read R8 s = m /\
        read RCX s = word w /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (z,i) s = q /\
        read R9 s = word i /\
        bignum_from_memory (word_add z' (word (8 * k)),p - k) s =
        highdigits a (k + i) /\
        read R14 s = word cout /\
        read (memory :> bytes64 z') s = word q0 /\
        read R10 s = word k /\
        read RBX s = word q0 /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read R11 s)) +
        bignum_from_memory(z',k) s + r0 =
        q0 + lowdigits z1 k + q0 * lowdigits n k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_EMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
      ASM_REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_PAUP_TAC `1` `k:num` `pc + 0x3c` `pc + 0x5d`
     `\j s. (read RDI s = word k /\
             read RSI s = z' /\
             read R8 s = m /\
             read RCX s = word w /\
             bignum_from_memory (m,k) s = n /\
             bignum_from_memory (z,i) s = q /\
             read R9 s = word i /\
             bignum_from_memory (word_add z' (word (8 * k)),p - k) s =
             highdigits a (k + i) /\
             read R14 s = word cout /\
             bignum_from_memory (word_add z' (word (8 * j)),k - j) s =
             highdigits z1 j /\
             bignum_from_memory (word_add m (word (8 * j)),k - j) s =
             highdigits n j /\
             read (memory :> bytes64 z') s = word q0 /\
             read R10 s = word j /\
             read R13 s = word(k - j) /\
             read RBX s = word q0 /\
             2 EXP (64 * j) * (bitval(read CF s) + val(read R11 s)) +
             bignum_from_memory(z',j) s + r0 =
             q0 + lowdigits z1 j + q0 * lowdigits n j) /\
            (read ZF s <=> j = k)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_EMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_SING] THEN
      ASM_REWRITE_TAC[GSYM highdigits; BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_1] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read R11` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - j:num`; `a:num`; `j:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      UNDISCH_THEN `val(word q0:int64) = q0` (K ALL_TAC) THEN
      SUBGOAL_THEN
       `nonoverlapping (word_add z' (word (8 * j)):int64,8)
                       (word_add z' (word (8 * k)),8 * (p - k))`
      MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
       [SUBGOAL_THEN `word_add z' (word (8 * k)):int64 =
                    word_add (word_add z' (word (8 * j)))
                             (word(8 + 8 * ((k - j) - 1)))`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
          NONOVERLAPPING_TAC];
        DISCH_TAC] THEN
      ABBREV_TAC `z'':int64 = word_add z' (word (8 * k))` THEN
      X86_ACCSTEPS_TAC BIGNUM_EMONTREDC_EXEC [1;4] (1--5) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
       `word_sub x (word_neg y):int64 = word_add x y`]) THEN
      ACCUMULATE_ARITH_TAC "s5" THEN
      X86_ACCSTEPS_TAC BIGNUM_EMONTREDC_EXEC [6] (6--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        ASM_SIMP_TAC[ARITH_RULE
         `j < k ==> (j + 1 = k <=> k - (j + 1) = 0)`] THEN
        REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC WORD_EQ_0 THEN
        REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `k < 2 EXP 64` THEN
        ARITH_TAC] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `q + (e * d1 + d0) + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + q + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (j + 1) = 64 * j + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
       [TAUT `p /\ q /\ r /\ s <=> p /\ s /\ q /\ r`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      X86_SIM_TAC BIGNUM_EMONTREDC_EXEC [1];
      X86_SIM_TAC BIGNUM_EMONTREDC_EXEC [1]];
    ALL_TAC] THEN

  SUBGOAL_THEN `cout < 2` MP_TAC THENL
   [SUBGOAL_THEN `q * n + lowdigits a (k + i) < 2 EXP (64 * (k + i)) * 2`
    MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x < e /\ y < e ==> x + y < e * 2`) THEN
      REWRITE_TAC[LOWDIGITS_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (k + i) = 64 * i + 64 * k`] THEN
      ASM_SIMP_TAC[LT_MULT2; EXP_ADD];
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ARITH_RULE `64 * k + 64 * i = 64 * (i + k)`] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `a + b:num < c ==> a < c`)) THEN
      REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `tc:bool` SUBST_ALL_TAC)] THEN

  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read R11` THEN
  GHOST_INTRO_TAC `z2:num` `bignum_from_memory (z',k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z2:num` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  X86_ACCSIM_TAC BIGNUM_EMONTREDC_EXEC [1;5;7] (1--9) THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  EXISTS_TAC `2 EXP (64 * i) * r0 + r` THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    MATCH_MP_TAC(ARITH_RULE
      `q1 < e /\ q0 < ee /\ (q1 < e ==> (q1 + 1) * ee <= e * ee)
       ==> ee * q1 + q0 < ee * e`) THEN
     ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
     ASM_REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`];
     ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
      ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
    ASM_REWRITE_TAC[EXP_LT_0; ARITH_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `ee * x + w + r = q + z
      ==> e divides ee /\ (w == q) (mod e) /\ (z == 0) (mod e)
          ==> (r == 0) (mod e)`)) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
      UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      EXPAND_TAC "z2" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      CONV_TAC NUMBER_RULE;
      UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
      REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
       `(n * w + 1 == 0) (mod e) ==> (z + (w * z) * n == 0) (mod e)`) THEN
      ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
   [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM LEFT_ADD_DISTRIB] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 1 + k - 1 = k`] THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  SUBGOAL_THEN `(i + 1) + (k - 1) = i + k` SUBST1_TAC THENL
   [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE `k + i + 1 = (k + i) + 1`] THEN
  REWRITE_TAC[ARITH_RULE `64 * (k + i) = 64 * k + 64 * i`; EXP_ADD] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check
   (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
  UNDISCH_TAC `read (memory :> bytes (z',8 * k)) s9 = z2` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [BIGNUM_FROM_MEMORY_EXPAND] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_BITVAL; ADD_CLAUSES;
               BIGDIGIT_BOUND] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING);;

let BIGNUM_EMONTREDC_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 32),40)
                       (z,8 * 2 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_emontredc_tmc); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_emontredc_tmc) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_emontredc_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                      memory :> bytes(word_sub stackpointer (word 32),32)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_emontredc_tmc BIGNUM_EMONTREDC_CORRECT
   `[RBX;  R12; R13; R14]` 32);;

let BIGNUM_EMONTREDC_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 32),40)
                       (z,8 * 2 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_emontredc_mc); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_emontredc_mc) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_emontredc_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                      memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_EMONTREDC_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_emontredc_windows_mc = define_from_elf
   "bignum_emontredc_windows_mc" "x86/generic/bignum_emontredc.obj";;

let bignum_emontredc_windows_tmc = define_trimmed "bignum_emontredc_windows_tmc" bignum_emontredc_windows_mc;;

let BIGNUM_EMONTREDC_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 48),56)
                       (z,8 * 2 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_emontredc_windows_tmc); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_emontredc_windows_tmc) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_emontredc_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(WINDOWS_C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                      memory :> bytes(word_sub stackpointer (word 48),48)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_emontredc_windows_tmc bignum_emontredc_tmc
    BIGNUM_EMONTREDC_CORRECT `[RBX;  R12; R13; R14]` 32);;

let BIGNUM_EMONTREDC_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 48),56)
                       (z,8 * 2 * val k) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_emontredc_windows_mc); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_emontredc_windows_mc) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_emontredc_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(WINDOWS_C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                      memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_EMONTREDC_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

