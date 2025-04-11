(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Division of bignum by a single word when known a priori to be exact.      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_cdiv_exact.o";;
 ****)

let bignum_cdiv_exact_mc =
  define_assert_from_elf "bignum_cdiv_exact_mc" "x86/generic/bignum_cdiv_exact.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x0f; 0x84; 0xba; 0x00; 0x00; 0x00;
                           (* JE (Imm32 (word 186)) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x49; 0x89; 0xca;        (* MOV (% r10) (% rcx) *)
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
  0x4d; 0x89; 0xc5;        (* MOV (% r13) (% r8) *)
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
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_cdiv_exact_tmc = define_trimmed "bignum_cdiv_exact_tmc" bignum_cdiv_exact_mc;;

let BIGNUM_CDIV_EXACT_EXEC = X86_MK_CORE_EXEC_RULE bignum_cdiv_exact_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
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

let BIGNUM_CDIV_EXACT_CORRECT = prove
 (`!k z n x m a pc.
        nonoverlapping (word pc,0xd2) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cdiv_exact_tmc) /\
                  read RIP s = word(pc + 0x7) /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = word(pc + 0xca) /\
                  (~(val m = 0) /\ val m divides a
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k)))
             (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10; R11;
                         RBX; R12; R13; R14] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN W64_GEN_TAC `n:num` THEN
  X_GEN_TAC `x:int64` THEN W64_GEN_TAC `m:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN

  (*** Degenerate case when output size is zero ***)

  ASM_CASES_TAC `k = 0` THENL
   [X86_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--2) THEN
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

  ENSURES_SEQUENCE_TAC `pc + 0x1d`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R9 s = word n /\
        read R10 s = x /\
        bignum_from_memory (x,n) s = a /\
        read R8 s = word m /\
        (~(m = 0) ==> read RCX s = word e)` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--6) THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; WORD_USHR_0] THEN
    ASM_REWRITE_TAC[WORD_CTZ_INDEX; GSYM VAL_EQ_0; MULT_EQ_0;
                    EXP_EQ_0; ARITH_EQ; MOD_64_CLAUSES; MOD_LT] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR] THEN
    ASM_SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ; MOD_LT];
    ALL_TAC] THEN

  (*** The negated modular inverse computation ****)

  ENSURES_SEQUENCE_TAC `pc + 0x75`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R9 s = word n /\
        read R10 s = x /\
        bignum_from_memory (x,n) s = a /\
        read R8 s = word m /\
        (~(m = 0) ==> read RCX s = word e) /\
        (~(m = 0) ==> (m * val(read R11 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--23) THEN
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

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x8c` `pc + 0xc5`
   `\i s. read RDI s = word k /\
          read RSI s = z /\
          read R9 s = word(if n = 0 then 0 else n - 1) /\
          read R10 s = (if n = 0 then x else word_add x (word 8)) /\
          read R8 s = word m /\
          (~(m = 0) ==> read RCX s = word e) /\
          read R11 s = w /\
          read RBX s = word i /\
          (~(m = 0) ==> read R12 s = word(bigdigit a i)) /\
          bignum_from_memory(word_add x (word (8 * i)),MIN n (k + 1) - i) s =
          highdigits (lowdigits a (k + 1)) i /\
          (~(m = 0)
           ==> &(lowdigits (a DIV 2 EXP e) i) +
               (&2 pow (64 * i) - &(bignum_from_memory(z,i) s)) * &m:real =
               &2 pow (64 * i) * &(val(read R13 s)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
      X86_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--5) THEN
      REWRITE_TAC[ARITH_RULE `MIN 0 n = 0`; LOWDIGITS_0; SUB_0] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; DIV_0; BIGDIGIT_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL;
                  LOWDIGITS_TRIVIAL; HIGHDIGITS_0] THEN
      REWRITE_TAC[LOWDIGITS_0; MULT_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
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
    X86_STEPS_TAC BIGNUM_CDIV_EXACT_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; LE] THEN
    ASM_SIMP_TAC[WORD_SUB; LE_1; word_jushr; DIMINDEX_64; MOD_LT] THEN
    REWRITE_TAC[word_ushr; VAL_WORD_BIGDIGIT] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
    REAL_ARITH_TAC;

    ALL_TAC; (*** The main loop invariant ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    X86_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--2);

    GHOST_INTRO_TAC `c:int64` `read R13` THEN
    GHOST_INTRO_TAC `q:num` `bignum_from_memory (z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `q:num` THEN
    X86_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--2) THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    UNDISCH_TAC `m = 0 \/ ODD m` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * k)` THEN
    ASM_REWRITE_TAC[LOWDIGITS_BOUND] THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `lowdigits (a DIV 2 EXP e) k` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN FIRST_ASSUM(SUBST1_TAC o
        MATCH_MP(REAL_ARITH
         `l + (e - q) * m:real = e * c ==> (m * q - l) = e * (m - c)`)) THEN
      REWRITE_TAC[REAL_FIELD `(&2 pow e * a) / &2 pow e = a`] THEN
      REAL_INTEGER_TAC;
      REWRITE_TAC[CONG; lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[GSYM DIV_DIV] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      ASM_SIMP_TAC[GSYM DIVIDES_DIV_MULT; DIVIDES_DIVIDES_DIV_IMP]]] THEN

  (*** Start tackling the main loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `c:int64` `read R13` THEN
  GHOST_INTRO_TAC `q:num` `bignum_from_memory (z,i)` THEN
  BIGNUM_TERMRANGE_TAC `i:num` `q:num` THEN GLOBALIZE_PRECONDITION_TAC THEN

  (*** The optional load depending on whether i < n ***)

  ENSURES_SEQUENCE_TAC `pc + 0x98`
   `\s. read RDI s = word k /\
        read RSI s = z /\
        read R9 s = word(if n = 0 then 0 else n - 1) /\
        read R10 s = (if n = 0 then x else word_add x (word 8)) /\
        read R8 s = word m /\
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
      X86_STEPS_TAC BIGNUM_CDIV_EXACT_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      X86_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--3) THEN
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
   [X86_SIM_TAC BIGNUM_CDIV_EXACT_EXEC (1--14) THEN REWRITE_TAC[WORD_ADD];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  UNDISCH_TAC `m = 0 \/ ODD m` THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN

  X86_ACCSIM_TAC BIGNUM_CDIV_EXACT_EXEC [2;10;11;12] (1--14) THEN
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
    REWRITE_TAC[LE_0; VAL_BOUND_64];
    ALL_TAC] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[REAL_FIELD `(a - &2 pow e * b) / (&2 pow e * &2 pow f) =
                          a / &2 pow f / &2 pow e - b / &2 pow f`] THEN
  REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
  REWRITE_TAC[REAL_ARITH
   `(a + b) + (ee * e - (q + ee * (e - &1 - v))) * m:real =
    (b + (ee - q) * m) + ee * v * m + a`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; REAL_FIELD
   `(&2 pow e * x) / &2 pow 64 / (&2 pow e * &2 pow 64) = x / &2 pow 128`] THEN
  ABBREV_TAC `qd:int64 = word_mul w sum_s2` THEN
  REWRITE_TAC[REAL_ARITH
   `(x + q * m + l) / &2 pow 128 - s / &2 pow 64 =
    ((l + x) + (q * m - &2 pow 64 * s)) / &2 pow 128`] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  FIRST_X_ASSUM(fun th ->
   GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [SYM th]) THEN
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
    EXPAND_TAC "qd" THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
    SIMP_TAC[DIMINDEX_64; MOD_MULT_ADD; VAL_WORD_MUL; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `(w * s) * m + s = (m * w + 1) * s`] THEN
    SIMP_TAC[MOD_LT; VAL_BOUND_64] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM DIVIDES_MOD] THEN
    UNDISCH_TAC `(m * val(w:int64) + 1 == 0) (mod (2 EXP 64))` THEN
    SPEC_TAC(`2 EXP 64`,`p:num`) THEN CONV_TAC NUMBER_RULE;
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 64 * c + s = x ==> x = &2 pow 64 * c + s`)) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN DISCH_THEN SUBST1_TAC THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_CDIV_EXACT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z n x m a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 32),40) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_cdiv_exact_tmc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cdiv_exact_tmc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cdiv_exact_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (~(val m = 0) /\ val m divides a
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_cdiv_exact_tmc BIGNUM_CDIV_EXACT_CORRECT
    `[RBX; R12; R13; R14]` 32);;

let BIGNUM_CDIV_EXACT_SUBROUTINE_CORRECT = prove
 (`!k z n x m a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 32),40) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_cdiv_exact_mc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cdiv_exact_mc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cdiv_exact_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (~(val m = 0) /\ val m divides a
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CDIV_EXACT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cdiv_exact_windows_mc = define_from_elf
   "bignum_cdiv_exact_windows_mc" "x86/generic/bignum_cdiv_exact.obj";;

let bignum_cdiv_exact_windows_tmc = define_trimmed "bignum_cdiv_exact_windows_tmc" bignum_cdiv_exact_windows_mc;;

let BIGNUM_CDIV_EXACT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n x m a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_cdiv_exact_windows_tmc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cdiv_exact_windows_tmc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cdiv_exact_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (~(val m = 0) /\ val m divides a
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_cdiv_exact_windows_tmc bignum_cdiv_exact_tmc
    BIGNUM_CDIV_EXACT_CORRECT `[RBX; R12; R13; R14]` 32);;

let BIGNUM_CDIV_EXACT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z n x m a pc stackpointer returnaddress.
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_cdiv_exact_windows_mc); (x,8 * val n)] /\
        nonoverlapping (word pc,LENGTH bignum_cdiv_exact_windows_mc) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val n) (z,8 * val k))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cdiv_exact_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (~(val m = 0) /\ val m divides a
                   ==> bignum_from_memory (z,val k) s =
                       lowdigits (a DIV val m) (val k)))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CDIV_EXACT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

