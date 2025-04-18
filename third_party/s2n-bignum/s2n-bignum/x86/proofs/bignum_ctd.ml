(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Counting trailing zero digits in a bignum.                                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_ctd.o";;
 ****)

let bignum_ctd_mc = define_assert_from_elf "bignum_ctd_mc" "x86/generic/bignum_ctd.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x1d;              (* JE (Imm8 (word 29)) *)
  0x48; 0x89; 0xfa;        (* MOV (% rdx) (% rdi) *)
  0x48; 0xff; 0xc2;        (* INC (% rdx) *)
  0x48; 0x8b; 0x44; 0xfe; 0xf8;
                           (* MOV (% rax) (Memop Quadword (%%%% (rsi,3,rdi,-- &8))) *)
  0x48; 0x85; 0xc0;        (* TEST (% rax) (% rax) *)
  0x48; 0x0f; 0x45; 0xd7;  (* CMOVNE (% rdx) (% rdi) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xef;              (* JNE (Imm8 (word 239)) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0xc3                     (* RET *)
];;

let bignum_ctd_tmc = define_trimmed "bignum_ctd_tmc" bignum_ctd_mc;;

let BIGNUM_CTD_EXEC = X86_MK_CORE_EXEC_RULE bignum_ctd_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_CTD_CORRECT = prove
 (`!k a x pc.
        ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST bignum_ctd_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read RIP s' = word (pc + 0x25) /\
               C_RETURN s' = if x = 0 then k else word(index 2 x DIV 64))
         (MAYCHANGE [RIP; RDI; RDX; RAX] ,,
          MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_RANGE_TAC "k" "x" THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_TAC `x < 2 EXP (64 * k)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ARITH_RULE `x < 1 <=> x = 0`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CTD_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  ENSURES_WHILE_PDOWN_TAC `k:num` `pc + 0xe` `pc + 0x1d`
   `\i s. (bignum_from_memory (a,k) s = x /\
           read RDI s = word i /\
           read RSI s = a /\
           bignum_from_memory
            (word_add a (word(8 * i)),
             val(word_sub (read RDX s) (word 1)) - i) s = 0 /\
           (val(word_sub (read RDX s) (word 1)) = k \/
            val(word_sub (read RDX s) (word 1)) < k /\
            ~(bigdigit x (val(word_sub (read RDX s) (word 1))) = 0))) /\
          (read ZF s <=> i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CTD_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add x y) y = x`] THEN
    ASM_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_REFL] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    GHOST_INTRO_TAC `i:int64` `read RDX` THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CTD_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    GHOST_INTRO_TAC `i:num` `\s. val(word_sub (read RDX s) (word 1))` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    REWRITE_TAC[WORD_RULE
    `word_sub x (word 1) = word i <=> x = word(i + 1)`] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_CTD_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `word_sub (word (i + 1)) (word 1) = word i`] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
      STRIP_TAC] THEN
    ABBREV_TAC `d = bigdigit x i` THEN
    SUBGOAL_THEN `x = 2 EXP (64 * i) * highdigits x i + lowdigits x i`
    SUBST1_TAC THENL [REWRITE_TAC[HIGH_LOW_DIGITS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
    ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "x" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[lowdigits; BIGNUM_FROM_MEMORY_MOD] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k ==> MIN k i = i`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[INDEX_MUL; INDEX_EXP; PRIME_2; INDEX_REFL; ARITH_LE;
                 ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ; MULT_CLAUSES] THEN
    AP_TERM_TAC THEN SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `i = i + n DIV 64 <=> n < 64`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) (CONJUNCT1 INDEX_MULT_ADD) o
        lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(ARITH_RULE
     `y < 64 ==> (y < 64 ==> x = y) ==> x < 64`) THEN
    MATCH_MP_TAC INDEX_LT THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[BIGDIGIT_BOUND]] THEN

  X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
  VAL_INT64_TAC `j + 1` THEN
  ASSUME_TAC(WORD_RULE
   `!j. word_sub (word (j + 1)) (word 1):int64 = word j`) THEN
  GHOST_INTRO_TAC `i:num` `\s. val(word_sub (read RDX s) (word 1))` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  REWRITE_TAC[WORD_RULE
  `word_sub x (word 1) = word i <=> x = word(i + 1)`] THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read(memory :>
         bytes64(word_add a (word (8 * (j + 1) + 18446744073709551608)))) s0 =
    word(bigdigit x j)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_INDEX_WRAP] THEN EXPAND_TAC "x" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    ASM_REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  X86_STEPS_TAC BIGNUM_CTD_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_SUB_0; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  ASM_CASES_TAC `bigdigit x j = 0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_REFL] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; WORD_RULE
   `word(i + 1):int64 = word(k + 1) <=> word i:int64 = word k`] THEN
  ASM_SIMP_TAC[WORD_EQ_IMP; DIMINDEX_64] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
  REWRITE_TAC[SUB_EQ_0] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add a (word (8 * j))) (word 8) =
    word_add a (word (8 * (j + 1)))`] THEN
  REWRITE_TAC[ARITH_RULE `m - n - 1 = m - (n + 1)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_INDEX_WRAP]) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]);;

let BIGNUM_CTD_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) bignum_ctd_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read RIP s' = returnaddress /\
               read RSP s' = word_add stackpointer (word 8) /\
               C_RETURN s' = if x = 0 then k else word(index 2 x DIV 64))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_ctd_tmc BIGNUM_CTD_CORRECT);;

let BIGNUM_CTD_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) bignum_ctd_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read RIP s' = returnaddress /\
               read RSP s' = word_add stackpointer (word 8) /\
               C_RETURN s' = if x = 0 then k else word(index 2 x DIV 64))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CTD_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_ctd_windows_mc = define_from_elf
   "bignum_ctd_windows_mc" "x86/generic/bignum_ctd.obj";;

let bignum_ctd_windows_tmc = define_trimmed "bignum_ctd_windows_tmc" bignum_ctd_windows_mc;;

let BIGNUM_CTD_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_ctd_windows_tmc); (a,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_ctd_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;a] s /\
                  bignum_from_memory(a,val k) s = x)
             (\s'. read RIP s' = returnaddress /\
                   read RSP s' = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s' =
                   if x = 0 then k else word(index 2 x DIV 64))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_ctd_windows_tmc bignum_ctd_tmc
    BIGNUM_CTD_CORRECT);;

let BIGNUM_CTD_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_ctd_windows_mc); (a,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_ctd_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;a] s /\
                  bignum_from_memory(a,val k) s = x)
             (\s'. read RIP s' = returnaddress /\
                   read RSP s' = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s' =
                   if x = 0 then k else word(index 2 x DIV 64))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CTD_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

