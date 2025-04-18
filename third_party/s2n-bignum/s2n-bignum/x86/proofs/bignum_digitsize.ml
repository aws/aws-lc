(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Size in digits of a bignum.                                               *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_digitsize.o";;
 ****)

let bignum_digitsize_mc = define_assert_from_elf "bignum_digitsize_mc" "x86/generic/bignum_digitsize.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x16;              (* JE (Imm8 (word 22)) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x48; 0x8b; 0x0c; 0xd6;  (* MOV (% rcx) (Memop Quadword (%%% (rsi,3,rdx))) *)
  0x48; 0xff; 0xc2;        (* INC (% rdx) *)
  0x48; 0x85; 0xc9;        (* TEST (% rcx) (% rcx) *)
  0x48; 0x0f; 0x45; 0xc2;  (* CMOVNE (% rax) (% rdx) *)
  0x48; 0x39; 0xfa;        (* CMP (% rdx) (% rdi) *)
  0x75; 0xed;              (* JNE (Imm8 (word 237)) *)
  0xc3                     (* RET *)
];;

let bignum_digitsize_tmc = define_trimmed "bignum_digitsize_tmc" bignum_digitsize_mc;;

let BIGNUM_DIGITSIZE_EXEC = X86_MK_CORE_EXEC_RULE bignum_digitsize_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_DIGITSIZE_CORRECT = prove
 (`!k a x pc.
        ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST bignum_digitsize_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read RIP s' = word (pc + 0x1e) /\
               C_RETURN s' = word((bitsize x + 63) DIV 64))
         (MAYCHANGE [RIP; RDI; RDX; RCX; RAX] ,,
          MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_RANGE_TAC "k" "x" THEN

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_TAC `x < 2 EXP (64 * k)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ARITH_RULE `x < 1 <=> x = 0`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_DIGITSIZE_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[BITSIZE_0] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0xb` `pc + 0x1c`
   `\i s. (bignum_from_memory (a,k) s = x /\
           read RDI s = word k /\
           read RSI s = a /\
           read RDX s = word i /\
           bignum_from_memory(word_add a (word(8 * val(read RAX s))),
                              i - val(read RAX s)) s = 0 /\
           (read RAX s = word 0 \/
            ~(read RAX s = word 0) /\ val(read RAX s) <= i /\
            ~(bigdigit x (val(word_sub (read RAX s) (word 1))) = 0))) /\
          (read ZF s <=> i = k)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_DIGITSIZE_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0; SUB_REFL] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    GHOST_INTRO_TAC `r:int64` `read RAX` THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_DIGITSIZE_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `r:int64` `read RAX` THEN
    ABBREV_TAC `i = val(r:int64)` THEN
    SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL
     [ASM_MESON_TAC[VAL_BOUND_64]; ALL_TAC] THEN
    VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_DIGITSIZE_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `val(word 0:int64) = i` THEN
      REWRITE_TAC[VAL_WORD_0] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; SUB_0; WORD_ADD_0]) THEN
      UNDISCH_TAC `read (memory :> bytes (a,8 * k)) s1 = x` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[BITSIZE_0; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `val(word_sub r (word 1):int64) = i - 1` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= i <=> ~(i = 0)`];
      ALL_TAC] THEN
    ABBREV_TAC `d = bigdigit x (i - 1)` THEN
    SUBGOAL_THEN `x = 2 EXP (64 * i) * highdigits x i + lowdigits x i`
    SUBST1_TAC THENL [REWRITE_TAC[HIGH_LOW_DIGITS]; ALL_TAC] THEN
    SUBGOAL_THEN `highdigits x i = 0` SUBST1_TAC THENL
     [EXPAND_TAC "x" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[highdigits; BIGNUM_FROM_MEMORY_DIV] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]] THEN
    SUBGOAL_THEN `i = (i - 1) + 1` SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
    ASM_SIMP_TAC[BITSIZE_MULT_ADD; LOWDIGITS_BOUND] THEN
    TRANS_TAC EQ_TRANS `word i:int64` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[WORD_VAL]; AP_TERM_TAC] THEN
    MP_TAC(SPEC `d:num` BITSIZE_EQ_0) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `bitsize (bigdigit x (i - 1)) <= 64` MP_TAC THENL
     [REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND];
      MAP_EVERY UNDISCH_TAC [`~(i = 0)`; `i:num <= k`]] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN

  X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
  VAL_INT64_TAC `j + 1` THEN
  GHOST_INTRO_TAC `r:int64` `read RAX` THEN
  ABBREV_TAC `i = val(r:int64)` THEN
  SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL
   [ASM_MESON_TAC[VAL_BOUND_64]; ALL_TAC] THEN
  VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read(memory :> bytes64(word_add a (word(8 * j)))) s0 = word(bigdigit x j)`
  ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    ASM_REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  X86_STEPS_TAC BIGNUM_DIGITSIZE_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; REWRITE_TAC[CONJ_ASSOC]] THEN
  CONJ_TAC THENL
   [SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND];
    REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM WORD_ADD] THEN
    MATCH_MP_TAC WORD_EQ_IMP THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
  ASM_CASES_TAC `bigdigit x j = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r:int64 = word 0` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `val(r:int64) = i` THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; ADD_CLAUSES; MULT_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0; MULT_CLAUSES; SUB_0]) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
    SIMP_TAC[ARITH_RULE `i <= j ==> i <= j + 1`] THEN
    SIMP_TAC[ARITH_RULE `i <= j ==> (j + 1) - i = (j - i) + 1`] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; MULT_EQ_0; ADD_CLAUSES] THEN
    DISJ2_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= j ==> 8 * i + 8 * (j - i) = 8 * j`] THEN
    REWRITE_TAC[VAL_WORD_0];
    UNDISCH_TAC `val(r:int64) = i` THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add x y) y = x`] THEN
    VAL_INT64_TAC `j:num` THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    REWRITE_TAC[SUB_REFL; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    DISJ2_TAC THEN REWRITE_TAC[LE_REFL] THEN
    VAL_INT64_TAC `j + 1` THEN ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN
    ARITH_TAC;
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM VAL_EQ_0]) THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `1 <= i <=> ~(i = 0)`] THEN
    VAL_INT64_TAC `j:num` THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; ADD_EQ_0; ARITH_EQ; ADD_SUB; LE_REFL] THEN
    REWRITE_TAC[SUB_REFL; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]]);;

let BIGNUM_DIGITSIZE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) bignum_digitsize_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read RIP s' = returnaddress /\
               read RSP s' = word_add stackpointer (word 8) /\
               C_RETURN s' = word((bitsize x + 63) DIV 64))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_digitsize_tmc BIGNUM_DIGITSIZE_CORRECT);;

let BIGNUM_DIGITSIZE_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) bignum_digitsize_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [k;a] s /\
              bignum_from_memory(a,val k) s = x)
         (\s'. read RIP s' = returnaddress /\
               read RSP s' = word_add stackpointer (word 8) /\
               C_RETURN s' = word((bitsize x + 63) DIV 64))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DIGITSIZE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_digitsize_windows_mc = define_from_elf
   "bignum_digitsize_windows_mc" "x86/generic/bignum_digitsize.obj";;

let bignum_digitsize_windows_tmc = define_trimmed "bignum_digitsize_windows_tmc" bignum_digitsize_windows_mc;;

let BIGNUM_DIGITSIZE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_digitsize_windows_tmc); (a,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_digitsize_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;a] s /\
                  bignum_from_memory(a,val k) s = x)
             (\s'. read RIP s' = returnaddress /\
                   read RSP s' = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s' = word((bitsize x + 63) DIV 64))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_digitsize_windows_tmc bignum_digitsize_tmc
   BIGNUM_DIGITSIZE_CORRECT);;

let BIGNUM_DIGITSIZE_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k a x pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_digitsize_windows_mc); (a,8 * val k)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_digitsize_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;a] s /\
                  bignum_from_memory(a,val k) s = x)
             (\s'. read RIP s' = returnaddress /\
                   read RSP s' = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s' = word((bitsize x + 63) DIV 64))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DIGITSIZE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

