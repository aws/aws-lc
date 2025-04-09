(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Division by 10 with remainder.                                            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_divmod10.o";;
 ****)

let bignum_divmod10_mc =
  define_assert_from_elf "bignum_divmod10_mc" "x86/generic/bignum_divmod10.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x4a;              (* JE (Imm8 (word 74)) *)
  0x49; 0xb9; 0x34; 0x33; 0x33; 0x33; 0x33; 0x33; 0x33; 0x33;
                           (* MOV (% r9) (Imm64 (word 3689348814741910324)) *)
  0x41; 0xba; 0x33; 0x33; 0x33; 0x03;
                           (* MOV (% r10d) (Imm32 (word 53687091)) *)
  0x48; 0x8b; 0x4c; 0xfe; 0xf8;
                           (* MOV (% rcx) (Memop Quadword (%%%% (rsi,3,rdi,-- &8))) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x48; 0xc1; 0xe2; 0x23;  (* SHL (% rdx) (Imm8 (word 35)) *)
  0x48; 0x0f; 0xa4; 0xc8; 0x23;
                           (* SHLD (% rax) (% rcx) (Imm8 (word 35)) *)
  0x48; 0xc1; 0xea; 0x24;  (* SHR (% rdx) (Imm8 (word 36)) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x01; 0xd0;        (* ADD (% rax) (% rdx) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x4d; 0x0f; 0xaf; 0xc2;  (* IMUL (% r8) (% r10) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x4c; 0x89; 0x44; 0xfe; 0xf8;
                           (* MOV (Memop Quadword (%%%% (rsi,3,rdi,-- &8))) (% r8) *)
  0x4f; 0x8d; 0x04; 0x80;  (* LEA (% r8) (%%% (r8,2,r8)) *)
  0x49; 0xf7; 0xd8;        (* NEG (% r8) *)
  0x4a; 0x8d; 0x04; 0x41;  (* LEA (% rax) (%%% (rcx,1,r8)) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xc6;              (* JNE (Imm8 (word 198)) *)
  0xc3                     (* RET *)
];;

let bignum_divmod10_tmc = define_trimmed "bignum_divmod10_tmc" bignum_divmod10_mc;;

let BIGNUM_DIVMOD10_EXEC = X86_MK_CORE_EXEC_RULE bignum_divmod10_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let divmodsteplemma = prove
 (`(2 EXP 64 * h + l) DIV 10 =
   2 EXP 64 * h DIV 10 + (2 EXP 64 * h MOD 10 + l) DIV 10 /\
   (2 EXP 64 * h + l) MOD 10 =
   (2 EXP 64 * h MOD 10 + l) MOD 10`,
  MATCH_MP_TAC DIVMOD_UNIQ THEN ARITH_TAC);;

let BIGNUM_DIVMOD10_CORRECT = time prove
 (`!k z n pc.
      nonoverlapping (word pc,0x52) (z,8 * val k)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_divmod10_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [k; z] s /\
                bignum_from_memory (z,val k) s = n)
           (\s. read RIP s = word (pc + 0x51) /\
                bignum_from_memory (z,val k) s = n DIV 10 /\
                C_RETURN s = word(n MOD 10))
          (MAYCHANGE [RIP; RDI; RAX; RDX; RCX; R8; R9; R10] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Degenerate case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    X86_SIM_TAC BIGNUM_DIVMOD10_EXEC (1--3) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** Setup of the loop ***)

  ENSURES_WHILE_PDOWN_TAC `k:num` `pc + 0x17` `pc + 0x4f`
   `\i s. (read RSI s = z /\
           read R9 s = word 0x3333333333333334 /\
           read R10 s = word 0x3333333 /\
           read RDI s = word i /\
           bignum_from_memory(z,i) s = lowdigits n i /\
           bignum_from_memory (word_add z (word (8 * i)),k - i) s =
           highdigits n i DIV 10 /\
           read RAX s = word(highdigits n i MOD 10)) /\
          (read ZF s <=> i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X86_SIM_TAC BIGNUM_DIVMOD10_EXEC (1--5) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC; (*** The main loop invariant ***)
    REPEAT STRIP_TAC THEN X86_SIM_TAC BIGNUM_DIVMOD10_EXEC [1];
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0] THEN
    X86_SIM_TAC BIGNUM_DIVMOD10_EXEC [1] THEN ASM_REWRITE_TAC[HIGHDIGITS_0]] THEN

  (*** The loop invariant, starting with tweaking then simulation ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_LOWDIGITS] THEN
  SUBGOAL_THEN
   `word(8 * val(word(i + 1):int64) + 18446744073709551608):int64 =
    word(8 * i)`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN
    REWRITE_TAC[SYM(WORD_REDUCE_CONV `word_neg(word 8):int64`)] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP] THEN
  MP_TAC(SPEC `k - i:num` BIGNUM_FROM_MEMORY_EXPAND) THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add z (word(8 * i))) (word 8) =
    word_add z (word(8 * (i + 1)))`] THEN
  ONCE_REWRITE_TAC[divmodsteplemma] THEN
  MAP_EVERY ABBREV_TAC
   [`q = highdigits n (i + 1) DIV 10`; `r = highdigits n (i + 1) MOD 10`] THEN
  SUBGOAL_THEN `r <= 9` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ARITH_TAC; ALL_TAC] THEN
  X86_SIM_TAC BIGNUM_DIVMOD10_EXEC (1--15) THEN

  (*** The basic mathematics, reducing to the quotient computation ***)

  MAP_EVERY ABBREV_TAC
   [`h:int64 = word_subword
     ((word_join:int64->int64->int128) (word r) (word (bigdigit n i)))
     (29,64)`;
    `l:int64 = word_ushr (word_shl (word (bigdigit n i)) 35) 36`] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ; WORD_RULE
   `word(i + 1):int64 = word 1 <=> word i:int64 = word 0`] THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0] THEN REWRITE_TAC[VAL_EQ] THEN
  REWRITE_TAC[WORD_RULE
   `word_add x (word(2 * val(word_neg(word_add q (word(4 * val q)))))) =
    (y:int64) <=>
    word_add y (word(10 * val(q:int64))) = x`] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word a) (word(10 * val(b:int64))):int64 =
    word(10 * val b + a)`] THEN
  MATCH_MP_TAC(MESON[ADD_SYM]
   `(x:num = y ==> q) /\ x = y ==> x + a = a + y /\ q`) THEN
  CONJ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG; DIVISION_SIMP] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_USHR; VAL_WORD_ZX_GEN] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN UNDISCH_TAC `r <= 9` THEN
    MP_TAC(SPECL [`n:num`; `i:num`] BIGDIGIT_BOUND) THEN ARITH_TAC;
    CONV_TAC WORD_REDUCE_CONV] THEN

  (*** The re-splitting into h and l ***)

  SUBGOAL_THEN `val(l:int64) < 2 EXP 28` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    REWRITE_TAC[ARITH_RULE `n DIV 2 EXP 36 < 2 EXP 28 <=> n < 2 EXP 64`] THEN
    REWRITE_TAC[VAL_BOUND_64];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(h:int64) < 2 EXP 39` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    MATCH_MP_TAC(ARITH_RULE
     `r <= 9 /\ w < 2 EXP 64
      ==> 2 EXP (64 - 29) * r MOD 2 EXP 29 + w DIV 2 EXP 29 < 2 EXP 39`) THEN
    REWRITE_TAC[VAL_BOUND_64] THEN MATCH_MP_TAC VAL_WORD_LE THEN
    EXPAND_TAC "r" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(2 EXP 64 * r + bigdigit n i) DIV 10 =
    (2 EXP 28 * val(h:int64) + val(l:int64)) DIV 5`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_SHL; VAL_WORD_BIGDIGIT] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `r <= 9 ==> r < 2 EXP MIN 64 29`] THEN
    REWRITE_TAC[ARITH_RULE
     `(2 EXP 64 * h + l) DIV 2 = 2 EXP 63 * h + l DIV 2`] THEN
    REWRITE_TAC[GSYM DIV_MOD; ARITH_RULE `2 EXP 64 = 2 EXP 36 * 2 EXP 28`] THEN
    SIMP_TAC[DIV_MULT2; GSYM DIV_DIV; EXP_EQ_0; ARITH_EQ; ARITH_RULE
     `2 EXP 36 = 2 EXP 35 * 2 /\ 2 EXP 29 = 2 * 2 EXP 28`] THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The core reciprocal multiplication ***)

  REWRITE_TAC[CONG_ADD_LCANCEL_EQ; ARITH_RULE
   `(2 EXP 28 * h + l) DIV 5 = h * 53687091 + (h + l) DIV 5`] THEN
  ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; DIMINDEX_128; MOD_LT; ARITH_RULE
    `h < 2 EXP 39 /\ l < 2 EXP 28
      ==> h + l < 2 EXP 64 /\
          (h + l) * 3689348814741910324 < 2 EXP 128`] THEN
  MATCH_MP_TAC EQ_IMP_CONG THEN
  MAP_EVERY UNDISCH_TAC
   [`val(l:int64) < 2 EXP 28`; `val(h:int64) < 2 EXP 39`] THEN
  ARITH_TAC);;

let BIGNUM_DIVMOD10_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!k z n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_divmod10_tmc) (z,8 * val k) /\
      nonoverlapping (stackpointer,8) (z,8 * val k)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_divmod10_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [k; z] s /\
                bignum_from_memory (z,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s = n DIV 10 /\
                C_RETURN s = word (n MOD 10))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_divmod10_tmc BIGNUM_DIVMOD10_CORRECT);;

let BIGNUM_DIVMOD10_SUBROUTINE_CORRECT = time prove
 (`!k z n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_divmod10_mc) (z,8 * val k) /\
      nonoverlapping (stackpointer,8) (z,8 * val k)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_divmod10_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [k; z] s /\
                bignum_from_memory (z,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s = n DIV 10 /\
                C_RETURN s = word (n MOD 10))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DIVMOD10_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_divmod10_windows_mc = define_from_elf
   "bignum_divmod10_windows_mc" "x86/generic/bignum_divmod10.obj";;

let bignum_divmod10_windows_tmc = define_trimmed "bignum_divmod10_windows_tmc" bignum_divmod10_windows_mc;;

let BIGNUM_DIVMOD10_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH bignum_divmod10_windows_tmc) /\
      nonoverlapping (word pc,LENGTH bignum_divmod10_windows_tmc) (z,8 * val k) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_divmod10_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z] s /\
                bignum_from_memory (z,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s = n DIV 10 /\
                WINDOWS_C_RETURN s = word (n MOD 10))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_divmod10_windows_tmc bignum_divmod10_tmc
    BIGNUM_DIVMOD10_CORRECT);;

let BIGNUM_DIVMOD10_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!k z n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH bignum_divmod10_windows_mc) /\
      nonoverlapping (word pc,LENGTH bignum_divmod10_windows_mc) (z,8 * val k) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_divmod10_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [k; z] s /\
                bignum_from_memory (z,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val k) s = n DIV 10 /\
                WINDOWS_C_RETURN s = word (n MOD 10))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,val k);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DIVMOD10_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

