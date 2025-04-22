(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time bitfield selection from bignum.                             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_bitfield.o";;
 ****)

let bignum_bitfield_mc =
  define_assert_from_elf "bignum_bitfield_mc" "x86/generic/bignum_bitfield.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x5a;              (* JE (Imm8 (word 90)) *)
  0x41; 0xbb; 0x3f; 0x00; 0x00; 0x00;
                           (* MOV (% r11d) (Imm32 (word 63)) *)
  0x49; 0x21; 0xd3;        (* AND (% r11) (% rdx) *)
  0x48; 0xc1; 0xea; 0x06;  (* SHR (% rdx) (Imm8 (word 6)) *)
  0x48; 0xff; 0xc2;        (* INC (% rdx) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4e; 0x8b; 0x14; 0xce;  (* MOV (% r10) (Memop Quadword (%%% (rsi,3,r9))) *)
  0x49; 0x39; 0xd1;        (* CMP (% r9) (% rdx) *)
  0x4d; 0x0f; 0x42; 0xc2;  (* CMOVB (% r8) (% r10) *)
  0x49; 0x0f; 0x44; 0xc2;  (* CMOVE (% rax) (% r10) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0xe9;              (* JB (Imm8 (word 233)) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x49; 0x39; 0xd1;        (* CMP (% r9) (% rdx) *)
  0x4d; 0x0f; 0x42; 0xc2;  (* CMOVB (% r8) (% r10) *)
  0x4d; 0x85; 0xdb;        (* TEST (% r11) (% r11) *)
  0x49; 0x0f; 0x44; 0xc2;  (* CMOVE (% rax) (% r10) *)
  0x48; 0x83; 0xf9; 0x40;  (* CMP (% rcx) (Imm8 (word 64)) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x49; 0xd3; 0xe2;        (* SHL (% r10) (% cl) *)
  0x49; 0xff; 0xca;        (* DEC (% r10) *)
  0x4c; 0x89; 0xd9;        (* MOV (% rcx) (% r11) *)
  0x49; 0xd3; 0xe8;        (* SHR (% r8) (% cl) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x48; 0xd3; 0xe0;        (* SHL (% rax) (% cl) *)
  0x4c; 0x09; 0xc0;        (* OR (% rax) (% r8) *)
  0x4c; 0x21; 0xd0;        (* AND (% rax) (% r10) *)
  0xc3                     (* RET *)
];;

let bignum_bitfield_tmc = define_trimmed "bignum_bitfield_tmc" bignum_bitfield_mc;;

let BIGNUM_BITFIELD_EXEC = X86_MK_CORE_EXEC_RULE bignum_bitfield_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_BITFIELD_CORRECT = prove
 (`!k x n l a pc.
        ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST bignum_bitfield_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [k;x;n;l] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read RIP s = word(pc + 0x62) /\
              C_RETURN s = word((a DIV (2 EXP val n)) MOD (2 EXP val l)))
         (MAYCHANGE [RIP; RDX; RCX; RAX; R8; R9; R10; R11] ,,
          MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `x:int64` THEN
  MAP_EVERY W64_GEN_TAC [`n:num`; `l:num`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `a:num` THEN

  (*** The trivial case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[DIV_0; MOD_0];
    ALL_TAC] THEN

  (*** Ghost the uninitialized variable d, which gets assigned in the loop ***)

  GHOST_INTRO_TAC `d0:int64` `read R8` THEN

  (*** Main loop setup ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x1b` `pc + 0x2d`
   `\i s. read RDI s = word k /\
          read RSI s = x /\
          read RDX s = word(n DIV 64 + 1) /\
          read RCX s = word l /\
          read R8 s = (if i = 0 then d0
                       else word(bigdigit a (MIN (i - 1) (n DIV 64)))) /\
          read RAX s = (if i <= n DIV 64 + 1 then word 0
                       else word(bigdigit a (n DIV 64 + 1))) /\
          read R9 s = word i /\
          read R11 s = word(n MOD 64) /\
          bignum_from_memory(word_add x (word(8 * i)),k - i) s =
          highdigits a i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; LOWDIGITS_0; BIGDIGIT_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[HIGHDIGITS_0; LE_0] THEN
    REWRITE_TAC[ARITH_RULE `64 = 2 EXP 6 /\ 63 = 2 EXP 6 - 1`] THEN
    ASM_REWRITE_TAC[word_ushr; WORD_ADD] THEN CONV_TAC SYM_CONV THEN
    ASM_REWRITE_TAC[WORD_AND_MASK_WORD];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    VAL_INT64_TAC `n DIV 64 + 1` THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
    CONJ_TAC THEN AP_TERM_TAC THENL
     [SIMP_TAC[ARITH_RULE `~(i < n + 1) ==> MIN (i - 1) n = n`] THEN
      REWRITE_TAC[ADD_SUB; ARITH_RULE
       `MIN i n = if i < n + 1 then i else n`] THEN
      ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[ARITH_RULE `0 < n + 1`] THEN
      MESON_TAC[];
      ASM_CASES_TAC `i = n DIV 64 + 1` THEN
      ASM_REWRITE_TAC[LE_ADD_RCANCEL; ARITH_RULE `~(n + 1 <= n)`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `i <= n + 1 <=> i = n + 1 \/ i <= n`]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Outcome of the digit-pair selection tidied up and uncluttered ***)

  ENSURES_SEQUENCE_TAC `pc + 0x3c`
   `\s. read RCX s = word l /\
        read R8 s = word(bigdigit a (n DIV 64)) /\
        read RAX s = word(bigdigit a (n DIV 64 + 1)) /\
        read R10 s = word 0 /\
        read R11 s = word(n MOD 64)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    VAL_INT64_TAC `n DIV 64 + 1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `k < n + 1 <=> k <= n`] THEN
    SIMP_TAC[ARITH_RULE `~(k <= n) ==> MIN (k - 1) n = n`] THEN
    CONJ_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BIGDIGIT_ZERO THEN
    TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN ASM_REWRITE_TAC[LE_EXP] THENL
     [UNDISCH_TAC `k <= n DIV 64`; UNDISCH_TAC `k <= n DIV 64 + 1`] THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The fiddling round to make the final bitfield ***)

  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_BITFIELD_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  VAL_INT64_TAC `n MOD 64` THEN
  ASM_REWRITE_TAC[WORD_SUB_0; WORD_SUB_LZERO; word_jshl; word_jushr] THEN
  REWRITE_TAC[word_shl; word_ushr; DIMINDEX_64; VAL_WORD_1; MULT_CLAUSES] THEN
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; MOD_MOD_REFL] THEN

  REWRITE_TAC[VAL_WORD_BITVAL] THEN
  REWRITE_TAC[VAL_WORD; ARITH_RULE `256 = 2 EXP 8 /\ 64 = 2 EXP 6`] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN; DIMINDEX_8; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN

  SUBGOAL_THEN
   `word_sub
     (word(bitval (l < 64) * 2 EXP (l MOD 64))) (word 1):int64 =
    word(2 EXP l - 1)`
  SUBST1_TAC THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[GSYM MASK_WORD_SUB] THEN
    REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[MOD_LT; VAL_WORD_0; VAL_WORD_1; MULT_CLAUSES] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64; GSYM DIVIDES_MOD] THEN
    MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_ARITH_TAC;
    REWRITE_TAC[WORD_AND_MASK_WORD]] THEN

  GEN_REWRITE_TAC BINOP_CONV [GSYM WORD_MOD_SIZE] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `MIN a b = MIN b a`] THEN
  REWRITE_TAC[GSYM MOD_MOD_EXP_MIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN

  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; WORD_OR_0; EXP; DIV_1] THEN
    SIMP_TAC[VAL_WORD; MOD_MOD_REFL; bigdigit; DIMINDEX_64; MOD_MOD_REFL] THEN
    MP_TAC(SPECL [`n:num`; `64`] (CONJUNCT2 DIVISION_SIMP)) THEN
    ASM_SIMP_TAC[ADD_CLAUSES];
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND]] THEN

  SUBGOAL_THEN
   `val(word_neg(word (n MOD 64)):int64) MOD 64 = 64 - n MOD 64`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `64` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(n MOD 64 = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `n - b + b = n /\ (a + b == 0) (mod n) ==> (a == n - b) (mod n)`) THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `word(n MOD 64):int64` CONG_WORD_NEG) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o SPEC `2 EXP 6` o MATCH_MP (NUMBER_RULE
     `!m:num. (a == b) (mod n) ==> m divides n ==> (a == b) (mod m)`)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN

  W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o
    lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; BIT_WORD_AND] THEN
    MP_TAC(ISPECL [`word(bigdigit a (n DIV 64)):int64`; `n MOD 64`]
        BIT_WORD_USHR) THEN
    MP_TAC(ISPECL [`word(bigdigit a (n DIV 64 + 1)):int64`; `64 - n MOD 64`]
        BIT_WORD_SHL) THEN
    REWRITE_TAC[word_ushr; word_shl] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REPEAT(DISCH_THEN(K ALL_TAC)) THEN
    REWRITE_TAC[ARITH_RULE `64 - n MOD 64 <= i <=> 64 <= i + n MOD 64`] THEN
    REWRITE_TAC[GSYM DIMINDEX_64] THEN MESON_TAC[BIT_TRIVIAL];
    DISCH_THEN SUBST1_TAC] THEN

  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN

  MP_TAC(ARITH_RULE `n = 64 * n DIV 64 + n MOD 64`) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  REWRITE_TAC[GSYM highdigits; EXP_ADD; GSYM DIV_DIV] THEN
  REPLICATE_TAC 2 (ONCE_REWRITE_TAC[HIGHDIGITS_STEP]) THEN

  REWRITE_TAC[DIV_MOD; DIV_DIV; GSYM EXP_ADD; ARITH_RULE
   `(e * (e * a + b) + c):num = (e * e) * a + e * b + c`] THEN
  SUBGOAL_THEN
   `2 EXP (64 + 64) =
    2 EXP (n MOD 64 + 64) * 2 EXP (64 - n MOD 64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[GSYM MULT_ASSOC; MOD_MULT_ADD]] THEN

  REWRITE_TAC[GSYM DIV_MOD; EXP_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `2 EXP 64 = 2 EXP (n MOD 64) * 2 EXP (64 - n MOD 64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; EXP_EQ_0; ARITH]] THEN
  ARITH_TAC);;

let BIGNUM_BITFIELD_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k x n l a pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) bignum_bitfield_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [k;x;n;l] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word((a DIV (2 EXP val n)) MOD (2 EXP val l)))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_bitfield_tmc BIGNUM_BITFIELD_CORRECT);;

let BIGNUM_BITFIELD_SUBROUTINE_CORRECT = prove
 (`!k x n l a pc stackpointer returnaddress.
        ensures x86
         (\s. bytes_loaded s (word pc) bignum_bitfield_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [k;x;n;l] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s = word((a DIV (2 EXP val n)) MOD (2 EXP val l)))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_BITFIELD_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_bitfield_windows_mc = define_from_elf
   "bignum_bitfield_windows_mc" "x86/generic/bignum_bitfield.obj";;

let bignum_bitfield_windows_tmc = define_trimmed "bignum_bitfield_windows_tmc" bignum_bitfield_windows_mc;;

let BIGNUM_BITFIELD_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k x n l a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_bitfield_windows_tmc); (x,8 * val k)]
        ==> ensures x86
               (\s. bytes_loaded s (word pc) bignum_bitfield_windows_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    WINDOWS_C_ARGUMENTS [k;x;n;l] s /\
                    bignum_from_memory (x,val k) s = a)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    WINDOWS_C_RETURN s =
                    word((a DIV (2 EXP val n)) MOD (2 EXP val l)))
               (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_bitfield_windows_tmc bignum_bitfield_tmc
    BIGNUM_BITFIELD_CORRECT);;

let BIGNUM_BITFIELD_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k x n l a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_bitfield_windows_mc); (x,8 * val k)]
        ==> ensures x86
               (\s. bytes_loaded s (word pc) bignum_bitfield_windows_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    WINDOWS_C_ARGUMENTS [k;x;n;l] s /\
                    bignum_from_memory (x,val k) s = a)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    WINDOWS_C_RETURN s =
                    word((a DIV (2 EXP val n)) MOD (2 EXP val l)))
               (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_BITFIELD_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

