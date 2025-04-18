(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_256 of a single word and a bignum < p_256.        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p256/bignum_cmul_p256_alt.o";;
 ****)

let bignum_cmul_p256_alt_mc =
  define_assert_from_elf "bignum_cmul_p256_alt_mc" "x86/p256/bignum_cmul_p256_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x8b; 0x01;        (* MOV (% rax) (Memop Quadword (%% (rcx,0))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x41; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rcx,8))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x41; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rcx,16))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x8b; 0x41; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rcx,24))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0xf0;        (* MOV (% rax) (% rsi) *)
  0x4c; 0x0f; 0xa4; 0xd8; 0x20;
                           (* SHLD (% rax) (% r11) (Imm8 (word 32)) *)
  0x48; 0x89; 0xf1;        (* MOV (% rcx) (% rsi) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x31; 0xd2;        (* XOR (% rdx) (% rdx) *)
  0x48; 0x83; 0xea; 0x01;  (* SUB (% rdx) (Imm8 (word 1)) *)
  0x4c; 0x11; 0xd8;        (* ADC (% rax) (% r11) *)
  0x48; 0x11; 0xf1;        (* ADC (% rcx) (% rsi) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294967296)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc8;        (* ADD (% r8) (% rcx) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x29; 0xc1;        (* SUB (% r9) (% rax) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x48; 0x83; 0xde; 0x00;  (* SBB (% rsi) (Imm8 (word 0)) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x29; 0xc3;        (* SUB (% r11) (% rax) *)
  0x48; 0x19; 0xd6;        (* SBB (% rsi) (% rdx) *)
  0xb8; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967295)) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x48; 0x31; 0xc9;        (* XOR (% rcx) (% rcx) *)
  0x48; 0x29; 0xc1;        (* SUB (% rcx) (% rax) *)
  0x49; 0x01; 0xf0;        (* ADD (% r8) (% rsi) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_cmul_p256_alt_tmc = define_trimmed "bignum_cmul_p256_alt_tmc" bignum_cmul_p256_alt_mc;;

let BIGNUM_CMUL_P256_ALT_EXEC = X86_MK_CORE_EXEC_RULE bignum_cmul_p256_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let p256redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_256 - 1)
       ==> let q = (n DIV 2 EXP 192 + n DIV 2 EXP 224 + 1) DIV 2 EXP 64 in
           q < 2 EXP 64 /\
           q * p_256 <= n + p_256 /\
           n < q * p_256 + p_256`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256] THEN ARITH_TAC);;

let BIGNUM_CMUL_P256_ALT_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0xbe) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cmul_p256_alt_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0xbd) /\
                  (a < p_256
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256))
             (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_256 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_256` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_CMUL_P256_ALT_EXEC (1--53)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Intermediate result from initial multiply ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P256_ALT_EXEC (1--20) (1--20) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s3; sum_s9; sum_s14; sum_s19; sum_s20] =
    val(c:int64) * a`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The quotient approximation logic ***)

  MP_TAC(SPEC `val(c:int64) * a` p256redlemma) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN
    MP_TAC(ISPEC `c:int64` VAL_BOUND) THEN UNDISCH_TAC `a < p_256` THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV)] THEN
  ABBREV_TAC
   `q = ((val(c:int64) * a) DIV 2 EXP 192 +
         (val(c:int64) * a) DIV 2 EXP 224 + 1) DIV 2 EXP 64` THEN
  STRIP_TAC THEN
  X86_ACCSTEPS_TAC BIGNUM_CMUL_P256_ALT_EXEC [27;28] (21--28) THEN
  SUBGOAL_THEN `q = val(sum_s28:int64)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(MESON[MOD_LT]
     `q < 2 EXP 64 /\ q MOD 2 EXP 64 = a ==> q = a`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[DIV_MOD] THEN MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `val(sum_s27:int64)` THEN REWRITE_TAC[VAL_BOUND_64] THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `bitval carry_s28` THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT; VAL_WORD_USHR] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [mullo_s3; sum_s9; sum_s14; sum_s19; sum_s20] =
      val(c:int64) * a`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Pre-reduction subtraction ****)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P256_ALT_EXEC (29--41) (29--41) THEN
  SUBGOAL_THEN
   `sum_s41:int64 = word_neg(word(bitval(val c * a < val sum_s28 * p_256))) /\
    &(bignum_of_wordlist [sum_s31; sum_s34; sum_s35; sum_s40]):real =
    (if val c * a < val sum_s28 * p_256
     then &(val c * a) - &(val sum_s28 * p_256) + &2 pow 256
     else &(val(c:int64) * a) - &(val(sum_s28:int64) * p_256))`
  (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [MATCH_MP_TAC MASK_AND_VALUE_FROM_CARRY_LT THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(sum_s28:int64) * p_256 <= val(c:int64) * a + p_256`;
        `val(c:int64) * a < val(sum_s28:int64) * p_256 + p_256`] THEN
      REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; CONV_TAC NUM_REDUCE_CONV] THEN
    SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [mullo_s3; sum_s9; sum_s14; sum_s19; sum_s20] =
      val(c:int64) * a`)) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P256_ALT_EXEC [46;48;50;52] (42--53) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s28:int64)`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b <=> val(c:int64) * a < val(sum_s28:int64) * p_256` THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MESON[bitval; REAL_ADD_RID; REAL_MUL_RZERO; REAL_MUL_RID]
     `(if b then x + e else x:real) = x + e * &(bitval b)`]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = y - z + e * b ==> y = (x + z) - e * b`)) THEN
  REWRITE_TAC[p_256] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_CMUL_P256_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_p256_alt_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p256_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_256
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_cmul_p256_alt_tmc
    BIGNUM_CMUL_P256_ALT_CORRECT);;

let BIGNUM_CMUL_P256_ALT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_p256_alt_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p256_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_256
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P256_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cmul_p256_alt_windows_mc = define_from_elf
   "bignum_cmul_p256_alt_windows_mc" "x86/p256/bignum_cmul_p256_alt.obj";;

let bignum_cmul_p256_alt_windows_tmc = define_trimmed "bignum_cmul_p256_alt_windows_tmc" bignum_cmul_p256_alt_windows_mc;;

let BIGNUM_CMUL_P256_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_p256_alt_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_p256_alt_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p256_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_256
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_cmul_p256_alt_windows_tmc
    bignum_cmul_p256_alt_tmc BIGNUM_CMUL_P256_ALT_CORRECT);;

let BIGNUM_CMUL_P256_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_p256_alt_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_p256_alt_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p256_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_256
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P256_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

