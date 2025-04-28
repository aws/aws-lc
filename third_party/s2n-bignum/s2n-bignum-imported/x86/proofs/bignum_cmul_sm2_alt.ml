(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_sm2 of a single word and a bignum < p_sm2.        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/sm2/bignum_cmul_sm2_alt.o";;
 ****)

let bignum_cmul_sm2_alt_mc =
  define_assert_from_elf "bignum_cmul_sm2_alt_mc" "x86/sm2/bignum_cmul_sm2_alt.o"
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
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x01; 0xf0;        (* ADD (% rax) (% rsi) *)
  0x48; 0x11; 0xf2;        (* ADC (% rdx) (% rsi) *)
  0x48; 0xc1; 0xe8; 0x20;  (* SHR (% rax) (Imm8 (word 32)) *)
  0x48; 0x01; 0xf0;        (* ADD (% rax) (% rsi) *)
  0x48; 0xc1; 0xe8; 0x20;  (* SHR (% rax) (Imm8 (word 32)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xc1; 0xe0; 0x20;  (* SHL (% rax) (Imm8 (word 32)) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x11; 0xce;        (* ADC (% rsi) (% rcx) *)
  0x48; 0x29; 0xd0;        (* SUB (% rax) (% rdx) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x29; 0xd6;        (* SUB (% rsi) (% rdx) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584320)) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x48; 0xb9; 0xff; 0xff; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584319)) *)
  0x48; 0x21; 0xf1;        (* AND (% rcx) (% rsi) *)
  0x49; 0x01; 0xf0;        (* ADD (% r8) (% rsi) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x11; 0xf2;        (* ADC (% r10) (% rsi) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_cmul_sm2_alt_tmc = define_trimmed "bignum_cmul_sm2_alt_tmc" bignum_cmul_sm2_alt_mc;;

let BIGNUM_CMUL_SM2_ALT_EXEC = X86_MK_CORE_EXEC_RULE bignum_cmul_sm2_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_sm2 = new_definition `p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF`;;

let sm2redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_sm2 - 1)
       ==> let q = (n DIV 2 EXP 192 + (1 + 2 EXP 32) *
                    n DIV 2 EXP 256 + 2 EXP 64) DIV (2 EXP 64) in
           q < 2 EXP 64 /\
           q * p_sm2 <= n + p_sm2 /\
           n < q * p_sm2 + p_sm2`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_sm2] THEN ARITH_TAC);;

let BIGNUM_CMUL_SM2_ALT_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0xbf) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cmul_sm2_alt_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0xbe) /\
                  (a < p_sm2
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_sm2))
             (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_sm2 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_sm2` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_CMUL_SM2_ALT_EXEC (1--54)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Intermediate result from initial multiply ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_SM2_ALT_EXEC (1--20) (1--20) THEN
  ABBREV_TAC `ca = val(c:int64) * a` THEN
  SUBGOAL_THEN `ca <= (2 EXP 64 - 1) * (p_sm2 - 1)` ASSUME_TAC THENL
   [EXPAND_TAC "ca" THEN MATCH_MP_TAC LE_MULT2 THEN
    ASM_SIMP_TAC[ARITH_RULE `a < n ==> a <= n - 1`; VAL_BOUND_64];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [mullo_s3; sum_s9; sum_s14; sum_s19; sum_s20] =
    val(c:int64) * a`
  (SUBST_ALL_TAC o SYM) THENL
   [EXPAND_TAC "a" THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The computation of the quotient estimate q ***)

  MP_TAC(SPEC `ca:num` sm2redlemma) THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN STRIP_TAC THEN
  X86_ACCSTEPS_TAC BIGNUM_CMUL_SM2_ALT_EXEC [23;24;26;28] (21--28) THEN
  SUBGOAL_THEN `q = val(sum_s28:int64)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `!c. q < 2 EXP 64 /\ (2 EXP 64 * c < 2 EXP 64 * 1 ==> c = 0) /\
          2 EXP 64 * c + s = q ==> q = s`) THEN
    EXISTS_TAC `bitval carry_s28` THEN ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["q"; "ca"] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ca DIV 2 EXP 256 <= p_sm2 DIV 2 EXP 192` MP_TAC THENL
     [UNDISCH_TAC `ca <= (2 EXP 64 - 1) * (p_sm2 - 1)` THEN
      REWRITE_TAC[p_sm2] THEN ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[p_sm2] THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
    ACCUMULATOR_ASSUM_LIST(fun ths -> ASSUM_LIST (fun thc ->
      MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE thc ths)))) THEN
    REWRITE_TAC[VAL_WORD_USHR; REAL_OF_NUM_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ARITH_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`read(rvalue y) d = c`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Main subtraction of q * p_sm2 ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_SM2_ALT_EXEC (29--42) (29--42) THEN
  MP_TAC(ISPECL
   [`sum_s42:int64`;
    `&(bignum_of_wordlist[sum_s38; sum_s39; sum_s40; sum_s41]):real`;
    `256`; `ca:num`; `val(sum_s28:int64) * p_sm2`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(sum_s28:int64) * p_sm2 <= ca + p_sm2`;
        `ca < val(sum_s28:int64) * p_sm2 + p_sm2`] THEN
      REWRITE_TAC[p_sm2; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV)] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_sm2] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REPEAT(MATCH_MP_TAC INTEGER_ADD THEN CONJ_TAC) THEN
    TRY REAL_INTEGER_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC] THEN

  (*** Final correction ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_SM2_ALT_EXEC [47;49;51;53] (43--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s28:int64)`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b <=> ca < val(sum_s28:int64) * p_sm2` THEN
  REWRITE_TAC[REAL_ARITH
   `m - s - (w - b) * n:real = (m - w * n) + (b * n - s)`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[REAL_ADD_RID]
   `x = (if p then y + z else y) ==> x = y + (if p then z else &0)`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_sm2] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `x:real = y + z <=> y = x - z`] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_CMUL_SM2_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_sm2_alt_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_sm2_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_sm2
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_sm2))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_cmul_sm2_alt_tmc
    BIGNUM_CMUL_SM2_ALT_CORRECT);;

let BIGNUM_CMUL_SM2_ALT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_sm2_alt_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_sm2_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_sm2
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_sm2))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_SM2_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cmul_sm2_alt_windows_mc = define_from_elf
   "bignum_cmul_sm2_alt_windows_mc" "x86/sm2/bignum_cmul_sm2_alt.obj";;

let bignum_cmul_sm2_alt_windows_tmc = define_trimmed "bignum_cmul_sm2_alt_windows_tmc" bignum_cmul_sm2_alt_windows_mc;;

let BIGNUM_CMUL_SM2_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_sm2_alt_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_sm2_alt_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_sm2_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_sm2
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_sm2))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_cmul_sm2_alt_windows_tmc
    bignum_cmul_sm2_alt_tmc BIGNUM_CMUL_SM2_ALT_CORRECT);;

let BIGNUM_CMUL_SM2_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_sm2_alt_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_sm2_alt_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_sm2_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_sm2
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_sm2))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_SM2_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

