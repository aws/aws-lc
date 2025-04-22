(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_384 of a single word and a bignum < p_384.        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_cmul_p384_alt.o";;
 ****)

let bignum_cmul_p384_alt_mc =
  define_assert_from_elf "bignum_cmul_p384_alt_mc" "x86/p384/bignum_cmul_p384_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x41; 0x54;              (* PUSH (% r12) *)
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
  0x4d; 0x31; 0xe4;        (* XOR (% r12) (% r12) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x48; 0x8b; 0x41; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rcx,32))) *)
  0x48; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% rsi) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0xf0;        (* MOV (% rax) (% rsi) *)
  0x48; 0x89; 0xd6;        (* MOV (% rsi) (% rdx) *)
  0x48; 0xf7; 0x61; 0x28;  (* MUL2 (% rdx,% rax) (Memop Quadword (%% (rcx,40))) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0xb8; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x48; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% rdx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0xf7; 0xd1;        (* NOT (% rcx) *)
  0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% edx) (Imm32 (word 4294967295)) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x21; 0xca;        (* AND (% rdx) (% rcx) *)
  0x48; 0x29; 0xd0;        (* SUB (% rax) (% rdx) *)
  0x48; 0x83; 0xe1; 0x01;  (* AND (% rcx) (Imm8 (word 1)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x67; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r12) *)
  0x48; 0x83; 0xde; 0x00;  (* SBB (% rsi) (Imm8 (word 0)) *)
  0x48; 0x89; 0x77; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rsi) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0xc3                     (* RET *)
];;

let bignum_cmul_p384_alt_tmc = define_trimmed "bignum_cmul_p384_alt_tmc" bignum_cmul_p384_alt_mc;;

let BIGNUM_CMUL_P384_ALT_EXEC = X86_MK_CORE_EXEC_RULE bignum_cmul_p384_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let p384redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_384 - 1)
       ==> let q = n DIV 2 EXP 384 + 1 in
           q < 2 EXP 64 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let BIGNUM_CMUL_P384_ALT_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0xe3) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cmul_p384_alt_tmc) /\
                  read RIP s = word(pc + 0x02) /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = word (pc + 0xe0) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s = (val c * a) MOD p_384))
             (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11; R12] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_384 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_384` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_CMUL_P384_ALT_EXEC (1--64)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Introduce variables for top and bottom of initial product ***)

  MAP_EVERY ABBREV_TAC
   [`h = (val(c:int64) * a) DIV 2 EXP 384`;
    `l = (val(c:int64) * a) MOD 2 EXP 384`] THEN
  SUBGOAL_THEN `2 EXP 384 * h + l = val(c:int64) * a` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    MESON_TAC[DIVISION_SIMP; MULT_SYM];
    ALL_TAC] THEN

  (*** Intermediate result from initial multiply ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P384_ALT_EXEC (1--30) (1--30) THEN
  SUBGOAL_THEN
   `h + 1 = val(sum_s30:int64) /\
    bignum_of_wordlist[mullo_s3; sum_s9; sum_s14; sum_s19; sum_s23; sum_s29] =
    l`
  STRIP_ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN MP_TAC(SPECL
     [`val(c:int64) * a + 1 * 2 EXP 384`; `2 EXP 384`] DIVMOD_UNIQ) THEN
    SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ; EXP_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "a" THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P384_ALT_EXEC (32--45) (31--47) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NOT_MASK; WORD_NEG_NEG]) THEN
  DISCARD_FLAGS_TAC THEN
  ABBREV_TAC `b <=> ~carry_s45` THEN
  ABBREV_TAC
   `m = bignum_of_wordlist
         [sum_s33; sum_s41; sum_s42; sum_s43; sum_s44; sum_s45]` THEN
  SUBGOAL_THEN
   `m + (h + 1) * p_384 = 2 EXP 384 * bitval b + val(c:int64) * a`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `x = y + e * h + z <=> e + x = e * (h + 1) + y + z`] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["l"; "m"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  SUBGOAL_THEN `val(c:int64) * a < val(sum_s30:int64) * p_384 <=> b`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `m + (h + 1) * p_384 = 2 EXP 384 * bitval b + val(c:int64) * a` THEN
    BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES]
    THENL [ALL_TAC; REAL_ARITH_TAC] THEN MATCH_MP_TAC(REAL_ARITH
     `m:real < e ==> m + s = e + ca ==> ca < s`) THEN
    EXPAND_TAC "m" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Final correction ****)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P384_ALT_EXEC [53;55;57;59;61;63] (48--64) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `val(c:int64) * a` p384redlemma) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN
    MP_TAC(ISPEC `c:int64` VAL_BOUND) THEN UNDISCH_TAC `a < p_384` THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s30:int64)`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p_384] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC
   `m + (h + 1) * p_384 = 2 EXP 384 * bitval b + val(c:int64) * a` THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP
   (REAL_ARITH `a:real = b + x ==> x = a - b`)) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_CMUL_P384_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 8),8) (x,8 * 6) /\
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 8),16) /\
        ALL (nonoverlapping (word pc,LENGTH bignum_cmul_p384_alt_tmc))
            [(z,8 * 6); (word_sub stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p384_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s = (val c * a) MOD p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`,
  X86_PROMOTE_RETURN_STACK_TAC
    bignum_cmul_p384_alt_tmc BIGNUM_CMUL_P384_ALT_CORRECT
    `[R12]` 8);;

let BIGNUM_CMUL_P384_ALT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 8),8) (x,8 * 6) /\
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 8),16) /\
        ALL (nonoverlapping (word pc,LENGTH bignum_cmul_p384_alt_mc))
            [(z,8 * 6); (word_sub stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p384_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s = (val c * a) MOD p_384))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P384_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cmul_p384_alt_windows_mc = define_from_elf
   "bignum_cmul_p384_alt_windows_mc" "x86/p384/bignum_cmul_p384_alt.obj";;

let bignum_cmul_p384_alt_windows_tmc = define_trimmed "bignum_cmul_p384_alt_windows_tmc" bignum_cmul_p384_alt_windows_mc;;

let BIGNUM_CMUL_P384_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 24),24) (x,8 * 6) /\
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 24),32) /\
        ALL (nonoverlapping (word pc,LENGTH bignum_cmul_p384_alt_windows_tmc))
            [(z,8 * 6); (word_sub stackpointer (word 24),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p384_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s = (val c * a) MOD p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                         memory :> bytes(word_sub stackpointer (word 24),24)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    bignum_cmul_p384_alt_windows_tmc bignum_cmul_p384_alt_tmc
    BIGNUM_CMUL_P384_ALT_CORRECT `[R12]` 8);;

let BIGNUM_CMUL_P384_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 24),24) (x,8 * 6) /\
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 24),32) /\
        ALL (nonoverlapping (word pc,LENGTH bignum_cmul_p384_alt_windows_mc))
            [(z,8 * 6); (word_sub stackpointer (word 24),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p384_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s = (val c * a) MOD p_384))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6);
                         memory :> bytes(word_sub stackpointer (word 24),24)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P384_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

