(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tripling modulo p_384, the field characteristic for the NIST P-384 curve. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_triple_p384_alt.o";;
 ****)

let bignum_triple_p384_alt_mc = define_assert_from_elf "bignum_triple_p384_alt_mc" "x86/p384/bignum_triple_p384_alt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0xb9; 0x03; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 3)) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc2;        (* ADD (% r10) (% rax) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x48; 0x8b; 0x46; 0x18;  (* MOV (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x46; 0x20;  (* MOV (% rax) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x8b; 0x46; 0x28;  (* MOV (% rax) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x89; 0xd6;        (* MOV (% rsi) (% rdx) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 1)) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x48; 0xc1; 0xe2; 0x20;  (* SHL (% rdx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x48; 0x29; 0xd0;        (* SUB (% rax) (% rdx) *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd3; 0x00;  (* ADC (% rbx) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd6; 0x00;  (* ADC (% rsi) (Imm8 (word 0)) *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x48; 0xf7; 0xd2;        (* NOT (% rdx) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x21; 0xd1;        (* AND (% rcx) (% rdx) *)
  0x48; 0x29; 0xc8;        (* SUB (% rax) (% rcx) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x19; 0xc9;        (* SBB (% r9) (% rcx) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x5f; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% rbx) *)
  0x48; 0x83; 0xde; 0x00;  (* SBB (% rsi) (Imm8 (word 0)) *)
  0x48; 0x89; 0x77; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rsi) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_triple_p384_alt_tmc = define_trimmed "bignum_triple_p384_alt_tmc" bignum_triple_p384_alt_mc;;

let BIGNUM_TRIPLE_P384_ALT_EXEC = X86_MK_CORE_EXEC_RULE bignum_triple_p384_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let p384genshortredlemma = prove
 (`!n. n < 3 * 2 EXP 384
       ==> let q = (n DIV 2 EXP 384) + 1 in
           q <= 3 /\
           q * p_384 <= n + p_384 /\
           n < q * p_384 + p_384`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_384] THEN ARITH_TAC);;

let BIGNUM_TRIPLE_P384_ALT_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0xcf) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_triple_p384_alt_tmc) /\
                  read RIP s = word(pc + 0x1) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = word (pc + 0xcd) /\
                  bignum_from_memory (z,6) s = (3 * n) MOD p_384)
             (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11; RBX] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `6` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  (*** Input load and initial multiplication by 3 ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P384_ALT_EXEC (1--30) (1--30) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [mullo_s3; sum_s9; sum_s14; sum_s19; sum_s23; sum_s28; sum_s30] =
    2 EXP 384 + 3 * n`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC] THEN

  (*** Properties of quotient estimate q = h + 1 ***)

  ABBREV_TAC `h = (3 * n) DIV 2 EXP 384` THEN
  SUBGOAL_THEN `h < 3` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 6)` THEN EXPAND_TAC "h" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum_s30:int64 = word(h + 1)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[ARITH_RULE
     `(3 * n) DIV 2 EXP 384 + 1 = (2 EXP 384 + 3 * n) DIV 2 EXP 384`] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  MP_TAC(SPEC `3 * n` p384genshortredlemma) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `n < 2 EXP (64 * 6)` THEN ARITH_TAC;
    CONV_TAC(LAND_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Computation of 3 * n - (h + 1) * p_384 ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P384_ALT_EXEC (36--41) (31--43) THEN
  MP_TAC(SPECL
   [`word_neg(word(bitval(~carry_s41))):int64`;
    `&(bignum_of_wordlist
        [sum_s36; sum_s37; sum_s38; sum_s39; sum_s40; sum_s41]):real`;
    `384`; `3 * n`; `(h + 1) * p_384`]
   MASK_AND_VALUE_FROM_CARRY_LT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(h + 1) * p_384 <= 3 * n + p_384`;
        `3 * n < (h + 1) * p_384 + p_384`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      BOUNDER_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `bignum_of_wordlist
      [mullo_s3; sum_s9; sum_s14; sum_s19; sum_s23; sum_s28; word (h + 1)] =
      2 EXP 384 + 3 * n` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `a:real = b + x ==> x = a - b`)) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    UNDISCH_TAC `h < 3` THEN
    SPEC_TAC(`h:num`,`h:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[REAL_VAL_WORD_MASK; REAL_BITVAL_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCARD_FLAGS_TAC THEN
    GEN_REWRITE_TAC (funpow 3 LAND_CONV) [GSYM WORD_NOT_MASK] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; bitval]
     `(if p then x + a else x):real = x + a * &(bitval p)`] THEN
    DISCH_TAC] THEN

  (*** Final corrective masked addition ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P384_ALT_EXEC [49;51;53;55;57;59] (44--60) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`h + 1`; `384`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `topcar <=> 3 * n < (h + 1) * p_384` THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `x:real = &(3 * n) - y + z ==> &(3 * n) = x + y - z`)) THEN
  REWRITE_TAC[p_384] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BOOL_CASES_TAC `topcar:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_TRIPLE_P384_ALT_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 8),8) (x,8 * 6) /\
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 8),16) /\
        ALL (nonoverlapping (word pc,LENGTH bignum_triple_p384_alt_tmc))
            [(z,8 * 6); (word_sub stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p384_alt_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,6) s = (3 * n) MOD p_384)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,6);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`,
  X86_PROMOTE_RETURN_STACK_TAC
    bignum_triple_p384_alt_tmc BIGNUM_TRIPLE_P384_ALT_CORRECT
    `[RBX]` 8);;

let BIGNUM_TRIPLE_P384_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 8),8) (x,8 * 6) /\
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 8),16) /\
        ALL (nonoverlapping (word pc,LENGTH bignum_triple_p384_alt_mc))
            [(z,8 * 6); (word_sub stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p384_alt_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,6) s = (3 * n) MOD p_384)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,6);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P384_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_triple_p384_alt_windows_mc = define_from_elf
   "bignum_triple_p384_alt_windows_mc" "x86/p384/bignum_triple_p384_alt.obj";;

let bignum_triple_p384_alt_windows_tmc = define_trimmed "bignum_triple_p384_alt_windows_tmc" bignum_triple_p384_alt_windows_mc;;

let BIGNUM_TRIPLE_P384_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 24),24) (x,8 * 6) /\
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 24),32) /\
        ALL (nonoverlapping (word pc,LENGTH bignum_triple_p384_alt_windows_tmc))
            [(z,8 * 6); (word_sub stackpointer (word 24),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p384_alt_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,6) s = (3 * n) MOD p_384)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,6);
                         memory :> bytes(word_sub stackpointer (word 24),24)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    bignum_triple_p384_alt_windows_tmc bignum_triple_p384_alt_tmc
    BIGNUM_TRIPLE_P384_ALT_CORRECT `[RBX]` 8);;

let BIGNUM_TRIPLE_P384_ALT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 24),24) (x,8 * 6) /\
        nonoverlapping (z,8 * 6) (word_sub stackpointer (word 24),32) /\
        ALL (nonoverlapping (word pc,LENGTH bignum_triple_p384_alt_windows_mc))
            [(z,8 * 6); (word_sub stackpointer (word 24),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p384_alt_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,6) s = (3 * n) MOD p_384)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,6);
                         memory :> bytes(word_sub stackpointer (word 24),24)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P384_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

