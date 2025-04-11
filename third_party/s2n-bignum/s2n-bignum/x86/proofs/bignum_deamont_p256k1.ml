(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of almost-Montgomery representation modulo p_256k1.           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_deamont_p256k1.o";;
 ****)

let bignum_deamont_p256k1_mc =
  define_assert_from_elf "bignum_deamont_p256k1_mc" "x86/secp256k1/bignum_deamont_p256k1.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0xbe; 0x31; 0x35; 0x25; 0xd2; 0x1d; 0x09; 0x38; 0xd8;
                           (* MOV (% rsi) (Imm64 (word 15580212934572586289)) *)
  0x4c; 0x0f; 0xaf; 0xc6;  (* IMUL (% r8) (% rsi) *)
  0x48; 0xb8; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294968273)) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x29; 0xd1;        (* SUB (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x0f; 0xaf; 0xce;  (* IMUL (% r9) (% rsi) *)
  0x48; 0xb8; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294968273)) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x0f; 0xaf; 0xd6;  (* IMUL (% r10) (% rsi) *)
  0x48; 0xb8; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294968273)) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x4c; 0x0f; 0xaf; 0xde;  (* IMUL (% r11) (% rsi) *)
  0x48; 0xb8; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 4294968273)) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0x4c; 0x89; 0xc6;        (* MOV (% rsi) (% r8) *)
  0x4c; 0x21; 0xce;        (* AND (% rsi) (% r9) *)
  0x4c; 0x21; 0xd6;        (* AND (% rsi) (% r10) *)
  0x4c; 0x21; 0xde;        (* AND (% rsi) (% r11) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x49; 0x19; 0xc2;        (* SBB (% r10) (% rax) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x48; 0xba; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294968273)) *)
  0x4c; 0x01; 0xc2;        (* ADD (% rdx) (% r8) *)
  0x48; 0x83; 0xc6; 0x01;  (* ADD (% rsi) (Imm8 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc2;  (* CMOVE (% r8) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc8;  (* CMOVE (% r9) (% rax) *)
  0x4c; 0x0f; 0x44; 0xd0;  (* CMOVE (% r10) (% rax) *)
  0x4c; 0x0f; 0x44; 0xd8;  (* CMOVE (% r11) (% rax) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_deamont_p256k1_tmc = define_trimmed "bignum_deamont_p256k1_tmc" bignum_deamont_p256k1_mc;;

let BIGNUM_DEAMONT_P256K1_EXEC = X86_MK_CORE_EXEC_RULE bignum_deamont_p256k1_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let P_256K1_AS_WORDLIST = prove
 (`p_256k1 =
   bignum_of_wordlist
    [word 0xfffffffefffffc2f;
     word_not(word 0);word_not(word 0);word_not(word 0)]`,
  REWRITE_TAC[p_256k1; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &4294968273 * &(val(word_mul x (word 15580212934572586289):int64))
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &4294968273 * &(val(word_mul x (word 15580212934572586289):int64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; VAL_WORD_MUL; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> (a * x * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_DEAMONT_P256K1_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0xc4) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_deamont_p256k1_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0xc3) /\
                  bignum_from_memory (z,4) s =
                    (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1)
             (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Special-case a = p_256k1 by explicit calculation ***)

  ASM_CASES_TAC `a = p_256k1` THENL
   [FIRST_ASSUM MP_TAC THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[P_256K1_AS_WORDLIST; BIGNUM_OF_WORDLIST_EQ] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    X86_STEPS_TAC BIGNUM_DEAMONT_P256K1_EXEC (1--46) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT];
    ALL_TAC] THEN

  (*** Main simulation of the general case ***)

  X86_ACCSTEPS_TAC BIGNUM_DEAMONT_P256K1_EXEC (1--38) (1--46) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0]) THEN

  (*** Do the congruential reasoning on the chosen multipliers ***)

  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Identify cofactor and collapse the computed test ***)

  ABBREV_TAC
   `q = bignum_of_wordlist
         [word_mul x_0 (word 15580212934572586289);
          word_mul sum_s9 (word 15580212934572586289);
          word_mul sum_s15 (word 15580212934572586289);
          word_mul sum_s21 (word 15580212934572586289)]` THEN
  REWRITE_TAC[VAL_EQ_0; WORD_RULE
   `word_add x (word 1) = word 0 <=> word_not x = word 0`] THEN
  REWRITE_TAC[WORD_NOT_AND; WORD_OR_EQ_0] THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `\x. x = 2 EXP 256 - 1`) THEN
  SIMP_TAC[BIGNUM_OF_WORDLIST_EQ_MAX; LENGTH; ARITH_MULT; ARITH_ADD; ARITH_SUC;
           ALL; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[WORD_RULE `x = word_not(word 0) <=> word_not x = word 0`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN

  (*** The unchecked result from the Montgomery array ***)

  SUBGOAL_THEN
   `2 EXP 256 * bignum_of_wordlist [sum_s32; sum_s33; sum_s34; sum_s35] =
    a + q * p_256k1`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "a"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Show the result is in fact reduced ***)

  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    REWRITE_TAC[ARITH_RULE
      `2 EXP 256 * x = a + (2 EXP 256 - 1) * p <=>
       2 EXP 256 * x + p = a + 2 EXP 256 * p`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(e * x + p:num = a + e * p) ==> (a == p) (mod e)`)) THEN
    UNDISCH_TAC `~(a = p_256k1)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[p_256k1] THEN EXPAND_TAC "a" THEN
    BOUNDER_TAC[];
    DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `a < b <=> 2 EXP 256 * a < 2 EXP 256 * b`] THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `a + q * p:num < e * p <=> a < e * p - q * p`] THEN
    TRANS_TAC LTE_TRANS `2 * p_256k1` THEN CONJ_TAC THENL
     [REWRITE_TAC[p_256k1] THEN EXPAND_TAC "a" THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `q < 2 EXP 256 - 1 ==> 2 <= 2 EXP 256 - q`) THEN
      ASM_REWRITE_TAC[LT_LE] THEN EXPAND_TAC "q" THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]];
    MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `2 EXP 256` THEN
    ASM_REWRITE_TAC[COPRIME_LEXP; COPRIME_2] THEN CONJ_TAC THENL
     [REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `(e * i == 1) (mod p) ==> (e * i * a == a + q * p) (mod p)`) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV]);;

let BIGNUM_DEAMONT_P256K1_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_deamont_p256k1_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p256k1_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                    (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC
    bignum_deamont_p256k1_tmc BIGNUM_DEAMONT_P256K1_CORRECT);;

let BIGNUM_DEAMONT_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_deamont_p256k1_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p256k1_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                    (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEAMONT_P256K1_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_deamont_p256k1_windows_mc = define_from_elf
   "bignum_deamont_p256k1_windows_mc" "x86/secp256k1/bignum_deamont_p256k1.obj";;

let bignum_deamont_p256k1_windows_tmc = define_trimmed "bignum_deamont_p256k1_windows_tmc" bignum_deamont_p256k1_windows_mc;;

let BIGNUM_DEAMONT_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_deamont_p256k1_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p256k1_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p256k1_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                    (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    bignum_deamont_p256k1_windows_tmc bignum_deamont_p256k1_tmc
    BIGNUM_DEAMONT_P256K1_CORRECT);;

let BIGNUM_DEAMONT_P256K1_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_deamont_p256k1_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p256k1_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p256k1_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                    (inverse_mod p_256k1 (2 EXP 256) * a) MOD p_256k1)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEAMONT_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

