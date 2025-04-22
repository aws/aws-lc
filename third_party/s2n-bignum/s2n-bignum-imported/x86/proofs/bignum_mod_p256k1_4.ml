(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo p_256k1, the field characteristic for secp256k1.         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_mod_p256k1_4.o";;
 ****)

let bignum_mod_p256k1_4_mc =
  define_assert_from_elf "bignum_mod_p256k1_4_mc" "x86/secp256k1/bignum_mod_p256k1_4.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x21; 0xc0;        (* AND (% rax) (% r8) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x21; 0xc8;        (* AND (% rax) (% r9) *)
  0x49; 0xba; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Imm64 (word 4294968273)) *)
  0x49; 0x01; 0xd2;        (* ADD (% r10) (% rdx) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x49; 0x0f; 0x42; 0xd2;  (* CMOVB (% rdx) (% r10) *)
  0x48; 0x89; 0x17;        (* MOV (Memop Quadword (%% (rdi,0))) (% rdx) *)
  0x48; 0x0f; 0x42; 0xc8;  (* CMOVB (% rcx) (% rax) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xc0;  (* CMOVB (% r8) (% rax) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x4c; 0x0f; 0x42; 0xc8;  (* CMOVB (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0xc3                     (* RET *)
];;

let bignum_mod_p256k1_4_tmc = define_trimmed "bignum_mod_p256k1_4_tmc" bignum_mod_p256k1_4_mc;;

let BIGNUM_MOD_P256K1_4_EXEC = X86_MK_CORE_EXEC_RULE bignum_mod_p256k1_4_tmc;;

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

let BIGNUM_OF_WORDLIST_P256K1_LE = prove
 (`p_256k1 <= bignum_of_wordlist[n0;n1;n2;n3] <=>
   0xfffffffefffffc2f <= val n0 /\
   n1 = word_not(word 0) /\ n2 = word_not(word 0) /\ n3 = word_not(word 0)`,
  REWRITE_TAC[P_256K1_AS_WORDLIST] THEN
  ONCE_REWRITE_TAC[BIGNUM_OF_WORDLIST_LE] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[word_not(word 0);word_not(word 0);word_not(word 0)] =
    2 EXP 192 - 1`
  SUBST1_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 192 - 1 < n <=> ~(n < 2 EXP (64 * 3))`] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  SIMP_TAC[BIGNUM_OF_WORDLIST_EQ_MAX; BIGNUM_FROM_WORDLIST_BOUND_GEN; ALL;
           LENGTH; ARITH_MULT; ARITH_ADD; ARITH_SUC; ARITH_LE; ARITH_LT] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[CONJ_ACI]);;

let BIGNUM_OF_WORDLIST_LT_P256K1 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3] < p_256k1 <=>
   n1 = word_not(word 0) /\ n2 = word_not(word 0) /\ n3 = word_not(word 0)
   ==> val n0 < 0xfffffffefffffc2f`,
  REWRITE_TAC[GSYM NOT_LE; BIGNUM_OF_WORDLIST_P256K1_LE] THEN
  CONV_TAC TAUT);;

let BIGNUM_OF_WORDLIST_LT_P256K1_CONDENSED = prove
 (`bignum_of_wordlist[n0;n1;n2;n3] < p_256k1 <=>
   bignum_of_wordlist[n0;word_and n1 (word_and n2 n3)] <
   340282366920938463463374607427473243183`,
  TRANS_TAC EQ_TRANS
   `bignum_of_wordlist[n0;word_and n1 (word_and n2 n3)] <
    bignum_of_wordlist[word 0xfffffffefffffc2f; word 0xffffffffffffffff]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_OF_WORDLIST_LT_P256K1] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_LT; LT_REFL; BIGNUM_OF_WORDLIST_SING] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[GSYM DIMINDEX_64; SYM(NUM_REDUCE_CONV `2 EXP 64 - 1`)] THEN
    SIMP_TAC[VAL_BOUND; ARITH_RULE `x < e ==> (x < e - 1 <=> ~(x = e - 1))`;
             VAL_WORD_AND_EQ_MAX] THEN
    REWRITE_TAC[GSYM VAL_EQ; DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC TAUT;
    AP_TERM_TAC THEN REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)]);;

let BIGNUM_MOD_P256K1_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x49) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_mod_p256k1_4_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = word (pc + 0x48) /\
                bignum_from_memory (z,4) s = n MOD p_256k1)
          (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9; R10] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `4` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  X86_ACCSTEPS_TAC BIGNUM_MOD_P256K1_4_EXEC [9;10] (1--18) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s18" THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`64 * 4`;
    `if n < p_256k1 then &n else &n - &p_256k1:real`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ALL_TAC;
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT; GSYM COND_RAND] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MOD_CASES THEN
    UNDISCH_TAC `n < 2 EXP (64 * 4)` THEN REWRITE_TAC[p_256k1] THEN
    ARITH_TAC] THEN

  ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN
  SUBGOAL_THEN `~carry_s10 <=> n < p_256k1` SUBST_ALL_TAC THENL
   [REWRITE_TAC[TAUT `(p <=> ~q) <=> (~p <=> q)`] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_LT_P256K1_CONDENSED] THEN
    REWRITE_TAC[WORD_AND_ASSOC] THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THENL
   [REAL_INTEGER_TAC; ALL_TAC] THEN

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_P256K1_LE] THEN
  STRIP_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ASM_CASES_TAC `carry_s9:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
   [DISCH_THEN(CONJUNCTS_THEN2
     (fun th -> MP_TAC(end_itlist CONJ (DECARRY_RULE [th])))
     (fun th -> MP_TAC(end_itlist CONJ (DESUM_RULE [th])))) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[p_256k1] THEN REAL_INTEGER_TAC;
    DISCH_THEN(MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES] o CONJUNCT2) THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    UNDISCH_TAC `18446744069414583343 <= val(n_0:int64)` THEN
    MP_TAC(SPEC `sum_s9:int64` VAL_BOUND_64) THEN ARITH_TAC]);;

let BIGNUM_MOD_P256K1_4_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_p256k1_4_tmc) (z,8 * 4) /\
      nonoverlapping (stackpointer,8) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p256k1_4_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD p_256k1)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_mod_p256k1_4_tmc
    BIGNUM_MOD_P256K1_4_CORRECT);;

let BIGNUM_MOD_P256K1_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_p256k1_4_mc) (z,8 * 4) /\
      nonoverlapping (stackpointer,8) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p256k1_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD p_256k1)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_P256K1_4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mod_p256k1_4_windows_mc = define_from_elf
   "bignum_mod_p256k1_4_windows_mc" "x86/secp256k1/bignum_mod_p256k1_4.obj";;

let bignum_mod_p256k1_4_windows_tmc = define_trimmed "bignum_mod_p256k1_4_windows_tmc" bignum_mod_p256k1_4_windows_mc;;

let BIGNUM_MOD_P256K1_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_p256k1_4_windows_tmc); (x,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_p256k1_4_windows_tmc) (z,8 * 4) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p256k1_4_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD p_256k1)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_mod_p256k1_4_windows_tmc
    bignum_mod_p256k1_4_tmc BIGNUM_MOD_P256K1_4_CORRECT);;

let BIGNUM_MOD_P256K1_4_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_p256k1_4_windows_mc); (x,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_p256k1_4_windows_mc) (z,8 * 4) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p256k1_4_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD p_256k1)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_P256K1_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

