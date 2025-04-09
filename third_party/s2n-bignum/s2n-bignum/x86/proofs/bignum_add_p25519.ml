(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition modulo p_25519, the field characteristic for curve25519.         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/curve25519/bignum_add_p25519.o";;
 ****)

let bignum_add_p25519_mc = define_assert_from_elf "bignum_add_p25519_mc" "x86/curve25519/bignum_add_p25519.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x03; 0x02;        (* ADD (% r8) (Memop Quadword (%% (rdx,0))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x13; 0x4a; 0x08;  (* ADC (% r9) (Memop Quadword (%% (rdx,8))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x13; 0x52; 0x10;  (* ADC (% r10) (Memop Quadword (%% (rdx,16))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x13; 0x5a; 0x18;  (* ADC (% r11) (Memop Quadword (%% (rdx,24))) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x4c; 0x01; 0xc0;        (* ADD (% rax) (% r8) *)
  0x4c; 0x11; 0xc9;        (* ADC (% rcx) (% r9) *)
  0x4c; 0x11; 0xd6;        (* ADC (% rsi) (% r10) *)
  0x4c; 0x11; 0xda;        (* ADC (% rdx) (% r11) *)
  0x48; 0x0f; 0xba; 0xf2; 0x3f;
                           (* BTR (% rdx) (Imm8 (word 63)) *)
  0x4c; 0x0f; 0x42; 0xc0;  (* CMOVB (% r8) (% rax) *)
  0x4c; 0x0f; 0x42; 0xc9;  (* CMOVB (% r9) (% rcx) *)
  0x4c; 0x0f; 0x42; 0xd6;  (* CMOVB (% r10) (% rsi) *)
  0x4c; 0x0f; 0x42; 0xda;  (* CMOVB (% r11) (% rdx) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_add_p25519_tmc = define_trimmed "bignum_add_p25519_tmc" bignum_add_p25519_mc;;

let BIGNUM_ADD_P25519_EXEC = X86_MK_CORE_EXEC_RULE bignum_add_p25519_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let BIGNUM_ADD_P25519_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x5a) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_add_p25519_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = word (pc + 0x59) /\
                  (m < p_25519 /\ n < p_25519
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_25519))
          (MAYCHANGE [RIP; RSI; RDX; RAX; RCX; R8; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  (*** Do the whole simulation as a single block ***)

  X86_ACCSTEPS_TAC BIGNUM_ADD_P25519_EXEC [2;4;6;8;13;14;15;16] (1--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Confirm computations of the two alternatives ***)

  SUBGOAL_THEN
   `bignum_of_wordlist[sum_s2; sum_s4; sum_s6; sum_s8] = m + n /\
    bignum_of_wordlist[sum_s13; sum_s14; sum_s15; sum_s16] = m + n + 19`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    CONJ_TAC THEN
    (MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
     MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
     CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
      [MAP_EVERY UNDISCH_TAC [`m < p_25519`; `n < p_25519`] THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN
       CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
       MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
       REWRITE_TAC[INTEGER_CLOSED; GSYM REAL_OF_NUM_CLAUSES]] THEN
     ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Characterize the top bit that is tested and cleared ***)

  SUBGOAL_THEN `bit (dimindex(:64) - 1) (sum_s16:int64) <=> p_25519 <= m + n`
  MP_TAC THENL
   [REWRITE_TAC[MSB_VAL] THEN REWRITE_TAC[DIMINDEX_64] THEN
    TRANS_TAC EQ_TRANS `2 EXP 63 <= (m + n + 19) DIV 2 EXP 192` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th ->
       GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN ARITH_TAC;
      REWRITE_TAC[p_25519] THEN ARITH_TAC];
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
    DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)] THEN

  (*** Hence the overall result ***)

  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOD_ADD_CASES o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p_25519] THEN MATCH_MP_TAC(ARITH_RULE
   `l + 2 EXP 255 = m + n + 19 ==> l = (m + n) - (57896044618658097711785492504343953926634992332820282019728792003956564819949)`) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[bignum_of_wordlist; LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN REPEAT AP_TERM_TAC THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; ARITH_RULE
   `2 EXP 255 = 2 EXP 64 * 2 EXP 64 * 2 EXP 64 * 2 EXP 63`] THEN
  REPEAT AP_TERM_TAC THEN REWRITE_TAC[val_def] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  ASM_REWRITE_TAC[BIT_WORD_AND; BITVAL_CLAUSES; DIMINDEX_64] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN ARITH_TAC);;

let BIGNUM_ADD_P25519_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_add_p25519_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_p25519_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_25519 /\ n < p_25519
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_25519))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_add_p25519_tmc BIGNUM_ADD_P25519_CORRECT);;

let BIGNUM_ADD_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_add_p25519_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_p25519_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_25519 /\ n < p_25519
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_25519))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_P25519_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_add_p25519_windows_mc = define_from_elf
   "bignum_add_p25519_windows_mc" "x86/curve25519/bignum_add_p25519.obj";;

let bignum_add_p25519_windows_tmc = define_trimmed "bignum_add_p25519_windows_tmc" bignum_add_p25519_windows_mc;;

let BIGNUM_ADD_P25519_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_add_p25519_windows_tmc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_add_p25519_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_p25519_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_25519 /\ n < p_25519
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_25519))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_add_p25519_windows_tmc
    bignum_add_p25519_tmc BIGNUM_ADD_P25519_CORRECT);;

let BIGNUM_ADD_P25519_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_add_p25519_windows_mc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_add_p25519_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_p25519_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_25519 /\ n < p_25519
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_25519))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_P25519_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

