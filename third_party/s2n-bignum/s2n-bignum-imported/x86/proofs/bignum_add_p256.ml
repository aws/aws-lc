(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition modulo p_256, the field characteristic for the NIST P-256 curve. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p256/bignum_add_p256.o";;
 ****)

let bignum_add_p256_mc = define_assert_from_elf "bignum_add_p256_mc" "x86/p256/bignum_add_p256.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x03; 0x02;        (* ADD (% rax) (Memop Quadword (%% (rdx,0))) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x13; 0x4a; 0x08;  (* ADC (% rcx) (Memop Quadword (%% (rdx,8))) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x13; 0x42; 0x10;  (* ADC (% r8) (Memop Quadword (%% (rdx,16))) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x13; 0x4a; 0x18;  (* ADC (% r9) (Memop Quadword (%% (rdx,24))) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0x48; 0x83; 0xe8; 0xff;  (* SUB (% rax) (Imm8 (word 255)) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x4c; 0x19; 0xd1;        (* SBB (% rcx) (% r10) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x4c; 0x21; 0xda;        (* AND (% rdx) (% r11) *)
  0x4c; 0x01; 0xd8;        (* ADD (% rax) (% r11) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0xc3                     (* RET *)
];;

let bignum_add_p256_tmc = define_trimmed "bignum_add_p256_tmc" bignum_add_p256_mc;;

let BIGNUM_ADD_P256_EXEC = X86_MK_CORE_EXEC_RULE bignum_add_p256_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let BIGNUM_ADD_P256_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x69) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_add_p256_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = word (pc + 0x68) /\
                  (m < p_256 /\ n < p_256
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256))
          (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  X86_ACCSTEPS_TAC BIGNUM_ADD_P256_EXEC (1--27) (1--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s27" THEN
  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `m < p /\ n < p ==> m + n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_256`; `n < p_256`] THEN
    REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN

  SUBGOAL_THEN
   `sum_s17:int64 = word_neg(word(bitval(m + n < p_256))) /\
    (carry_s17 <=> m + n < p_256)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`m < p_256`; `n < p_256`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_256] THEN REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
      REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ALL_TAC] THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_ARITH `p * &0 + &0:real = x - &0 - y <=> x = y`] THEN
    REWRITE_TAC[REAL_EQ_BITVAL] THEN
    ASM_CASES_TAC `carry_s16 <=> carry_s9` THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[p_256; REAL_RAT_REDUCE_CONV `(&2 pow 64 - &1) * &1:real`] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_ADD_P256_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_add_p256_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_p256_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_256 /\ n < p_256
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_add_p256_tmc BIGNUM_ADD_P256_CORRECT);;

let BIGNUM_ADD_P256_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_add_p256_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_p256_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_256 /\ n < p_256
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_P256_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_add_p256_windows_mc = define_from_elf
   "bignum_add_p256_windows_mc" "x86/p256/bignum_add_p256.obj";;

let bignum_add_p256_windows_tmc = define_trimmed "bignum_add_p256_windows_tmc" bignum_add_p256_windows_mc;;

let BIGNUM_ADD_P256_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_add_p256_windows_tmc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_add_p256_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_p256_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_256 /\ n < p_256
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_add_p256_windows_tmc bignum_add_p256_tmc
    BIGNUM_ADD_P256_CORRECT);;

let BIGNUM_ADD_P256_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_add_p256_windows_mc); (x,8 * 4); (y,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_add_p256_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_p256_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_256 /\ n < p_256
                   ==> bignum_from_memory (z,4) s = (m + n) MOD p_256))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_P256_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

