(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_256k1, the order of the secp256k1 curve.               *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_mod_n256k1_4.o";;
 ****)

let bignum_mod_n256k1_4_mc =
  define_assert_from_elf "bignum_mod_n256k1_4_mc" "x86/secp256k1/bignum_mod_n256k1_4.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0xb8; 0xbf; 0xbe; 0xc9; 0x2f; 0x73; 0xa1; 0x2d; 0x40;
                           (* MOV (% rax) (Imm64 (word 4624529908474429119)) *)
  0x49; 0xba; 0xc4; 0x5f; 0xb7; 0x50; 0x19; 0x23; 0x51; 0x45;
                           (* MOV (% r10) (Imm64 (word 4994812053365940164)) *)
  0x41; 0xbb; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r11d) (Imm32 (word 1)) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4d; 0x11; 0xd8;        (* ADC (% r8) (% r11) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x48; 0x19; 0xf6;        (* SBB (% rsi) (% rsi) *)
  0x48; 0xf7; 0xd6;        (* NOT (% rsi) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x49; 0x21; 0xf2;        (* AND (% r10) (% rsi) *)
  0x49; 0x21; 0xf3;        (* AND (% r11) (% rsi) *)
  0x48; 0x29; 0xc2;        (* SUB (% rdx) (% rax) *)
  0x48; 0x89; 0x17;        (* MOV (Memop Quadword (%% (rdi,0))) (% rdx) *)
  0x4c; 0x19; 0xd1;        (* SBB (% rcx) (% r10) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x4d; 0x19; 0xd8;        (* SBB (% r8) (% r11) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0xc3                     (* RET *)
];;

let bignum_mod_n256k1_4_tmc = define_trimmed "bignum_mod_n256k1_4_tmc" bignum_mod_n256k1_4_mc;;

let BIGNUM_MOD_N256K1_4_EXEC = X86_MK_CORE_EXEC_RULE bignum_mod_n256k1_4_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_256k1 = define `n_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141`;;

let BIGNUM_MOD_N256K1_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x62) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_mod_n256k1_4_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = word (pc + 0x61) /\
                bignum_from_memory (z,4) s = n MOD n_256k1)
          (MAYCHANGE [RIP; RSI; RAX; RDX; RCX; R8; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  BIGNUM_TERMRANGE_TAC `4` `m:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  X86_ACCSTEPS_TAC BIGNUM_MOD_N256K1_4_EXEC (1--11) (1--11) THEN
  SUBGOAL_THEN `carry_s11 <=> n_256k1 <= m` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[n_256k1; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC BIGNUM_MOD_N256K1_4_EXEC (17--24) (12--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s24" THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[n_256k1] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN

  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `m < 2 EXP (64 * 4)` THEN REWRITE_TAC[n_256k1] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  EXPAND_TAC "m" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[REAL_BITVAL_NOT; n_256k1] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_N256K1_4_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_n256k1_4_tmc) (z,8 * 4) /\
      nonoverlapping (stackpointer,8) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n256k1_4_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD n_256k1)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_mod_n256k1_4_tmc BIGNUM_MOD_N256K1_4_CORRECT);;

let BIGNUM_MOD_N256K1_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_n256k1_4_mc) (z,8 * 4) /\
      nonoverlapping (stackpointer,8) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n256k1_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD n_256k1)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_N256K1_4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mod_n256k1_4_windows_mc = define_from_elf
   "bignum_mod_n256k1_4_windows_mc" "x86/secp256k1/bignum_mod_n256k1_4.obj";;

let bignum_mod_n256k1_4_windows_tmc = define_trimmed "bignum_mod_n256k1_4_windows_tmc" bignum_mod_n256k1_4_windows_mc;;

let BIGNUM_MOD_N256K1_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_n256k1_4_windows_tmc); (x,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_n256k1_4_windows_tmc) (z,8 * 4) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n256k1_4_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD n_256k1)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_mod_n256k1_4_windows_tmc
    bignum_mod_n256k1_4_tmc BIGNUM_MOD_N256K1_4_CORRECT);;

let BIGNUM_MOD_N256K1_4_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_n256k1_4_windows_mc); (x,8 * 4)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_n256k1_4_windows_mc) (z,8 * 4) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_n256k1_4_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD n_256k1)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_N256K1_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

