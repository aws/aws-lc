(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo p_384, the field characteristic of the NIST curve P-384. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_mod_p384_6.o";;
 ****)

let bignum_mod_p384_6_mc =
  define_assert_from_elf "bignum_mod_p384_6_mc" "x86/p384/bignum_mod_p384_6.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xb8; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967295)) *)
  0x48; 0x29; 0xc2;        (* SUB (% rdx) (% rax) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x19; 0xc1;        (* SBB (% rcx) (% rax) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x83; 0xd8; 0xfe;  (* SBB (% r8) (Imm8 (word 254)) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x83; 0xd9; 0xff;  (* SBB (% r9) (Imm8 (word 255)) *)
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x49; 0x83; 0xda; 0xff;  (* SBB (% r10) (Imm8 (word 255)) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x49; 0x83; 0xdb; 0xff;  (* SBB (% r11) (Imm8 (word 255)) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x19; 0xf6;        (* SBB (% rsi) (% rsi) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x29; 0xf2;        (* SUB (% rdx) (% rsi) *)
  0x48; 0x89; 0x17;        (* MOV (Memop Quadword (%% (rdi,0))) (% rdx) *)
  0x48; 0x19; 0xc1;        (* SBB (% rcx) (% rax) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x49; 0x19; 0xc0;        (* SBB (% r8) (% rax) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_mod_p384_6_tmc = define_trimmed "bignum_mod_p384_6_tmc" bignum_mod_p384_6_mc;;

let BIGNUM_MOD_P384_6_EXEC = X86_MK_CORE_EXEC_RULE bignum_mod_p384_6_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let BIGNUM_MOD_P384_6_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x7a) (z,8 * 6)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_mod_p384_6_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,6) s = n)
           (\s. read RIP s = word (pc + 0x79) /\
                bignum_from_memory (z,6) s = n MOD p_384)
          (MAYCHANGE [RIP; RSI; RAX; RDX; RCX; R8; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  BIGNUM_TERMRANGE_TAC `6` `m:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  X86_ACCSTEPS_TAC BIGNUM_MOD_P384_6_EXEC (1--14) (1--14) THEN

  SUBGOAL_THEN
   `carry_s14 <=> m < p_384`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `384` THEN REWRITE_TAC[] THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC BIGNUM_MOD_P384_6_EXEC [20;22;27;29;31;33] (15--34) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s34" THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p_384] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN

  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `m < 2 EXP (64 * 6)` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  EXPAND_TAC "m" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[WORD_BITVAL_EQ_0; WORD_NEG_EQ_0] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_CLAUSES; REAL_BITVAL_NOT] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[p_384] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_P384_6_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_p384_6_tmc) (z,8 * 6) /\
      nonoverlapping (stackpointer,8) (z,8 * 6)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p384_6_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,6) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,6) s = n MOD p_384)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_mod_p384_6_tmc BIGNUM_MOD_P384_6_CORRECT);;

let BIGNUM_MOD_P384_6_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (word pc,LENGTH bignum_mod_p384_6_mc) (z,8 * 6) /\
      nonoverlapping (stackpointer,8) (z,8 * 6)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p384_6_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,6) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,6) s = n MOD p_384)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_P384_6_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mod_p384_6_windows_mc = define_from_elf
   "bignum_mod_p384_6_windows_mc" "x86/p384/bignum_mod_p384_6.obj";;

let bignum_mod_p384_6_windows_tmc = define_trimmed "bignum_mod_p384_6_windows_tmc" bignum_mod_p384_6_windows_mc;;

let BIGNUM_MOD_P384_6_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_p384_6_windows_tmc); (x,8 * 6)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_p384_6_windows_tmc) (z,8 * 6) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 6)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p384_6_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,6) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,6) s = n MOD p_384)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_mod_p384_6_windows_tmc
     bignum_mod_p384_6_tmc BIGNUM_MOD_P384_6_CORRECT);;

let BIGNUM_MOD_P384_6_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_mod_p384_6_windows_mc); (x,8 * 6)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_p384_6_windows_mc) (z,8 * 6) /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 6)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_p384_6_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,6) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,6) s = n MOD p_384)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_P384_6_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

