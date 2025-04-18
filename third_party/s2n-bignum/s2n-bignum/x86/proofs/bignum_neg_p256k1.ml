(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Negation modulo p_256k1, the field characteristic for secp256k1.          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_neg_p256k1.o";;
 ****)

let bignum_neg_p256k1_mc = define_assert_from_elf "bignum_neg_p256k1_mc" "x86/secp256k1/bignum_neg_p256k1.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x09; 0xca;        (* OR (% rdx) (% rcx) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x09; 0xc2;        (* OR (% rdx) (% r8) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x09; 0xca;        (* OR (% rdx) (% r9) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x49; 0xba; 0x2f; 0xfc; 0xff; 0xff; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% r10) (Imm64 (word 18446744069414583343)) *)
  0x49; 0x21; 0xd2;        (* AND (% r10) (% rdx) *)
  0x49; 0x29; 0xc2;        (* SUB (% r10) (% rax) *)
  0x4c; 0x89; 0x17;        (* MOV (Memop Quadword (%% (rdi,0))) (% r10) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x49; 0x19; 0xca;        (* SBB (% r10) (% rcx) *)
  0x4c; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r10) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x4d; 0x19; 0xc2;        (* SBB (% r10) (% r8) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x19; 0xca;        (* SBB (% rdx) (% r9) *)
  0x48; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rdx) *)
  0xc3                     (* RET *)
];;

let bignum_neg_p256k1_tmc = define_trimmed "bignum_neg_p256k1_tmc" bignum_neg_p256k1_mc;;

let BIGNUM_NEG_P256K1_EXEC = X86_MK_CORE_EXEC_RULE bignum_neg_p256k1_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let BIGNUM_NEG_P256K1_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x50) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_neg_p256k1_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = word (pc + 0x4f) /\
                  (n <= p_256k1
                   ==> bignum_from_memory (z,4) s = (p_256k1 - n) MOD p_256k1))
          (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  X86_ACCSTEPS_TAC BIGNUM_NEG_P256K1_EXEC [13;16;19;21] (1--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s22" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `n <= p_256k1` THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; p_256k1] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `(p_256k1 - n) MOD p_256k1 = if n = 0 then 0 else p_256k1 - n`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_0; MOD_REFL] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[COND_RAND]] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK; COND_SWAP; WORD_OR_EQ_0; VAL_EQ_0] THEN
  REWRITE_TAC[CONJ_ACI] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[p_256k1; GSYM REAL_OF_NUM_CLAUSES; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_NEG_P256K1_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 4)) [(word pc,LENGTH bignum_neg_p256k1_tmc); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_neg_p256k1_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_256k1
                   ==> bignum_from_memory (z,4) s = (p_256k1 - n) MOD p_256k1))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_neg_p256k1_tmc
      BIGNUM_NEG_P256K1_CORRECT);;

let BIGNUM_NEG_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 4)) [(word pc,LENGTH bignum_neg_p256k1_mc); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_neg_p256k1_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_256k1
                   ==> bignum_from_memory (z,4) s = (p_256k1 - n) MOD p_256k1))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NEG_P256K1_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_neg_p256k1_windows_mc = define_from_elf
   "bignum_neg_p256k1_windows_mc" "x86/secp256k1/bignum_neg_p256k1.obj";;

let bignum_neg_p256k1_windows_tmc = define_trimmed "bignum_neg_p256k1_windows_tmc" bignum_neg_p256k1_windows_mc;;

let BIGNUM_NEG_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_neg_p256k1_windows_tmc); (x,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 4))
            [(word pc,LENGTH bignum_neg_p256k1_windows_tmc); (word_sub stackpointer (word 16),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_neg_p256k1_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_256k1
                   ==> bignum_from_memory (z,4) s = (p_256k1 - n) MOD p_256k1))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_neg_p256k1_windows_tmc bignum_neg_p256k1_tmc
      BIGNUM_NEG_P256K1_CORRECT);;

let BIGNUM_NEG_P256K1_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_neg_p256k1_windows_mc); (x,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 4))
            [(word pc,LENGTH bignum_neg_p256k1_windows_mc); (word_sub stackpointer (word 16),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_neg_p256k1_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_256k1
                   ==> bignum_from_memory (z,4) s = (p_256k1 - n) MOD p_256k1))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NEG_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

