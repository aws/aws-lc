(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Optional negation modulo p_256k1, the field characteristic for secp256k1. *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_optneg_p256k1.o";;
 ****)

let bignum_optneg_p256k1_mc = define_assert_from_elf "bignum_optneg_p256k1_mc" "x86/secp256k1/bignum_optneg_p256k1.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x02;        (* MOV (% rax) (Memop Quadword (%% (rdx,0))) *)
  0x49; 0x89; 0xc2;        (* MOV (% r10) (% rax) *)
  0x48; 0x8b; 0x4a; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rdx,8))) *)
  0x49; 0x09; 0xca;        (* OR (% r10) (% rcx) *)
  0x4c; 0x8b; 0x42; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rdx,16))) *)
  0x4d; 0x09; 0xc2;        (* OR (% r10) (% r8) *)
  0x4c; 0x8b; 0x4a; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rdx,24))) *)
  0x4d; 0x09; 0xca;        (* OR (% r10) (% r9) *)
  0x49; 0x0f; 0x44; 0xf2;  (* CMOVE (% rsi) (% r10) *)
  0x48; 0xf7; 0xde;        (* NEG (% rsi) *)
  0x48; 0x19; 0xf6;        (* SBB (% rsi) (% rsi) *)
  0x48; 0x31; 0xf0;        (* XOR (% rax) (% rsi) *)
  0x48; 0x31; 0xf1;        (* XOR (% rcx) (% rsi) *)
  0x49; 0x31; 0xf0;        (* XOR (% r8) (% rsi) *)
  0x49; 0x31; 0xf1;        (* XOR (% r9) (% rsi) *)
  0x49; 0xba; 0xd0; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Imm64 (word 4294968272)) *)
  0x49; 0x21; 0xf2;        (* AND (% r10) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x4c; 0x29; 0xd0;        (* SUB (% rax) (% r10) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x19; 0xf1;        (* SBB (% rcx) (% rsi) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x49; 0x19; 0xf0;        (* SBB (% r8) (% rsi) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x19; 0xf1;        (* SBB (% r9) (% rsi) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0xc3                     (* RET *)
];;

let bignum_optneg_p256k1_tmc = define_trimmed "bignum_optneg_p256k1_tmc" bignum_optneg_p256k1_mc;;

let BIGNUM_OPTNEG_P256K1_EXEC = X86_MK_CORE_EXEC_RULE bignum_optneg_p256k1_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let BIGNUM_OPTNEG_P256K1_CORRECT = time prove
 (`!z q x n pc.
        nonoverlapping (word pc,0x5c) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_optneg_p256k1_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; q; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = word (pc + 0x5b) /\
                  (n < p_256k1
                   ==> (bignum_from_memory (z,4) s =
                        if ~(q = word 0) then (p_256k1 - n) MOD p_256k1
                        else n)))
          (MAYCHANGE [RIP; RSI; RAX; RCX; R8; R9; R10] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `q:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN

  X86_STEPS_TAC BIGNUM_OPTNEG_P256K1_EXEC (1--11) THEN
  FIRST_X_ASSUM(MP_TAC o
    SPEC `word_neg(word(bitval(~(q:int64 = word 0 \/ n = 0)))):int64` o
    MATCH_MP (MESON[] `read RSI s = z ==> !a. z = a ==> read RSI s = a`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WORD_NOT_MASK] THEN REPLICATE_TAC 3 AP_TERM_TAC THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[VAL_EQ_0; WORD_OR_EQ_0; CONJ_ACI; WORD_OR_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  X86_ACCSTEPS_TAC BIGNUM_OPTNEG_P256K1_EXEC [19;21;23;25] (12--26) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  SUBGOAL_THEN
   `(if ~(q:int64 = word 0) then (p_256k1 - n) MOD p_256k1 else n) =
    (if q = word 0 \/ n = 0 then n else p_256k1 - n)`
  SUBST1_TAC THENL
   [ASM_CASES_TAC `q:int64 = word 0` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `n < p_256k1` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < p /\ ~(n = 0) ==> p - n < p`] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s26" THEN
  ABBREV_TAC `P <=> q:int64 = word 0 \/ n = 0` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `n < p_256k1` THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; p_256k1] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[WORD_XOR_MASK; WORD_OR_MASK; BITVAL_CLAUSES; p_256k1] THEN
  REWRITE_TAC[WORD_NEG_0; WORD_XOR_0; WORD_AND_0] THEN
  REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_OPTNEG_P256K1_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z q x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 4)) [(word pc,LENGTH bignum_optneg_p256k1_tmc); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optneg_p256k1_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; q; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> (bignum_from_memory (z,4) s =
                        if ~(q = word 0) then (p_256k1 - n) MOD p_256k1
                        else n)))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_optneg_p256k1_tmc
      BIGNUM_OPTNEG_P256K1_CORRECT);;

let BIGNUM_OPTNEG_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z q x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 4)) [(word pc,LENGTH bignum_optneg_p256k1_mc); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optneg_p256k1_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; q; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> (bignum_from_memory (z,4) s =
                        if ~(q = word 0) then (p_256k1 - n) MOD p_256k1
                        else n)))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTNEG_P256K1_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_optneg_p256k1_windows_mc = define_from_elf
   "bignum_optneg_p256k1_windows_mc" "x86/secp256k1/bignum_optneg_p256k1.obj";;

let bignum_optneg_p256k1_windows_tmc = define_trimmed "bignum_optneg_p256k1_windows_tmc" bignum_optneg_p256k1_windows_mc;;

let BIGNUM_OPTNEG_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z q x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_optneg_p256k1_windows_tmc); (x,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 4))
            [(word pc,LENGTH bignum_optneg_p256k1_windows_tmc); (word_sub stackpointer (word 16),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optneg_p256k1_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; q; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> (bignum_from_memory (z,4) s =
                        if ~(q = word 0) then (p_256k1 - n) MOD p_256k1
                        else n)))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    bignum_optneg_p256k1_windows_tmc bignum_optneg_p256k1_tmc
    BIGNUM_OPTNEG_P256K1_CORRECT);;

let BIGNUM_OPTNEG_P256K1_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z q x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_optneg_p256k1_windows_mc); (x,8 * 4)] /\
        ALL (nonoverlapping (z,8 * 4))
            [(word pc,LENGTH bignum_optneg_p256k1_windows_mc); (word_sub stackpointer (word 16),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_optneg_p256k1_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; q; x] s /\
                  bignum_from_memory (x,4) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_256k1
                   ==> (bignum_from_memory (z,4) s =
                        if ~(q = word 0) then (p_256k1 - n) MOD p_256k1
                        else n)))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_OPTNEG_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

