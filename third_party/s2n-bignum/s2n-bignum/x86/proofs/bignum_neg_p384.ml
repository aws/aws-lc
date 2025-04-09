(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Negation mod p_384, field characteristic for NIST P-384 curve.            *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_neg_p384.o";;
 ****)

let bignum_neg_p384_mc = define_assert_from_elf "bignum_neg_p384_mc" "x86/p384/bignum_neg_p384.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x0b; 0x46; 0x08;  (* OR (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x8b; 0x4e; 0x10;  (* MOV (% rcx) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x0b; 0x4e; 0x18;  (* OR (% rcx) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x8b; 0x56; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rsi,32))) *)
  0x48; 0x0b; 0x56; 0x28;  (* OR (% rdx) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x09; 0xc8;        (* OR (% rax) (% rcx) *)
  0x48; 0x09; 0xd0;        (* OR (% rax) (% rdx) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0xb8; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% eax) (Imm32 (word 4294967295)) *)
  0x4c; 0x21; 0xd0;        (* AND (% rax) (% r10) *)
  0x48; 0xb9; 0x00; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm64 (word 18446744069414584320))
*)
  0x4c; 0x21; 0xd1;        (* AND (% rcx) (% r10) *)
  0x48; 0xc7; 0xc2; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm32 (word 4294967294)) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x4d; 0x89; 0xd0;        (* MOV (% r8) (% r10) *)
  0x4d; 0x89; 0xd1;        (* MOV (% r9) (% r10) *)
  0x48; 0x2b; 0x06;        (* SUB (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x1b; 0x4e; 0x08;  (* SBB (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x1b; 0x56; 0x10;  (* SBB (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x1b; 0x46; 0x18;  (* SBB (% r8) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x1b; 0x4e; 0x20;  (* SBB (% r9) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x1b; 0x56; 0x28;  (* SBB (% r10) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x48; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rdx) *)
  0x4c; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r9) *)
  0x4c; 0x89; 0x57; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r10) *)
  0xc3                     (* RET *)
];;

let bignum_neg_p384_tmc = define_trimmed "bignum_neg_p384_tmc" bignum_neg_p384_mc;;

let BIGNUM_NEG_P384_EXEC = X86_MK_CORE_EXEC_RULE bignum_neg_p384_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let BIGNUM_NEG_P384_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x77) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_neg_p384_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = word (pc + 0x76) /\
                  (n <= p_384
                   ==> bignum_from_memory (z,6) s = (p_384 - n) MOD p_384))
          (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  X86_ACCSTEPS_TAC BIGNUM_NEG_P384_EXEC (19--24) (1--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s30" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `n <= p_384` THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; p_384] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `(p_384 - n) MOD p_384 = if n = 0 then 0 else p_384 - n`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_0; MOD_REFL] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[COND_RAND]] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK; COND_SWAP; WORD_OR_EQ_0; VAL_EQ_0] THEN
  REWRITE_TAC[CONJ_ACI] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[p_384; GSYM REAL_OF_NUM_CLAUSES; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_NEG_P384_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 6)) [(word pc,LENGTH bignum_neg_p384_tmc); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_neg_p384_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_384
                   ==> bignum_from_memory (z,6) s = (p_384 - n) MOD p_384))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_neg_p384_tmc
      BIGNUM_NEG_P384_CORRECT);;

let BIGNUM_NEG_P384_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * 6)) [(word pc,LENGTH bignum_neg_p384_mc); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_neg_p384_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_384
                   ==> bignum_from_memory (z,6) s = (p_384 - n) MOD p_384))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NEG_P384_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_neg_p384_windows_mc = define_from_elf
   "bignum_neg_p384_windows_mc" "x86/p384/bignum_neg_p384.obj";;

let bignum_neg_p384_windows_tmc = define_trimmed "bignum_neg_p384_windows_tmc" bignum_neg_p384_windows_mc;;

let BIGNUM_NEG_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_neg_p384_windows_tmc); (x,8 * 6)] /\
        ALL (nonoverlapping (z,8 * 6)) [(word pc,LENGTH bignum_neg_p384_windows_tmc); (word_sub stackpointer (word 16),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_neg_p384_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_384
                   ==> bignum_from_memory (z,6) s = (p_384 - n) MOD p_384))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_neg_p384_windows_tmc bignum_neg_p384_tmc
      BIGNUM_NEG_P384_CORRECT);;

let BIGNUM_NEG_P384_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_neg_p384_windows_mc); (x,8 * 6)] /\
        ALL (nonoverlapping (z,8 * 6)) [(word pc,LENGTH bignum_neg_p384_windows_mc); (word_sub stackpointer (word 16),24)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_neg_p384_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_384
                   ==> bignum_from_memory (z,6) s = (p_384 - n) MOD p_384))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,6);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_NEG_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

