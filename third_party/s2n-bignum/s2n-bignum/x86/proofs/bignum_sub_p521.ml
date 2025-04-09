(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Subtraction modulo p_521, the field characteristic for NIST P-521 curve.  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_sub_p521.o";;
 ****)

let bignum_sub_p521_mc = define_assert_from_elf "bignum_sub_p521_mc" "x86/p521/bignum_sub_p521.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x2b; 0x02;        (* SUB (% rax) (Memop Quadword (%% (rdx,0))) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x1b; 0x4a; 0x08;  (* SBB (% rcx) (Memop Quadword (%% (rdx,8))) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x1b; 0x42; 0x10;  (* SBB (% r8) (Memop Quadword (%% (rdx,16))) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x1b; 0x4a; 0x18;  (* SBB (% r9) (Memop Quadword (%% (rdx,24))) *)
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x1b; 0x52; 0x20;  (* SBB (% r10) (Memop Quadword (%% (rdx,32))) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x1b; 0x5a; 0x28;  (* SBB (% r11) (Memop Quadword (%% (rdx,40))) *)
  0x4c; 0x8b; 0x66; 0x30;  (* MOV (% r12) (Memop Quadword (%% (rsi,48))) *)
  0x4c; 0x1b; 0x62; 0x30;  (* SBB (% r12) (Memop Quadword (%% (rdx,48))) *)
  0x48; 0x8b; 0x5e; 0x38;  (* MOV (% rbx) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x1b; 0x5a; 0x38;  (* SBB (% rbx) (Memop Quadword (%% (rdx,56))) *)
  0x48; 0x8b; 0x76; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x1b; 0x72; 0x40;  (* SBB (% rsi) (Memop Quadword (%% (rdx,64))) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0x48; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% rax) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rcx) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x57; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r10) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x5f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r11) *)
  0x49; 0x83; 0xdc; 0x00;  (* SBB (% r12) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x67; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% r12) *)
  0x48; 0x83; 0xdb; 0x00;  (* SBB (% rbx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x5f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rbx) *)
  0x48; 0x83; 0xde; 0x00;  (* SBB (% rsi) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe6; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rsi) (Imm32 (word 511)) *)
  0x48; 0x89; 0x77; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rsi) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_sub_p521_tmc = define_trimmed "bignum_sub_p521_tmc" bignum_sub_p521_mc;;

let BIGNUM_SUB_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_sub_p521_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_SUB_P521_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x9b) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_sub_p521_tmc) /\
                  read RIP s = word(pc + 0x3) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = m /\
                  bignum_from_memory (y,9) s = n)
             (\s. read RIP s = word (pc + 0x97) /\
                  (m < p_521 /\ n < p_521
                   ==> &(bignum_from_memory (z,9) s) = (&m - &n) rem &p_521))
          (MAYCHANGE [RIP; RSI; RAX; RCX; R8; R9; R10; R11; RBX; R12] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "m_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (y,8 * 9)) s0` THEN

  (*** Initial subtraction x - y, comparison result ***)

  X86_ACCSTEPS_TAC BIGNUM_SUB_P521_EXEC [2;4;6;8;10;12;14;16;18] (1--18) THEN

  SUBGOAL_THEN `carry_s18 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Further optional subtraction mod 2^521 ***)

  X86_ACCSTEPS_TAC BIGNUM_SUB_P521_EXEC
   [19;21;23;25;27;29;31;33;35] (19--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Map things into the reals, doing case analysis over comparison ***)

  TRANS_TAC EQ_TRANS `if m < n then &m - &n + &p_521:int else &m - &n` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
   REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th];
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_UNIQ THEN
   EXISTS_TAC `if m:num < n then --(&1):int else &0` THEN
   MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
   REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_521] THEN INT_ARITH_TAC] THEN

  (*** Hence show that we get the right result in 521 bits ***)

  CONV_TAC SYM_CONV THEN
  CONV_TAC(RAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`521`; `&0:real`] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m < p_521`; `n < p_521`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_521] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,1)] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; VAL_WORD_AND_MASK_WORD] THEN
    MATCH_MP_TAC(ARITH_RULE
     `x < 2 EXP (64 * 8) ==> x + 2 EXP 512 * n MOD 2 EXP 9 < 2 EXP 521`) THEN
    MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_SUB_P521_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_sub_p521_tmc); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_sub_p521_tmc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_p521_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = m /\
                  bignum_from_memory (y,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_521 /\ n < p_521
                   ==> &(bignum_from_memory (z,9) s) = (&m - &n) rem &p_521))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_sub_p521_tmc BIGNUM_SUB_P521_CORRECT
    `[RBX; R12]` 16);;

let BIGNUM_SUB_P521_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_sub_p521_mc); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_sub_p521_mc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_p521_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = m /\
                  bignum_from_memory (y,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_521 /\ n < p_521
                   ==> &(bignum_from_memory (z,9) s) = (&m - &n) rem &p_521))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SUB_P521_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_sub_p521_windows_mc = define_from_elf
   "bignum_sub_p521_windows_mc" "x86/p521/bignum_sub_p521.obj";;

let bignum_sub_p521_windows_tmc = define_trimmed "bignum_sub_p521_windows_tmc" bignum_sub_p521_windows_mc;;

let BIGNUM_SUB_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 32),40) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_sub_p521_windows_tmc); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_sub_p521_windows_tmc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_p521_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = m /\
                  bignum_from_memory (y,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_521 /\ n < p_521
                   ==> &(bignum_from_memory (z,9) s) = (&m - &n) rem &p_521))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 32),32)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_sub_p521_windows_tmc bignum_sub_p521_tmc
    BIGNUM_SUB_P521_CORRECT `[RBX; R12]` 16);;

let BIGNUM_SUB_P521_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 32),40) (z,8 * 9) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_sub_p521_windows_mc); (x,8 * 9); (y,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_sub_p521_windows_mc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_sub_p521_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,9) s = m /\
                  bignum_from_memory (y,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (m < p_521 /\ n < p_521
                   ==> &(bignum_from_memory (z,9) s) = (&m - &n) rem &p_521))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_SUB_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

