(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_256k1 of a single word and a bignum < p_256k1.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_cmul_p256k1.o";;
 ****)

let bignum_cmul_p256k1_mc = define_assert_from_elf "bignum_cmul_p256k1_mc" "x86/secp256k1/bignum_cmul_p256k1.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x89; 0xf2;        (* MOV (% rdx) (% rsi) *)
  0xc4; 0x62; 0xcb; 0xf6; 0x01;
                           (* MULX4 (% r8,% rsi) (% rdx,Memop Quadword (%% (rcx,0))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x49; 0x08;
                           (* MULX4 (% r9,% rax) (% rdx,Memop Quadword (%% (rcx,8))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x51; 0x10;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rcx,16))) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x51; 0x18;
                           (* MULX4 (% rdx,% rax) (% rdx,Memop Quadword (%% (rcx,24))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x48; 0x8d; 0x42; 0x01;  (* LEA (% rax) (%% (rdx,1)) *)
  0x48; 0xb9; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Imm64 (word 4294968273)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x48; 0xc7; 0xc0; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Imm32 (word 0)) *)
  0x48; 0x0f; 0x42; 0xc8;  (* CMOVB (% rcx) (% rax) *)
  0x48; 0x29; 0xce;        (* SUB (% rsi) (% rcx) *)
  0x48; 0x89; 0x37;        (* MOV (Memop Quadword (%% (rdi,0))) (% rsi) *)
  0x49; 0x19; 0xc0;        (* SBB (% r8) (% rax) *)
  0x4c; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r8) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r9) *)
  0x49; 0x19; 0xc2;        (* SBB (% r10) (% rax) *)
  0x4c; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r10) *)
  0xc3                     (* RET *)
];;

let bignum_cmul_p256k1_tmc = define_trimmed "bignum_cmul_p256k1_tmc" bignum_cmul_p256k1_mc;;

let BIGNUM_CMUL_P256K1_EXEC = X86_MK_CORE_EXEC_RULE bignum_cmul_p256k1_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let p256k1redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_256k1 - 1)
       ==> let q = n DIV 2 EXP 256 + 1 in
           q < 2 EXP 64 /\
           q * p_256k1 <= n + p_256k1 /\
           n < q * p_256k1 + p_256k1`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC);;

let BIGNUM_CMUL_P256K1_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0x70) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cmul_p256k1_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0x6f) /\
                  (a < p_256k1
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256k1))
          (MAYCHANGE [RIP; RSI; RAX; RDX; RCX; R8; R9; R10] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_256k1 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_256k1` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_CMUL_P256K1_EXEC (1--27)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `val(c:int64) * a` p256k1redlemma) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN
    MP_TAC(ISPEC `c:int64` VAL_BOUND) THEN UNDISCH_TAC `a < p_256k1` THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Intermediate result from initial multiply ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P256K1_EXEC (1--10) (1--10) THEN
  ABBREV_TAC
  `ca = bignum_of_wordlist [mullo_s3; sum_s5; sum_s7; sum_s9; sum_s10]` THEN
  SUBGOAL_THEN `val(c:int64) * a = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check((fun l -> not(l = [])) o
        intersect [`a:num`; `x:int64`; `c:int64`] o frees o concl))) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(sum_s10:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `n + 1 < 2 EXP 64 ==> n < 2 EXP 64 - 1`))] THEN
  X86_STEPS_TAC BIGNUM_CMUL_P256K1_EXEC [11] THEN
  ABBREV_TAC `q:int64 = word_add sum_s10 (word 1)` THEN
  SUBGOAL_THEN `val(sum_s10:int64) + 1 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P256K1_EXEC
   [13;14;15;16;17;18;20;22;24;26] (12--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < val(q:int64) * p_256k1 <=> ~carry_s17` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    SUBGOAL_THEN `&(val(sum_s10:int64)):real = &(val(q:int64)) - &1`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n < 2 EXP 64 - 1 ==> n + 1 < 2 EXP 64`)) THEN
      UNDISCH_THEN `word_add sum_s10 (word 1):int64 = q` (SUBST1_TAC o SYM) THEN
      SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s17:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_CMUL_P256K1_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_p256k1_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p256k1_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_256k1
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256k1))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_cmul_p256k1_tmc
    BIGNUM_CMUL_P256K1_CORRECT);;

let BIGNUM_CMUL_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_cmul_p256k1_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p256k1_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_256k1
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256k1))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P256K1_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cmul_p256k1_windows_mc = define_from_elf
   "bignum_cmul_p256k1_windows_mc" "x86/secp256k1/bignum_cmul_p256k1.obj";;

let bignum_cmul_p256k1_windows_tmc = define_trimmed "bignum_cmul_p256k1_windows_tmc" bignum_cmul_p256k1_windows_mc;;

let BIGNUM_CMUL_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_p256k1_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_p256k1_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p256k1_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_256k1
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256k1))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_cmul_p256k1_windows_tmc
    bignum_cmul_p256k1_tmc BIGNUM_CMUL_P256K1_CORRECT);;

let BIGNUM_CMUL_P256K1_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_cmul_p256k1_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_cmul_p256k1_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_cmul_p256k1_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a < p_256k1
                   ==> bignum_from_memory (z,4) s = (val c * a) MOD p_256k1))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

