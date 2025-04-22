(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tripling modulo p_256k1, the field characteristic for secp256k1.          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_triple_p256k1.o";;
 ****)

let bignum_triple_p256k1_mc =
  define_assert_from_elf "bignum_triple_p256k1_mc" "x86/secp256k1/bignum_triple_p256k1.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc2;
                           (* ADOX (% r8) (% rdx) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0x49; 0x89; 0xd1;        (* MOV (% r9) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xca;
                           (* ADOX (% r9) (% rdx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0x49; 0x89; 0xd2;        (* MOV (% r10) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADOX (% r10) (% rdx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% rdx) (% rdx) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xda;
                           (* ADOX (% r11) (% rdx) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% rdx) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% rdx) (% rax) *)
  0x48; 0xb9; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rcx) (Imm64 (word 4294968273)) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc1;        (* ADC (% r9) (% rax) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x48; 0x0f; 0x42; 0xc8;  (* CMOVB (% rcx) (% rax) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x49; 0x19; 0xc1;        (* SBB (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x49; 0x19; 0xc2;        (* SBB (% r10) (% rax) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x49; 0x19; 0xc3;        (* SBB (% r11) (% rax) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_triple_p256k1_tmc = define_trimmed "bignum_triple_p256k1_tmc" bignum_triple_p256k1_mc;;

let BIGNUM_TRIPLE_P256K1_EXEC = X86_MK_CORE_EXEC_RULE bignum_triple_p256k1_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let p256k1veryshortredlemma = prove
 (`!n. n < 3 * 2 EXP 256
       ==> let q = n DIV 2 EXP 256 + 1 in
           q < 4 /\
           q < 2 EXP 64 /\
           q * p_256k1 <= n + p_256k1 /\
           n < q * p_256k1 + p_256k1`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_256k1] THEN ARITH_TAC);;

let BIGNUM_TRIPLE_P256K1_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x9b) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_triple_p256k1_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0x9a) /\
                  bignum_from_memory (z,4) s = (3 * a) MOD p_256k1)
             (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `3 * a` p256k1veryshortredlemma) THEN ANTS_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[p_256k1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
   `x DIV 2 EXP 256 + 1 = (x + 2 EXP 256) DIV 2 EXP 256`]) THEN

  (*** Intermediate result from tripling and +1 ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P256K1_EXEC (1--20) (1--20) THEN
  ABBREV_TAC
  `ca = bignum_of_wordlist [sum_s5; sum_s9; sum_s13; sum_s17; sum_s20]` THEN
  SUBGOAL_THEN `3 * a + 2 EXP 256 = ca` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "ca"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN
       SUBST_ALL_TAC th THEN ASSUME_TAC th THEN DISCH_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check((fun l -> not(l = [])) o
        intersect [`x:int64`; `c:int64`] o frees o concl))) THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate is just the top word after the +1 ***)

  ABBREV_TAC `q:int64 = sum_s20` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (vfree_in `sum_s20:int64` o concl))) THEN
  SUBGOAL_THEN `ca DIV 2 EXP 256 = val(q:int64)` SUBST_ALL_TAC THENL
   [EXPAND_TAC "ca" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC BIGNUM_TRIPLE_P256K1_EXEC
   [23;24;25;26;27;29;31;33;35] (21--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(q:int64)`; `256`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_256k1] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** The fact that a simple product doesn't overflow ***)

  SUBGOAL_THEN
    `&(val(word_mul q (word 4294968273):int64)):real = &(val q) * &4294968273`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_MUL; VAL_WORD; REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(q:int64) < 4` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `3 * a < val(q:int64) * p_256k1 <=> ~carry_s27`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `a < b <=> a + 2 EXP 256 < b + 2 EXP 256`] THEN
    ASM_REWRITE_TAC[] THEN
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH
     `&(3 * a):real =
      (&(3 * a) + &2 pow 256) - &2 pow 256`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN EXPAND_TAC "ca" THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN
    REWRITE_TAC[p_256k1; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s27:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

let BIGNUM_TRIPLE_P256K1_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_triple_p256k1_tmc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p256k1_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (3 * a) MOD p_256k1)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_triple_p256k1_tmc
    BIGNUM_TRIPLE_P256K1_CORRECT);;

let BIGNUM_TRIPLE_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_triple_p256k1_mc) (z,8 * 4) /\
        nonoverlapping (stackpointer,8) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p256k1_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (3 * a) MOD p_256k1)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P256K1_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_triple_p256k1_windows_mc = define_from_elf
   "bignum_triple_p256k1_windows_mc" "x86/secp256k1/bignum_triple_p256k1.obj";;

let bignum_triple_p256k1_windows_tmc = define_trimmed "bignum_triple_p256k1_windows_tmc" bignum_triple_p256k1_windows_mc;;

let BIGNUM_TRIPLE_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_triple_p256k1_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p256k1_windows_tmc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p256k1_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (3 * a) MOD p_256k1)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    bignum_triple_p256k1_windows_tmc bignum_triple_p256k1_tmc
    BIGNUM_TRIPLE_P256K1_CORRECT);;

let BIGNUM_TRIPLE_P256K1_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_triple_p256k1_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_triple_p256k1_windows_mc) (z,8 * 4) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_triple_p256k1_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s = (3 * a) MOD p_256k1)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TRIPLE_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

