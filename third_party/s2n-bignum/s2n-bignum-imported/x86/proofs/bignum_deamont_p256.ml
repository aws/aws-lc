(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of almost-Montgomery representation modulo p_256.             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p256/bignum_deamont_p256.o";;
 ****)

let bignum_deamont_p256_mc =
  define_assert_from_elf "bignum_deamont_p256_mc" "x86/p256/bignum_deamont_p256.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x4c; 0x8b; 0x06;        (* MOV (% r8) (Memop Quadword (%% (rsi,0))) *)
  0x4c; 0x8b; 0x4e; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x56; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x5e; 0x18;  (* MOV (% r11) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x31; 0xdb;        (* XOR (% rbx) (% rbx) *)
  0x48; 0x31; 0xf6;        (* XOR (% rsi) (% rsi) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd1;
                           (* ADOX (% r10) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% rax) (% rdx,% r9) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% r11) (% rcx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc8;
                           (* MULX4 (% rcx,% rax) (% rdx,% r8) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% rbx) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xc9;
                           (* MULX4 (% rcx,% rax) (% rdx,% r9) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% rbx) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% rsi) (% rcx) *)
  0x41; 0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 0)) *)
  0x66; 0x49; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% rsi) (% r8) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x48; 0xba; 0x00; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Imm64 (word 4294967296)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rax) (% rdx,% r10) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xd9;
                           (* ADOX (% rbx) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcb;
                           (* MULX4 (% rcx,% rax) (% rdx,% r11) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% rbx) (% rax) *)
  0xf3; 0x48; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% rsi) (% rcx) *)
  0x48; 0xba; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm64 (word 18446744069414584321)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xca;
                           (* MULX4 (% rcx,% rax) (% rdx,% r10) *)
  0x66; 0x48; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% rsi) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc1;
                           (* ADOX (% r8) (% rcx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xcb;
                           (* MULX4 (% rcx,% rax) (% rdx,% r11) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADOX (% r9) (% rcx) *)
  0x41; 0xba; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 0)) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xca;
                           (* ADCX (% r9) (% r10) *)
  0x41; 0xba; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r10d) (Imm32 (word 4294967295)) *)
  0x49; 0xbb; 0x01; 0x00; 0x00; 0x00; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11) (Imm64 (word 18446744069414584321)) *)
  0x48; 0xc7; 0xc2; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rdx) (Imm32 (word 4294967294)) *)
  0x48; 0x29; 0xda;        (* SUB (% rdx) (% rbx) *)
  0x4c; 0x89; 0xd2;        (* MOV (% rdx) (% r10) *)
  0x48; 0x19; 0xf2;        (* SBB (% rdx) (% rsi) *)
  0xba; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 0)) *)
  0x4c; 0x19; 0xc2;        (* SBB (% rdx) (% r8) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x4c; 0x19; 0xca;        (* SBB (% rdx) (% r9) *)
  0x48; 0x19; 0xd2;        (* SBB (% rdx) (% rdx) *)
  0x49; 0x21; 0xd2;        (* AND (% r10) (% rdx) *)
  0x49; 0x21; 0xd3;        (* AND (% r11) (% rdx) *)
  0x48; 0x29; 0xd3;        (* SUB (% rbx) (% rdx) *)
  0x4c; 0x19; 0xd6;        (* SBB (% rsi) (% r10) *)
  0x49; 0x83; 0xd8; 0x00;  (* SBB (% r8) (Imm8 (word 0)) *)
  0x4d; 0x19; 0xd9;        (* SBB (% r9) (% r11) *)
  0x48; 0x89; 0x1f;        (* MOV (Memop Quadword (%% (rdi,0))) (% rbx) *)
  0x48; 0x89; 0x77; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rsi) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_deamont_p256_tmc = define_trimmed "bignum_deamont_p256_tmc" bignum_deamont_p256_mc;;

let BIGNUM_DEAMONT_P256_EXEC = X86_MK_CORE_EXEC_RULE bignum_deamont_p256_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256 = new_definition `p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951`;;

let BIGNUM_DEAMONT_P256_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x136) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_deamont_p256_tmc) /\
                  read RIP s = word(pc + 0x01) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0x134) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_256 (2 EXP 256) * a) MOD p_256)
             (MAYCHANGE [RIP; RSI; RAX; RBX; RCX; RDX; R8; R9; R10; R11] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  X86_ACCSTEPS_TAC BIGNUM_DEAMONT_P256_EXEC (1--39) (1--39) THEN

  (*** Show that the pre-reduced dd satisfies the key congruence ***)

  ABBREV_TAC `dd = bignum_of_wordlist[sum_s29;sum_s33;sum_s36;sum_s39]` THEN
  SUBGOAL_THEN `(inverse_mod p_256 (2 EXP 256) * a == dd) (mod p_256)`
  MP_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE
     `!e. (e * d == a) (mod p) /\ (e * i == 1) (mod p)
           ==> (i * a == d) (mod p)`) THEN
    EXISTS_TAC `2 EXP 256` THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN CONJ_TAC
    THENL [ALL_TAC; REWRITE_TAC[p_256] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    MAP_EVERY EXPAND_TAC ["dd"; "a"] THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES; p_256] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[CONG] THEN
    DISCH_THEN SUBST1_TAC] THEN

  X86_ACCSTEPS_TAC BIGNUM_DEAMONT_P256_EXEC
   [43;45;47;49;53;54;55;56] (40--60) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  SUBGOAL_THEN `carry_s49 <=> p_256 <= dd` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "dd" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s60" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; p_256] THEN ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN `dd MOD p_256 = if p_256 <= dd then dd - p_256 else dd`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN MATCH_MP_TAC MOD_CASES THEN
    EXPAND_TAC "dd" THEN REWRITE_TAC[p_256; bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ONCE_REWRITE_TAC[COND_RAND] THEN SIMP_TAC[GSYM REAL_OF_NUM_SUB]] THEN
  ABBREV_TAC `q <=> p_256 <= dd` THEN
  EXPAND_TAC "dd" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[p_256; GSYM REAL_OF_NUM_CLAUSES; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DEAMONT_P256_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 8),16) /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,LENGTH bignum_deamont_p256_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p256_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p256_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_256 (2 EXP 256) * a) MOD p_256)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 8),8)])`,
  X86_PROMOTE_RETURN_STACK_TAC
    bignum_deamont_p256_tmc BIGNUM_DEAMONT_P256_CORRECT `[RBX]` 8);;

let BIGNUM_DEAMONT_P256_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 8),16) /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,LENGTH bignum_deamont_p256_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p256_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p256_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_256 (2 EXP 256) * a) MOD p_256)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 8),8)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEAMONT_P256_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_deamont_p256_windows_mc = define_from_elf
   "bignum_deamont_p256_windows_mc" "x86/p256/bignum_deamont_p256.obj";;

let bignum_deamont_p256_windows_tmc = define_trimmed "bignum_deamont_p256_windows_tmc" bignum_deamont_p256_windows_mc;;

let BIGNUM_DEAMONT_P256_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 24),32) /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,LENGTH bignum_deamont_p256_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p256_windows_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p256_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_256 (2 EXP 256) * a) MOD p_256)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 24),24)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    bignum_deamont_p256_windows_tmc bignum_deamont_p256_tmc
    BIGNUM_DEAMONT_P256_CORRECT `[RBX]` 8);;

let BIGNUM_DEAMONT_P256_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 24),32) /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,LENGTH bignum_deamont_p256_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p256_windows_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p256_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,4) s =
                  (inverse_mod p_256 (2 EXP 256) * a) MOD p_256)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                       memory :> bytes(word_sub stackpointer (word 24),24)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEAMONT_P256_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

