(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery square mod p_256k1, the field characteristic for secp256k1.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/secp256k1/bignum_montsqr_p256k1.o";;
 ****)

let bignum_montsqr_p256k1_mc =
  define_assert_from_elf "bignum_montsqr_p256k1_mc" "x86/secp256k1/bignum_montsqr_p256k1.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% r8) (% rdx,% rdx) *)
  0xc4; 0x62; 0xb3; 0xf6; 0x56; 0x08;
                           (* MULX4 (% r10,% r9) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0xc4; 0x62; 0xa3; 0xf6; 0x66; 0x18;
                           (* MULX4 (% r12,% r11) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0x62; 0x93; 0xf6; 0x76; 0x18;
                           (* MULX4 (% r14,% r13) (% rdx,Memop Quadword (%% (rsi,24))) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x1e;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,0))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x5e; 0x08;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsi,8))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf5;
                           (* ADOX (% r14) (% rbp) *)
  0x49; 0x11; 0xee;        (* ADC (% r14) (% rbp) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xc9;
                           (* ADCX (% r9) (% r9) *)
  0xf3; 0x4d; 0x0f; 0x38; 0xf6; 0xcf;
                           (* ADOX (% r9) (% r15) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xd2;
                           (* ADCX (% r10) (% r10) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADOX (% r10) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADCX (% r11) (% r11) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xda;
                           (* ADOX (% r11) (% rdx) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0xd2;
                           (* MULX4 (% rdx,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xe4;
                           (* ADCX (% r12) (% r12) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADOX (% r12) (% rax) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xed;
                           (* ADCX (% r13) (% r13) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xea;
                           (* ADOX (% r13) (% rdx) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xfa;
                           (* MULX4 (% r15,% rax) (% rdx,% rdx) *)
  0x66; 0x4d; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% r14) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADOX (% r14) (% rax) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADCX (% r15) (% rbp) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfd;
                           (* ADOX (% r15) (% rbp) *)
  0x48; 0xbd; 0x31; 0x35; 0x25; 0xd2; 0x1d; 0x09; 0x38; 0xd8;
                           (* MOV (% rbp) (Imm64 (word 15580212934572586289)) *)
  0x48; 0xbb; 0xd1; 0x03; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Imm64 (word 4294968273)) *)
  0x48; 0x89; 0xd8;        (* MOV (% rax) (% rbx) *)
  0x4c; 0x0f; 0xaf; 0xc5;  (* IMUL (% r8) (% rbp) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x29; 0xd1;        (* SUB (% r9) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x89; 0xd8;        (* MOV (% rax) (% rbx) *)
  0x4c; 0x0f; 0xaf; 0xcd;  (* IMUL (% r9) (% rbp) *)
  0x49; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% r9) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0x19; 0xd2;        (* SBB (% r10) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x89; 0xd8;        (* MOV (% rax) (% rbx) *)
  0x4c; 0x0f; 0xaf; 0xd5;  (* IMUL (% r10) (% rbp) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0x19; 0xd3;        (* SBB (% r11) (% rdx) *)
  0x48; 0x19; 0xc9;        (* SBB (% rcx) (% rcx) *)
  0x48; 0x89; 0xd8;        (* MOV (% rax) (% rbx) *)
  0x4c; 0x0f; 0xaf; 0xdd;  (* IMUL (% r11) (% rbp) *)
  0x49; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% r11) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0x19; 0xd0;        (* SBB (% r8) (% rdx) *)
  0x49; 0x83; 0xd9; 0x00;  (* SBB (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x4d; 0x01; 0xc4;        (* ADD (% r12) (% r8) *)
  0x4d; 0x11; 0xcd;        (* ADC (% r13) (% r9) *)
  0x4d; 0x11; 0xd6;        (* ADC (% r14) (% r10) *)
  0x4d; 0x11; 0xdf;        (* ADC (% r15) (% r11) *)
  0x48; 0x19; 0xed;        (* SBB (% rbp) (% rbp) *)
  0x4d; 0x89; 0xe0;        (* MOV (% r8) (% r12) *)
  0x49; 0x01; 0xd8;        (* ADD (% r8) (% rbx) *)
  0x4d; 0x89; 0xe9;        (* MOV (% r9) (% r13) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x4d; 0x89; 0xf2;        (* MOV (% r10) (% r14) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x4d; 0x89; 0xfb;        (* MOV (% r11) (% r15) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x48; 0x83; 0xd5; 0xff;  (* ADC (% rbp) (Imm8 (word 255)) *)
  0x4d; 0x0f; 0x42; 0xe0;  (* CMOVB (% r12) (% r8) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4d; 0x0f; 0x42; 0xe9;  (* CMOVB (% r13) (% r9) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4d; 0x0f; 0x42; 0xf2;  (* CMOVB (% r14) (% r10) *)
  0x4c; 0x89; 0x77; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r14) *)
  0x4d; 0x0f; 0x42; 0xfb;  (* CMOVB (% r15) (% r11) *)
  0x4c; 0x89; 0x7f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r15) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_montsqr_p256k1_tmc = define_trimmed "bignum_montsqr_p256k1_tmc" bignum_montsqr_p256k1_mc;;

let BIGNUM_MONTSQR_P256K1_EXEC = X86_MK_CORE_EXEC_RULE bignum_montsqr_p256k1_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_256k1 = new_definition `p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &4294968273 * &(val(word_mul x (word 15580212934572586289):int64))
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &4294968273 * &(val(word_mul x (word 15580212934572586289):int64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; VAL_WORD_MUL; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> (a * x * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_MONTSQR_P256K1_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x1a1) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_montsqr_p256k1_tmc) /\
                  read RIP s = word(pc + 0xa) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = word (pc + 0x196) /\
                  (a EXP 2 <= 2 EXP 256 * p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a EXP 2) MOD p_256k1))
             (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP;
                         R8; R9; R10; R11; R12; R13; R14; R15] ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 256 * p_256k1  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 256 * p_256k1` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_MONTSQR_P256K1_EXEC (1--90)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,4) s0` THEN

  (*** The initial multiplication, separate from Montgomery reduction ***)

  X86_ACCSTEPS_TAC BIGNUM_MONTSQR_P256K1_EXEC (1--41) (1--41) THEN
  ABBREV_TAC
   `l = bignum_of_wordlist
     [mullo_s2; sum_s23; sum_s27; sum_s29;
      sum_s33; sum_s35; sum_s39; sum_s41]` THEN
  SUBGOAL_THEN `a EXP 2 = l` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l"; "a"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The main Montgomery reduction to 4 words plus 1 bit ***)

  X86_ACCSTEPS_TAC BIGNUM_MONTSQR_P256K1_EXEC
   [46;47;48;51;53;57;59;63;65;66;67;68;69;70;71;72]
   (42--73) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_EQ_0; WORD_BITVAL_EQ_0]) THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN
  ABBREV_TAC
   `t = bignum_of_wordlist[sum_s69; sum_s70; sum_s71; sum_s72;
                           word(bitval(carry_s72))]` THEN
  SUBGOAL_THEN
   `t < 2 * p_256k1 /\ (2 EXP 256 * t == l) (mod p_256k1)`
  STRIP_ASSUME_TAC THENL
   [ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 256 * p
         ==> 2 EXP 256 * t < ab + 2 EXP 256 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["l"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_256k1; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["l"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  X86_ACCSTEPS_TAC BIGNUM_MONTSQR_P256K1_EXEC [75;77;79;81] (74--90) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_256k1` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == l) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * l) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_256k1] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `if t < p_256k1 then &t:real else &t - &p_256k1`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    REWRITE_TAC[p_256k1] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN

  (*** The slightly wacky comparison and hence the final result ***)

  SUBGOAL_THEN `2 EXP 64 <= val(word_neg(word(bitval carry_s72):int64)) +
                            18446744073709551615 + bitval carry_s81 <=>
                p_256k1 <= t` SUBST_ALL_TAC THENL
   [EXPAND_TAC "t" THEN BOOL_CASES_TAC `carry_s72:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; p_256k1; bignum_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THENL
     [ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `carry_s81:bool` THEN CONJ_TAC THENL
     [REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_256k1] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTSQR_P256K1_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_montsqr_p256k1_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256k1_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p256k1_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a EXP 2 <= 2 EXP 256 * p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a EXP 2) MOD p_256k1))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 48),48)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_montsqr_p256k1_tmc BIGNUM_MONTSQR_P256K1_CORRECT
   `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_MONTSQR_P256K1_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_montsqr_p256k1_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256k1_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p256k1_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a EXP 2 <= 2 EXP 256 * p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a EXP 2) MOD p_256k1))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTSQR_P256K1_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_montsqr_p256k1_windows_mc = define_from_elf
   "bignum_montsqr_p256k1_windows_mc" "x86/secp256k1/bignum_montsqr_p256k1.obj";;

let bignum_montsqr_p256k1_windows_tmc = define_trimmed "bignum_montsqr_p256k1_windows_tmc" bignum_montsqr_p256k1_windows_mc;;

let BIGNUM_MONTSQR_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 64),72) /\
        ALL (nonoverlapping (word_sub stackpointer (word 64),64))
            [(word pc,LENGTH bignum_montsqr_p256k1_windows_tmc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256k1_windows_tmc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p256k1_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a EXP 2 <= 2 EXP 256 * p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a EXP 2) MOD p_256k1))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 64),64)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_montsqr_p256k1_windows_tmc bignum_montsqr_p256k1_tmc
   BIGNUM_MONTSQR_P256K1_CORRECT `[RBX; RBP; R12; R13; R14; R15]` 48);;

let BIGNUM_MONTSQR_P256K1_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 4) (word_sub stackpointer (word 64),72) /\
        ALL (nonoverlapping (word_sub stackpointer (word 64),64))
            [(word pc,LENGTH bignum_montsqr_p256k1_windows_mc); (x,8 * 4)] /\
        nonoverlapping (word pc,LENGTH bignum_montsqr_p256k1_windows_mc) (z,8 * 4)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_montsqr_p256k1_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,4) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (a EXP 2 <= 2 EXP 256 * p_256k1
                   ==> bignum_from_memory (z,4) s =
                       (inverse_mod p_256k1 (2 EXP 256) * a EXP 2) MOD p_256k1))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4);
                         memory :> bytes(word_sub stackpointer (word 64),64)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MONTSQR_P256K1_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

