(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of almost-Montgomery representation modulo p_521.             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_deamont_p521.o";;
 ****)

let bignum_deamont_p521_mc =
  define_assert_from_elf "bignum_deamont_p521_mc" "x86/p521/bignum_deamont_p521.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x55;                    (* PUSH (% rbp) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xc1; 0xe0; 0x09;  (* SHL (% rax) (Imm8 (word 9)) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x0f; 0xac; 0xca; 0x37;
                           (* SHRD (% rdx) (% rcx) (Imm8 (word 55)) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x0f; 0xac; 0xc1; 0x37;
                           (* SHRD (% rcx) (% r8) (Imm8 (word 55)) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4d; 0x0f; 0xac; 0xc8; 0x37;
                           (* SHRD (% r8) (% r9) (Imm8 (word 55)) *)
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x4d; 0x0f; 0xac; 0xd1; 0x37;
                           (* SHRD (% r9) (% r10) (Imm8 (word 55)) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x4d; 0x0f; 0xac; 0xda; 0x37;
                           (* SHRD (% r10) (% r11) (Imm8 (word 55)) *)
  0x4c; 0x8b; 0x66; 0x30;  (* MOV (% r12) (Memop Quadword (%% (rsi,48))) *)
  0x4d; 0x0f; 0xac; 0xe3; 0x37;
                           (* SHRD (% r11) (% r12) (Imm8 (word 55)) *)
  0x4c; 0x8b; 0x6e; 0x38;  (* MOV (% r13) (Memop Quadword (%% (rsi,56))) *)
  0x4d; 0x0f; 0xac; 0xec; 0x37;
                           (* SHRD (% r12) (% r13) (Imm8 (word 55)) *)
  0x48; 0x8b; 0x6e; 0x40;  (* MOV (% rbp) (Memop Quadword (%% (rsi,64))) *)
  0x49; 0x0f; 0xac; 0xed; 0x37;
                           (* SHRD (% r13) (% rbp) (Imm8 (word 55)) *)
  0x48; 0xc1; 0xed; 0x37;  (* SHR (% rbp) (Imm8 (word 55)) *)
  0x48; 0x89; 0xc3;        (* MOV (% rbx) (% rax) *)
  0x48; 0xc1; 0xe8; 0x37;  (* SHR (% rax) (Imm8 (word 55)) *)
  0x48; 0xc1; 0xe3; 0x09;  (* SHL (% rbx) (Imm8 (word 9)) *)
  0x48; 0x81; 0xcd; 0x00; 0xfe; 0xff; 0xff;
                           (* OR (% rbp) (Imm32 (word 4294966784)) *)
  0x48; 0x83; 0xc2; 0x01;  (* ADD (% rdx) (Imm8 (word 1)) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd0; 0x00;  (* ADC (% r8) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x83; 0xd4; 0x00;  (* ADC (% r12) (Imm8 (word 0)) *)
  0x49; 0x11; 0xdd;        (* ADC (% r13) (% rbx) *)
  0x48; 0x11; 0xc5;        (* ADC (% rbp) (% rax) *)
  0xf5;                    (* CMC *)
  0x48; 0x83; 0xda; 0x00;  (* SBB (% rdx) (Imm8 (word 0)) *)
  0x48; 0x89; 0x17;        (* MOV (Memop Quadword (%% (rdi,0))) (% rdx) *)
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
  0x49; 0x83; 0xdd; 0x00;  (* SBB (% r13) (Imm8 (word 0)) *)
  0x4c; 0x89; 0x6f; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r13) *)
  0x48; 0x83; 0xdd; 0x00;  (* SBB (% rbp) (Imm8 (word 0)) *)
  0x48; 0x81; 0xe5; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rbp) (Imm32 (word 511)) *)
  0x48; 0x89; 0x6f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% rbp) *)
  0x5d;                    (* POP (% rbp) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_deamont_p521_tmc = define_trimmed "bignum_deamont_p521_tmc" bignum_deamont_p521_mc;;

let BIGNUM_DEAMONT_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_deamont_p521_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_DEAMONT_P521_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0xe6) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_deamont_p521_tmc) /\
                  read RIP s = word(pc + 0x06) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = a)
             (\s. read RIP s = word (pc + 0xdf) /\
                  bignum_from_memory (z,9) s =
                  (inverse_mod p_521 (2 EXP 576) * a) MOD p_521)
             (MAYCHANGE [RIP; RAX; RCX; RDX;
                         R8; R9; R10; R11; RBX; RBP; R12; R13] ,,
              MAYCHANGE [memory :> bytes(z,8 * 9)] ,,
              MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Digitize and break the input into n = 2 * 55 * h + l ***)

  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,9) s0` THEN
  MAP_EVERY ABBREV_TAC [`h = n DIV 2 EXP 55`; `l = n MOD 2 EXP 55`] THEN
  SUBGOAL_THEN `l < 2 EXP 55` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h < 2 EXP 521` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 55 < 2 EXP 521 <=> n < 2 EXP (64 * 9)`] THEN
    EXPAND_TAC "n" THEN MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(inverse_mod p_521 (2 EXP 576) * n) MOD p_521 =
    (h + 2 EXP 466 * l) MOD p_521`
  SUBST1_TAC THENL
   [SUBST1_TAC(ARITH_RULE
     `n = 2 EXP 55 * n DIV 2 EXP 55 + n MOD 2 EXP 55`) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `!e. (e * i == 1) (mod n) /\ (e * hl == a) (mod n)
          ==> (i * a == hl) (mod n)`) THEN
    EXISTS_TAC `2 EXP 576` THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 576`); INVERSE_MOD_RMUL_EQ] THEN
    REWRITE_TAC[COPRIME_REXP; COPRIME_2; p_521] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_CONGRUENCE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** The actual computations of h and l ***)

  X86_STEPS_TAC BIGNUM_DEAMONT_P521_EXEC (1--20) THEN
  MAP_EVERY ABBREV_TAC
   [`d0:int64 =
       word_subword ((word_join:int64->int64->int128) x_1 x_0) (55,64)`;
    `d1:int64 =
       word_subword ((word_join:int64->int64->int128) x_2 x_1) (55,64)`;
    `d2:int64 =
       word_subword ((word_join:int64->int64->int128) x_3 x_2) (55,64)`;
    `d3:int64 =
       word_subword ((word_join:int64->int64->int128) x_4 x_3) (55,64)`;
    `d4:int64 =
       word_subword ((word_join:int64->int64->int128) x_5 x_4) (55,64)`;
    `d5:int64 =
       word_subword ((word_join:int64->int64->int128) x_6 x_5) (55,64)`;
    `d6:int64 =
       word_subword ((word_join:int64->int64->int128) x_7 x_6) (55,64)`;
    `d7:int64 =
       word_subword ((word_join:int64->int64->int128) x_8 x_7) (55,64)`;
    `d8:int64 = word_ushr x_8 55`] THEN
  SUBGOAL_THEN `word_shl (x_0:int64) 9 = word(2 EXP 9 * l)` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l"; "n"] THEN REWRITE_TAC[word_shl; WORD_EQ] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(1,8)] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 = 55 + 9`; EXP_ADD] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; MOD_MULT_ADD] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `(a:num == b) (mod n) ==> (a * e == e * b) (mod (n * e))`) THEN
    REWRITE_TAC[CONG; BIGNUM_OF_WORDLIST_SING] THEN CONV_TAC MOD_DOWN_CONV THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `n DIV 2 EXP 55 = bignum_of_wordlist[d0;d1;d2;d3;d4;d5;d6;d7;d8]`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `val(x_0:int64) MOD 2 EXP 55` THEN
    REWRITE_TAC[ARITH_RULE `x MOD 2 EXP 55 < 2 EXP 55`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN EXPAND_TAC "n" THEN
    MAP_EVERY EXPAND_TAC
     ["d0"; "d1"; "d2"; "d3"; "d4"; "d5"; "d6"; "d7"; "d8"] THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_AND;
                BIT_WORD_USHR; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ONCE_REWRITE_TAC[BIT_GUARD] THEN
    REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
                        GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    CONV_TAC NUM_RING;
    ALL_TAC] THEN

  (*** The comparison ***)

  SUBGOAL_THEN
   `&(val(word_or d8 (word 18446744073709551104):int64)):real =
    &2 pow 9 * (&2 pow 55 - &1) + &(val d8)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; EQ_ADD_LCANCEL] THEN
    AP_TERM_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
    EXPAND_TAC "d8" THEN
    REWRITE_TAC[BIT_WORD_AND; BIT_WORD_USHR; DIMINDEX_64] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));
    ALL_TAC] THEN

  SUBGOAL_THEN
   `bignum_of_wordlist
     [word_shl (word (512 * l)) 9; word_ushr (word (512 * l)) 55] =
    2 EXP 18 * l`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; VAL_WORD_SHL; VAL_WORD_USHR] THEN
    REWRITE_TAC[DIMINDEX_64; EXP_ADD; ARITH_RULE `64 = 9 + 55`] THEN
    REWRITE_TAC[MOD_MULT2; GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN MATCH_MP_TAC(ARITH_RULE
     `x = 512 * l
      ==> 2 EXP 9 * (x MOD 2 EXP 55 + 2 EXP 55 * x DIV 2 EXP 55) =
          2 EXP 18 * l`) THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN EXPAND_TAC "l" THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN

  X86_ACCSTEPS_TAC BIGNUM_DEAMONT_P521_EXEC (25--33) (21--33) THEN
  SUBGOAL_THEN `carry_s33 <=> p_521 <= h + 2 EXP 466 * l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    SUBGOAL_THEN
     `2 EXP 466 * l =
      2 EXP 448 * bignum_of_wordlist
       [word_shl (word (512 * l)) 9; word_ushr (word (512 * l)) 55]`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "h" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_REWRITE_TAC[p_521] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final correction ***)

  ABBREV_TAC `hl = h + 2 EXP 466 * l` THEN
  X86_ACCSTEPS_TAC BIGNUM_DEAMONT_P521_EXEC (34--53) (34--53) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if h + 2 EXP 466 * l < p_521
     then &(h + 2 EXP 466 * l)
     else &(h + 2 EXP 466 * l) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[GSYM COND_RAND] THEN AP_TERM_TAC THEN EXPAND_TAC "hl" THEN
    REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN MATCH_MP_TAC MOD_CASES THEN
    MAP_EVERY UNDISCH_TAC [`h < 2 EXP 521`; `l < 2 EXP 55`] THEN
    REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `bb <=> hl < p_521` THEN MAP_EVERY EXPAND_TAC ["hl"; "h"] THEN
  SUBGOAL_THEN
   `2 EXP 466 * l =
    2 EXP 448 * bignum_of_wordlist
      [word_shl (word (512 * l)) 9; word_ushr (word (512 * l)) 55]`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_DEAMONT_P521_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 9) (word_sub stackpointer (word 32),40) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_deamont_p521_tmc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p521_tmc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p521_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,9) s =
                  (inverse_mod p_521 (2 EXP 576) * a) MOD p_521)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                     memory :> bytes(word_sub stackpointer (word 32),32)])`,
  X86_PROMOTE_RETURN_STACK_TAC
   bignum_deamont_p521_tmc BIGNUM_DEAMONT_P521_CORRECT
   `[RBX; R12; R13; RBP]` 32);;

let BIGNUM_DEAMONT_P521_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 9) (word_sub stackpointer (word 32),40) /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,LENGTH bignum_deamont_p521_mc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p521_mc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p521_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,9) s =
                  (inverse_mod p_521 (2 EXP 576) * a) MOD p_521)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                     memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEAMONT_P521_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_deamont_p521_windows_mc = define_from_elf
   "bignum_deamont_p521_windows_mc" "x86/p521/bignum_deamont_p521.obj";;

let bignum_deamont_p521_windows_tmc = define_trimmed "bignum_deamont_p521_windows_tmc" bignum_deamont_p521_windows_mc;;

let BIGNUM_DEAMONT_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 9) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_deamont_p521_windows_tmc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p521_windows_tmc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p521_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,9) s =
                  (inverse_mod p_521 (2 EXP 576) * a) MOD p_521)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                     memory :> bytes(word_sub stackpointer (word 48),48)])`,
  WINDOWS_X86_WRAP_STACK_TAC
   bignum_deamont_p521_windows_tmc bignum_deamont_p521_tmc
   BIGNUM_DEAMONT_P521_CORRECT `[RBX; R12; R13; RBP]` 32);;

let BIGNUM_DEAMONT_P521_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
        nonoverlapping (z,8 * 9) (word_sub stackpointer (word 48),56) /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(word pc,LENGTH bignum_deamont_p521_windows_mc); (x,8 * 9)] /\
        nonoverlapping (word pc,LENGTH bignum_deamont_p521_windows_mc) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_deamont_p521_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = a)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,9) s =
                  (inverse_mod p_521 (2 EXP 576) * a) MOD p_521)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 9);
                     memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_DEAMONT_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

