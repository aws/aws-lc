(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_521 of a single word and a bignum < p_521.        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p521/bignum_cmul_p521.o";;
 ****)

let bignum_cmul_p521_mc = define_assert_from_elf "bignum_cmul_p521_mc" "x86/p521/bignum_cmul_p521.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
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
  0xc4; 0x62; 0xfb; 0xf6; 0x59; 0x18;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rcx,24))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x59; 0x20;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rcx,32))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x69; 0x28;
                           (* MULX4 (% rbp,% rax) (% rdx,Memop Quadword (%% (rcx,40))) *)
  0x48; 0x11; 0xc3;        (* ADC (% rbx) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x61; 0x30;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rcx,48))) *)
  0x48; 0x11; 0xc5;        (* ADC (% rbp) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x69; 0x38;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rcx,56))) *)
  0x49; 0x11; 0xc4;        (* ADC (% r12) (% rax) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x49; 0x40;
                           (* MULX4 (% rcx,% rax) (% rdx,Memop Quadword (%% (rcx,64))) *)
  0x49; 0x11; 0xc5;        (* ADC (% r13) (% rax) *)
  0x48; 0x83; 0xd1; 0x00;  (* ADC (% rcx) (Imm8 (word 0)) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x4c; 0x21; 0xc8;        (* AND (% rax) (% r9) *)
  0x4c; 0x21; 0xd0;        (* AND (% rax) (% r10) *)
  0x4c; 0x21; 0xd8;        (* AND (% rax) (% r11) *)
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0x21; 0xe8;        (* AND (% rax) (% rbp) *)
  0x4c; 0x21; 0xe0;        (* AND (% rax) (% r12) *)
  0x4c; 0x0f; 0xa4; 0xe9; 0x37;
                           (* SHLD (% rcx) (% r13) (Imm8 (word 55)) *)
  0x49; 0x81; 0xcd; 0x00; 0xfe; 0xff; 0xff;
                           (* OR (% r13) (Imm32 (word 4294966784)) *)
  0x48; 0x8d; 0x51; 0x01;  (* LEA (% rdx) (%% (rcx,1)) *)
  0x48; 0x01; 0xf2;        (* ADD (% rdx) (% rsi) *)
  0xba; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 0)) *)
  0x48; 0x11; 0xd0;        (* ADC (% rax) (% rdx) *)
  0x4c; 0x89; 0xe8;        (* MOV (% rax) (% r13) *)
  0x48; 0x11; 0xd0;        (* ADC (% rax) (% rdx) *)
  0x48; 0x11; 0xce;        (* ADC (% rsi) (% rcx) *)
  0x48; 0x89; 0x37;        (* MOV (Memop Quadword (%% (rdi,0))) (% rsi) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4c; 0x89; 0x47; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r8) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0x4f; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r9) *)
  0x49; 0x11; 0xd2;        (* ADC (% r10) (% rdx) *)
  0x4c; 0x89; 0x57; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r10) *)
  0x49; 0x11; 0xd3;        (* ADC (% r11) (% rdx) *)
  0x4c; 0x89; 0x5f; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r11) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x89; 0x5f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% rbx) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x89; 0x6f; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rbp) *)
  0x49; 0x11; 0xd4;        (* ADC (% r12) (% rdx) *)
  0x4c; 0x89; 0x67; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% r12) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x49; 0x81; 0xe5; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% r13) (Imm32 (word 511)) *)
  0x4c; 0x89; 0x6f; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r13) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_cmul_p521_tmc = define_trimmed "bignum_cmul_p521_tmc" bignum_cmul_p521_mc;;

let BIGNUM_CMUL_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_cmul_p521_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_CMUL_P521_CORRECT = time prove
 (`!z c x a pc.
        nonoverlapping (word pc,0xdf) (z,8 * 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_cmul_p521_tmc) /\
                  read RIP s = word(pc + 0x6) /\
                  C_ARGUMENTS [z; c; x] s /\
                  bignum_from_memory (x,9) s = a)
             (\s. read RIP s = word (pc + 0xd8) /\
                  (a < p_521
                   ==> bignum_from_memory (z,9) s = (val c * a) MOD p_521))
             (MAYCHANGE [RIP; RSI; RAX; RCX; RDX; R8; R9; R10; R11;
                         RBX; RBP; R12; R13] ,,
              MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `c:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `a < p_521` THENL
   [ASM_REWRITE_TAC[]; X86_SIM_TAC BIGNUM_CMUL_P521_EXEC (1--54)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,9) s0` THEN

  (*** The initial basic multiply, after which we forget a and c ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P521_EXEC (1--27) (1--27) THEN
  ABBREV_TAC `n = val(c:int64) * a` THEN
  SUBGOAL_THEN `n < (2 EXP 64 - 1) * 2 EXP 521` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `n <= (2 EXP 64 - 1) * (2 EXP 521 - 1)
      ==> n < (2 EXP 64 - 1) * 2 EXP 521`) THEN
    EXPAND_TAC "n" THEN MATCH_MP_TAC LE_MULT2 THEN
    REWRITE_TAC[VAL_BOUND_64; ARITH_RULE
     `x <= 2 EXP 64 - 1 <=> x < 2 EXP 64`] THEN
    UNDISCH_TAC `a < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [mullo_s3; sum_s5; sum_s7; sum_s9; sum_s11;
      sum_s13; sum_s15; sum_s17; sum_s19; sum_s20] = n`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n"; "a"] THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`word(a):int64 = c`] THEN
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `c:int64` o concl))) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num` o concl)))] THEN

  (*** Breaking the problem down to (h + l) MOD p_521 ***)

  SUBGOAL_THEN `n MOD p_521 = (n DIV 2 EXP 521 + n MOD 2 EXP 521) MOD p_521`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [ARITH_RULE `n = 2 EXP 521 * n DIV 2 EXP 521 + n MOD 2 EXP 521`] THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[p_521; CONG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n DIV 2 EXP 521 < 2 EXP 64 - 1 /\ n MOD 2 EXP 521 < 2 EXP 521`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN
    UNDISCH_TAC `n < (2 EXP 64 - 1) * 2 EXP 521` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Splitting up and stuffing 1 bits into the low part ***)

  X86_STEPS_TAC BIGNUM_CMUL_P521_EXEC (28--29) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_AND_ASSOC; DIMINDEX_64]) THEN
  MAP_EVERY ABBREV_TAC
   [`h:int64 =
     word_subword(word_join (sum_s20:int64) (sum_s19:int64):int128) (9,64)`;
    `d:int64 = word_or sum_s19 (word 18446744073709551104)`;
    `dd:int64 = word_and sum_s5 (word_and sum_s7 (word_and sum_s9
      (word_and sum_s11 (word_and sum_s13 (word_and sum_s15 sum_s17)))))`] THEN

  (*** The comparison in its direct condensed form ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P521_EXEC [31;33;35] (30--35) THEN
  SUBGOAL_THEN
   `&(val (word_add h (word 1):int64)):real = &(val h) + &1`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD_CASES] THEN
    REWRITE_TAC[DIMINDEX_64; VAL_WORD_1] THEN
    MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
    SUBST1_TAC(SYM(ASSUME
     `word_subword(word_join (sum_s20:int64) (sum_s19:int64):int128) (9,64) =
      (h:int64)`)) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LT; ARITH_LE] THEN
    MATCH_MP_TAC(ARITH_RULE
     `x < 2 EXP 64 - 1 /\ (x < 2 EXP 64 ==> x MOD 2 EXP 64 = x)
      ==> x MOD 2 EXP 64 + 1 < 2 EXP 64`) THEN
    SIMP_TAC[MOD_LT] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `n < (2 EXP 64 - 1) * 2 EXP 521
      ==> n DIV 2 EXP 512 = x ==> x DIV 2 EXP 9 < 2 EXP 64 - 1`)) THEN
    EXPAND_TAC "n" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `carry_s35 <=>
    2 EXP 192 <=
      2 EXP 128 * val(d:int64) + 2 EXP 64 * val(dd:int64) +
      val(h:int64) + val(mullo_s3:int64) + 1`
  (ASSUME_TAC o SYM) THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `192` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Finish the simulation before completing the mathematics ***)

  X86_ACCSTEPS_TAC BIGNUM_CMUL_P521_EXEC
   [36;38;40;42;44;46;48;50;52] (36--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s54" THEN

  (*** Evaluate d and un-condense the inequality ***)

  SUBGOAL_THEN
   `val(d:int64) = 2 EXP 9 * (2 EXP 55 - 1) + val(sum_s19:int64) MOD 2 EXP 9`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "d" THEN ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 512 * val(sum_s19:int64) MOD 2 EXP 9 +
    bignum_of_wordlist
     [mullo_s3; sum_s5; sum_s7; sum_s9; sum_s11; sum_s13; sum_s15; sum_s17] =
    n MOD 2 EXP 521`
  (LABEL_TAC "*") THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(8,2)] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 521 = 2 EXP 512 * 2 EXP 9`] THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `64 * 8`)] THEN
    SIMP_TAC[LENGTH; ARITH_LT; ARITH_LE; MOD_MULT_MOD; ADD_CLAUSES;
             ARITH_SUC; BIGNUM_OF_WORDLIST_BOUND; MOD_LT; DIV_LT;
             MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN
     `bignum_of_wordlist[sum_s19; sum_s20] MOD 2 EXP 9 =
      val sum_s19 MOD 2 EXP 9`
    SUBST1_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; MOD_MULT_ADD; GSYM MULT_ASSOC;
                  ARITH_RULE `2 EXP 64 = 2 EXP 9 * 2 EXP 55`];
      ARITH_TAC];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `2 EXP 521 <= n MOD 2 EXP 521 + val(h:int64) + 1 <=> carry_s35`
  MP_TAC THENL
   [REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN EXPAND_TAC "carry_s35" THEN
    ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MATCH_MP_TAC(TAUT
     `!p q. ((p ==> ~r) /\ (q ==> ~s)) /\ (p <=> q) /\ (~p /\ ~q ==> (r <=> s))
            ==> (r <=> s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`bignum_of_wordlist
        [sum_s5; sum_s7; sum_s9; sum_s11; sum_s13; sum_s15; sum_s17] <
       2 EXP (64 * 7) - 1`;
      `val(dd:int64) < 2 EXP 64 - 1`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `2 EXP 64 * b + d < 2 EXP 64 * (a + 1) + c ==> a < b ==> ~(c <= d)`) THEN
      MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
      MP_TAC(SPEC `mullo_s3:int64` VAL_BOUND_64) THEN ARITH_TAC;
      SIMP_TAC[BIGNUM_OF_WORDLIST_LT_MAX; LENGTH; ARITH_EQ; ARITH_SUC]] THEN
    REWRITE_TAC[GSYM NOT_ALL] THEN MP_TAC(ISPEC `dd:int64` VAL_EQ_MAX) THEN
    SIMP_TAC[VAL_BOUND_64; DIMINDEX_64; ARITH_RULE
      `a < n ==> (a < n - 1 <=> ~(a = n - 1))`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[WORD_NOT_AND; ALL; WORD_OR_EQ_0] THEN
    REWRITE_TAC[WORD_RULE `word_not d = e <=> d = word_not e`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `val(sum_s19:int64) MOD 2 EXP 9 = 511 \/
                       val(sum_s19:int64) MOD 2 EXP 9 < 511`) THEN
    MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN
    MP_TAC(SPEC `mullo_s3:int64` VAL_BOUND_64) THEN ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (is_iff o concl))] THEN

  (*** Also evaluate h ***)

  SUBGOAL_THEN `val(h:int64) = n DIV 2 EXP 521` SUBST_ALL_TAC THENL
   [EXPAND_TAC "h" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LT; ARITH_LE] THEN
    MATCH_MP_TAC(MESON[MOD_LT] `x = y /\ y < d ==> x MOD d = y`) THEN
    ASM_SIMP_TAC[ARITH_RULE `n < 2 EXP 64 - 1 ==> n < 2 EXP 64`] THEN
    MATCH_MP_TAC(ARITH_RULE
     `n DIV 2 EXP 512 = x ==> x DIV 2 EXP 9 = n DIV 2 EXP 521`) THEN
    EXPAND_TAC "n" THEN CONV_TAC(LAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Now complete the mathematics ***)

  SUBGOAL_THEN
   `2 EXP 521 <= n MOD 2 EXP 521 + n DIV 2 EXP 521 + 1 <=>
    p_521 <= n DIV 2 EXP 521 + n MOD 2 EXP 521`
  SUBST1_TAC THENL [REWRITE_TAC[p_521] THEN ARITH_TAC; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`521`;
    `if n DIV 2 EXP 521 + n MOD 2 EXP 521 < p_521
     then &(n DIV 2 EXP 521 + n MOD 2 EXP 521)
     else &(n DIV 2 EXP 521 + n MOD 2 EXP 521) - &p_521`] THEN
  REPEAT CONJ_TAC THENL
   [BOUNDER_TAC[];
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC;
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `n < (2 EXP 64 - 1) * 2 EXP 521` THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[GSYM NOT_LE; COND_SWAP; GSYM REAL_OF_NUM_SUB; COND_ID]] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  REMOVE_THEN "*" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 9 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD; p_521] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_CMUL_P521_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
       nonoverlapping (word_sub stackpointer (word 32),32) (x,8 * 9) /\
       nonoverlapping (z,8 * 9) (word_sub stackpointer (word 32),40) /\
       ALL (nonoverlapping (word pc,LENGTH bignum_cmul_p521_tmc))
           [(z,8 * 9); (word_sub stackpointer (word 32),32)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_cmul_p521_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [z; c; x] s /\
                 bignum_from_memory (x,9) s = a)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (a < p_521
                  ==> bignum_from_memory (z,9) s = (val c * a) MOD p_521))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,9);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_cmul_p521_tmc BIGNUM_CMUL_P521_CORRECT
   `[RBX; RBP; R12; R13]` 32);;

let BIGNUM_CMUL_P521_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
       nonoverlapping (word_sub stackpointer (word 32),32) (x,8 * 9) /\
       nonoverlapping (z,8 * 9) (word_sub stackpointer (word 32),40) /\
       ALL (nonoverlapping (word pc,LENGTH bignum_cmul_p521_mc))
           [(z,8 * 9); (word_sub stackpointer (word 32),32)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_cmul_p521_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [z; c; x] s /\
                 bignum_from_memory (x,9) s = a)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (a < p_521
                  ==> bignum_from_memory (z,9) s = (val c * a) MOD p_521))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,9);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P521_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_cmul_p521_windows_mc = define_from_elf
   "bignum_cmul_p521_windows_mc" "x86/p521/bignum_cmul_p521.obj";;

let bignum_cmul_p521_windows_tmc = define_trimmed "bignum_cmul_p521_windows_tmc" bignum_cmul_p521_windows_mc;;

let BIGNUM_CMUL_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
       nonoverlapping (word_sub stackpointer (word 48),48) (x,8 * 9) /\
       nonoverlapping (z,8 * 9) (word_sub stackpointer (word 48),56) /\
       ALL (nonoverlapping (word pc,LENGTH bignum_cmul_p521_windows_tmc))
           [(z,8 * 9); (word_sub stackpointer (word 48),48)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_cmul_p521_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [z; c; x] s /\
                 bignum_from_memory (x,9) s = a)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (a < p_521
                  ==> bignum_from_memory (z,9) s = (val c * a) MOD p_521))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,9);
                        memory :> bytes(word_sub stackpointer (word 48),48)])`,
  WINDOWS_X86_WRAP_STACK_TAC bignum_cmul_p521_windows_tmc bignum_cmul_p521_tmc
    BIGNUM_CMUL_P521_CORRECT `[RBX; RBP; R12; R13]` 32);;

let BIGNUM_CMUL_P521_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z c x a pc stackpointer returnaddress.
       nonoverlapping (word_sub stackpointer (word 48),48) (x,8 * 9) /\
       nonoverlapping (z,8 * 9) (word_sub stackpointer (word 48),56) /\
       ALL (nonoverlapping (word pc,LENGTH bignum_cmul_p521_windows_mc))
           [(z,8 * 9); (word_sub stackpointer (word 48),48)]
       ==> ensures x86
            (\s. bytes_loaded s (word pc) bignum_cmul_p521_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [z; c; x] s /\
                 bignum_from_memory (x,9) s = a)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (a < p_521
                  ==> bignum_from_memory (z,9) s = (val c * a) MOD p_521))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,9);
                        memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_CMUL_P521_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

