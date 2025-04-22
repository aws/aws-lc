(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Mapping out of Montgomery representation modulo p_384.                    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_demont_p384.o";;
 ****)

let bignum_demont_p384_mc =
  define_assert_from_elf "bignum_demont_p384_mc" "arm/p384/bignum_demont_p384.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xd3607c4a;       (* arm_LSL X10 X2 (rvalue (word 32)) *)
  0x8b020142;       (* arm_ADD X2 X10 X2 *)
  0xd360fc4a;       (* arm_LSR X10 X2 (rvalue (word 32)) *)
  0xeb02014a;       (* arm_SUBS X10 X10 X2 *)
  0xda1f0049;       (* arm_SBC X9 X2 XZR *)
  0x93ca812a;       (* arm_EXTR X10 X9 X10 (rvalue (word 32)) *)
  0xd360fd29;       (* arm_LSR X9 X9 (rvalue (word 32)) *)
  0xab020129;       (* arm_ADDS X9 X9 X2 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0xeb0a0063;       (* arm_SUBS X3 X3 X10 *)
  0xfa090084;       (* arm_SBCS X4 X4 X9 *)
  0xfa0800a5;       (* arm_SBCS X5 X5 X8 *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xda1f0042;       (* arm_SBC X2 X2 XZR *)
  0xd3607c6a;       (* arm_LSL X10 X3 (rvalue (word 32)) *)
  0x8b030143;       (* arm_ADD X3 X10 X3 *)
  0xd360fc6a;       (* arm_LSR X10 X3 (rvalue (word 32)) *)
  0xeb03014a;       (* arm_SUBS X10 X10 X3 *)
  0xda1f0069;       (* arm_SBC X9 X3 XZR *)
  0x93ca812a;       (* arm_EXTR X10 X9 X10 (rvalue (word 32)) *)
  0xd360fd29;       (* arm_LSR X9 X9 (rvalue (word 32)) *)
  0xab030129;       (* arm_ADDS X9 X9 X3 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0xeb0a0084;       (* arm_SUBS X4 X4 X10 *)
  0xfa0900a5;       (* arm_SBCS X5 X5 X9 *)
  0xfa0800c6;       (* arm_SBCS X6 X6 X8 *)
  0xfa1f00e7;       (* arm_SBCS X7 X7 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0063;       (* arm_SBC X3 X3 XZR *)
  0xd3607c8a;       (* arm_LSL X10 X4 (rvalue (word 32)) *)
  0x8b040144;       (* arm_ADD X4 X10 X4 *)
  0xd360fc8a;       (* arm_LSR X10 X4 (rvalue (word 32)) *)
  0xeb04014a;       (* arm_SUBS X10 X10 X4 *)
  0xda1f0089;       (* arm_SBC X9 X4 XZR *)
  0x93ca812a;       (* arm_EXTR X10 X9 X10 (rvalue (word 32)) *)
  0xd360fd29;       (* arm_LSR X9 X9 (rvalue (word 32)) *)
  0xab040129;       (* arm_ADDS X9 X9 X4 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0xeb0a00a5;       (* arm_SUBS X5 X5 X10 *)
  0xfa0900c6;       (* arm_SBCS X6 X6 X9 *)
  0xfa0800e7;       (* arm_SBCS X7 X7 X8 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xda1f0084;       (* arm_SBC X4 X4 XZR *)
  0xd3607caa;       (* arm_LSL X10 X5 (rvalue (word 32)) *)
  0x8b050145;       (* arm_ADD X5 X10 X5 *)
  0xd360fcaa;       (* arm_LSR X10 X5 (rvalue (word 32)) *)
  0xeb05014a;       (* arm_SUBS X10 X10 X5 *)
  0xda1f00a9;       (* arm_SBC X9 X5 XZR *)
  0x93ca812a;       (* arm_EXTR X10 X9 X10 (rvalue (word 32)) *)
  0xd360fd29;       (* arm_LSR X9 X9 (rvalue (word 32)) *)
  0xab050129;       (* arm_ADDS X9 X9 X5 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0xeb0a00c6;       (* arm_SUBS X6 X6 X10 *)
  0xfa0900e7;       (* arm_SBCS X7 X7 X9 *)
  0xfa080042;       (* arm_SBCS X2 X2 X8 *)
  0xfa1f0063;       (* arm_SBCS X3 X3 XZR *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xda1f00a5;       (* arm_SBC X5 X5 XZR *)
  0xd3607cca;       (* arm_LSL X10 X6 (rvalue (word 32)) *)
  0x8b060146;       (* arm_ADD X6 X10 X6 *)
  0xd360fcca;       (* arm_LSR X10 X6 (rvalue (word 32)) *)
  0xeb06014a;       (* arm_SUBS X10 X10 X6 *)
  0xda1f00c9;       (* arm_SBC X9 X6 XZR *)
  0x93ca812a;       (* arm_EXTR X10 X9 X10 (rvalue (word 32)) *)
  0xd360fd29;       (* arm_LSR X9 X9 (rvalue (word 32)) *)
  0xab060129;       (* arm_ADDS X9 X9 X6 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0xeb0a00e7;       (* arm_SUBS X7 X7 X10 *)
  0xfa090042;       (* arm_SBCS X2 X2 X9 *)
  0xfa080063;       (* arm_SBCS X3 X3 X8 *)
  0xfa1f0084;       (* arm_SBCS X4 X4 XZR *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xda1f00c6;       (* arm_SBC X6 X6 XZR *)
  0xd3607cea;       (* arm_LSL X10 X7 (rvalue (word 32)) *)
  0x8b070147;       (* arm_ADD X7 X10 X7 *)
  0xd360fcea;       (* arm_LSR X10 X7 (rvalue (word 32)) *)
  0xeb07014a;       (* arm_SUBS X10 X10 X7 *)
  0xda1f00e9;       (* arm_SBC X9 X7 XZR *)
  0x93ca812a;       (* arm_EXTR X10 X9 X10 (rvalue (word 32)) *)
  0xd360fd29;       (* arm_LSR X9 X9 (rvalue (word 32)) *)
  0xab070129;       (* arm_ADDS X9 X9 X7 *)
  0x9a1f03e8;       (* arm_ADC X8 XZR XZR *)
  0xeb0a0042;       (* arm_SUBS X2 X2 X10 *)
  0xfa090063;       (* arm_SBCS X3 X3 X9 *)
  0xfa080084;       (* arm_SBCS X4 X4 X8 *)
  0xfa1f00a5;       (* arm_SBCS X5 X5 XZR *)
  0xfa1f00c6;       (* arm_SBCS X6 X6 XZR *)
  0xda1f00e7;       (* arm_SBC X7 X7 XZR *)
  0xa9000c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011404;       (* arm_STP X4 X5 X0 (Immediate_Offset (iword (&16))) *)
  0xa9021c06;       (* arm_STP X6 X7 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DEMONT_P384_EXEC = ARM_MK_EXEC_RULE bignum_demont_p384_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let swlemma = WORD_RULE
  `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &(val(word(4294967297 * val x):int64)) * &18446744069414584321
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &(val(word(4294967297 * val x):int64)) * &18446744069414584321`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> ((a * x) * b == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** Intricate Montgomery steps done generically ***)

let montred_tac execth regs n =
  let topflag,[d7;d6;d5;d4;d3;d2;d1;d0; t3;t2;t1] =
    let rlist = dest_list regs in
    if length rlist = 11 then true,rlist
    else false,`XZR`::rlist in
  let modterm = subst
   ([d0,`X2`; d1,`X3`; d2,`X4`; d3,`X5`; d4,`X6`; d5,`X7`; d6,`X1`; d7,`X0`;
     t1,`X10`; t2,`X9`; t3,`X8`] @
    (map (fun i -> mk_var("s"^string_of_int(i+n-3),`:armstate`),
                   mk_var("s"^string_of_int(i),`:armstate`))
         (3--20)) @
    [mk_var("sum_s"^string_of_int(7+n-3),`:int64`),
     mk_var("sum_s"^string_of_int(7),`:int64`);
     mk_var("sum_s"^string_of_int(8+n-3),`:int64`),
     mk_var("sum_s"^string_of_int(8),`:int64`)] @
    [mk_var("mvl_"^string_of_int n,`:num`),mk_var("mvl",`:num`);
     mk_var("nvl_"^string_of_int n,`:num`),mk_var("nvl",`:num`);
     mk_var("ww_"^string_of_int n,`:int64`),mk_var("w",`:int64`);
     mk_var("tt_"^string_of_int n,`:num`),mk_var("t",`:num`)])
  and modstring =
   C assoc
    (zip (statenames "s" (3--20)) (statenames "s" (n--(n+17))) @
    ["mvl","mvl_"^string_of_int n;
     "w","ww_"^string_of_int n;
     "t","tt_"^string_of_int n]) in
  (*** Abbreviate the input ***)
  ABBREV_TAC
   (modterm `mvl =
    bignum_of_wordlist[read X2 s3; read X3 s3; read X4 s3; read X5 s3;
                       read X6 s3; read X7 s3]`) THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (if topflag then
     ABBREV_TAC
     (modterm `nvl =
      bignum_of_wordlist[read X2 s3; read X3 s3; read X4 s3; read X5 s3;
                         read X6 s3; read X7 s3; read X1 s3]`) THEN
     POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
   else ALL_TAC) THEN
  (*** Selection of the multiplier, similar to the x86 case ***)
  MAP_EVERY (ARM_SINGLE_STEP_TAC execth)
            (map modstring (statenames "s" (4--5))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[swlemma]) THEN
  REABBREV_TAC (modterm `w = read X2 s5`) THEN
  (*** Next three steps setting up [t2;t1] = 2^64 * w - w + w_hi ***)
  ARM_SINGLE_STEP_TAC execth (modstring "s6") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s7") THEN
  ACCUMULATE_ARITH_TAC (modstring "s7") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s8") THEN
  ACCUMULATE_ARITH_TAC (modstring "s8") THEN
  SUBGOAL_THEN
   (modterm `&2 pow 64 * &(val(read X9 s8)) + &(val(read X10 s8)):real =
    &2 pow 64 * &(val(w:int64)) - &(val w) + &(val w DIV 2 EXP 32)`)
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VAL_WORD_USHR] THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  (*** Next four steps setting up
   *** [t3;t2;t1] = (2^128 + 2^96 - 2^32 + 1) * w - w MOD 2^32
   ***)
  ARM_SINGLE_STEP_TAC execth (modstring "s9") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s10") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s11") THEN
  ACCUMULATE_ARITH_TAC (modstring "s11") THEN
  ARM_SINGLE_STEP_TAC execth (modstring "s12") THEN
  (*** This is what we really want ***)
  ABBREV_TAC
   (modterm `t = 2 EXP 64 * val(sum_s8:int64) + val(sum_s7:int64)`) THEN
  SUBGOAL_THEN
   (modterm `&(bignum_of_wordlist
       [word(mvl MOD 2 EXP 64); read X10 s12; read X9 s12; read X8 s12]):real =
    (&2 pow 128 + &2 pow 96 - &2 pow 32 + &1) * &(val(w:int64))`)
  MP_TAC THEN
  EXPAND_TAC (modstring "mvl") THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_MOD; WORD_VAL] THENL
   [TRANS_TAC EQ_TRANS
     (modterm `&2 pow 128 * &(val(w:int64)) +
      &2 pow 32 * &t + &(val w MOD 2 EXP 32)`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL EQ_DIVMOD))));
      EXPAND_TAC (modstring "t") THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
      REAL_ARITH_TAC] THEN
    EXISTS_TAC `2 EXP 64` THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[DIV_LT; VAL_BOUND_64; ADD_CLAUSES] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE
       `(2 EXP 128 * w + 2 EXP 32 * t + r MOD 2 EXP 32) DIV 2 EXP 64 =
        2 EXP 64 * w + t DIV 2 EXP 32`];
      REWRITE_TAC[GSYM CONG; num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC(INTEGER_RULE
       `!y:int. z = y /\ (y == x) (mod n)
                ==> (x == z) (mod n)`) THEN
      EXISTS_TAC
       (modterm `(&2 pow 128 + &2 pow 96 - &2 pow 32 + &1) *
                 &(val(w:int64)):int`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[int_eq; int_pow_th; int_mul_th; int_sub_th; int_add_th;
                    int_of_num_th] THEN
        EXPAND_TAC (modstring "t") THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_MOD; GSYM REAL_OF_NUM_CLAUSES] THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check
         (can (term_match [] `word(4294967297 * x) = w`) o concl)) THEN
        REWRITE_TAC[GSYM INT_REM_EQ; VAL_WORD; DIMINDEX_64] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
        CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
        MATCH_MP_TAC(INTEGER_RULE
         `(a * b:int == &1) (mod p) ==> (a * b * x == x) (mod p)`) THEN
        REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV]] THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `s + 2 EXP 64 * c = 2 EXP 64 * c + s`] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; ARITH_LE; ARITH_LT; VAL_WORD_USHR] THEN
    REWRITE_TAC[VAL_WORD_0] THEN EXPAND_TAC (modstring "t") THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  (*** The main accumulation of the same-size portion and adding to w ***)
  MAP_EVERY (fun s ->
        ARM_SINGLE_STEP_TAC execth s THEN
        ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
    (map modstring (statenames "s" (13--18))) THEN
  SUBGOAL_THEN
   (modterm
     (if topflag then
       `&2 pow 64 * &(bignum_of_wordlist[read X3 s18; read X4 s18; read X5 s18;
                                  read X6 s18; read X7 s18; read X2 s18]) =
        &mvl + &p_384 * &(val(w:int64))`
      else
       `&2 pow 64 * &(bignum_of_wordlist[read X3 s18; read X4 s18; read X5 s18;
                                  read X6 s18; read X7 s18; read X1 s18]) =
        &mvl + &p_384 * &(val(w:int64))`))
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`448`; `&0:real`] THEN
    EXPAND_TAC(modstring "mvl") THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (LAND_CONV o RAND_CONV)
     [CONJUNCT2 bignum_of_wordlist]) THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    REWRITE_TAC[VAL_WORD_BITVAL] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `x + a:real = b ==> x = b - a`)) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ASM_REWRITE_TAC[] THEN ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN
  (*** Final little accumulation in the non-short case ***)
  (if topflag then
     DISCH_TAC THEN
     ARM_SINGLE_STEP_TAC execth (modstring "s19") THEN
     ACCUMULATE_ARITH_TAC (modstring "s19") THEN
     ARM_SINGLE_STEP_TAC execth (modstring "s20") THEN
     SUBGOAL_THEN (modterm
      `&2 pow 64 * &(bignum_of_wordlist[read X3 s20; read X4 s20; read X5 s20;
                       read X6 s20; read X7 s20; read X1 s20; read X0 s20]) =
        &nvl + &p_384 * &(val(w:int64))`)
     MP_TAC THENL
      [ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
        `x:real = m + p * w  ==> n - m = y - x ==> y = n + p * w`)) THEN
       FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
       FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
       REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
       ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN REAL_ARITH_TAC;
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
        `x:real = m + p * w ==> (y = n + p * w ==> q)
         ==> y = n + p * w ==> q`)) THEN
       ASM_REWRITE_TAC[ADD_CLAUSES] THEN
       ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])]
   else ALL_TAC);;

let montred_subst_tac execth regs n =
  montred_tac execth regs n THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> b = a - c`));;

let BIGNUM_DEMONT_P384_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x184) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_demont_p384_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + 0x180) /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a) MOD p_384))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  MAP_EVERY (ARM_SINGLE_STEP_TAC BIGNUM_DEMONT_P384_EXEC)
            (statenames "s" (1--3)) THEN
  montred_tac BIGNUM_DEMONT_P384_EXEC
   `[X2;X7;X6;X5;X4;X3;X2; X8;X9;X10]` 3 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_DEMONT_P384_EXEC
   `[X3;X2;X7;X6;X5;X4;X3; X8;X9;X10]` 18 THEN
  montred_subst_tac BIGNUM_DEMONT_P384_EXEC
   `[X4;X3;X2;X7;X6;X5;X4; X8;X9;X10]` 33 THEN
  montred_subst_tac BIGNUM_DEMONT_P384_EXEC
   `[X5;X4;X3;X2;X7;X6;X5; X8;X9;X10]` 48 THEN
  montred_subst_tac BIGNUM_DEMONT_P384_EXEC
  `[X6;X5;X4;X3;X2;X7;X6; X8;X9;X10]` 63 THEN
  montred_subst_tac BIGNUM_DEMONT_P384_EXEC
   `[X7;X6;X5;X4;X3;X2;X7; X8;X9;X10]` 78 THEN

  ARM_STEPS_TAC BIGNUM_DEMONT_P384_EXEC (94--96) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  MATCH_MP_TAC(MESON[]
   `(2 EXP 384 * t <= (2 EXP 384 - 1) * p_384 + a /\
     (2 EXP 384 * t == a) (mod p_384)
     ==> t = (inverse_mod p_384 (2 EXP 384) * a) MOD p_384) /\
    2 EXP 384 * t <= (2 EXP 384 - 1) * p_384 + a /\
    (2 EXP 384 * t == a) (mod p_384)
    ==> t = (inverse_mod p_384 (2 EXP 384) * a) MOD p_384`) THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM NOT_LT]) THEN
      UNDISCH_TAC `a < p_384` THEN REWRITE_TAC[p_384] THEN ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(NUMBER_RULE
       `(e * t == a) (mod p)
        ==> (e * i == 1) (mod p) ==> (i * a == t) (mod p)`)) THEN
      REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
      REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN

  EXPAND_TAC "a" THEN
  REWRITE_TAC[REAL_CONGRUENCE; GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a:real <= b + c <=> a - c <= b`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE
   (RAND_CONV o RAND_CONV) [bignum_of_wordlist]) THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o TOP_DEPTH_CONV)
   [REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[p_384] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; REAL_INTEGER_TAC]);;

let BIGNUM_DEMONT_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,0x184) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_demont_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  (a < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a) MOD p_384))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_DEMONT_P384_EXEC
    BIGNUM_DEMONT_P384_CORRECT);;
