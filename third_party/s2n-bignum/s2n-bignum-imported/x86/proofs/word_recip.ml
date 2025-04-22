(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Word-level negated modular inverse.                                       *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/word_recip.o";;
 ****)

let word_recip_mc = define_assert_from_elf "word_recip_mc" "x86/generic/word_recip.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x89; 0xfe;        (* MOV (% rsi) (% rdi) *)
  0x48; 0xb9; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x01; 0x00;
                           (* MOV (% rcx) (Imm64 (word 562949953421311)) *)
  0x48; 0xc1; 0xee; 0x10;  (* SHR (% rsi) (Imm8 (word 16)) *)
  0x48; 0x31; 0xf1;        (* XOR (% rcx) (% rsi) *)
  0x48; 0xff; 0xc6;        (* INC (% rsi) *)
  0x48; 0xc1; 0xe9; 0x20;  (* SHR (% rcx) (Imm8 (word 32)) *)
  0x48; 0x89; 0xf2;        (* MOV (% rdx) (% rsi) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0x89; 0xd0;        (* MOV (% rax) (% rdx) *)
  0x48; 0xc1; 0xe8; 0x31;  (* SHR (% rax) (Imm8 (word 49)) *)
  0x48; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% rax) *)
  0x48; 0xc1; 0xea; 0x22;  (* SHR (% rdx) (Imm8 (word 34)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x48; 0x0d; 0x00; 0x00; 0x00; 0x40;
                           (* OR (% rax) (Imm32 (word 1073741824)) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x48; 0xc1; 0xe8; 0x1e;  (* SHR (% rax) (Imm8 (word 30)) *)
  0x48; 0x0f; 0xaf; 0xc1;  (* IMUL (% rax) (% rcx) *)
  0x48; 0xc1; 0xe1; 0x1e;  (* SHL (% rcx) (Imm8 (word 30)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0xc1; 0xe9; 0x1e;  (* SHR (% rcx) (Imm8 (word 30)) *)
  0x48; 0x89; 0xf2;        (* MOV (% rdx) (% rsi) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0xc1; 0xea; 0x18;  (* SHR (% rdx) (Imm8 (word 24)) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xc1; 0xe1; 0x10;  (* SHL (% rcx) (Imm8 (word 16)) *)
  0x48; 0xc1; 0xea; 0x18;  (* SHR (% rdx) (Imm8 (word 24)) *)
  0x48; 0x01; 0xd1;        (* ADD (% rcx) (% rdx) *)
  0x48; 0x89; 0xf2;        (* MOV (% rdx) (% rsi) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xf7; 0xda;        (* NEG (% rdx) *)
  0x48; 0xc1; 0xea; 0x20;  (* SHR (% rdx) (Imm8 (word 32)) *)
  0x48; 0x0f; 0xaf; 0xd1;  (* IMUL (% rdx) (% rcx) *)
  0x48; 0xc1; 0xe1; 0x1f;  (* SHL (% rcx) (Imm8 (word 31)) *)
  0x48; 0xc1; 0xea; 0x11;  (* SHR (% rdx) (Imm8 (word 17)) *)
  0x48; 0x01; 0xd1;        (* ADD (% rcx) (% rdx) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x0f; 0xac; 0xd0; 0x3c;
                           (* SHRD (% rax) (% rdx) (Imm8 (word 60)) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x48; 0xc1; 0xea; 0x21;  (* SHR (% rdx) (Imm8 (word 33)) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% rdx) *)
  0x48; 0xd1; 0xe1;        (* SHL (% rcx) (Imm8 (word 1)) *)
  0x48; 0xc1; 0xe8; 0x21;  (* SHR (% rax) (Imm8 (word 33)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x83; 0xc1; 0x01;  (* ADD (% rcx) (Imm8 (word 1)) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0x83; 0xd9; 0x00;  (* SBB (% rcx) (Imm8 (word 0)) *)
  0x48; 0xf7; 0xe1;        (* MUL2 (% rdx,% rax) (% rcx) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x48; 0x01; 0xfa;        (* ADD (% rdx) (% rdi) *)
  0x48; 0x83; 0xd8; 0x00;  (* SBB (% rax) (Imm8 (word 0)) *)
  0xc3                     (* RET *)
];;

let word_recip_tmc = define_trimmed "word_recip_tmc" word_recip_mc;;

let WORD_RECIP_EXEC = X86_MK_CORE_EXEC_RULE word_recip_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_NEG_MUL_MNEG_LEMMA = prove
 (`!a b:int64.
        word_neg(word_mul a b) = iword(&0 - ival a * ival b)`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_MADD_LEMMA = prove
 (`!a b:int64.
        word_mul a b = word(0 + val a * val b)`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_MUL_MADD_LEMMA = prove
 (`!a b c:int64.
        word_add a (word_mul b c) = word(val a + val b * val c)`,
  CONV_TAC WORD_RULE);;

let WORD_RECIP_CORRECT = prove
 (`!a pc.
    ensures x86
      (\s. bytes_loaded s (word pc) (BUTLAST word_recip_tmc) /\
           read RIP s = word pc /\
           C_ARGUMENTS [a] s)
      (\s. read RIP s = word(pc + 0xc9) /\
           (bit 63 a
            ==> &2 pow 64 + &(val(C_RETURN s)) < &2 pow 128 / &(val a) /\
                &2 pow 128 / &(val a) <= &2 pow 64 + &(val(C_RETURN s)) + &1))
      (MAYCHANGE [RIP; RAX; RCX; RDX; RSI] ,,
       MAYCHANGE SOME_FLAGS)`,
  X_GEN_TAC `a:int64` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN

  (*** Globablize the top-bit-set assumption ***)

  ASM_CASES_TAC `bit 63 (a:int64)` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0";
    X86_ACCSIM_TAC WORD_RECIP_EXEC (1--54) (1--54)] THEN

  (*** Handle the special case a = 2^63 explicitly ***)

  ASM_CASES_TAC `a:int64 = word(2 EXP 63)` THENL
   [UNDISCH_THEN `a:int64 = word(2 EXP 63)` SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    X86_STEPS_TAC WORD_RECIP_EXEC (1--54) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Establish initial range of the input ***)

  SUBGOAL_THEN
   `(&2:real) pow 63 + &1 <= &(val(a:int64)) /\
    &(val(a:int64)):real <= &2 pow 64 - &1`
  STRIP_ASSUME_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN MP_TAC(ISPEC `a:int64` MSB_VAL) THEN
    MP_TAC(SPEC `a:int64` VAL_BOUND_64) THEN
    REWRITE_TAC[DIMINDEX_64; REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM VAL_EQ]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Initial switch to a shorter b, initial approximation x = z0 ***)

  X86_STEPS_TAC WORD_RECIP_EXEC (1--3) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t3:int64`; `e3:real`] THEN
  STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [4] THEN
  MP_TAC(ISPECL [`49`; `t3:int64`] WORD_SUB_MASK_WORD) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM BOUNDER_TAC[];
    DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SUB) THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t4:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [5] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
  ASM_REWRITE_TAC[VAL_WORD_1] THEN
  ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
  SUBGOAL_THEN
   `&2 pow 47 + &1 <= &(val(b:int64)) /\ &(val(b:int64)) <= &2 pow 48`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN
    POP_ASSUM(SUBST1_TAC o SYM) THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [6] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z0:int64`; `e6:real`] THEN
  ASM_REWRITE_TAC[REAL_ARITH
   `&562949953421311 - x = &2 pow 49 - (x + &1)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM)) THEN

  SUBGOAL_THEN
   `&2 pow 15 <= &(val(z0:int64)) /\
    &(val(z0:int64)) <= &2 pow 16 + &2 pow 15 - &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN
    POP_ASSUM(SUBST1_TAC o SYM) THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&2 pow 64 - &2 pow 62 - &2 pow 48  <= &(val(b:int64)) * &(val(z0:int64)) /\
    &(val(b:int64)) * &(val(z0:int64)) <= &2 pow 64`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
     (PAT_CONV `\z:real. l <= b * z /\ b * z <= u`) [SYM th]) THEN
    REWRITE_TAC[REAL_ARITH
     `b * ((&2 pow 49 - b) / &2 pow 32 - e) =
      &2 pow 64 - (&2 pow 48 - b) pow 2 / &2 pow 32 - b * e`] THEN
    ASM PURE_BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Computation of initial error d0 ***)

  X86_STEPS_TAC WORD_RECIP_EXEC (7--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_MUL_MNEG_LEMMA]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MNEG) THEN
  ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
  W(fun (asl,w) ->
      FIRST_ASSUM (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Accumulation of the polynomial giving z1 ***)

  X86_STEPS_TAC WORD_RECIP_EXEC (10--11) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t11:int64`; `e11:real`] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [12] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t12:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [13] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t13:int64`; `e13:real`] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [14] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD o
    GEN_REWRITE_RULE RAND_CONV [WORD_ADD_SYM]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t14:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [15] THEN
  MP_TAC(ISPECL [`t12:int64`; `word 1073741824:int64`] WORD_ADD_OR) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WORD_AND_EQ_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[SET_RULE `DISJOINT s {a} <=> ~(a IN s)`] THEN
    REWRITE_TAC[IN_BITS_OF_WORD; BIT_VAL] THEN
    MATCH_MP_TAC(MESON[ODD; DIV_LT] `a < n ==> ~ODD(a DIV n)`) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
    DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `t15:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [16] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_MUL_SYM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t16:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [17] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t17:int64`; `e17:real`] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC (18--19) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t19:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [20] THEN
  FIRST_X_ASSUM(ASSUME_TAC o
   GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [WORD_MUL_SYM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_MUL_MADD_LEMMA]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MADD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t20:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [21] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z1:int64`; `e21:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (STRIP_ASSUME_TAC o GSYM)) THEN

  (*** Accuracy of z1 then bounds on z1 and tidying up ***)

  SUBGOAL_THEN
   `&2 pow 64 - (&2 pow 54 + &2 pow 50) <= &(val(b:int64)) * &(val(z1:int64)) /\
    &(val(b:int64)) * &(val(z1:int64)) <= &2 pow 64`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH
     `b * ((a * z + z * c) / &2 pow 30 - e:real) =
      (b * z) * (a + c) / &2 pow 30 - b * e`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
      ASM BOUNDER_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(x * x + x') * (x * x + a):real =
        a * x' + a * x * x + x' * x * x + x * x * x * x`] THEN
    REWRITE_TAC[REAL_ARITH
     `bz * (&2 pow 30 + x / &2 pow 30 - e) / &2 pow 30 - be <= u <=>
      bz * (&2 pow 60 + x) <= &2 pow 60 * (u + be + bz * e / &2 pow 30)`] THEN
    REWRITE_TAC[REAL_ARITH
     `(x - d) * (y - e):real = x * y - (d * y + e * (x - d)) /\
      (x - d) + (y - e):real = (x + y) - (d + e) /\
      &c * (x - y) = (&c * x - &c * y)`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `bz * (&2 pow 60 + x) <= &2 pow 124 /\ &0 <= u /\ &0 <= bz * y
      ==> bz * (&2 pow 60 + x - y) <= &2 pow 60 * (&2 pow 64 + u)`) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
      ASM BOUNDER_TAC[];
      ASM BOUNDER_TAC[];
      SUBGOAL_THEN
       `&(val(t11:int64)) <= &2 pow 15 /\ &(val(t13:int64)) <= &2 pow 30`
      STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
      MAP_EVERY (C UNDISCH_THEN (SUBST_ALL_TAC o SYM))
       [`&(val(t11:int64)) = &(val(d0:int64)) / &2 pow 49 - e11`;
        `&(val(t13:int64)) = &(val(d0:int64)) / &2 pow 34 - e13`] THEN
      ASM BOUNDER_TAC[]];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&2 pow 15 <= &(val(z1:int64)) /\ &(val(z1:int64)) <= &130945`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THENL
     [ALL_TAC; ASM BOUNDER_TAC[]] THEN
    REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
     `&(val x) = a ==> a = &(val x)`))) THEN
    ASM BOUNDER_TAC[];
    DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

  (*** First Newton step ***)

  X86_STEPS_TAC WORD_RECIP_EXEC (22--24) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_MUL_MNEG_LEMMA]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MNEG) THEN
  ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
  W(fun (asl,w) ->
      FIRST_ASSUM (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [25] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t25:int64`; `e25:real`] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [26] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t26:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [27] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t27:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [28] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t28:int64`; `e28:real`] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [29] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [REAL_ARITH `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
  DISCH_THEN(X_CHOOSE_THEN `z2:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN

  SUBGOAL_THEN
   `&2 pow 80 - &5 / &4 * &2 pow 60 <= &(val(b:int64)) * &(val(z2:int64)) /\
    &(val(b:int64)) * &(val(z2:int64)) <= &2 pow 80`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `b * (z * d - e):real = (b * z) * d - b * e`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
    CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `(&2 pow 64 - d) * (&2 pow 16 + (d / &2 pow 24 - e) / &2 pow 24) =
      (&2 pow 128 - d pow 2) / &2 pow 48 -
      (&2 pow 64 - d) * e / &2 pow 24`] THEN
    CONV_TAC(funpow 3 LAND_CONV REAL_POLY_CONV) THEN
    ASM PURE_BOUNDER_TAC[];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&2 pow 31 <= &(val(z2:int64)) /\ &(val(z2:int64)) <= &2 pow 33 - &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SHARPEN_INEQ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
       `&(val x) = a ==> a = &(val x)`))) THEN
      ASM BOUNDER_TAC[];
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(b:int64))` THEN
      CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN ASM PURE_BOUNDER_TAC[]];
    DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

  (*** Second Newton step ***)

  X86_STEPS_TAC WORD_RECIP_EXEC (30--32) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_NEG_MUL_MNEG_LEMMA]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_IWORD) THEN
  DISCH_THEN(MP_TAC o SPEC
   `&2 pow 80 - &(val(b:int64)) * &(val(z2:int64)):int`) THEN
  REWRITE_TAC[int_le; int_lt; int_sub_th; int_mul_th;
                int_pow_th; int_of_num_th] THEN
  ANTS_TAC THENL
   [REPEAT(CONJ_TAC THENL [ASM PURE_BOUNDER_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC(INTEGER_RULE
     `e divides n /\ (b == b') (mod e) /\ (z == z') (mod e)
      ==> (&0 - b * z:int == n - b' * z') (mod e)`) THEN
    REWRITE_TAC[REWRITE_RULE[DIMINDEX_64]
     (INST_TYPE [`:64`,`:N`]IVAL_VAL_CONG)] THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
  W(fun (asl,w) ->
      FIRST_ASSUM (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [33] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t33:int64`; `e33:real`] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [34] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t34:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [35] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t35:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [36] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t36:int64`; `e36:real`] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [37] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
  ASM_REWRITE_TAC[REAL_ARITH
   `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(b:int64))` THEN
    CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `b * (z * d - e):real = (b * z) * d - b * e`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 80 - b * z = d ==> b * z:real = &2 pow 80 - d`)) THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN
    ASM BOUNDER_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [REAL_ARITH `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
  DISCH_THEN(X_CHOOSE_THEN `z3:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN

  SUBGOAL_THEN
   `&2 pow 111 - &201 / &128 * &2 pow 71
    <= &(val(b:int64)) * &(val(z3:int64)) /\
    &(val(b:int64)) * &(val(z3:int64)) <= &2 pow 111`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `b * (z * d - e):real = (b * z) * d - b * e`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 80 - b * z = d ==> b * z:real = &2 pow 80 - d`)) THEN
    CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `(&2 pow 80 - d) * (&2 pow 31 + (d / &2 pow 32 - e) / &2 pow 17) =
      (&2 pow 160 - d pow 2) / &2 pow 49 -
      (&2 pow 80 - d) * e / &2 pow 17`] THEN
    CONV_TAC(funpow 3 LAND_CONV REAL_POLY_CONV) THEN
    ASM PURE_BOUNDER_TAC[];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&2 pow 62 <= &(val(z3:int64)) /\ &(val(z3:int64)) <= &2 pow 64 - &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
    SHARPEN_INEQ_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
     `&(val x) = a ==> a = &(val x)`))) THEN
    ASM BOUNDER_TAC[];
    DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

  (*** Transfer accuracy to original input a, throw away facts about b ***)

  SUBGOAL_THEN
   `&2 pow 127 - &2 pow 88 + &1 <= &(val(a:int64)) * &(val(z3:int64)) /\
    &(val(a:int64)) * &(val(z3:int64)) <= &2 pow 127`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `a / &2 pow 16 - e + &1 = b ==> a = &2 pow 16 * (b + e - &1)`)) THEN
   REWRITE_TAC[REAL_ARITH `(c * (b + x)) * z:real = c * (b * z + x * z)`] THEN
   CONJ_TAC THEN ASM PURE_BOUNDER_TAC[];
   REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `b:int64` o concl)))] THEN

  (*** Observe this, which implies in particular the result is not exact ***)

  SUBGOAL_THEN `!w p. ~(val(a:int64) * w = 2 EXP p)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] PRIME_POWER_MULT)) THEN
    REWRITE_TAC[PRIME_2] THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 EXP 63 < val(a:int64) /\ val a < 2 EXP 64` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
      ASM_REWRITE_TAC[LT_EXP] THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** The full-sized Newton step ***)

  X86_ACCSTEPS_TAC WORD_RECIP_EXEC [39] (38--40) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC (41--42) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t42:int64`; `e42:real`] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [43] THEN
  REABBREV_TAC `bf = read RAX s43` THEN

  SUBGOAL_THEN
   `?e. &0 <= e /\ e <= &1 /\
        &(val(bf:int64)):real =
        (&2 pow 127 - &(val(a:int64)) * &(val(z3:int64))) / &2 pow 60 - e`
  (X_CHOOSE_THEN `e32:real` STRIP_ASSUME_TAC) THENL
   [MP_TAC(SPEC `&2 pow 127 - &(val(a:int64)) * &(val(z3:int64)):real`
          INTEGER_POS) THEN
    ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `d3:num`) THEN
    SUBGOAL_THEN `&d3:real <= &2 pow 88 - &1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      ASM BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `d3 < 2 EXP 88` ASSUME_TAC THENL
     [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= d3` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; REAL_SUB_0] THEN
      DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM int_of_num_th] THEN
    SUBGOAL_THEN `&(val(bf:int64)):int = &((d3 - 1) DIV 2 EXP 60)`
    SUBST1_TAC THENL
     [EXPAND_TAC "bf" THEN
      SIMP_TAC[GSYM WORD_SUBWORD_NOT; GSYM WORD_JOIN_NOT;
               DIMINDEX_64; DIMINDEX_128; ARITH] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; DIMINDEX_128;
               ARITH_LE; ARITH_LT] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM;
                  GSYM INT_OF_NUM_DIV; INT_VAL_WORD_NOT; DIMINDEX_64] THEN
      REWRITE_TAC[INT_ARITH
        `e * (e - &1 - h) + e - &1 - l:int = e * e - &1 - (e * h + l)`] THEN
      SIMP_TAC[INT_DIV_REM; INT_POS; INT_POW_LE; GSYM INT_POW_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      FIRST_ASSUM(MP_TAC o check (is_eq o concl)) THEN
      REWRITE_TAC[IMP_IMP; REAL_EQ_SUB_RADD] THEN
      GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [REAL_OF_NUM_CLAUSES] THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
       [GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_EQ_SUB_RADD] THEN DISCH_THEN(fun th ->
        REWRITE_TAC[th; INT_ARITH
        `&2 pow 128 - &1 - x:int = (&2 pow 127 - &1) + &2 pow 127 - x`]) THEN
      SUBGOAL_THEN `(&2 pow 127 - &1 + &d3) rem &2 pow 124 = &(d3 - 1)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN MATCH_MP_TAC INT_REM_UNIQ THEN
        EXISTS_TAC `&8:int` THEN CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[INT_SUB_LE; INT_LT_SUB_RADD] THEN
        REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_ABS_NUM] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
        REWRITE_TAC[INT_OF_NUM_DIV; INT_OF_NUM_CLAUSES] THEN ARITH_TAC];
      ASM_REWRITE_TAC[int_of_num_th]] THEN
    EXISTS_TAC `&((d3 - 1) MOD 2 EXP 60 + 1):real / &2 pow 60` THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
     [SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LE_1] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [44] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_MUL_SYM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL_MADD_LEMMA]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM PURE_BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t44:int64` STRIP_ASSUME_TAC) THEN

  X86_STEPS_TAC WORD_RECIP_EXEC (45--46) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t46:int64`; `e46:real`] THEN STRIP_TAC THEN

  X86_STEPS_TAC WORD_RECIP_EXEC [47] THEN

  (*** Analysis of provisional result w before the final truncation ***)

  ABBREV_TAC `w = 2 * val(z3:int64) + val(t46:int64)` THEN
  SUBGOAL_THEN
   `&2 pow 128 - &2 pow 62 <= &(val(a:int64)) * &w + &(val a) /\
    &(val(a:int64)) * &w <= &2 pow 128`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `d3 = &2 pow 127 - &(val(a:int64)) * &(val(z3:int64))` THEN
    SUBGOAL_THEN `&0 <= d3 /\ d3:real <= &2 pow 88 - &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "d3" THEN ASM PURE_BOUNDER_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "w" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ASM_REWRITE_TAC[REAL_ARITH
     `a * (&2 * z + ((z / &2 pow 33 - d) * c) / &2 pow 33 - f):real =
      (a * z) * (&2 + c / &2 pow 66) - d * c * a / &2 pow 33 - a * f`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 127 - a * z = d ==> a * z:real = &2 pow 127 - d`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= a * (&1 - e) /\ l <= b - c
        ==> l:real <= b - c - a * e + a`) THEN
      CONJ_TAC THENL [ASM PURE_BOUNDER_TAC[]; ASM BOUNDER_TAC[]];
      REWRITE_TAC[REAL_ARITH
       `(&2 pow 127 - d) * (&2 + (d / &2 pow 60 - e) / &2 pow 66) =
        (&2 pow 254 - d pow 2) / &2 pow 126 -
        (&2 pow 127 - d) * e / &2 pow 66`] THEN
      SUBST1_TAC(SYM(ASSUME `&(val(bf:int64)) = d3 / &2 pow 60 - e32`)) THEN
      ASM PURE_BOUNDER_TAC[]];
    ALL_TAC] THEN

  (*** Now the computed result with implicit 1 bit ***)

  ABBREV_TAC `z:int64 = word_add (word_shl z3 1) t46` THEN
  SUBGOAL_THEN `&w:real = (&2 pow 64) + &(val(z:int64))` SUBST_ALL_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL] THEN
    REWRITE_TAC[DIMINDEX_64; EXP_1] THEN CONV_TAC MOD_DOWN_CONV THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `2 EXP 64 <= w /\ w < 2 * 2 EXP 64` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT; ARITH_RULE `a <= b <=> a < b + 1`];
      SIMP_TAC[GSYM NOT_LE; MOD_CASES; GSYM REAL_OF_NUM_SUB] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(a:int64))` THEN
     CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC])
    THENL
     [REWRITE_TAC[REAL_ARITH `a * (w + &1):real = a * w + a`] THEN
      TRANS_TAC REAL_LTE_TRANS `&2 pow 128 - &2 pow 62`;
      TRANS_TAC REAL_LET_TRANS `&2 pow 128`] THEN
    ASM_REWRITE_TAC[] THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** In this non-trivial case the increment does not wrap ***)

  X86_STEPS_TAC WORD_RECIP_EXEC (48--50) THEN
  REABBREV_TAC `z' = read RCX s50` THEN
  SUBGOAL_THEN `&(val(z':int64)):real = &(val(z:int64)) + &1` ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN
    SUBGOAL_THEN `val(z:int64) + 1 < 2 EXP 64` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES];
      SIMP_TAC[GSYM NOT_LT; BITVAL_CLAUSES; ADD_CLAUSES] THEN
      SIMP_TAC[WORD_SUB_0; VAL_WORD_ADD_CASES; DIMINDEX_64; VAL_WORD_1] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES]] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(&2 pow 63 + &1) * (&2 pow 64 + z) <= &2 pow 128
      ==> z + &1 < &2 pow 64`) THEN
    TRANS_TAC REAL_LE_TRANS
     `&(val(a:int64)) * (&2 pow 64 + &(val(z:int64)))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final bounds check and selection ***)

  X86_STEPS_TAC WORD_RECIP_EXEC (51--54) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ;
               REAL_ARITH `&2 pow 63 + &1 <= a ==> &0 < a`] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; ADD_CLAUSES] THEN
  SIMP_TAC[DIMINDEX_64; DIMINDEX_128; MOD_LT; VAL_BOUND_64; LT_MULT2;
           ARITH_RULE `a < 2 EXP 64 * 2 EXP 64
                       ==> a DIV 2 EXP 64 < 2 EXP 64 /\ a < 2 EXP 128`;
           ARITH_RULE `2 EXP 64 <= h DIV 2 EXP 64 + a <=>
                       2 EXP 128 <= 2 EXP 64 * a + h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; LT_LE] THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bitval] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0] THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1; DIMINDEX_64] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REAL_ARITH_TAC);;

let WORD_RECIP_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
    ensures x86
      (\s. bytes_loaded s (word pc) word_recip_tmc /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a] s)
      (\s. read RIP s = returnaddress /\
           (bit 63 a
            ==> &2 pow 64 + &(val(C_RETURN s)) < &2 pow 128 / &(val a) /\
                &2 pow 128 / &(val a) <= &2 pow 64 + &(val(C_RETURN s)) + &1))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_recip_tmc WORD_RECIP_CORRECT);;

let WORD_RECIP_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
    ensures x86
      (\s. bytes_loaded s (word pc) word_recip_mc /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a] s)
      (\s. read RIP s = returnaddress /\
           (bit 63 a
            ==> &2 pow 64 + &(val(C_RETURN s)) < &2 pow 128 / &(val a) /\
                &2 pow 128 / &(val a) <= &2 pow 64 + &(val(C_RETURN s)) + &1))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_RECIP_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let word_recip_windows_mc = define_from_elf
   "word_recip_windows_mc" "x86/generic/word_recip.obj";;

let word_recip_windows_tmc = define_trimmed "word_recip_windows_tmc" word_recip_windows_mc;;

let WORD_RECIP_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_recip_windows_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) word_recip_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s)
             (\s. read RIP s = returnaddress /\
                  (bit 63 a
                   ==> &2 pow 64 + &(val(WINDOWS_C_RETURN s)) <
                       &2 pow 128 / &(val a) /\
                       &2 pow 128 / &(val a) <=
                       &2 pow 64 + &(val(WINDOWS_C_RETURN s)) + &1))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC word_recip_windows_tmc word_recip_tmc
    WORD_RECIP_CORRECT);;

let WORD_RECIP_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_recip_windows_mc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) word_recip_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s)
             (\s. read RIP s = returnaddress /\
                  (bit 63 a
                   ==> &2 pow 64 + &(val(WINDOWS_C_RETURN s)) <
                       &2 pow 128 / &(val a) /\
                       &2 pow 128 / &(val a) <=
                       &2 pow 64 + &(val(WINDOWS_C_RETURN s)) + &1))
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_RECIP_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

