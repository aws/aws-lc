(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication modulo p_25519, the field characteristic for curve25519.   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_mul_p25519.o";;
 ****)

let bignum_mul_p25519_mc = define_assert_from_elf "bignum_mul_p25519_mc" "arm/curve25519/bignum_mul_p25519.o"
[
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9401845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&0))) *)
  0x9ba57c67;       (* arm_UMULL X7 W3 W5 *)
  0xd360fc71;       (* arm_LSR X17 X3 32 *)
  0x9ba57e2f;       (* arm_UMULL X15 W17 W5 *)
  0xd360fcb0;       (* arm_LSR X16 X5 32 *)
  0x9bb17e08;       (* arm_UMULL X8 W16 W17 *)
  0x9bb07c70;       (* arm_UMULL X16 W3 W16 *)
  0xab0f80e7;       (* arm_ADDS X7 X7 (Shiftedreg X15 LSL 32) *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x9a0f0108;       (* arm_ADC X8 X8 X15 *)
  0xab1080e7;       (* arm_ADDS X7 X7 (Shiftedreg X16 LSL 32) *)
  0xd360fe10;       (* arm_LSR X16 X16 32 *)
  0x9a100108;       (* arm_ADC X8 X8 X16 *)
  0x9b067c89;       (* arm_MUL X9 X4 X6 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xeb0600a3;       (* arm_SUBS X3 X5 X6 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda902210;       (* arm_CINV X16 X16 Condition_CC *)
  0x9b037c8f;       (* arm_MUL X15 X4 X3 *)
  0x9bc37c83;       (* arm_UMULH X3 X4 X3 *)
  0xab0900e8;       (* arm_ADDS X8 X7 X9 *)
  0xba0a0129;       (* arm_ADCS X9 X9 X10 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0801e8;       (* arm_ADCS X8 X15 X8 *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xba090069;       (* arm_ADCS X9 X3 X9 *)
  0x9a10014a;       (* arm_ADC X10 X10 X16 *)
  0xa9411023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&16))) *)
  0xa9411845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&16))) *)
  0x9ba57c6b;       (* arm_UMULL X11 W3 W5 *)
  0xd360fc71;       (* arm_LSR X17 X3 32 *)
  0x9ba57e2f;       (* arm_UMULL X15 W17 W5 *)
  0xd360fcb0;       (* arm_LSR X16 X5 32 *)
  0x9bb17e0c;       (* arm_UMULL X12 W16 W17 *)
  0x9bb07c70;       (* arm_UMULL X16 W3 W16 *)
  0xab0f816b;       (* arm_ADDS X11 X11 (Shiftedreg X15 LSL 32) *)
  0xd360fdef;       (* arm_LSR X15 X15 32 *)
  0x9a0f018c;       (* arm_ADC X12 X12 X15 *)
  0xab10816b;       (* arm_ADDS X11 X11 (Shiftedreg X16 LSL 32) *)
  0xd360fe10;       (* arm_LSR X16 X16 32 *)
  0x9a10018c;       (* arm_ADC X12 X12 X16 *)
  0x9b067c8d;       (* arm_MUL X13 X4 X6 *)
  0x9bc67c8e;       (* arm_UMULH X14 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xab0c01ad;       (* arm_ADDS X13 X13 X12 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xeb0600a3;       (* arm_SUBS X3 X5 X6 *)
  0xda832463;       (* arm_CNEG X3 X3 Condition_CC *)
  0xda902210;       (* arm_CINV X16 X16 Condition_CC *)
  0x9b037c8f;       (* arm_MUL X15 X4 X3 *)
  0x9bc37c83;       (* arm_UMULH X3 X4 X3 *)
  0xab0d016c;       (* arm_ADDS X12 X11 X13 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0c01ec;       (* arm_ADCS X12 X15 X12 *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xba0d006d;       (* arm_ADCS X13 X3 X13 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xa9411023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&16))) *)
  0xa940402f;       (* arm_LDP X15 X16 X1 (Immediate_Offset (iword (&0))) *)
  0xeb0f0063;       (* arm_SUBS X3 X3 X15 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa940444f;       (* arm_LDP X15 X17 X2 (Immediate_Offset (iword (&0))) *)
  0xeb0501e5;       (* arm_SUBS X5 X15 X5 *)
  0xfa060226;       (* arm_SBCS X6 X17 X6 *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xca100063;       (* arm_EOR X3 X3 X16 *)
  0xeb100063;       (* arm_SUBS X3 X3 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca1100a5;       (* arm_EOR X5 X5 X17 *)
  0xeb1100a5;       (* arm_SUBS X5 X5 X17 *)
  0xca1100c6;       (* arm_EOR X6 X6 X17 *)
  0xda1100c6;       (* arm_SBC X6 X6 X17 *)
  0xca100230;       (* arm_EOR X16 X17 X16 *)
  0xab09016b;       (* arm_ADDS X11 X11 X9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b057c62;       (* arm_MUL X2 X3 X5 *)
  0x9bc57c71;       (* arm_UMULH X17 X3 X5 *)
  0x9b067c8f;       (* arm_MUL X15 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb030084;       (* arm_SUBS X4 X4 X3 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda892129;       (* arm_CINV X9 X9 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab0f0051;       (* arm_ADDS X17 X2 X15 *)
  0xba0101ef;       (* arm_ADCS X15 X15 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100053f;       (* arm_CMN X9 (rvalue (word 1)) *)
  0xca0900a5;       (* arm_EOR X5 X5 X9 *)
  0xba1100b1;       (* arm_ADCS X17 X5 X17 *)
  0xca0900c6;       (* arm_EOR X6 X6 X9 *)
  0xba0f00cf;       (* arm_ADCS X15 X6 X15 *)
  0x9a090021;       (* arm_ADC X1 X1 X9 *)
  0xab070169;       (* arm_ADDS X9 X11 X7 *)
  0xba08018a;       (* arm_ADCS X10 X12 X8 *)
  0xba0b01ab;       (* arm_ADCS X11 X13 X11 *)
  0xba0c01cc;       (* arm_ADCS X12 X14 X12 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca100042;       (* arm_EOR X2 X2 X16 *)
  0xba090049;       (* arm_ADCS X9 X2 X9 *)
  0xca100231;       (* arm_EOR X17 X17 X16 *)
  0xba0a022a;       (* arm_ADCS X10 X17 X10 *)
  0xca1001ef;       (* arm_EOR X15 X15 X16 *)
  0xba0b01eb;       (* arm_ADCS X11 X15 X11 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0c002c;       (* arm_ADCS X12 X1 X12 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1001ce;       (* arm_ADC X14 X14 X16 *)
  0xd28004c3;       (* arm_MOV X3 (rvalue (word 38)) *)
  0x9ba37d64;       (* arm_UMULL X4 W11 W3 *)
  0x8b274084;       (* arm_ADD X4 X4 (Extendedreg W7 UXTW) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0xd360fd6b;       (* arm_LSR X11 X11 32 *)
  0x9ba31d6b;       (* arm_UMADDL X11 W11 W3 X7 *)
  0xaa0403e7;       (* arm_MOV X7 X4 *)
  0x9ba37d84;       (* arm_UMULL X4 W12 W3 *)
  0x8b284084;       (* arm_ADD X4 X4 (Extendedreg W8 UXTW) *)
  0xd360fd08;       (* arm_LSR X8 X8 32 *)
  0xd360fd8c;       (* arm_LSR X12 X12 32 *)
  0x9ba3218c;       (* arm_UMADDL X12 W12 W3 X8 *)
  0xaa0403e8;       (* arm_MOV X8 X4 *)
  0x9ba37da4;       (* arm_UMULL X4 W13 W3 *)
  0x8b294084;       (* arm_ADD X4 X4 (Extendedreg W9 UXTW) *)
  0xd360fd29;       (* arm_LSR X9 X9 32 *)
  0xd360fdad;       (* arm_LSR X13 X13 32 *)
  0x9ba325ad;       (* arm_UMADDL X13 W13 W3 X9 *)
  0xaa0403e9;       (* arm_MOV X9 X4 *)
  0x9ba37dc4;       (* arm_UMULL X4 W14 W3 *)
  0x8b2a4084;       (* arm_ADD X4 X4 (Extendedreg W10 UXTW) *)
  0xd360fd4a;       (* arm_LSR X10 X10 32 *)
  0xd360fdce;       (* arm_LSR X14 X14 32 *)
  0x9ba329ce;       (* arm_UMADDL X14 W14 W3 X10 *)
  0xaa0403ea;       (* arm_MOV X10 X4 *)
  0xd35ffdd1;       (* arm_LSR X17 X14 31 *)
  0xd2800265;       (* arm_MOV X5 (rvalue (word 19)) *)
  0x9bb114a5;       (* arm_UMADDL X5 W5 W17 X5 *)
  0x8b0500e7;       (* arm_ADD X7 X7 X5 *)
  0xab0b80e7;       (* arm_ADDS X7 X7 (Shiftedreg X11 LSL 32) *)
  0x93cb8183;       (* arm_EXTR X3 X12 X11 32 *)
  0xba030108;       (* arm_ADCS X8 X8 X3 *)
  0x93cc81a3;       (* arm_EXTR X3 X13 X12 32 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0x93cd81c3;       (* arm_EXTR X3 X14 X13 32 *)
  0xd3410225;       (* arm_LSL X5 X17 63 *)
  0xca05014a;       (* arm_EOR X10 X10 X5 *)
  0x9a03014a;       (* arm_ADC X10 X10 X3 *)
  0xd2800263;       (* arm_MOV X3 (rvalue (word 19)) *)
  0xf241015f;       (* arm_TST X10 (rvalue (word 9223372036854775808)) *)
  0x9a9f5063;       (* arm_CSEL X3 X3 XZR Condition_PL *)
  0xeb0300e7;       (* arm_SUBS X7 X7 X3 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0x9240f94a;       (* arm_AND X10 X10 (rvalue (word 9223372036854775807)) *)
  0xa9002007;       (* arm_STP X7 X8 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MUL_P25519_EXEC = ARM_MK_EXEC_RULE bignum_mul_p25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_25519 = new_definition `p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949`;;

let lemma0 = prove
 (`!x0 x1:int64.
        &(val(if val x0 <= val x1 then word_sub x1 x0
         else word_neg(word_sub x1 x0))):real = abs(&(val x1) - &(val x0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[WORD_NEG_SUB; REAL_ARITH
   `abs(x - y):real = if y <= x then x - y else y - x`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_OF_NUM_CLAUSES; NOT_LE]) THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES; LT_IMP_LE; REAL_OF_NUM_SUB]);;

let lemma1 = prove
 (`!(x0:num) x1 (y0:num) y1.
       (if y0 <= y1
        then if x1 <= x0 then word 0 else word 18446744073709551615
        else word_not
         (if x1 <= x0 then word 0 else word 18446744073709551615)):int64 =
   word_neg(word(bitval(y0 <= y1 <=> x0 < x1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let lemma2 = prove
 (`!p x0 x1 y0 y1:real.
    (x0 + p * x1) * (y0 + p * y1) =
    x0 * y0 + p pow 2 * x1 * y1 +
    p * (x0 * y0 + x1 * y1 +
         --(&1) pow bitval(y1 <= y0 <=> x1 < x0) *
         abs(x1 - x0) * abs(y0 - y1))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`y1:real <= y0`; `x1:real < x0`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ASM_REAL_ARITH_TAC);;

let VAL_WORD_MADDL_0 = prove
 (`!x y. val(word(0 + val(x:int32) * val(y:int32)):int64) = val x * val y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; VAL_WORD_EQ_EQ] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC[GSYM DIMINDEX_32; VAL_BOUND]);;

let DIVMOD_32_32 = prove
 (`!n. (2 EXP 32 * n) MOD 2 EXP 64 = 2 EXP 32 * n MOD 2 EXP 32`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let VAL_WORD_SPLIT32 = prove
 (`!x. 2 EXP 32 * val(word_zx(word_ushr x 32):int32) + val(word_zx x:int32) =
       val(x:int64)`,
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM MOD_MULT_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND_64]);;

let DIVMOD_63_64 = prove
 (`!n. (2 EXP 63 * n) MOD 2 EXP 64 = 2 EXP 63 * n MOD 2`,
  REWRITE_TAC[GSYM MOD_MULT2] THEN ARITH_TAC);;

let p25519redlemma32 = prove
 (`!h l. h < 2 EXP 256 /\ l < 2 EXP 256
         ==> let q = (38 * h DIV 2 EXP 224 + l DIV 2 EXP 224) DIV 2 EXP 31 in
             q <= 77 /\
             q < 2 EXP 64 /\
             (q + 1) * p_25519 <= (38 * h + l) + p_25519 /\
             38 * h + l < (q + 1) * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let endp25519redlemma = prove
 (`(&z == &2 pow 255 + x) (mod (&2 pow 256)) /\
   --(&p_25519) <= x /\ x < &p_25519 /\ z < 2 EXP 256
   ==> x rem &p_25519 =
       if z < 2 EXP 255 then &z - &19  else &z - &2 pow 255`,
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&z:int < &2 pow 255 <=> x:int < &0` SUBST1_TAC THENL
   [ALL_TAC;
   COND_CASES_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THENL
    [EXISTS_TAC `--(&1):int`; EXISTS_TAC `&0:int`]] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_IMP_EQ)) THEN
  REWRITE_TAC[p_25519] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p_25519]) THEN ASM_INT_ARITH_TAC);;

let KARATSUBA12_TAC =
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[lemma2; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
  ACCUMULATOR_POP_ASSUM_LIST(fun thl ->
    MP_TAC(end_itlist CONJ(rev thl)) THEN
    REWRITE_TAC[WORD_XOR_MASK] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; GSYM NOT_LE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC(filter(is_ratconst o rand o concl) (DECARRY_RULE thl)) THEN
    REAL_INTEGER_TAC);;

let BIGNUM_MUL_P25519_CORRECT = time prove
 (`!z x y m n pc.
        nonoverlapping (word pc,0x2d4) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p25519_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,4) s = m /\
                  bignum_from_memory (y,4) s = n)
             (\s. read PC s = word (pc + 0x2d0) /\
                  bignum_from_memory (z,4) s = (m * n) MOD p_25519)
         (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                     X13; X14; X15; X16; X17] ,,
           MAYCHANGE [memory :> bytes(z,8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  BIGNUM_LDIGITIZE_TAC "y_" `read (memory :> bytes (y,8 * 4)) s0` THEN

  (*** Retrofitted insertion for the 32-bit fiddling (1 of 2) ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC [9;11;12;14] (1--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; VAL_WORD_USHR; VAL_WORD_SHL;
    DIVMOD_32_32; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s14:int64)) + &(val(sum_s12:int64)):real =
    &(val(x_0:int64)) * &(val(y_0:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_0:int64`; `y_0:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    SPEC_TAC(`sum_s12:int64`,`mullo_s3:int64`) THEN
    SPEC_TAC(`sum_s14:int64`,`mulhi_s3:int64`) THEN
    SPEC_TAC(`s14:armstate`,`s4:armstate`) THEN REPEAT STRIP_TAC] THEN

  (*** First nested block multiplying the lower halves ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC
   [5;10;11;15;17;18;19;22;24;25] (5--25) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lemma0; lemma1]) THEN

  MAP_EVERY ABBREV_TAC
   [`q0 = bignum_of_wordlist[mullo_s3;sum_s22]`;
    `q1 = bignum_of_wordlist[sum_s24;sum_s25]`] THEN
  SUBGOAL_THEN
   `2 EXP 128 * q1 + q0 =
    bignum_of_wordlist [x_0;x_1] * bignum_of_wordlist[y_0;y_1]`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q0"; "q1"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    KARATSUBA12_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Retrofitted insertion for the 32-bit fiddling (2 of 2) ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC [34;36;37;39] (26--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VAL_WORD_MADDL_0; VAL_WORD_USHR; VAL_WORD_SHL;
    DIVMOD_32_32; DIMINDEX_64]) THEN
  SUBGOAL_THEN
   `&2 pow 64 * &(val(sum_s39:int64)) + &(val(sum_s37:int64)):real =
    &(val(x_2:int64)) * &(val(y_2:int64))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    MAP_EVERY (SUBST_ALL_TAC o SYM o C SPEC VAL_WORD_SPLIT32)
     [`x_2:int64`; `y_2:int64`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    SPEC_TAC(`sum_s37:int64`,`mullo_s28:int64`) THEN
    SPEC_TAC(`sum_s39:int64`,`mulhi_s28:int64`) THEN
    SPEC_TAC(`s39:armstate`,`s29:armstate`) THEN REPEAT STRIP_TAC] THEN

  (*** Second nested block multiplying the upper halves ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC
   [30;35;36;40;42;43;44;47;49;50] (30--50) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lemma0; lemma1]) THEN

  ABBREV_TAC
   `q23 = bignum_of_wordlist[mullo_s28;sum_s47; sum_s49;sum_s50]` THEN
  SUBGOAL_THEN
   `q23 = bignum_of_wordlist [x_2;x_3] * bignum_of_wordlist[y_2;y_3]`
  ASSUME_TAC THENL
   [EXPAND_TAC "q23" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    KARATSUBA12_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** The sign-magnitude difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC
    [53;54; 57;58; 61;63; 65;67] (51--68) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN

  MAP_EVERY ABBREV_TAC
  [`sgn <=> ~(carry_s58 <=> carry_s54)`;
   `xd = bignum_of_wordlist[sum_s61;sum_s63]`;
   `yd = bignum_of_wordlist[sum_s65;sum_s67]`] THEN
  SUBGOAL_THEN
   `(&(bignum_of_wordlist[x_2;x_3]) -
     &(bignum_of_wordlist[x_0;x_1])) *
    (&(bignum_of_wordlist[y_0;y_1]) -
     &(bignum_of_wordlist[y_2;y_3])):real =
    --(&1) pow bitval sgn * &xd * &yd`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `(--(&1) pow bitval carry_s54 * &xd) *
      (--(&1) pow bitval carry_s58 * &yd):real` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "sgn" THEN REWRITE_TAC[BITVAL_NOT; BITVAL_IFF] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     `(carry_s54 <=>
       bignum_of_wordlist[x_2;x_3] < bignum_of_wordlist[x_0;x_1]) /\
      (carry_s58 <=>
       bignum_of_wordlist[y_0;y_1] < bignum_of_wordlist[y_2;y_3])`
     (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `128` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    BINOP_TAC THEN REWRITE_TAC[bitval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `x - y:real = --(&1) pow 1 * z <=> y - x = z`] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`128`; `&0:real`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH
        `y:real <= x /\ (&0 <= x /\ x < e) /\ (&0 <= y /\ y < e)
         ==> &0 <= x - y /\ x - y < e`) THEN
       ASM_SIMP_TAC[REAL_OF_NUM_CLAUSES; LT_IMP_LE;
                    ARITH_RULE `~(a:num < b) ==> b <= a`] THEN
       REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
       CONJ_TAC THEN BOUNDER_TAC[];
       ALL_TAC] THEN
     MAP_EVERY EXPAND_TAC ["xd"; "yd"] THEN
     REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
     CONJ_TAC THENL [BOUNDER_TAC[]; REWRITE_TAC[INTEGER_CLOSED]]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_REWRITE_TAC[WORD_XOR_MASK] THEN
    REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Clean up the overall sign ***)

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_XOR_MASKS]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** The augmented H' = H + L_top ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC (69--72) (69--72) THEN
  MAP_EVERY ABBREV_TAC
   [`q2 = bignum_of_wordlist[sum_s69;sum_s70]`;
    `q3 = bignum_of_wordlist[sum_s71;sum_s72]`] THEN
  SUBGOAL_THEN
   `2 EXP 128 * q3 + q2 =
    bignum_of_wordlist [x_2;x_3] * bignum_of_wordlist[y_2;y_3] + q1`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q1"; "q2"; "q3"] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 256` THEN
    REPEAT(CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[]; ALL_TAC]) THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
      (LAND_CONV o LAND_CONV) [SYM th]) THEN
    MAP_EVERY EXPAND_TAC ["q23"] THEN
    REWRITE_TAC[REAL_CONGRUENCE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Third nested block multiplying the absolute differences ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC
   [73;75;80;81;85;87;88;89;92;94;95] (73--95) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lemma0; lemma1]) THEN
  SUBGOAL_THEN
   `&xd * &yd:real =
    &(bignum_of_wordlist[mullo_s73; sum_s92; sum_s94; sum_s95])`
  SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xd"; "yd"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    KARATSUBA12_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** The rest of the basic 4x4->8 multiply computation and its proof ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC
   [96;97;98;99;100;101;104;106;108;110;111;112] (96--112) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s22; sum_s104; sum_s106]`;
    `h = bignum_of_wordlist[sum_s108; sum_s110; sum_s111; sum_s112]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [DISCARD_STATE_TAC "s112" THEN MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    SUBGOAL_THEN
     `&m * &n:real =
      (&1 + &2 pow 128) * (&q0 + &2 pow 128 * &q2 + &2 pow 256 * &q3) +
      &2 pow 128 *
      (&(bignum_of_wordlist [x_2; x_3]) -
       &(bignum_of_wordlist [x_0; x_1])) *
      (&(bignum_of_wordlist [y_0; y_1]) -
       &(bignum_of_wordlist [y_2; y_3]))`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`2 EXP 128 * q1 + q0 =
         bignum_of_wordlist[x_0; x_1] * bignum_of_wordlist[y_0; y_1]`;
        `2 EXP 128 * q3 + q2 =
         bignum_of_wordlist[x_2; x_3] * bignum_of_wordlist[y_2; y_3] +
         q1`] THEN
      MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[]] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"; "q0"; "q2"; "q3"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[WORD_XOR_MASK] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_VAL_WORD_NOT; BITVAL_CLAUSES; DIMINDEX_64] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPECL [`h:num`; `l:num`] p25519redlemma32) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    LET_TAC THEN STRIP_TAC] THEN

  (*** The somewhat fiddly reduction with 32-bit operations etc. ***)

  ARM_STEPS_TAC BIGNUM_MUL_P25519_EXEC (113--137) THEN

  MAP_EVERY (fun t -> REABBREV_TAC t THEN POP_ASSUM MP_TAC)
   [`u0 = read X7 s137`;
    `u1 = read X8 s137`;
    `u2 = read X9 s137`;
    `u3 = read X10 s137`;
    `u4 = read X11 s137`;
    `u5 = read X12 s137`;
    `u6 = read X13 s137`;
    `u7 = read X14 s137`] THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [word_add; modular; ADD_CLAUSES; VAL_WORD; VAL_WORD_ZX_GEN;
    VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
   `n < 2 EXP 64 ==> n MOD 2 EXP 32 * 38 < 2 EXP 64`] THEN
  STRIP_TAC THEN
  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC [142;144;146;150] (138--150) THEN
  SUBGOAL_THEN `word_ushr u7 31:int64 = word q` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_USHR] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT] THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s106:int64) DIV 2 EXP 32 +
           val(sum_s112:int64) DIV 2 EXP 32 * 38):int64 = u7`)) THEN
    MAP_EVERY EXPAND_TAC ["q"; "l"; "h"] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_WORD; ARITH_RULE `a + b * 38 = 38 * b + a`] THEN
    MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[DIMINDEX_64] THEN
    REWRITE_TAC[GSYM VAL_WORD_USHR] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_add (u0:int64)
       (word(19 + 19 * val((word_zx:int64->int32)(word q)))))):real =
    &(val u0) + &19 * (&q + &1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD_ADD; VAL_WORD; VAL_WORD_ZX_GEN;
                DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC[ARITH_RULE `q <= 77 ==> q < 2 EXP MIN 64 32`; MOD_LT] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[ARITH_RULE `19 + 19 * q = 19 * (q + 1)`] THEN
    MATCH_MP_TAC MOD_LT THEN SUBST1_TAC(SYM(ASSUME
     `word(val(sum_s108:int64) MOD 2 EXP 32 * 38 +
           val(mullo_s3:int64) MOD 2 EXP 32):int64 = u0`)) THEN
    MATCH_MP_TAC(ARITH_RULE
     `w <= 2 EXP 63 /\ q <= 77 ==> w + 19 * (q + 1) < 2 EXP 64`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_LE; FIRST_ASSUM ACCEPT_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  REWRITE_TAC[REAL_VAL_WORD_XOR; WORD_AND_POW2_BITVAL;
              REWRITE_RULE[DIMINDEX_64; NUM_REDUCE_CONV `64 - 1`]
                (ISPEC `x:int64` WORD_SHL_LSB)] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; DIVMOD_63_64] THEN
  SIMP_TAC[MOD_LT; BITVAL_BOUND_ALT; GSYM REAL_OF_NUM_CLAUSES] THEN
  ASM_SIMP_TAC[GSYM VAL_MOD_2; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `r = bignum_of_wordlist[sum_s142; sum_s144; sum_s146; sum_s150]` THEN

  SUBGOAL_THEN
   `(&r:int == &2 pow 255 + &(38 * h + l) - (&q + &1) * &p_25519)
    (mod (&2 pow 256))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `38 * h + l =
      bignum_of_wordlist[u0;u1;u2;u3] +
      2 EXP 32 * bignum_of_wordlist[u4;u5;u6;u7]`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (can (term_match [] `word x = n`) o concl))) THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD; DIMINDEX_64] THEN
      SIMP_TAC[MOD_LT; VAL_BOUND_64; ARITH_RULE
        `m < 2 EXP 64 /\ n < 2 EXP 64
         ==> m DIV 2 EXP 32 + n DIV 2 EXP 32 * 38 < 2 EXP 64`;
        ARITH_RULE `m MOD 2 EXP 32 * 38 + n MOD 2 EXP 32 < 2 EXP 64`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `2 EXP 32 * bignum_of_wordlist [u4; u5; u6; u7] =
      bignum_of_wordlist
       [word_shl u4 32;
        word_subword ((word_join:int64->int64->int128) u5 u4) (32,64);
        word_subword ((word_join:int64->int64->int128) u6 u5) (32,64);
        word_subword ((word_join:int64->int64->int128) u7 u6) (32,64);
        word_ushr u7 32]`
    SUBST1_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    SIMP_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th;
                int_mul_th; int_pow_th] THEN
    EXPAND_TAC "r" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The final optional correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MUL_P25519_EXEC (154--157) (151--160) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`255`;
    `(if r < 2 EXP 255 then &r - &19 else &r - &2 pow 255):real`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s160" THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `r < 2 EXP 255 <=> r DIV 2 EXP 192 < 2 EXP 63`] THEN
    EXPAND_TAC "r" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
    ABBREV_TAC `bb <=> val(sum_s150:int64) < 2 EXP 63` THEN
    SUBGOAL_THEN
     `ival(word_and sum_s150 (word 9223372036854775808):int64) < &0 <=> ~bb`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM MSB_IVAL; BIT_WORD_AND] THEN
      REWRITE_TAC[MSB_VAL] THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      EXPAND_TAC "bb" THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        endp25519redlemma)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INT_ARITH `--p:int <= x - y <=> y <= x + p`] THEN
      REWRITE_TAC[INT_ARITH `x - y:int < p <=> x < y + p`] THEN
      ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
      EXPAND_TAC "r" THEN BOUNDER_TAC[];
      REWRITE_TAC[INT_ARITH `x - q * p:int = --q * p + x`] THEN
      REWRITE_TAC[INT_REM_MUL_ADD] THEN
      REWRITE_TAC[int_eq; int_of_num_th; INT_OF_NUM_REM] THEN
      DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[int_of_num_th; int_sub_th; int_pow_th]]]);;

let BIGNUM_MUL_P25519_SUBROUTINE_CORRECT = time prove
 (`!z x y m n pc returnaddress.
        nonoverlapping (word pc,0x2d4) (z,8 * 4)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mul_p25519_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory(x,4) s = m /\
                  bignum_from_memory(y,4) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory(z,4) s = (m * n) MOD p_25519)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
   BIGNUM_MUL_P25519_EXEC BIGNUM_MUL_P25519_CORRECT);;
