(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiply-add mod n_25519, basepoint order for curve25519/edwards25519.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_madd_n25519.o";;
 ****)

let bignum_madd_n25519_mc =
  define_assert_from_elf "bignum_madd_n25519_mc" "arm/curve25519/bignum_madd_n25519.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xaa0003f3;       (* arm_MOV X19 X0 *)
  0xa9401020;       (* arm_LDP X0 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9401845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&0))) *)
  0x9ba57c08;       (* arm_UMULL X8 W0 W5 *)
  0xd360fc11;       (* arm_LSR X17 X0 32 *)
  0x9ba57e27;       (* arm_UMULL X7 W17 W5 *)
  0xd360fcb0;       (* arm_LSR X16 X5 32 *)
  0x9bb17e09;       (* arm_UMULL X9 W16 W17 *)
  0x9bb07c10;       (* arm_UMULL X16 W0 W16 *)
  0xab078108;       (* arm_ADDS X8 X8 (Shiftedreg X7 LSL 32) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9a070129;       (* arm_ADC X9 X9 X7 *)
  0xab108108;       (* arm_ADDS X8 X8 (Shiftedreg X16 LSL 32) *)
  0xd360fe10;       (* arm_LSR X16 X16 32 *)
  0x9a100129;       (* arm_ADC X9 X9 X16 *)
  0x9b067c8a;       (* arm_MUL X10 X4 X6 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xeb000084;       (* arm_SUBS X4 X4 X0 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xab09014a;       (* arm_ADDS X10 X10 X9 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xeb0600a0;       (* arm_SUBS X0 X5 X6 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0xda902210;       (* arm_CINV X16 X16 Condition_CC *)
  0x9b007c87;       (* arm_MUL X7 X4 X0 *)
  0x9bc07c80;       (* arm_UMULH X0 X4 X0 *)
  0xab0a0109;       (* arm_ADDS X9 X8 X10 *)
  0xba0b014a;       (* arm_ADCS X10 X10 X11 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca1000e7;       (* arm_EOR X7 X7 X16 *)
  0xba0900e9;       (* arm_ADCS X9 X7 X9 *)
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba0a000a;       (* arm_ADCS X10 X0 X10 *)
  0x9a10016b;       (* arm_ADC X11 X11 X16 *)
  0xa9411020;       (* arm_LDP X0 X4 X1 (Immediate_Offset (iword (&16))) *)
  0xa9411845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&16))) *)
  0x9ba57c0c;       (* arm_UMULL X12 W0 W5 *)
  0xd360fc11;       (* arm_LSR X17 X0 32 *)
  0x9ba57e27;       (* arm_UMULL X7 W17 W5 *)
  0xd360fcb0;       (* arm_LSR X16 X5 32 *)
  0x9bb17e0d;       (* arm_UMULL X13 W16 W17 *)
  0x9bb07c10;       (* arm_UMULL X16 W0 W16 *)
  0xab07818c;       (* arm_ADDS X12 X12 (Shiftedreg X7 LSL 32) *)
  0xd360fce7;       (* arm_LSR X7 X7 32 *)
  0x9a0701ad;       (* arm_ADC X13 X13 X7 *)
  0xab10818c;       (* arm_ADDS X12 X12 (Shiftedreg X16 LSL 32) *)
  0xd360fe10;       (* arm_LSR X16 X16 32 *)
  0x9a1001ad;       (* arm_ADC X13 X13 X16 *)
  0x9b067c8e;       (* arm_MUL X14 X4 X6 *)
  0x9bc67c8f;       (* arm_UMULH X15 X4 X6 *)
  0xeb000084;       (* arm_SUBS X4 X4 X0 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xab0d01ce;       (* arm_ADDS X14 X14 X13 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xeb0600a0;       (* arm_SUBS X0 X5 X6 *)
  0xda802400;       (* arm_CNEG X0 X0 Condition_CC *)
  0xda902210;       (* arm_CINV X16 X16 Condition_CC *)
  0x9b007c87;       (* arm_MUL X7 X4 X0 *)
  0x9bc07c80;       (* arm_UMULH X0 X4 X0 *)
  0xab0e018d;       (* arm_ADDS X13 X12 X14 *)
  0xba0f01ce;       (* arm_ADCS X14 X14 X15 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca1000e7;       (* arm_EOR X7 X7 X16 *)
  0xba0d00ed;       (* arm_ADCS X13 X7 X13 *)
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xba0e000e;       (* arm_ADCS X14 X0 X14 *)
  0x9a1001ef;       (* arm_ADC X15 X15 X16 *)
  0xa9411020;       (* arm_LDP X0 X4 X1 (Immediate_Offset (iword (&16))) *)
  0xa9404027;       (* arm_LDP X7 X16 X1 (Immediate_Offset (iword (&0))) *)
  0xeb070000;       (* arm_SUBS X0 X0 X7 *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xda9f23f0;       (* arm_CSETM X16 Condition_CC *)
  0xa9404447;       (* arm_LDP X7 X17 X2 (Immediate_Offset (iword (&0))) *)
  0xeb0500e5;       (* arm_SUBS X5 X7 X5 *)
  0xfa060226;       (* arm_SBCS X6 X17 X6 *)
  0xda9f23f1;       (* arm_CSETM X17 Condition_CC *)
  0xca100000;       (* arm_EOR X0 X0 X16 *)
  0xeb100000;       (* arm_SUBS X0 X0 X16 *)
  0xca100084;       (* arm_EOR X4 X4 X16 *)
  0xda100084;       (* arm_SBC X4 X4 X16 *)
  0xca1100a5;       (* arm_EOR X5 X5 X17 *)
  0xeb1100a5;       (* arm_SUBS X5 X5 X17 *)
  0xca1100c6;       (* arm_EOR X6 X6 X17 *)
  0xda1100c6;       (* arm_SBC X6 X6 X17 *)
  0xca100230;       (* arm_EOR X16 X17 X16 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0xba0b01ad;       (* arm_ADCS X13 X13 X11 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0x9b057c02;       (* arm_MUL X2 X0 X5 *)
  0x9bc57c11;       (* arm_UMULH X17 X0 X5 *)
  0x9b067c87;       (* arm_MUL X7 X4 X6 *)
  0x9bc67c81;       (* arm_UMULH X1 X4 X6 *)
  0xeb000084;       (* arm_SUBS X4 X4 X0 *)
  0xda842484;       (* arm_CNEG X4 X4 Condition_CC *)
  0xda9f23ea;       (* arm_CSETM X10 Condition_CC *)
  0xab1100e7;       (* arm_ADDS X7 X7 X17 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xeb0600a6;       (* arm_SUBS X6 X5 X6 *)
  0xda8624c6;       (* arm_CNEG X6 X6 Condition_CC *)
  0xda8a214a;       (* arm_CINV X10 X10 Condition_CC *)
  0x9b067c85;       (* arm_MUL X5 X4 X6 *)
  0x9bc67c86;       (* arm_UMULH X6 X4 X6 *)
  0xab070051;       (* arm_ADDS X17 X2 X7 *)
  0xba0100e7;       (* arm_ADCS X7 X7 X1 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xb100055f;       (* arm_CMN X10 (rvalue (word 1)) *)
  0xca0a00a5;       (* arm_EOR X5 X5 X10 *)
  0xba1100b1;       (* arm_ADCS X17 X5 X17 *)
  0xca0a00c6;       (* arm_EOR X6 X6 X10 *)
  0xba0700c7;       (* arm_ADCS X7 X6 X7 *)
  0x9a0a0021;       (* arm_ADC X1 X1 X10 *)
  0xab08018a;       (* arm_ADDS X10 X12 X8 *)
  0xba0901ab;       (* arm_ADCS X11 X13 X9 *)
  0xba0c01cc;       (* arm_ADCS X12 X14 X12 *)
  0xba0d01ed;       (* arm_ADCS X13 X15 X13 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xb100061f;       (* arm_CMN X16 (rvalue (word 1)) *)
  0xca100042;       (* arm_EOR X2 X2 X16 *)
  0xba0a004a;       (* arm_ADCS X10 X2 X10 *)
  0xca100231;       (* arm_EOR X17 X17 X16 *)
  0xba0b022b;       (* arm_ADCS X11 X17 X11 *)
  0xca1000e7;       (* arm_EOR X7 X7 X16 *)
  0xba0c00ec;       (* arm_ADCS X12 X7 X12 *)
  0xca100021;       (* arm_EOR X1 X1 X16 *)
  0xba0d002d;       (* arm_ADCS X13 X1 X13 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0x9a1001ef;       (* arm_ADC X15 X15 X16 *)
  0xa9400460;       (* arm_LDP X0 X1 X3 (Immediate_Offset (iword (&0))) *)
  0xab000108;       (* arm_ADDS X8 X8 X0 *)
  0xba010129;       (* arm_ADCS X9 X9 X1 *)
  0xa9410460;       (* arm_LDP X0 X1 X3 (Immediate_Offset (iword (&16))) *)
  0xba00014a;       (* arm_ADCS X10 X10 X0 *)
  0xba01016b;       (* arm_ADCS X11 X11 X1 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0xd29a7da3;       (* arm_MOV X3 (rvalue (word 54253)) *)
  0xf2ab9ea3;       (* arm_MOVK X3 (word 23797) 16 *)
  0xf2cc6343;       (* arm_MOVK X3 (word 25370) 32 *)
  0xf2eb0243;       (* arm_MOVK X3 (word 22546) 48 *)
  0xd2939ac4;       (* arm_MOV X4 (rvalue (word 40150)) *)
  0xf2b45ee4;       (* arm_MOVK X4 (word 41719) 16 *)
  0xf2df3bc4;       (* arm_MOVK X4 (word 63966) 32 *)
  0xf2e29bc4;       (* arm_MOVK X4 (word 5342) 48 *)
  0xd37cfde2;       (* arm_LSR X2 X15 60 *)
  0x9240edef;       (* arm_AND X15 X15 (rvalue (word 1152921504606846975)) *)
  0x9b027c65;       (* arm_MUL X5 X3 X2 *)
  0x9b027c86;       (* arm_MUL X6 X4 X2 *)
  0x9bc27c67;       (* arm_UMULH X7 X3 X2 *)
  0xab0700c6;       (* arm_ADDS X6 X6 X7 *)
  0x9bc27c87;       (* arm_UMULH X7 X4 X2 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xeb05018c;       (* arm_SUBS X12 X12 X5 *)
  0xfa0601ad;       (* arm_SBCS X13 X13 X6 *)
  0xfa0701ce;       (* arm_SBCS X14 X14 X7 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0x9a9f3065;       (* arm_CSEL X5 X3 XZR Condition_CC *)
  0x9a9f3086;       (* arm_CSEL X6 X4 XZR Condition_CC *)
  0xab05018c;       (* arm_ADDS X12 X12 X5 *)
  0x924400a7;       (* arm_AND X7 X5 (rvalue (word 1152921504606846976)) *)
  0xba0601ad;       (* arm_ADCS X13 X13 X6 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0x9a0701ef;       (* arm_ADC X15 X15 X7 *)
  0x93cef1e2;       (* arm_EXTR X2 X15 X14 60 *)
  0x9240edce;       (* arm_AND X14 X14 (rvalue (word 1152921504606846975)) *)
  0xcb4ff042;       (* arm_SUB X2 X2 (Shiftedreg X15 LSR 60) *)
  0x92440de5;       (* arm_AND X5 X15 (rvalue (word 17293822569102704640)) *)
  0x8b0501ce;       (* arm_ADD X14 X14 X5 *)
  0x9b027c65;       (* arm_MUL X5 X3 X2 *)
  0x9b027c86;       (* arm_MUL X6 X4 X2 *)
  0x9bc27c67;       (* arm_UMULH X7 X3 X2 *)
  0xab0700c6;       (* arm_ADDS X6 X6 X7 *)
  0x9bc27c87;       (* arm_UMULH X7 X4 X2 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xeb05016b;       (* arm_SUBS X11 X11 X5 *)
  0xfa06018c;       (* arm_SBCS X12 X12 X6 *)
  0xfa0701ad;       (* arm_SBCS X13 X13 X7 *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0x9a9f3065;       (* arm_CSEL X5 X3 XZR Condition_CC *)
  0x9a9f3086;       (* arm_CSEL X6 X4 XZR Condition_CC *)
  0xab05016b;       (* arm_ADDS X11 X11 X5 *)
  0x924400a7;       (* arm_AND X7 X5 (rvalue (word 1152921504606846976)) *)
  0xba06018c;       (* arm_ADCS X12 X12 X6 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0x9a0701ce;       (* arm_ADC X14 X14 X7 *)
  0x93cdf1c2;       (* arm_EXTR X2 X14 X13 60 *)
  0x9240edad;       (* arm_AND X13 X13 (rvalue (word 1152921504606846975)) *)
  0xcb4ef042;       (* arm_SUB X2 X2 (Shiftedreg X14 LSR 60) *)
  0x92440dc5;       (* arm_AND X5 X14 (rvalue (word 17293822569102704640)) *)
  0x8b0501ad;       (* arm_ADD X13 X13 X5 *)
  0x9b027c65;       (* arm_MUL X5 X3 X2 *)
  0x9b027c86;       (* arm_MUL X6 X4 X2 *)
  0x9bc27c67;       (* arm_UMULH X7 X3 X2 *)
  0xab0700c6;       (* arm_ADDS X6 X6 X7 *)
  0x9bc27c87;       (* arm_UMULH X7 X4 X2 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xeb05014a;       (* arm_SUBS X10 X10 X5 *)
  0xfa06016b;       (* arm_SBCS X11 X11 X6 *)
  0xfa07018c;       (* arm_SBCS X12 X12 X7 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0x9a9f3065;       (* arm_CSEL X5 X3 XZR Condition_CC *)
  0x9a9f3086;       (* arm_CSEL X6 X4 XZR Condition_CC *)
  0xab05014a;       (* arm_ADDS X10 X10 X5 *)
  0x924400a7;       (* arm_AND X7 X5 (rvalue (word 1152921504606846976)) *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0x9a0701ad;       (* arm_ADC X13 X13 X7 *)
  0x93ccf1a2;       (* arm_EXTR X2 X13 X12 60 *)
  0x9240ed8c;       (* arm_AND X12 X12 (rvalue (word 1152921504606846975)) *)
  0xcb4df042;       (* arm_SUB X2 X2 (Shiftedreg X13 LSR 60) *)
  0x92440da5;       (* arm_AND X5 X13 (rvalue (word 17293822569102704640)) *)
  0x8b05018c;       (* arm_ADD X12 X12 X5 *)
  0x9b027c65;       (* arm_MUL X5 X3 X2 *)
  0x9b027c86;       (* arm_MUL X6 X4 X2 *)
  0x9bc27c67;       (* arm_UMULH X7 X3 X2 *)
  0xab0700c6;       (* arm_ADDS X6 X6 X7 *)
  0x9bc27c87;       (* arm_UMULH X7 X4 X2 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xeb050129;       (* arm_SUBS X9 X9 X5 *)
  0xfa06014a;       (* arm_SBCS X10 X10 X6 *)
  0xfa07016b;       (* arm_SBCS X11 X11 X7 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0x9a9f3065;       (* arm_CSEL X5 X3 XZR Condition_CC *)
  0x9a9f3086;       (* arm_CSEL X6 X4 XZR Condition_CC *)
  0xab050129;       (* arm_ADDS X9 X9 X5 *)
  0x924400a7;       (* arm_AND X7 X5 (rvalue (word 1152921504606846976)) *)
  0xba06014a;       (* arm_ADCS X10 X10 X6 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0x9a07018c;       (* arm_ADC X12 X12 X7 *)
  0x93cbf182;       (* arm_EXTR X2 X12 X11 60 *)
  0x9240ed6b;       (* arm_AND X11 X11 (rvalue (word 1152921504606846975)) *)
  0xcb4cf042;       (* arm_SUB X2 X2 (Shiftedreg X12 LSR 60) *)
  0x92440d85;       (* arm_AND X5 X12 (rvalue (word 17293822569102704640)) *)
  0x8b05016b;       (* arm_ADD X11 X11 X5 *)
  0x9b027c65;       (* arm_MUL X5 X3 X2 *)
  0x9b027c86;       (* arm_MUL X6 X4 X2 *)
  0x9bc27c67;       (* arm_UMULH X7 X3 X2 *)
  0xab0700c6;       (* arm_ADDS X6 X6 X7 *)
  0x9bc27c87;       (* arm_UMULH X7 X4 X2 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xeb050108;       (* arm_SUBS X8 X8 X5 *)
  0xfa060129;       (* arm_SBCS X9 X9 X6 *)
  0xfa07014a;       (* arm_SBCS X10 X10 X7 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0x9a9f3065;       (* arm_CSEL X5 X3 XZR Condition_CC *)
  0x9a9f3086;       (* arm_CSEL X6 X4 XZR Condition_CC *)
  0xab050108;       (* arm_ADDS X8 X8 X5 *)
  0x924400a7;       (* arm_AND X7 X5 (rvalue (word 1152921504606846976)) *)
  0xba060129;       (* arm_ADCS X9 X9 X6 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a07016b;       (* arm_ADC X11 X11 X7 *)
  0xa9002668;       (* arm_STP X8 X9 X19 (Immediate_Offset (iword (&0))) *)
  0xa9012e6a;       (* arm_STP X10 X11 X19 (Immediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MADD_N25519_EXEC = ARM_MK_EXEC_RULE bignum_madd_n25519_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_25519 = define `n_25519 = 7237005577332262213973186563042994240857116359379907606001950938285454250989`;;

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

let BIGNUM_MADD_N25519_CORRECT = time prove
 (`!z x m y n c r pc.
      nonoverlapping (word pc,0x41c) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_madd_n25519_mc /\
                read PC s = word(pc + 0x4) /\
                C_ARGUMENTS [z; x; y; c] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n /\
                bignum_from_memory (c,4) s = r)
           (\s. read PC s = word (pc + 0x414) /\
                bignum_from_memory (z,4) s = (m * n + r) MOD n_25519)
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14; X15; X16; X17; X19] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `m:num`; `y:int64`; `n:num`;
    `c:int64`; `r:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Initial Karatsuba multiplication block ***)
  (*** Use an offset state to segue into copy of bignum_mul_p25519 ***)

  ENSURES_SEQUENCE_TAC `pc + 0x218`
   `\s. read X19 s = z /\
        read X3 s = c /\
        bignum_from_memory(c,4) s = r /\
        m < 2 EXP 256 /\ n < 2 EXP 256 /\
        bignum_of_wordlist
         [read X8 s; read X9 s; read X10 s; read X11 s;
          read X12 s; read X13 s; read X14 s; read X15 s] = m * n` THEN
  CONJ_TAC THENL
   [MAP_EVERY (BIGNUM_TERMRANGE_TAC `4`) [`m:num`; `n:num`] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REPLICATE_TAC 2 (POP_ASSUM(fun th -> REWRITE_TAC[th])) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "ss" THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read(memory :> bytes(x,8 * 4)) ss` THEN
    BIGNUM_LDIGITIZE_TAC "y_" `read(memory :> bytes(y,8 * 4)) ss` THEN
    ARM_STEPS_TAC BIGNUM_MADD_N25519_EXEC [0] THEN
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC [9;11;12;14] (1--14) THEN
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
      RULE_ASSUM_TAC(REWRITE_RULE
       [GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      SPEC_TAC(`sum_s12:int64`,`mullo_s3:int64`) THEN
      SPEC_TAC(`sum_s14:int64`,`mulhi_s3:int64`) THEN
      SPEC_TAC(`s14:armstate`,`s4:armstate`) THEN REPEAT STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
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
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC [34;36;37;39] (26--39) THEN
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
      RULE_ASSUM_TAC(REWRITE_RULE
        [GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV]) THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      SPEC_TAC(`sum_s37:int64`,`mullo_s28:int64`) THEN
      SPEC_TAC(`sum_s39:int64`,`mulhi_s28:int64`) THEN
      SPEC_TAC(`s39:armstate`,`s29:armstate`) THEN REPEAT STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
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
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
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
       [CONJ_TAC THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
        EXISTS_TAC `128` THEN
        REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_POP_ASSUM_LIST
         (MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        ALL_TAC] THEN
      BINOP_TAC THEN REWRITE_TAC[bitval] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_ARITH
       `x - y:real = --(&1) pow 1 * z <=> y - x = z`] THEN
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
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [WORD_XOR_MASKS]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC (69--72) (69--72) THEN
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
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
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
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
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
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[bignum_of_wordlist] THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** Additional tail adding the constant term ***)

  ENSURES_SEQUENCE_TAC `pc + 0x240`
   `\s. read X19 s = z /\
        bignum_of_wordlist
         [read X8 s; read X9 s; read X10 s; read X11 s;
          read X12 s; read X13 s; read X14 s; read X15 s] = m * n + r` THEN
  CONJ_TAC THENL
   [BIGNUM_TERMRANGE_TAC `4` `r:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "c_" `read(memory :> bytes(c,8 * 4)) s0` THEN
    MAP_EVERY ABBREV_TAC
     [`d0 = read X8 s0`; `d1 = read X9 s0`; `d2 = read X10 s0`;
      `d3 = read X11 s0`; `d4 = read X12 s0`; `d5 = read X13 s0`;
      `d6 = read X14 s0`; `d7 = read X15 s0`] THEN
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC [2;3;5;6;7;8;9;10] (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 512` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
    EXPAND_TAC "r" THEN SUBST1_TAC(SYM(ASSUME
     `bignum_of_wordlist [d0; d1; d2; d3; d4; d5; d6; d7] = m * n`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    SPEC_TAC(`m * n + r:num`,`mnr:num`) THEN GEN_TAC THEN
    GHOST_INTRO_TAC `d0:int64` `read X8` THEN
    GHOST_INTRO_TAC `d1:int64` `read X9` THEN
    GHOST_INTRO_TAC `d2:int64` `read X10` THEN
    GHOST_INTRO_TAC `d3:int64` `read X11` THEN
    GHOST_INTRO_TAC `d4:int64` `read X12` THEN
    GHOST_INTRO_TAC `d5:int64` `read X13` THEN
    GHOST_INTRO_TAC `d6:int64` `read X14` THEN
    GHOST_INTRO_TAC `d7:int64` `read X15` THEN
    GLOBALIZE_PRECONDITION_TAC] THEN

  (*** Toplevel breakdown ****)

  MAP_EVERY ABBREV_TAC
   [`r0 = bignum_of_wordlist [d4; d5; d6; d7] MOD n_25519`;
    `r1 = (val(d3:int64) + 2 EXP 64 * r0) MOD n_25519`;
    `r2 = (val(d2:int64) + 2 EXP 64 * r1) MOD n_25519`;
    `r3 = (val(d1:int64) + 2 EXP 64 * r2) MOD n_25519`;
    `r4 = (val(d0:int64) + 2 EXP 64 * r3) MOD n_25519`] THEN
  SUBGOAL_THEN
   `r0 < n_25519 /\ r1 < n_25519 /\ r2 < n_25519 /\
    r3 < n_25519 /\ r4 < n_25519`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r0"; "r1"; "r2"; "r3"; "r4"] THEN
    REWRITE_TAC[MOD_LT_EQ; n_25519; ARITH_EQ];
    ALL_TAC] THEN

  SUBGOAL_THEN `mnr MOD n_25519 = r4:num` SUBST1_TAC THEN
  UNDISCH_TAC `bignum_of_wordlist [d0; d1; d2; d3; d4; d5; d6; d7] = mnr` THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXPAND_TAC ["r4"; "r3"; "r2"; "r1"; "r0"] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN CONV_TAC MOD_DOWN_CONV THEN
    REFL_TAC;
    DISCH_THEN(K ALL_TAC)] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  (*** Zeroth reduction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
   [11;12;14;16;17;18;19;20;23;25;26;27] (1--27) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s23;sum_s25;sum_s26;sum_s27] = r0`
  ASSUME_TAC THENL
   [ABBREV_TAC `m = bignum_of_wordlist [d4; d5; d6; d7]` THEN
    SUBGOAL_THEN `m < 2 EXP 256` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN BOUNDER_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `q:int64 = word_ushr d7 60` THEN
    SUBGOAL_THEN
     `&(val(word_and (d7:int64) (word 1152921504606846975))):real =
      &(val d7) - &2 pow 60 * &(val(q:int64))`
    SUBST_ALL_TAC THENL [EXPAND_TAC "q" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    EXPAND_TAC "r0" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    EXISTS_TAC `256` THEN
    EXISTS_TAC
     `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
           &n_25519:real` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `m < val(q:int64) * n_25519 <=> carry_s20`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        EXPAND_TAC "m" THEN REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        EXPAND_TAC "m" THEN
        REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        BOOL_CASES_TAC `carry_s20:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      SUBGOAL_THEN `val(q:int64) = m DIV 2 EXP 252` SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["m"; "q"] THEN
        CONV_TAC(RAND_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[VAL_WORD_USHR];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
      UNDISCH_TAC `m < 2 EXP 256` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
      COND_CASES_TAC THEN ASM_INT_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_THEN `bignum_of_wordlist [d4; d5; d6; d7] MOD n_25519 = r0`
     (K ALL_TAC)] THEN

  (*** First reduction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
   [33;34;36;38;39;40;41;42;45;47;48;49] (28--49) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s45;sum_s47;sum_s48;sum_s49] = r1`
  ASSUME_TAC THENL
   [ABBREV_TAC `m = val(d3:int64) + 2 EXP 64 * r0` THEN
    SUBGOAL_THEN `m < 2 EXP 64 * n_25519` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN UNDISCH_TAC `r0 < n_25519` THEN
      MP_TAC(ISPEC `d3:int64` VAL_BOUND_64) THEN ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
     `q:int64 =
      word_sub
       (word_subword((word_join:int64->int64->int128) sum_s27 sum_s26) (60,64))
       (word_ushr sum_s27 60)` THEN
    SUBGOAL_THEN
     `MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64) /\
      val q + m DIV 2 EXP 252 DIV 2 EXP 64 = m DIV 2 EXP 252`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN
      SUBGOAL_THEN
       `word_ushr (sum_s27:int64) 60 = word(m DIV 2 EXP 252 DIV 2 EXP 64) /\
        word_subword
          ((word_join:int64->int64->int128) sum_s27 sum_s26) (60,64):int64 =
        word(m DIV 2 EXP 252)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        MAP_EVERY EXPAND_TAC ["m"; "r0"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
        REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
        REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `m DIV 2 EXP 252 <= 2 EXP 64` MP_TAC THENL
       [UNDISCH_TAC `m < 2 EXP 64 * n_25519` THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
       [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(val(word_add (word_and sum_s26 (word 1152921504606846975))
              (word_and sum_s27 (word 17293822569102704640)):int64)):real =
      (&2 pow 64 * &(val(sum_s27:int64)) + &(val(sum_s26:int64))) -
      &2 pow 60 * &(val(q:int64))`
    SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_ADD_OR o
        rand o rand o lhand o snd) THEN
      ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN SUBST1_TAC] THEN
      POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `q + x:real = y ==> q = y - x`)) THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      MAP_EVERY EXPAND_TAC ["m"; "r0"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE
       `(a + 2 EXP 64 * q) DIV 2 EXP 60 =
        (2 EXP 60 * (16 * q) + a) DIV 2 EXP 60`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      CONV_TAC WORD_BLAST;
      POP_ASSUM(K ALL_TAC)] THEN
    EXPAND_TAC "r1" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN EXISTS_TAC `256` THEN
    EXISTS_TAC
     `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
           &n_25519:real` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `m < val(q:int64) * n_25519 <=> carry_s42`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        MAP_EVERY EXPAND_TAC ["m"; "r0"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["m"; "r0"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        BOOL_CASES_TAC `carry_s42:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
      MAP_EVERY UNDISCH_TAC
       [`MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64)`;
        `m < 2 EXP 64 * n_25519`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
      COND_CASES_TAC THEN ASM_INT_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_THEN `(val(d3:int64) + 2 EXP 64 * r0) MOD n_25519 = r1`
     (K ALL_TAC)] THEN

  (*** Second reduction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
   [55;56;58;60;61;62;63;64;67;69;70;71] (50--71) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s67;sum_s69;sum_s70;sum_s71] = r2`
  ASSUME_TAC THENL
   [ABBREV_TAC `m = val(d2:int64) + 2 EXP 64 * r1` THEN
    SUBGOAL_THEN `m < 2 EXP 64 * n_25519` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN UNDISCH_TAC `r1 < n_25519` THEN
      MP_TAC(ISPEC `d2:int64` VAL_BOUND_64) THEN ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
     `q:int64 =
      word_sub
       (word_subword((word_join:int64->int64->int128) sum_s49 sum_s48) (60,64))
       (word_ushr sum_s49 60)` THEN
    SUBGOAL_THEN
     `MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64) /\
      val q + m DIV 2 EXP 252 DIV 2 EXP 64 = m DIV 2 EXP 252`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN
      SUBGOAL_THEN
       `word_ushr (sum_s49:int64) 60 = word(m DIV 2 EXP 252 DIV 2 EXP 64) /\
        word_subword
          ((word_join:int64->int64->int128) sum_s49 sum_s48) (60,64):int64 =
        word(m DIV 2 EXP 252)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        MAP_EVERY EXPAND_TAC ["m"; "r1"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
        REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
        REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `m DIV 2 EXP 252 <= 2 EXP 64` MP_TAC THENL
       [UNDISCH_TAC `m < 2 EXP 64 * n_25519` THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
       [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(val(word_add (word_and sum_s48 (word 1152921504606846975))
              (word_and sum_s49 (word 17293822569102704640)):int64)):real =
      (&2 pow 64 * &(val(sum_s49:int64)) + &(val(sum_s48:int64))) -
      &2 pow 60 * &(val(q:int64))`
    SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_ADD_OR o
        rand o rand o lhand o snd) THEN
      ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN SUBST1_TAC] THEN
      POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `q + x:real = y ==> q = y - x`)) THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      MAP_EVERY EXPAND_TAC ["m"; "r1"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE
       `(a + 2 EXP 64 * q) DIV 2 EXP 60 =
        (2 EXP 60 * (16 * q) + a) DIV 2 EXP 60`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      CONV_TAC WORD_BLAST;
      POP_ASSUM(K ALL_TAC)] THEN
    EXPAND_TAC "r2" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN EXISTS_TAC `256` THEN
    EXISTS_TAC
     `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
           &n_25519:real` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `m < val(q:int64) * n_25519 <=> carry_s64`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        MAP_EVERY EXPAND_TAC ["m"; "r1"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["m"; "r1"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        BOOL_CASES_TAC `carry_s64:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
      MAP_EVERY UNDISCH_TAC
       [`MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64)`;
        `m < 2 EXP 64 * n_25519`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
      COND_CASES_TAC THEN ASM_INT_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_THEN `(val(d2:int64) + 2 EXP 64 * r1) MOD n_25519 = r2`
     (K ALL_TAC)] THEN

  (*** Third reduction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
   [77;78;80;82;83;84;85;86;89;91;92;93] (72--93) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist [sum_s89;sum_s91;sum_s92;sum_s93] = r3`
  ASSUME_TAC THENL
   [ABBREV_TAC `m = val(d1:int64) + 2 EXP 64 * r2` THEN
    SUBGOAL_THEN `m < 2 EXP 64 * n_25519` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN UNDISCH_TAC `r2 < n_25519` THEN
      MP_TAC(ISPEC `d1:int64` VAL_BOUND_64) THEN ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
     `q:int64 =
      word_sub
       (word_subword((word_join:int64->int64->int128) sum_s71 sum_s70) (60,64))
       (word_ushr sum_s71 60)` THEN
    SUBGOAL_THEN
     `MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64) /\
      val q + m DIV 2 EXP 252 DIV 2 EXP 64 = m DIV 2 EXP 252`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN
      SUBGOAL_THEN
       `word_ushr (sum_s71:int64) 60 = word(m DIV 2 EXP 252 DIV 2 EXP 64) /\
        word_subword
          ((word_join:int64->int64->int128) sum_s71 sum_s70) (60,64):int64 =
        word(m DIV 2 EXP 252)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        MAP_EVERY EXPAND_TAC ["m"; "r2"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
        REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
        REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
        REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `m DIV 2 EXP 252 <= 2 EXP 64` MP_TAC THENL
       [UNDISCH_TAC `m < 2 EXP 64 * n_25519` THEN
        REWRITE_TAC[n_25519] THEN ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
       [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(val(word_add (word_and sum_s70 (word 1152921504606846975))
              (word_and sum_s71 (word 17293822569102704640)):int64)):real =
      (&2 pow 64 * &(val(sum_s71:int64)) + &(val(sum_s70:int64))) -
      &2 pow 60 * &(val(q:int64))`
    SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_ADD_OR o
        rand o rand o lhand o snd) THEN
      ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN SUBST1_TAC] THEN
      POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `q + x:real = y ==> q = y - x`)) THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      MAP_EVERY EXPAND_TAC ["m"; "r2"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE
       `(a + 2 EXP 64 * q) DIV 2 EXP 60 =
        (2 EXP 60 * (16 * q) + a) DIV 2 EXP 60`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      CONV_TAC WORD_BLAST;
      POP_ASSUM(K ALL_TAC)] THEN
    EXPAND_TAC "r3" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN EXISTS_TAC `256` THEN
    EXISTS_TAC
     `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
           &n_25519:real` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `m < val(q:int64) * n_25519 <=> carry_s86`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
        MAP_EVERY EXPAND_TAC ["m"; "r2"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
        MAP_EVERY EXPAND_TAC ["m"; "r2"] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
        REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
        ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
        BOOL_CASES_TAC `carry_s86:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
          filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
      REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
      MAP_EVERY UNDISCH_TAC
       [`MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64)`;
        `m < 2 EXP 64 * n_25519`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
      COND_CASES_TAC THEN ASM_INT_ARITH_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    UNDISCH_THEN `(val(d1:int64) + 2 EXP 64 * r2) MOD n_25519 = r3`
     (K ALL_TAC)] THEN

  (*** Fourth and final reduction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_EXEC
   [99;100;102;104;105;106;107;108;111;113;114;115] (94--117) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s117" THEN
  ABBREV_TAC `m = val(d0:int64) + 2 EXP 64 * r3` THEN
  SUBGOAL_THEN `m < 2 EXP 64 * n_25519` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN UNDISCH_TAC `r3 < n_25519` THEN
    MP_TAC(ISPEC `d0:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `q:int64 =
    word_sub
     (word_subword((word_join:int64->int64->int128) sum_s93 sum_s92) (60,64))
     (word_ushr sum_s93 60)` THEN
  SUBGOAL_THEN
   `MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64) /\
    val q + m DIV 2 EXP 252 DIV 2 EXP 64 = m DIV 2 EXP 252`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    SUBGOAL_THEN
     `word_ushr (sum_s93:int64) 60 = word(m DIV 2 EXP 252 DIV 2 EXP 64) /\
      word_subword
        ((word_join:int64->int64->int128) sum_s93 sum_s92) (60,64):int64 =
      word(m DIV 2 EXP 252)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      MAP_EVERY EXPAND_TAC ["m"; "r3"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
      REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
      REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `m DIV 2 EXP 252 <= 2 EXP 64` MP_TAC THENL
     [UNDISCH_TAC `m < 2 EXP 64 * n_25519` THEN
      REWRITE_TAC[n_25519] THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
     [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_add (word_and sum_s92 (word 1152921504606846975))
            (word_and sum_s93 (word 17293822569102704640)):int64)):real =
    (&2 pow 64 * &(val(sum_s93:int64)) + &(val(sum_s92:int64))) -
    &2 pow 60 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_ADD_OR o
      rand o rand o lhand o snd) THEN
    ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_THEN SUBST1_TAC] THEN
    POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `q + x:real = y ==> q = y - x`)) THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    MAP_EVERY EXPAND_TAC ["m"; "r3"] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE
     `(a + 2 EXP 64 * q) DIV 2 EXP 60 =
      (2 EXP 60 * (16 * q) + a) DIV 2 EXP 60`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC WORD_BLAST;
    POP_ASSUM(K ALL_TAC)] THEN
  EXPAND_TAC "r4" THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN EXISTS_TAC `256` THEN
  EXISTS_TAC
   `&m - (&(val(q:int64)) - &(bitval(m < val q * n_25519))) *
         &n_25519:real` THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[n_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `m < val(q:int64) * n_25519 <=> carry_s108`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      MAP_EVERY EXPAND_TAC ["m"; "r3"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      REWRITE_TAC[n_25519; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      MAP_EVERY EXPAND_TAC ["m"; "r3"] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 bignum_of_wordlist)] THEN
      REWRITE_TAC[n_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      BOOL_CASES_TAC `carry_s108:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
    MAP_EVERY UNDISCH_TAC
     [`MIN (m DIV 2 EXP 252) (2 EXP 64 - 1) = val(q:int64)`;
      `m < 2 EXP 64 * n_25519`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[n_25519; bitval] THEN
    COND_CASES_TAC THEN ASM_INT_ARITH_TAC]);;

let BIGNUM_MADD_N25519_SUBROUTINE_CORRECT = time prove
 (`!z x m y n c r pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,0x41c); (x,8 * 4); (y,8 * 4); (c,8 * 4); (z,8 * 4)] /\
      nonoverlapping (word pc,0x41c) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_madd_n25519_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x; y; c] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n /\
                bignum_from_memory (c,4) s = r)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = (m * n + r) MOD n_25519)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,4);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  ARM_ADD_RETURN_STACK_TAC BIGNUM_MADD_N25519_EXEC BIGNUM_MADD_N25519_CORRECT
   `[X19;X20]` 16);;
