(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery squaring modulo p_521.                                         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p521/bignum_montsqr_p521_alt.o";;
 ****)

let bignum_montsqr_p521_alt_mc = define_assert_from_elf "bignum_montsqr_p521_alt_mc" "arm/p521/bignum_montsqr_p521_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf77fb;       (* arm_STP X27 X29 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x9b037c4c;       (* arm_MUL X12 X2 X3 *)
  0x9bc37c4d;       (* arm_UMULH X13 X2 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b047c4a;       (* arm_MUL X10 X2 X4 *)
  0x9bc47c4e;       (* arm_UMULH X14 X2 X4 *)
  0xab0a01ad;       (* arm_ADDS X13 X13 X10 *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x9b057c4a;       (* arm_MUL X10 X2 X5 *)
  0x9bc57c4f;       (* arm_UMULH X15 X2 X5 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9bc67c50;       (* arm_UMULH X16 X2 X6 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b077c4a;       (* arm_MUL X10 X2 X7 *)
  0x9bc77c51;       (* arm_UMULH X17 X2 X7 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b087c4a;       (* arm_MUL X10 X2 X8 *)
  0x9bc87c53;       (* arm_UMULH X19 X2 X8 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b097c4a;       (* arm_MUL X10 X2 X9 *)
  0x9bc97c54;       (* arm_UMULH X20 X2 X9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x9b047c6a;       (* arm_MUL X10 X3 X4 *)
  0xab0a01ce;       (* arm_ADDS X14 X14 X10 *)
  0x9b057c6a;       (* arm_MUL X10 X3 X5 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9b067c6a;       (* arm_MUL X10 X3 X6 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b077c6a;       (* arm_MUL X10 X3 X7 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b087c6a;       (* arm_MUL X10 X3 X8 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b097c6a;       (* arm_MUL X10 X3 X9 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9a9f37f5;       (* arm_CSET X21 Condition_CS *)
  0x9bc47c6a;       (* arm_UMULH X10 X3 X4 *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9bc57c6a;       (* arm_UMULH X10 X3 X5 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9bc67c6a;       (* arm_UMULH X10 X3 X6 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc77c6a;       (* arm_UMULH X10 X3 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc87c6a;       (* arm_UMULH X10 X3 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc97c6a;       (* arm_UMULH X10 X3 X9 *)
  0x9a0a02b5;       (* arm_ADC X21 X21 X10 *)
  0x9b077cca;       (* arm_MUL X10 X6 X7 *)
  0x9bc77cd6;       (* arm_UMULH X22 X6 X7 *)
  0xab0a02b5;       (* arm_ADDS X21 X21 X10 *)
  0x9a1f02d6;       (* arm_ADC X22 X22 XZR *)
  0x9b057c8a;       (* arm_MUL X10 X4 X5 *)
  0xab0a0210;       (* arm_ADDS X16 X16 X10 *)
  0x9b067c8a;       (* arm_MUL X10 X4 X6 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9b077c8a;       (* arm_MUL X10 X4 X7 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b087c8a;       (* arm_MUL X10 X4 X8 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b097c8a;       (* arm_MUL X10 X4 X9 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b087cca;       (* arm_MUL X10 X6 X8 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9a9f37f7;       (* arm_CSET X23 Condition_CS *)
  0x9bc57c8a;       (* arm_UMULH X10 X4 X5 *)
  0xab0a0231;       (* arm_ADDS X17 X17 X10 *)
  0x9bc67c8a;       (* arm_UMULH X10 X4 X6 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9bc77c8a;       (* arm_UMULH X10 X4 X7 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc87c8a;       (* arm_UMULH X10 X4 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc97c8a;       (* arm_UMULH X10 X4 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc87cca;       (* arm_UMULH X10 X6 X8 *)
  0x9a0a02f7;       (* arm_ADC X23 X23 X10 *)
  0x9b087cea;       (* arm_MUL X10 X7 X8 *)
  0x9bc87cf8;       (* arm_UMULH X24 X7 X8 *)
  0xab0a02f7;       (* arm_ADDS X23 X23 X10 *)
  0x9a1f0318;       (* arm_ADC X24 X24 XZR *)
  0x9b067caa;       (* arm_MUL X10 X5 X6 *)
  0xab0a0273;       (* arm_ADDS X19 X19 X10 *)
  0x9b077caa;       (* arm_MUL X10 X5 X7 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9b087caa;       (* arm_MUL X10 X5 X8 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b097caa;       (* arm_MUL X10 X5 X9 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b097cca;       (* arm_MUL X10 X6 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9b097cea;       (* arm_MUL X10 X7 X9 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9a9f37f9;       (* arm_CSET X25 Condition_CS *)
  0x9bc67caa;       (* arm_UMULH X10 X5 X6 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9bc77caa;       (* arm_UMULH X10 X5 X7 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9bc87caa;       (* arm_UMULH X10 X5 X8 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc97caa;       (* arm_UMULH X10 X5 X9 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc97cca;       (* arm_UMULH X10 X6 X9 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9bc97cea;       (* arm_UMULH X10 X7 X9 *)
  0x9a0a0339;       (* arm_ADC X25 X25 X10 *)
  0x9b097d0a;       (* arm_MUL X10 X8 X9 *)
  0x9bc97d1a;       (* arm_UMULH X26 X8 X9 *)
  0xab0a0339;       (* arm_ADDS X25 X25 X10 *)
  0x9a1f035a;       (* arm_ADC X26 X26 XZR *)
  0xab0c018c;       (* arm_ADDS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0xba1602d6;       (* arm_ADCS X22 X22 X22 *)
  0xba1702f7;       (* arm_ADCS X23 X23 X23 *)
  0xba180318;       (* arm_ADCS X24 X24 X24 *)
  0xba190339;       (* arm_ADCS X25 X25 X25 *)
  0xba1a035a;       (* arm_ADCS X26 X26 X26 *)
  0x9a9f37fb;       (* arm_CSET X27 Condition_CS *)
  0x9bc27c4a;       (* arm_UMULH X10 X2 X2 *)
  0x9b027c4b;       (* arm_MUL X11 X2 X2 *)
  0xab0a018c;       (* arm_ADDS X12 X12 X10 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9bc37c6a;       (* arm_UMULH X10 X3 X3 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x9b047c8a;       (* arm_MUL X10 X4 X4 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x9bc47c8a;       (* arm_UMULH X10 X4 X4 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x9b057caa;       (* arm_MUL X10 X5 X5 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x9bc57caa;       (* arm_UMULH X10 X5 X5 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0x9b067cca;       (* arm_MUL X10 X6 X6 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0x9bc67cca;       (* arm_UMULH X10 X6 X6 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b077cea;       (* arm_MUL X10 X7 X7 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc77cea;       (* arm_UMULH X10 X7 X7 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9b087d0a;       (* arm_MUL X10 X8 X8 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9bc87d0a;       (* arm_UMULH X10 X8 X8 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0xba0a035a;       (* arm_ADCS X26 X26 X10 *)
  0x9bc97d2a;       (* arm_UMULH X10 X9 X9 *)
  0x9a0a037b;       (* arm_ADC X27 X27 X10 *)
  0xf9402021;       (* arm_LDR X1 X1 (Immediate_Offset (word 64)) *)
  0x9b017c3d;       (* arm_MUL X29 X1 X1 *)
  0x8b010021;       (* arm_ADD X1 X1 X1 *)
  0x9b027c2a;       (* arm_MUL X10 X1 X2 *)
  0xab0a0294;       (* arm_ADDS X20 X20 X10 *)
  0x9b037c2a;       (* arm_MUL X10 X1 X3 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0x9b047c2a;       (* arm_MUL X10 X1 X4 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9b057c2a;       (* arm_MUL X10 X1 X5 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9b067c2a;       (* arm_MUL X10 X1 X6 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9b077c2a;       (* arm_MUL X10 X1 X7 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9b087c2a;       (* arm_MUL X10 X1 X8 *)
  0xba0a035a;       (* arm_ADCS X26 X26 X10 *)
  0x9b097c2a;       (* arm_MUL X10 X1 X9 *)
  0xba0a037b;       (* arm_ADCS X27 X27 X10 *)
  0x9a1f03bd;       (* arm_ADC X29 X29 XZR *)
  0x9bc27c2a;       (* arm_UMULH X10 X1 X2 *)
  0xab0a02b5;       (* arm_ADDS X21 X21 X10 *)
  0x9bc37c2a;       (* arm_UMULH X10 X1 X3 *)
  0xba0a02d6;       (* arm_ADCS X22 X22 X10 *)
  0x9bc47c2a;       (* arm_UMULH X10 X1 X4 *)
  0xba0a02f7;       (* arm_ADCS X23 X23 X10 *)
  0x9bc57c2a;       (* arm_UMULH X10 X1 X5 *)
  0xba0a0318;       (* arm_ADCS X24 X24 X10 *)
  0x9bc67c2a;       (* arm_UMULH X10 X1 X6 *)
  0xba0a0339;       (* arm_ADCS X25 X25 X10 *)
  0x9bc77c2a;       (* arm_UMULH X10 X1 X7 *)
  0xba0a035a;       (* arm_ADCS X26 X26 X10 *)
  0x9bc87c2a;       (* arm_UMULH X10 X1 X8 *)
  0xba0a037b;       (* arm_ADCS X27 X27 X10 *)
  0x9bc97c2a;       (* arm_UMULH X10 X1 X9 *)
  0x9a0a03bd;       (* arm_ADC X29 X29 X10 *)
  0xeb1f03ff;       (* arm_CMP XZR XZR *)
  0x93d426aa;       (* arm_EXTR X10 X21 X20 9 *)
  0xba0a016b;       (* arm_ADCS X11 X11 X10 *)
  0x93d526ca;       (* arm_EXTR X10 X22 X21 9 *)
  0xba0a018c;       (* arm_ADCS X12 X12 X10 *)
  0x93d626ea;       (* arm_EXTR X10 X23 X22 9 *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x93d7270a;       (* arm_EXTR X10 X24 X23 9 *)
  0xba0a01ce;       (* arm_ADCS X14 X14 X10 *)
  0x93d8272a;       (* arm_EXTR X10 X25 X24 9 *)
  0xba0a01ef;       (* arm_ADCS X15 X15 X10 *)
  0x93d9274a;       (* arm_EXTR X10 X26 X25 9 *)
  0xba0a0210;       (* arm_ADCS X16 X16 X10 *)
  0x93da276a;       (* arm_EXTR X10 X27 X26 9 *)
  0xba0a0231;       (* arm_ADCS X17 X17 X10 *)
  0x93db27aa;       (* arm_EXTR X10 X29 X27 9 *)
  0xba0a0273;       (* arm_ADCS X19 X19 X10 *)
  0xb277da94;       (* arm_ORR X20 X20 (rvalue (word 18446744073709551104)) *)
  0xd349ffaa;       (* arm_LSR X10 X29 9 *)
  0xba0a0294;       (* arm_ADCS X20 X20 X10 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xfa1f0273;       (* arm_SBCS X19 X19 XZR *)
  0xda1f0294;       (* arm_SBC X20 X20 XZR *)
  0x92402294;       (* arm_AND X20 X20 (rvalue (word 511)) *)
  0xd377d96a;       (* arm_LSL X10 X11 9 *)
  0x93cbdd8b;       (* arm_EXTR X11 X12 X11 55 *)
  0x93ccddac;       (* arm_EXTR X12 X13 X12 55 *)
  0x93cdddcd;       (* arm_EXTR X13 X14 X13 55 *)
  0x93ceddee;       (* arm_EXTR X14 X15 X14 55 *)
  0xaa0a0294;       (* arm_ORR X20 X20 X10 *)
  0x93cfde0f;       (* arm_EXTR X15 X16 X15 55 *)
  0x93d0de30;       (* arm_EXTR X16 X17 X16 55 *)
  0x93d1de71;       (* arm_EXTR X17 X19 X17 55 *)
  0x93d3de93;       (* arm_EXTR X19 X20 X19 55 *)
  0xd377fe94;       (* arm_LSR X20 X20 55 *)
  0xa900300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&0))) *)
  0xa901380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&16))) *)
  0xa902400f;       (* arm_STP X15 X16 X0 (Immediate_Offset (iword (&32))) *)
  0xa9034c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&48))) *)
  0xf9002014;       (* arm_STR X20 X0 (Immediate_Offset (word 64)) *)
  0xa8c177fb;       (* arm_LDP X27 X29 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTSQR_P521_ALT_EXEC = ARM_MK_EXEC_RULE bignum_montsqr_p521_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let P_521 = prove
 (`p_521 = 2 EXP 521 - 1`,
  REWRITE_TAC[p_521] THEN CONV_TAC NUM_REDUCE_CONV);;

let P_521_AS_WORDLIST = prove
 (`p_521 =
   bignum_of_wordlist
    [word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word_not(word 0);word_not(word 0);word_not(word 0);word_not(word 0);
     word(0x1FF)]`,
  REWRITE_TAC[p_521; bignum_of_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_EQ_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] = p_521 <=>
   (!i. i < 64
        ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
            bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
   (!i. i < 9 ==> bit i n8) /\ (!i. i < 64 ==> 9 <= i ==> ~bit i n8)`,
  REWRITE_TAC[P_521_AS_WORDLIST; BIGNUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC CONJ_ACI_RULE);;

let BIGNUM_FROM_MEMORY_LE_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] <= p_521 <=>
   !i. i < 64 ==> 9 <= i ==> ~bit i n8`,
  SIMP_TAC[P_521; ARITH_RULE `p_521 = 2 EXP 521 - 1 ==>
    (n <= p_521 <=> n DIV 2 EXP (8 * 64) < 2 EXP 9)`] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `8`; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[GSYM DIV_DIV; BIGNUM_OF_WORDLIST_DIV; EXP; DIV_1] THEN
  REWRITE_TAC[BIGNUM_OF_WORDLIST_SING; GSYM UPPER_BITS_ZERO] THEN
  MP_TAC(ISPEC `n8:int64` BIT_TRIVIAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
  MESON_TAC[NOT_LE]);;

let BIGNUM_FROM_MEMORY_LT_P521 = prove
 (`bignum_of_wordlist[n0;n1;n2;n3;n4;n5;n6;n7;n8] < p_521 <=>
   (!i. i < 64 ==> 9 <= i ==> ~bit i n8) /\
   ~((!i. i < 64
          ==> bit i n0 /\ bit i n1 /\ bit i n2 /\ bit i n3 /\
              bit i n4 /\ bit i n5 /\ bit i n6 /\ bit i n7) /\
     (!i. i < 9 ==> bit i n8))`,
  GEN_REWRITE_TAC LAND_CONV [LT_LE] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_EQ_P521; BIGNUM_FROM_MEMORY_LE_P521] THEN
  MESON_TAC[]);;

let BIGNUM_MONTSQR_P521_ALT_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x3ec) (z,8 * 9)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p521_alt_mc /\
                  read PC s = word(pc + 0x14) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read PC s = word (pc + 0x3d4) /\
                  (n < p_521
                   ==> bignum_from_memory (z,9) s =
                       (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
         (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                      X13; X14; X15; X16; X17; X19; X20; X21; X22; X23; X24;
                      X25; X26; X27; X29] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the n < p_521 assumption for simplicity's sake ***)

  ASM_CASES_TAC `n < p_521` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTSQR_P521_ALT_EXEC (1--240)] THEN

  (*** Digitize, deduce the bound on the top word specifically ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n < p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN

  (*** Simulate the initial squaring ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_ALT_EXEC (1--194) (1--194) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COND_SWAP; GSYM WORD_BITVAL]) THEN

  (*** Introduce more systematic names for the high part digits ***)

  MAP_EVERY (fun s -> REABBREV_TAC s THEN POP_ASSUM SUBST_ALL_TAC)
   [`l0 = read X11 s194`;
    `l1 = read X12 s194`;
    `l2 = read X13 s194`;
    `l3 = read X14 s194`;
    `l4 = read X15 s194`;
    `l5 = read X16 s194`;
    `l6 = read X17 s194`;
    `l7 = read X19 s194`;
    `h0 = read X20 s194`;
    `h1 = read X21 s194`;
    `h2 = read X22 s194`;
    `h3 = read X23 s194`;
    `h4 = read X24 s194`;
    `h5 = read X25 s194`;
    `h6 = read X26 s194`;
    `h7 = read X27 s194`;
    `h8 = read X29 s194`]  THEN

  (*** Show that the core squaring operation is correct ***)

  SUBGOAL_THEN
   `2 EXP 512 * bignum_of_wordlist[h0;h1;h2;h3;h4;h5;h6;h7;h8] +
    bignum_of_wordlist[l0;l1;l2;l3;l4;l5;l6;l7] =
    n EXP 2`
  ASSUME_TAC THENL
   [UNDISCH_THEN
     `&2 pow 64 * &(bitval carry_s161) + &(val(sum_s161:int64)) =
      &(val(n_8:int64)) + &(val n_8)`
     (MP_TAC o REWRITE_RULE[REAL_OF_NUM_CLAUSES]) THEN
    REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THENL
     [MATCH_MP_TAC(ARITH_RULE `a < b ==> b + s:num = a ==> u:num = v`) THEN
      ASM BOUNDER_TAC[];
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`1088`; `&0:real`] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
      REWRITE_TAC[EXP_2; ARITH_RULE `2 EXP 1088 = 2 EXP 544 EXP 2`] THEN
      MATCH_MP_TAC LT_MULT2 THEN UNDISCH_TAC `n < p_521` THEN
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    EXPAND_TAC "n" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
      filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES])] THEN

  (*** Now simulate the shift-and-add of high and lower parts ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_ALT_EXEC
   [197;199;201;203;205;207;209;211;214] (195--214) THEN

  (*** Break up into high and low parts ***)

  ABBREV_TAC `h = (n EXP 2) DIV 2 EXP 521` THEN
  ABBREV_TAC `l = (n EXP 2) MOD 2 EXP 521` THEN
  SUBGOAL_THEN `h < p_521 /\ l <= p_521` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_521] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LET_TRANS `(p_521 - 1) EXP 2` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[p_521] THEN ARITH_TAC] THEN
    REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < n ==> x <= n - 1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  SUBGOAL_THEN `(n EXP 2) MOD p_521 = (h + l) MOD p_521` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(SPECL
     [`n EXP 2:num`; `2 EXP 521`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(e == 1) (mod p) ==> (e * h + l == h + l) (mod p)`) THEN
    REWRITE_TAC[CONG; p_521] THEN ARITH_TAC;
    REWRITE_TAC[MOD_MULT_MOD2]] THEN
  SUBGOAL_THEN
   `(n EXP 2) DIV 2 EXP 521 =
    bignum_of_wordlist
     [word_subword (word_join (h1:int64) h0:int128) (9,64);
      word_subword (word_join (h2:int64) h1:int128) (9,64);
      word_subword (word_join (h3:int64) h2:int128) (9,64);
      word_subword (word_join (h4:int64) h3:int128) (9,64);
      word_subword (word_join (h5:int64) h4:int128) (9,64);
      word_subword (word_join (h6:int64) h5:int128) (9,64);
      word_subword (word_join (h7:int64) h6:int128) (9,64);
      word_subword (word_join (h8:int64) h7:int128) (9,64);
      word_ushr h8 9] /\
    (n EXP 2) MOD 2 EXP 521 =
    2 EXP 512 * val(word_and h0 (word 511):int64) +
    bignum_of_wordlist [l0; l1; l2; l3; l4; l5; l6; l7]`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD_USHR] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN_64; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
      ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `x < 2 EXP (64 * 8) ==> 2 EXP 512 * h MOD 2 EXP 9 + x < 2 EXP 521`) THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN REWRITE_TAC[LENGTH; ARITH]];
    ALL_TAC] THEN

  (*** The net comparison h + l >= p_521 ***)

  SUBGOAL_THEN
   `&(val (word_or h0 (word 18446744073709551104))):real =
    (&2 pow 64 - &2 pow 9) + &(val(word_and h0 (word 511):int64))`
  SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or a b = word_or b (word_and a (word_not b))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and x (word_and y (word_not x)) = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `carry_s214 <=> p_521 <= h + l` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `576` THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The  correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P521_ALT_EXEC (215--223) (215--240) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `bignum_of_wordlist
     [sum_s215; sum_s216; sum_s217; sum_s218;
      sum_s219; sum_s220; sum_s221; sum_s222;
      word_and sum_s223 (word 511)] =
    (h + l) MOD p_521`
  MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`521`;
      `if h + l < p_521 then &h + &l:real else (&h + &l) - &p_521`] THEN
    REPEAT CONJ_TAC THENL
     [BOUNDER_TAC[];
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      REWRITE_TAC[p_521] THEN ARITH_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      REWRITE_TAC[GSYM NOT_LT] THEN ABBREV_TAC `bb <=> h + l < p_521` THEN
      MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_521] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
      REWRITE_TAC[REAL_OF_NUM_MOD] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ASM_SIMP_TAC[MOD_CASES; ARITH_RULE
       `h < p /\ l <= p ==> h + l < 2 * p`] THEN
      SIMP_TAC[REAL_OF_NUM_CLAUSES; REAL_OF_NUM_SUB;
               COND_SWAP; GSYM NOT_LE] THEN
      MESON_TAC[]];
   ALL_TAC] THEN

  (*** The final rotation for the Montgomery ingredient ***)

  CONV_TAC(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV)) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC(BINOP_CONV SYM_CONV) THEN REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[p_521] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN
  REWRITE_TAC[GSYM p_521] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_LT_P521] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_SHL;
             BIT_WORD_JOIN; BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
    GEN_REWRITE_TAC I [CONTRAPOS_THM] THEN
    CONV_TAC(BINOP_CONV CONJ_CANON_CONV) THEN
    DISCH_THEN ACCEPT_TAC;
    MATCH_MP_TAC(NUMBER_RULE
     `!a. (a * i == 1) (mod p) /\ (a * q == n) (mod p)
          ==> (x == n) (mod p) ==> (i * x == q) (mod p)`) THEN
    EXISTS_TAC `2 EXP 576` THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2; p_521] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_CONGRUENCE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[val_def; DIMINDEX_64; bignum_of_wordlist] THEN
    REWRITE_TAC[ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN
    REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_SHL;
             BIT_WORD_JOIN; BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV
     (NUM_RED_CONV ORELSEC WORD_RED_CONV ORELSEC
      GEN_REWRITE_CONV I [BITVAL_CLAUSES])) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_INTEGER_TAC]);;

let BIGNUM_MONTSQR_P521_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (z,8 * 9) (word_sub stackpointer (word 80),80) /\
      ALLPAIRS nonoverlapping
       [(z,8 * 9); (word_sub stackpointer (word 80),80)]
       [(word pc,0x3ec); (x,8 * 9)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p521_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,9) s = n)
           (\s. read PC s = returnaddress /\
                (n < p_521
                 ==> bignum_from_memory (z,9) s =
                     (inverse_mod p_521 (2 EXP 576) * n EXP 2) MOD p_521))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 9);
                       memory :> bytes(word_sub stackpointer (word 80),80)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTSQR_P521_ALT_EXEC BIGNUM_MONTSQR_P521_ALT_CORRECT
   `[X19;X20;X21;X22;X23;X24;X25;X26;X27;X29]` 80);;
