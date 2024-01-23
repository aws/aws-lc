(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum.                        *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/fastmul/bignum_emontredc_8n.o";;
 ****)

let bignum_emontredc_8n_mc =
  define_assert_from_elf "bignum_emontredc_8n_mc" "arm/fastmul/bignum_emontredc_8n.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf73fb;       (* arm_STP X27 X28 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd342fc00;       (* arm_LSR X0 X0 (rvalue (word 2)) *)
  0xaa0003fa;       (* arm_MOV X26 X0 *)
  0xf100040c;       (* arm_SUBS X12 X0 (rvalue (word 1)) *)
  0x54001e43;       (* arm_BCC (word 968) *)
  0xaa1f03fc;       (* arm_MOV X28 XZR *)
  0xd37be980;       (* arm_LSL X0 X12 (rvalue (word 5)) *)
  0xa9404c31;       (* arm_LDP X17 X19 X1 (Immediate_Offset (iword (&0))) *)
  0xa9415434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0x9b037e24;       (* arm_MUL X4 X17 X3 *)
  0x9b087c8c;       (* arm_MUL X12 X4 X8 *)
  0x9b097c8d;       (* arm_MUL X13 X4 X9 *)
  0x9b0a7c8e;       (* arm_MUL X14 X4 X10 *)
  0x9b0b7c8f;       (* arm_MUL X15 X4 X11 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0x9bc87c8c;       (* arm_UMULH X12 X4 X8 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x9bc97c8d;       (* arm_UMULH X13 X4 X9 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0x9bcb7c8f;       (* arm_UMULH X15 X4 X11 *)
  0x9a1f03f6;       (* arm_ADC X22 XZR XZR *)
  0xab0c0273;       (* arm_ADDS X19 X19 X12 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9a0f02d6;       (* arm_ADC X22 X22 X15 *)
  0x9b037e65;       (* arm_MUL X5 X19 X3 *)
  0x9b087cac;       (* arm_MUL X12 X5 X8 *)
  0x9b097cad;       (* arm_MUL X13 X5 X9 *)
  0x9b0a7cae;       (* arm_MUL X14 X5 X10 *)
  0x9b0b7caf;       (* arm_MUL X15 X5 X11 *)
  0xab0c0273;       (* arm_ADDS X19 X19 X12 *)
  0x9bc87cac;       (* arm_UMULH X12 X5 X8 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0x9bc97cad;       (* arm_UMULH X13 X5 X9 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9bca7cae;       (* arm_UMULH X14 X5 X10 *)
  0xba0f02d6;       (* arm_ADCS X22 X22 X15 *)
  0x9bcb7caf;       (* arm_UMULH X15 X5 X11 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0xab0c0294;       (* arm_ADDS X20 X20 X12 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9a0f02f7;       (* arm_ADC X23 X23 X15 *)
  0x9b037e86;       (* arm_MUL X6 X20 X3 *)
  0x9b087ccc;       (* arm_MUL X12 X6 X8 *)
  0x9b097ccd;       (* arm_MUL X13 X6 X9 *)
  0x9b0a7cce;       (* arm_MUL X14 X6 X10 *)
  0x9b0b7ccf;       (* arm_MUL X15 X6 X11 *)
  0xab0c0294;       (* arm_ADDS X20 X20 X12 *)
  0x9bc87ccc;       (* arm_UMULH X12 X6 X8 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0x9bc97ccd;       (* arm_UMULH X13 X6 X9 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0f02f7;       (* arm_ADCS X23 X23 X15 *)
  0x9bcb7ccf;       (* arm_UMULH X15 X6 X11 *)
  0x9a1f03f8;       (* arm_ADC X24 XZR XZR *)
  0xab0c02b5;       (* arm_ADDS X21 X21 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9a0f0318;       (* arm_ADC X24 X24 X15 *)
  0x9b037ea7;       (* arm_MUL X7 X21 X3 *)
  0x9b087cec;       (* arm_MUL X12 X7 X8 *)
  0x9b097ced;       (* arm_MUL X13 X7 X9 *)
  0x9b0a7cee;       (* arm_MUL X14 X7 X10 *)
  0x9b0b7cef;       (* arm_MUL X15 X7 X11 *)
  0xab0c02b5;       (* arm_ADDS X21 X21 X12 *)
  0x9bc87cec;       (* arm_UMULH X12 X7 X8 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0x9bc97ced;       (* arm_UMULH X13 X7 X9 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bca7cee;       (* arm_UMULH X14 X7 X10 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0x9bcb7cef;       (* arm_UMULH X15 X7 X11 *)
  0x9a1f03f9;       (* arm_ADC X25 XZR XZR *)
  0xab0c02cc;       (* arm_ADDS X12 X22 X12 *)
  0xba0d02ed;       (* arm_ADCS X13 X23 X13 *)
  0xba0e030e;       (* arm_ADCS X14 X24 X14 *)
  0x9a0f032f;       (* arm_ADC X15 X25 X15 *)
  0xa9001424;       (* arm_STP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xa9011c26;       (* arm_STP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xb4001220;       (* arm_CBZ X0 (word 580) *)
  0xaa0003fb;       (* arm_MOV X27 X0 *)
  0x91008042;       (* arm_ADD X2 X2 (rvalue (word 32)) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0x9b087c91;       (* arm_MUL X17 X4 X8 *)
  0x9b097cb6;       (* arm_MUL X22 X5 X9 *)
  0x9b0a7cd7;       (* arm_MUL X23 X6 X10 *)
  0x9b0b7cf8;       (* arm_MUL X24 X7 X11 *)
  0x9bc87c90;       (* arm_UMULH X16 X4 X8 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9bc97cb0;       (* arm_UMULH X16 X5 X9 *)
  0xba1002f7;       (* arm_ADCS X23 X23 X16 *)
  0x9bca7cd0;       (* arm_UMULH X16 X6 X10 *)
  0xba100318;       (* arm_ADCS X24 X24 X16 *)
  0x9bcb7cf0;       (* arm_UMULH X16 X7 X11 *)
  0x9a1f0219;       (* arm_ADC X25 X16 XZR *)
  0xa9405434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&0))) *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xa9415434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0x9a1f03f0;       (* arm_ADC X16 XZR XZR *)
  0xab1102d3;       (* arm_ADDS X19 X22 X17 *)
  0xba1602f6;       (* arm_ADCS X22 X23 X22 *)
  0xba170317;       (* arm_ADCS X23 X24 X23 *)
  0xba180338;       (* arm_ADCS X24 X25 X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0xab1102d4;       (* arm_ADDS X20 X22 X17 *)
  0xba1302f5;       (* arm_ADCS X21 X23 X19 *)
  0xba160316;       (* arm_ADCS X22 X24 X22 *)
  0xba170337;       (* arm_ADCS X23 X25 X23 *)
  0xba1803f8;       (* arm_ADCS X24 XZR X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0xba1002d6;       (* arm_ADCS X22 X22 X16 *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0xba1f0318;       (* arm_ADCS X24 X24 XZR *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xeb0700cf;       (* arm_SUBS X15 X6 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb0a016d;       (* arm_SUBS X13 X11 X10 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d0318;       (* arm_ADCS X24 X24 X13 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb05008f;       (* arm_SUBS X15 X4 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb08012d;       (* arm_SUBS X13 X9 X8 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0xba0c02f7;       (* arm_ADCS X23 X23 X12 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb0700af;       (* arm_SUBS X15 X5 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb09016d;       (* arm_SUBS X13 X11 X9 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02f7;       (* arm_ADCS X23 X23 X13 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb06008f;       (* arm_SUBS X15 X4 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb08014d;       (* arm_SUBS X13 X10 X8 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0xba0c02f7;       (* arm_ADCS X23 X23 X12 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb07008f;       (* arm_SUBS X15 X4 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb08016d;       (* arm_SUBS X13 X11 X8 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0c02f7;       (* arm_ADCS X23 X23 X12 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb09014d;       (* arm_SUBS X13 X10 X9 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0c02ed;       (* arm_ADCS X13 X23 X12 *)
  0xba0c030e;       (* arm_ADCS X14 X24 X12 *)
  0x9a0c032f;       (* arm_ADC X15 X25 X12 *)
  0xaa1603ec;       (* arm_MOV X12 X22 *)
  0xa9004c31;       (* arm_STP X17 X19 X1 (Immediate_Offset (iword (&0))) *)
  0xa9015434;       (* arm_STP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xf100837b;       (* arm_SUBS X27 X27 (rvalue (word 32)) *)
  0x54ffee41;       (* arm_BNE (word 2096584) *)
  0xa9424c31;       (* arm_LDP X17 X19 X1 (Immediate_Offset (iword (&32))) *)
  0xa9435434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&48))) *)
  0xab1c039f;       (* arm_CMN X28 X28 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0xda9f33fc;       (* arm_CSETM X28 Condition_CS *)
  0xa9024c31;       (* arm_STP X17 X19 X1 (Immediate_Offset (iword (&32))) *)
  0xa9035434;       (* arm_STP X20 X21 X1 (Immediate_Offset (iword (&48))) *)
  0xcb000021;       (* arm_SUB X1 X1 X0 *)
  0xcb000042;       (* arm_SUB X2 X2 X0 *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xf100075a;       (* arm_SUBS X26 X26 (rvalue (word 1)) *)
  0x54ffe261;       (* arm_BNE (word 2096204) *)
  0xcb1c03e0;       (* arm_NEG X0 X28 *)
  0xa8c173fb;       (* arm_LDP X27 X28 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_EMONTREDC_8N_EXEC = ARM_MK_EXEC_RULE bignum_emontredc_8n_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** Lemma to justify zeros in the Montgomery steps ***)

let montgomery_lemma = prove
 (`!w n.
    (n * w + 1 == 0) (mod (2 EXP 64))
    ==> !h l x.
            &2 pow 64 * &h + &l:real =
            &(val (word(x * w):int64)) *
            &(val(word(bigdigit n 0):int64))
            ==> !h' l'. &2 pow 64 * &h' + &(val l'):real = &x + &l
                        ==> val(l':int64) = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; GSYM LOWDIGITS_1; lowdigits] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_MOD_REFL] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`)) THEN
  REWRITE_TAC[MOD_MULT_ADD; DIMINDEX_128; DIMINDEX_64; MULT_CLAUSES] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 64 = 64 /\ MIN 128 64 = 64`] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG; GSYM DIVIDES_MOD] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`2 EXP 64`,`p:num`) THEN
  CONV_TAC NUMBER_RULE);;

(*** Lemmas for the case splits in the ADK blocks ***)

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
 (`!(x0:int64) (x1:int64) (y0:int64) (y1:int64).
        &(val(if val x1 <= val x0 then word_sub x0 x1
              else word_neg (word_sub x0 x1))) *
        &(val(if val y0 <= val y1 then word_sub y1 y0
              else word_neg (word_sub y1 y0))):real =
        --(&1) pow bitval(val y0 <= val y1 <=> val x0 < val x1) *
        (&(val x0) - &(val x1)) * (&(val y1) - &(val y0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE; WORD_NEG_SUB] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
   `~(m:num <= n) ==> n <= m /\ ~(m <= n)`))) THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES; GSYM REAL_OF_NUM_SUB] THEN
  REAL_ARITH_TAC);;

let BIGNUM_EMONTREDC_8N_CORRECT = time prove
 (`!k z m w a n pc.
        nonoverlapping (word pc,0x400) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k) /\
        8 divides val k
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_8n_mc /\
                read PC s = word(pc + 0x14) /\
                C_ARGUMENTS [k; z; m; w] s /\
                bignum_from_memory (z,2 * val k) s = a /\
                bignum_from_memory (m,val k) s = n)
           (\s. read PC s = word(pc + 0x3e8) /\
                ((n * val w + 1 == 0) (mod (2 EXP 64))
                 ==> n * bignum_from_memory (z,val k) s + a =
                     2 EXP (64 * val k) *
                     (2 EXP (64 * val k) * val(C_RETURN s) +
                      bignum_from_memory
                        (word_add z (word(8 * val k)),val k) s)))
            (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11;
                        X12; X13; X14; X15; X16; X17; X19; X20;
                        X21; X22; X23; X24; X25; X26; X27; X28] ,,
             MAYCHANGE [memory :> bytes(z,8 * 2 * val k)] ,,
             MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`] THEN
  W64_GEN_TAC `w:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  ABBREV_TAC `k4 = k DIV 4` THEN

  (*** Degenerate k/4 = 0 case ***)

  ASM_CASES_TAC `k4 = 0` THENL
   [UNDISCH_THEN `k4 = 0` SUBST_ALL_TAC THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--4) THEN
    UNDISCH_TAC `8 divides k` THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`] THEN
    ASM_REWRITE_TAC[DIVIDES_DIV_MULT; MULT_CLAUSES; ARITH_RULE `0 < 1`;
                    DIV_0; ARITH_RULE `k DIV 8 = k DIV 4 DIV 2`] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN

  (*** Restate things in terms of k' = k * k DIV 4 for naturalness ***)

  ABBREV_TAC `k' = 4 * k4` THEN
  ABBREV_TAC `a' = lowdigits a (2 * k')` THEN
  ABBREV_TAC `n' = lowdigits n k'` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x24`
   `\s. read X12 s = word(k4 - 1) /\
        read X26 s = word k4 /\
        read X1 s = z /\
        read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory (z,2 * k') s = a' /\
        bignum_from_memory (m,k') s = n'` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--4) THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < 1 <=> n = 0`] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[WORD_RULE `word_sub x z = word_sub y z <=> x = y`] THEN
    ASM_REWRITE_TAC[word_ushr; NUM_REDUCE_CONV `2 EXP 2`] THEN
    MAP_EVERY EXPAND_TAC ["a'"; "n'"; "a"; "n"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN
    CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x3e8`
   `\s. ((n' * w + 1 == 0) (mod (2 EXP 64))
         ==> n' * bignum_from_memory (z,k') s + a' =
           2 EXP (64 * k') *
           (2 EXP (64 * k') * val(read X0 s) +
            bignum_from_memory (word_add z (word (8 * k')),k') s))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [] THEN REWRITE_TAC[IMP_CONJ] THEN
    UNDISCH_TAC `8 divides k` THEN
    DISCH_THEN(MP_TAC o SPEC `4` o MATCH_MP (NUMBER_RULE
     `y divides a ==> !x:num. x divides y ==> x divides a`)) THEN
    ANTS_TAC THENL [CONV_TAC DIVIDES_CONV; ALL_TAC] THEN
    ASM_REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIVIDES_DIV_MULT] THEN
    ASM_CASES_TAC `k':num = k` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `k':num = k` SUBST_ALL_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`lowdigits a (2 * k) = a'`; `lowdigits n k = n'`] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  SUBGOAL_THEN
   `nonoverlapping (z,8 * 2 * k') (word pc,0x400) /\
    nonoverlapping (z,8 * 2 * k') (m:int64,8 * k')`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE
     [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
      X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
    MAYCHANGE [memory :> bytes (z,8 * 2 * k')] ,,
    MAYCHANGE [NF; ZF; CF; VF]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `k:num`) o concl)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  MAP_EVERY SPEC_TAC
    [(`a':num`,`a:num`); (`n':num`,`n:num`); (`k':num`,`k:num`)] THEN
  REPEAT STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Get a basic bound on k and k4 from the nonoverlapping assumptions ***)

  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  MP_TAC(ASSUME
   `nonoverlapping_modulo (2 EXP 64)
     (val(z:int64),8 * 2 * k) (val(m:int64),8 * k)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `k4 < 2 EXP 58` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Main loop invariant for "outerloop" ***)

  ENSURES_WHILE_PUP_TAC `k4:num` `pc + 0x2c` `pc + 0x3e0`
   `\i s. (read X2 s = m /\
           read X3 s = word w /\
           bignum_from_memory (m,k) s = n /\
           read X0 s = word(32 * (k4 - 1)) /\
           read X26 s = word(k4 - i) /\
           read X1 s = word_add z (word(8 * 4 * i)) /\
           bignum_from_memory(word_add z (word(8 * (k + 4 * i))),
                              2 * k - (k + 4 * i)) s =
           highdigits a (k + 4 * i) /\
           ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 4 * i) *
                (2 EXP (64 * k) * val(word_neg(read X28 s)) +
                 bignum_from_memory(word_add z (word(8 * 4 * i)),k) s) =
               bignum_from_memory(z,4 * i) s * n + lowdigits a (k + 4 * i))) /\
          (read ZF s <=> i = k4)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        HIGHDIGITS_BIGNUM_FROM_MEMORY) THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        LOWDIGITS_BIGNUM_FROM_MEMORY) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `MIN (2 * k) k = k /\ 2 * k - k = k`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_0; WORD_NEG_0] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; VAL_WORD_0; ADD_CLAUSES; EXP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; ARITH_RULE `2 * k - k = k`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC WORD_RULE;
    ALL_TAC; (*** This is the main loop invariant: save for later ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1];
    GHOST_INTRO_TAC `ncout:int64` `read X28` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) THEN DISCH_TAC THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM MULT_2; WORD_SUB_LZERO] THEN
    REWRITE_TAC[MULT_SYM]] THEN

  (*** Start on the main outer loop invariant, rebase at z + 32 * i = rsi ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * (k + 4 * i))) =
    word_add (word_add z (word(8 * 4 * i))) (word(8 * k))`] THEN
  REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * 4 * (i + 1))) =
    word_add (word_add z (word(8 * 4 * i))) (word(8 * 4))`] THEN
  ABBREV_TAC `z':int64 = word_add z (word (8 * 4 * i))` THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add z (word (8 * 4))) (word (8 * k)) =
    word_add z (word (8 * (k + 4)))`] THEN
  REWRITE_TAC[ARITH_RULE `2 * k - (k  + i) = k - i`] THEN

  GHOST_INTRO_TAC `cout:num` `\s. val (word_neg (read X28 s))` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  REWRITE_TAC[WORD_RULE `word_neg x = y <=> x = word_neg y`] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory(z',k) s =
        lowdigits (bignum_from_memory(z',k+4) s) k`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[ARITH_RULE `MIN (k + 4) k = k`];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory (z,4 * (i + 1)) s =
        2 EXP (64 * 4 * i) * bignum_from_memory(z',4) s +
        bignum_from_memory(z,4 * i) s`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory (word_add z' (word (8 * k)),k - 4 * i) s =
        highdigits a (k + 4 * i) <=>
        highdigits (bignum_from_memory(z',k+4) s) k =
        lowdigits (highdigits a (k + 4 * i)) 4 /\
        bignum_from_memory
         (word_add z' (word (8 * (k + 4))),k - 4 * (i + 1)) s =
        highdigits a (k + 4 * (i + 1))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ADD_SUB2] THEN
    SUBGOAL_THEN
     `k - 4 * i = 4 + (k - 4 * (i + 1))`
    SUBST1_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    MP_TAC(SPECL [`highdigits a (k + 4 * i)`; `4`]
     (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM th]) THEN
    SIMP_TAC[LEXICOGRAPHIC_EQ; BIGNUM_FROM_MEMORY_BOUND; LOWDIGITS_BOUND] THEN
    REWRITE_TAC[HIGHDIGITS_HIGHDIGITS] THEN
    REWRITE_TAC[ARITH_RULE `(k + 4 * i) + 4 = k + 4 * (i + 1)`] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_add z (word (8 * k))) (word (8 * 4)) =
      word_add z (word (8 * (k + 4)))`] THEN
    MATCH_ACCEPT_TAC CONJ_SYM;
    ALL_TAC] THEN

  GHOST_INTRO_TAC `z1:num` `bignum_from_memory(z',k+4)` THEN
  BIGNUM_TERMRANGE_TAC `k + 4` `z1:num` THEN
  GHOST_INTRO_TAC `q1:num` `bignum_from_memory(z,4 * i)` THEN
  BIGNUM_TERMRANGE_TAC `4 * i` `q1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_SEQUENCE_TAC `pc + 0x3e0`
   `\s. read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = word (k4 - (i + 1)) /\
        (read ZF s <=> i + 1 = k4) /\
        read X1 s = word_add z' (word (8 * 4)) /\
        bignum_from_memory (word_add z' (word (8 * (k + 4))),k - 4 * (i + 1))
        s =
        highdigits a (k + 4 * (i + 1)) /\
        bignum_from_memory (z,4 * i) s = q1 /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             (2 EXP (64 * k) *
              val(word_neg(read X28 s)) +
              bignum_from_memory(word_add z' (word(8 * 4)),k) s) =
             bignum_from_memory(z',4) s * n + 2 EXP (64 * k) * cout + z1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;

    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [] THEN
    DISCH_THEN(fun th ->
     REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th))) THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE
     `64 * 4 * (i + 1) = 64 * 4 * i + 64 * 4`] THEN
    ASM_REWRITE_TAC[GSYM MULT_ASSOC] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; EQ_ADD_LCANCEL] THEN
    MP_TAC(SPECL [`z1:num`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `ee * e * c + ee * (e * h + l):num =
      (ee * (e * c + l)) + (ee * e) * h`] THEN
    REWRITE_TAC[GSYM EXP_ADD; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[lowdigits; highdigits; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `64 * 4 * i + 64 * k = 64 * k + 64 * 4 * i`] THEN
    SPEC_TAC(`64 * k + 64 * 4 * i`,`j:num`) THEN
    REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN ARITH_TAC] THEN

  (*** Now discard no-longer-relevant things outside the window ***)

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
     X14; X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
    MAYCHANGE [memory :> bytes(z',8 * (k + 4))] ,,
    MAYCHANGE [NF; ZF; CF; VF]` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (z':int64,8 * (k + 4)) (z,8 * 4 * i) /\
    nonoverlapping (z':int64,8 * (k + 4)) (word pc,0x400) /\
    nonoverlapping (z':int64,8 * (k + 4)) (m,8 * k) /\
    nonoverlapping (z':int64,8 * (k + 4))
     (word_add z' (word (8 * (k + 4))),8 * (k - 4 * (i + 1)))`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_FORGET_COMPONENTS_TAC
   [`memory :> bytes (z,8 * 4 * i)`;
    `memory :>
     bytes (word_add z' (word (8 * (k + 4))),8 * (k - 4 * (i + 1)))`] THEN

  (*** Get the cout < 2 before we forget too much context ***)

  SUBGOAL_THEN `(n * w + 1 == 0) (mod (2 EXP 64)) ==> cout < 2`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `2 EXP (64 * 4 * i) * (2 EXP (64 * k) * cout + lowdigits z1 k) <
      2 EXP (64 * 4 * i) * 2 EXP (64 * k) * 2`
    MP_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC (ARITH_RULE
       `x < d * e /\ y < e * d ==> x + y < d * e * 2`) THEN
      ASM_SIMP_TAC[LT_MULT2] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
      REWRITE_TAC[LOWDIGITS_BOUND; GSYM LEFT_ADD_DISTRIB];
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `d * (e * c + l):num < x ==> d * e * c < x`)) THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN

  (*** Now forget more things; back up a few steps and forget i as well ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `a:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `z:int64`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `q1:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `r1:num`) o concl)) THEN

  ENSURES_SEQUENCE_TAC `pc + 0x3d0`
   `\s. read X2 s = word_add m (word(32 * (k4 - 1))) /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = word (k4 - i) /\
        read X1 s = word_add z' (word(32 * (k4 - 1))) /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             (2 EXP (64 * k) * val(word_neg (read X28 s)) +
              bignum_from_memory(word_add z' (word(8 * 4)),k) s) =
              bignum_from_memory(z',4) s * n +
              2 EXP (64 * k) * cout + z1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--4) THEN REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
      VAL_INT64_TAC `k4 - i:num` THEN ASM_REWRITE_TAC[VAL_WORD_1] THEN
      UNDISCH_TAC `i:num < k4` THEN ARITH_TAC;
      CONV_TAC WORD_RULE]] THEN

  ABBREV_TAC `wouter:int64 = word (k4 - i)` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `i:num`) o concl)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  MAP_EVERY SPEC_TAC
    [(`z1:num`,`a:num`); (`z':int64`,`z:int64`)] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `4 <= k` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `4 * k4 = k`)) THEN UNDISCH_TAC `~(k4 = 0)` THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The initial Montgomery 4-block ***)

  ENSURES_SEQUENCE_TAC `pc + 0x164`
   `\s. read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory(m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = wouter /\
        read X1 s = z /\
        read X28 s = word_neg(word cout) /\
        bignum_from_memory(word_add z (word (8 * 4)),k) s =
        highdigits a 4 /\
        read X4 s = word(bigdigit (bignum_from_memory(z,4) s) 0) /\
        read X5 s = word(bigdigit (bignum_from_memory(z,4) s) 1) /\
        read X6 s = word(bigdigit (bignum_from_memory(z,4) s) 2) /\
        read X7 s = word(bigdigit (bignum_from_memory(z,4) s) 3) /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             bignum_of_wordlist
              [read X12 s; read X13 s; read X14 s; read X15 s] =
             bignum_from_memory(z,4) s * lowdigits n 4 + lowdigits a 4)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `highdigits (bignum_from_memory(z,k+4) s0) 4 = highdigits a 4`
    MP_TAC THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC] THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ADD_SUB] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[NUM_REDUCE_CONV `8 * 4`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(!i. i < 4
           ==> bigdigit (bignum_from_memory(z,k+4) s0) i = bigdigit a i) /\
      (!i. i < 4
           ==> bigdigit (bignum_from_memory(m,k) s0) i = bigdigit n i)`
    MP_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    SUBGOAL_THEN `!i. i < 4 ==> i < k /\ i < k + 4` MP_TAC THENL
     [UNDISCH_TAC `4 <= k` THEN ARITH_TAC; SIMP_TAC[]] THEN
    DISCH_THEN(K ALL_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(BINOP_CONV EXPAND_CASES_CONV)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] THEN
    STRIP_TAC THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--78) (1--78) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_LT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ASM_REWRITE_TAC[WORD_VAL; WORD_ADD_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RAND_CONV(TOP_DEPTH_CONV num_CONV) `lowdigits x 4`] THEN
    REWRITE_TAC[ADD1; LOWDIGITS_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP montgomery_lemma) THEN
    DISCH_THEN(fun ith ->
      EVERY_ASSUM(fun th ->
        try let th' = MATCH_MP ith th in
            EVERY_ASSUM(fun th'' ->
              try MP_TAC(MATCH_MP th' th'')
              with Failure _ -> ALL_TAC)
        with Failure _ -> ALL_TAC)) THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
     (MP_TAC o MATCH_MP (MESON[REAL_ADD_LID]
        `n = 0 ==> !x:real. &n + x = x`))) THEN
    REPEAT(DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Shared tail to handle the final carry chaining in k4 = 1 too ***)

  GHOST_INTRO_TAC `q:num` `bignum_from_memory(z,4)` THEN
  BIGNUM_TERMRANGE_TAC `4` `q:num` THEN

  (*** Set up a version with the whole z buffer ***)

  ENSURES_SEQUENCE_TAC `pc + 0x3a8`
   `\s. read X1 s = word_add z (word (32 * (k4 - 1))) /\
        read X2 s = word_add m (word (32 * (k4 - 1))) /\
        read X3 s = word w /\
        bignum_from_memory(m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = wouter /\
        read X28 s = word_neg(word cout) /\
        bignum_from_memory (word_add z (word (8 * k)),4) s =
        highdigits a k /\
        bignum_from_memory (z,4) s = q /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * k) *
             bignum_of_wordlist
              [read X12 s; read X13 s; read X14 s; read X15 s] +
             bignum_from_memory(z,k) s =
             q * n + lowdigits a k + q)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `g8:int64` `read X12` THEN
    GHOST_INTRO_TAC `g9:int64` `read X13` THEN
    GHOST_INTRO_TAC `g10:int64` `read X14` THEN
    GHOST_INTRO_TAC `g11:int64` `read X15` THEN

    (*** Rebase once again to avoid indexing messiness a bit ***)

    ABBREV_TAC `z':int64 = word_add z (word (8 * k))` THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
     `MAYCHANGE
       [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
        X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE [memory :> bytes (z',8 * 4)] ,,
      MAYCHANGE [NF; ZF; CF; VF]` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      MAP_EVERY EXPAND_TAC ["z'"] THEN SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `nonoverlapping (z':int64,8 * 4) (word pc,0x400) /\
      nonoverlapping (z':int64,8 * 4) (m,8 * k) /\
      nonoverlapping (z':int64,8 * 4) (z,8 * 4) /\
      nonoverlapping (z':int64,8 * 4) (z,8 * k)`
    MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
     [MAP_EVERY EXPAND_TAC ["z'"] THEN
      REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
      STRIP_TAC] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `!j. j < 4
          ==> bigdigit (bignum_from_memory(z',4) s0) j =
              bigdigit a (k + j)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BIGDIGIT_HIGHDIGITS];
      SIMP_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY]] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; GSYM WORD_ADD_ASSOC;
      GSYM WORD_ADD] THEN
    REWRITE_TAC[] THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0]) THEN
    SUBGOAL_THEN
     `word_add z (word (32 * (k4 - 1) + 32)):int64 = z' /\
      word_add z (word (32 * (k4 - 1) + 40)):int64 = word_add z' (word 8) /\
      word_add z (word (32 * (k4 - 1) + 48)):int64 = word_add z' (word 16) /\
      word_add z (word (32 * (k4 - 1) + 56)):int64 = word_add z' (word 24) /\
      word_add (word_add z (word (32 * (k4 - 1)))) (word 32):int64 =
      z' /\
      word_add (word_add z (word (32 * (k4 - 1)))) (word 48):int64 =
      word_add z' (word 16)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      SUBST1_TAC(SYM(ASSUME `word_add z (word (8 * k)):int64 = z'`)) THEN
      SUBGOAL_THEN `8 * k = 32 * (k4 - 1) + 32` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`4 * k4 = k`; `~(k4 = 0)`] THEN ARITH_TAC;
        CONV_TAC WORD_RULE];
      ALL_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (4--7) (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
      ASSUME_TAC th) THEN
    ABBREV_TAC `bout <=> ~(word cout:int64 = word 0)` THEN
    SUBGOAL_THEN `cout = bitval bout` SUBST_ALL_TAC THENL
     [EXPAND_TAC "bout" THEN UNDISCH_TAC `cout < 2` THEN
      SPEC_TAC(`cout:num`,`c:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `bitval
       (2 EXP 64 <=
        val (word_neg(word (bitval bout):int64)) +
        val (word_neg(word (bitval bout):int64))) =
      bitval bout`
    SUBST_ALL_TAC THENL
     [POP_ASSUM_LIST(K ALL_TAC) THEN AP_TERM_TAC THEN
      BOOL_CASES_TAC `bout:bool` THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
      CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_UNMASK_64; WORD_NEG_NEG; VAL_WORD_BITVAL]] THEN
    MP_TAC(SPECL [`a:num`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (ARITH_RULE
       `z = q * n + a + q
        ==> x + q = z + b + h
            ==> x = q * n + b + h + a`)) THEN
    SUBST1_TAC(SYM(ASSUME `read (memory :> bytes (z,8 * 4)) s10 = q`)) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_SPLIT] THEN
    ONCE_REWRITE_TAC[MESON[ADD_SYM]
     `bignum_from_memory (z,4 + k) = bignum_from_memory (z,k + 4)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
    REWRITE_TAC[EQ_ADD_RCANCEL; ADD_ASSOC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a * b * c:num = b * a * c`] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; VAL_WORD_BITVAL] THEN
    AP_TERM_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN
    REPLICATE_TAC 4
     (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP]) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC] THEN

  (*** The semi-degenerate case where we skip the inner loop ***)

  ASM_CASES_TAC `k4 = 1` THENL
   [UNDISCH_THEN `k4 = 1` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `4 * 1 = k ==> k = 4`)) THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN

  (*** Setup of the inner loop "maddloop" ***)

  ENSURES_WHILE_PAUP_TAC `1` `k4:num` `pc + 0x16c` `pc + 0x3a4`
   `\i s. (read X1 s = word_sub (word_add z (word(32 * i))) (word 32) /\
           read X2 s = word_sub (word_add m (word(32 * i))) (word 32) /\
           read X3 s = word w /\
           bignum_from_memory(m,k) s = n /\
           read X0 s = word (32 * (k4 - 1)) /\
           read X26 s = wouter /\
           read X28 s = word_neg(word cout) /\
           bignum_from_memory (z,4) s = q /\
           read X4 s = word (bigdigit q 0) /\
           read X5 s = word (bigdigit q 1) /\
           read X6 s = word (bigdigit q 2) /\
           read X7 s = word (bigdigit q 3) /\
           read X27 s = word (32 * (k4 - i)) /\
           bignum_from_memory (word_add z (word (8 * 4 * i)),
                               (k + 4) - 4 * i) s =
           highdigits a (4 * i) /\
           ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 4 * i) *
                bignum_of_wordlist
                [read X12 s; read X13 s; read X14 s; read X15 s] +
                bignum_from_memory(z,4 * i) s =
                q * lowdigits n (4 * i) + lowdigits a (4 * i) + q)) /\
          (read ZF s <=> i = k4)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0) /\ ~(k = 1)`];

    SUBGOAL_THEN `~(val(word (32 * (k4 - 1)):int64) = 0)` ASSUME_TAC THENL
     [VAL_INT64_TAC `32 * (k4 - 1)` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~(k4 = 0)`; `~(k4 = 1)`] THEN ARITH_TAC;
      ALL_TAC] THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_SUB] THEN
    ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    CONV_TAC WORD_RULE;

    ALL_TAC; (*** The main loop invariant preservation ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1];

    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
    ASM_REWRITE_TAC[] THEN

    REWRITE_TAC[LEFT_SUB_DISTRIB; WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `32 * 1 <= 32 * k4 <=> ~(k4 = 0)`] THEN
    SUBST1_TAC(SYM(ASSUME `4 * k4 = k`)) THEN CONV_TAC WORD_RULE] THEN

 (*** launch into the inner loop, but for simplicity localize our window ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `4 * i < k` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < k4`; `4 * k4 = k`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(k + 4) - 4 * (i + 1) = k - 4 * i`] THEN

  ABBREV_TAC `z':int64 = word_add z (word (32 * i))` THEN
  ABBREV_TAC `m':int64 = word_add m (word (32 * i))` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `4 * i + 4 = 4 * (i + 1)`] THEN
  ASM_REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * 4 * i)) = word_add z (word(32 * i))`] THEN

  SUBGOAL_THEN
   `ALL (nonoverlapping (z':int64,32))
        [(z,32); (z,8 * 4 * i); (m,8 * k); (word pc,0x400);
         (m',32); (word_add z (word (32 * (i + 1))),8 * (k - 4 * i))]`
  MP_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THENL
   [MAP_EVERY EXPAND_TAC ["z'"; "m'"] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE
       [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
        X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE [memory :> bytes (z',8 * 4)] ,,
      MAYCHANGE [NF; ZF; CF; VF]` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  GHOST_INTRO_TAC `g8:int64` `read X12` THEN
  GHOST_INTRO_TAC `g9:int64` `read X13` THEN
  GHOST_INTRO_TAC `g10:int64` `read X14` THEN
  GHOST_INTRO_TAC `g11:int64` `read X15` THEN
  GHOST_INTRO_TAC `zlo:num` `bignum_from_memory (z,4 * i)` THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  ABBREV_TAC `z'':int64 = word_add z (word (32 * (i + 1)))` THEN

  SUBGOAL_THEN
   `bignum_from_memory(z'',k - 4 * i) s0 = highdigits a (4 * (i + 1))`
  MP_TAC THENL
   [EXPAND_TAC "z''" THEN REWRITE_TAC[WORD_RULE
     `word_add z (word (32 * (i + 1))) =
      word_add (word_add z (word(8 * 4 * i))) (word(8 * 4))`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * i = 32 * i`] THEN
    SUBGOAL_THEN `k - 4 * i = ((k + 4) - 4 * i) - 4` SUBST1_TAC THENL
     [UNDISCH_TAC `4 * i < k` THEN ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV]] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_TAC] THEN

  SUBGOAL_THEN
   `(!j. j < 4
         ==> bigdigit (bignum_from_memory(z,4) s0) j = bigdigit q j) /\
    (!j. j < 4
         ==> bigdigit
              (bignum_from_memory(z',((k + 4) - 4 * i)) s0) j =
             bigdigit a (4 * i + j)) /\
    (!j. j < 4
         ==> bigdigit (highdigits (bignum_from_memory(m,k) s0) (4 * i)) j =
             bigdigit n (4 * i + j))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_HIGHDIGITS];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [HIGHDIGITS_BIGNUM_FROM_MEMORY; BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
  SUBGOAL_THEN `!j. j < 4 ==> j < (k + 4) - 4 * i /\ j < k - 4 * i`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < k4`; `4 * k4 = k`] THEN ARITH_TAC;
    SIMP_TAC[]] THEN
  DISCH_THEN(K ALL_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [BIGDIGIT_HIGHDIGITS; VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * i = 32 * i`] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ADD_CLAUSES; WORD_ADD_0] THEN
  STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 32)) (word 32) = x`]) THEN

  ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC
   ((5--8) @ [10;12;14;16;18;19] @ (21--42) @
    [48;53;55;56;62;67] @ (69--74) @
    [80;85;87;88;89] @
    [95;100;102;103;104;105;106] @
    [112;117;119;120;121;122] @
    [128;133;135;136;137;138])
   (3--142) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_add z (word (32 * (i + 1))):int64 = z''`)) THEN
    SUBST1_TAC(SYM(ASSUME `word_add z (word (32 * i)):int64 = z'`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_add m (word (32 * i)):int64 = m'`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word(32 * x)) (word 32) =
      word_mul (word 32) (word_sub (word x) (word 1))`] THEN
    REWRITE_TAC[WORD_MUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
    DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    VAL_INT64_TAC `32 * (k4 - (i + 1))` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`i:num < k4`; `4 * k4 = k`] THEN ARITH_TAC] THEN

  DISCH_THEN(fun th ->
   REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
   ASSUME_TAC th) THEN

  SUBST1_TAC(ARITH_RULE `32 * i = 8 * 4 * i`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [ADD_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o TOP_DEPTH_CONV)
   [ADD_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV
   [ARITH_RULE `(q * (x1 + l1) + (x2 + l2)) + q =
                (x1 * q + x2) + (q * l1 + l2 + q)`] THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB;
              EXP_ADD; GSYM MULT_ASSOC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN AP_TERM_TAC THEN
  UNDISCH_TAC `read (memory :> bytes (z,8 * 4)) s142 = q` THEN
  CONV_TAC(LAND_CONV(LAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bignum_of_wordlist] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN

  ONCE_REWRITE_TAC[GSYM VAL_WORD_BIGDIGIT] THEN REWRITE_TAC[WORD_VAL] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN

  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN

  FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VAL_WORD_BIGDIGIT; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_EMONTREDC_8N_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALLPAIRS nonoverlapping
         [(z,8 * 2 * val k); (word_sub stackpointer (word 80),80)]
         [(word pc,0x400); (m,8 * val k)] /\
        nonoverlapping (z,8 * 2 * val k)
                       (word_sub stackpointer (word 80),80) /\
        8 divides val k
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_8n_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
             MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                    memory :> bytes(word_sub stackpointer (word 80),80)])`,
  ARM_ADD_RETURN_STACK_TAC
    BIGNUM_EMONTREDC_8N_EXEC BIGNUM_EMONTREDC_8N_CORRECT
   `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28]` 80);;
