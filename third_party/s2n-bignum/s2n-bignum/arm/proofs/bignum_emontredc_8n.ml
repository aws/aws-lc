(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum.                        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

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
  0xd10083ff;       (* arm_SUB SP SP (rvalue (word 32)) *)
  0xd342fc00;       (* arm_LSR X0 X0 2 *)
  0xaa0003fa;       (* arm_MOV X26 X0 *)
  0xf100040c;       (* arm_SUBS X12 X0 (rvalue (word 1)) *)
  0x54006a63;       (* arm_BCC (word 3404) *)
  0xa9007fe3;       (* arm_STP X3 XZR SP (Immediate_Offset (iword (&0))) *)
  0xa9017ffa;       (* arm_STP X26 XZR SP (Immediate_Offset (iword (&16))) *)
  0xaa1f03fc;       (* arm_MOV X28 XZR *)
  0xd37be980;       (* arm_LSL X0 X12 5 *)
  0xa9407fe3;       (* arm_LDP X3 XZR SP (Immediate_Offset (iword (&0))) *)
  0xa9404c31;       (* arm_LDP X17 X19 X1 (Immediate_Offset (iword (&0))) *)
  0xa9415434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0x3dc00455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 16)) *)
  0x9b037e24;       (* arm_MUL X4 X17 X3 *)
  0x4e080c80;       (* arm_DUP_GEN Q0 X4 *)
  0x4e805aa3;       (* arm_UZP2 Q3 Q21 Q0 32 *)
  0x0ea12804;       (* arm_XTN Q4 Q0 32 *)
  0x0ea12aa5;       (* arm_XTN Q5 Q21 32 *)
  0x9b087c8c;       (* arm_MUL X12 X4 X8 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0x9bc87c8c;       (* arm_UMULH X12 X4 X8 *)
  0x9b097c8d;       (* arm_MUL X13 X4 X9 *)
  0x4ea00aa1;       (* arm_REV64_VEC Q1 Q21 32 *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0x2ea3c087;       (* arm_UMULL_VEC Q7 Q4 Q3 32 *)
  0x4e805810;       (* arm_UZP2 Q16 Q0 Q0 32 *)
  0x4ea09c20;       (* arm_MUL_VEC Q0 Q1 Q0 32 *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x2ea3c201;       (* arm_UMULL_VEC Q1 Q16 Q3 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0x4e221ce2;       (* arm_AND_VEC Q2 Q7 Q2 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f605400;       (* arm_SHL_VEC Q0 Q0 32 64 *)
  0x6f6014e1;       (* arm_USRA_VEC Q1 Q7 32 64 128 *)
  0x2ea58080;       (* arm_UMLAL_VEC Q0 Q4 Q5 32 *)
  0x4e083c0e;       (* arm_UMOV X14 Q0 0 8 *)
  0x4e183c0f;       (* arm_UMOV X15 Q0 1 8 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x9bc97c8d;       (* arm_UMULH X13 X4 X9 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x6f601441;       (* arm_USRA_VEC Q1 Q2 32 64 128 *)
  0x4e083c2e;       (* arm_UMOV X14 Q1 0 8 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0x4e183c2f;       (* arm_UMOV X15 Q1 1 8 *)
  0x9a1f03f6;       (* arm_ADC X22 XZR XZR *)
  0xab0c0273;       (* arm_ADDS X19 X19 X12 *)
  0x9b037e65;       (* arm_MUL X5 X19 X3 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9a0f02d6;       (* arm_ADC X22 X22 X15 *)
  0x4e080ca0;       (* arm_DUP_GEN Q0 X5 *)
  0x4e805aa3;       (* arm_UZP2 Q3 Q21 Q0 32 *)
  0x0ea12804;       (* arm_XTN Q4 Q0 32 *)
  0x0ea12aa5;       (* arm_XTN Q5 Q21 32 *)
  0x9b087cac;       (* arm_MUL X12 X5 X8 *)
  0xab0c0273;       (* arm_ADDS X19 X19 X12 *)
  0x9bc87cac;       (* arm_UMULH X12 X5 X8 *)
  0x9b097cad;       (* arm_MUL X13 X5 X9 *)
  0x4ea00aa1;       (* arm_REV64_VEC Q1 Q21 32 *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0x2ea3c087;       (* arm_UMULL_VEC Q7 Q4 Q3 32 *)
  0x4e805810;       (* arm_UZP2 Q16 Q0 Q0 32 *)
  0x4ea09c20;       (* arm_MUL_VEC Q0 Q1 Q0 32 *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x2ea3c201;       (* arm_UMULL_VEC Q1 Q16 Q3 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0x4e221ce2;       (* arm_AND_VEC Q2 Q7 Q2 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f605400;       (* arm_SHL_VEC Q0 Q0 32 64 *)
  0x6f6014e1;       (* arm_USRA_VEC Q1 Q7 32 64 128 *)
  0x2ea58080;       (* arm_UMLAL_VEC Q0 Q4 Q5 32 *)
  0x4e083c0e;       (* arm_UMOV X14 Q0 0 8 *)
  0x4e183c0f;       (* arm_UMOV X15 Q0 1 8 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0x9bc97cad;       (* arm_UMULH X13 X5 X9 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x6f601441;       (* arm_USRA_VEC Q1 Q2 32 64 128 *)
  0x4e083c2e;       (* arm_UMOV X14 Q1 0 8 *)
  0xba0f02d6;       (* arm_ADCS X22 X22 X15 *)
  0x4e183c2f;       (* arm_UMOV X15 Q1 1 8 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0xab0c0294;       (* arm_ADDS X20 X20 X12 *)
  0x9b037e86;       (* arm_MUL X6 X20 X3 *)
  0x4e080cc0;       (* arm_DUP_GEN Q0 X6 *)
  0x4e955803;       (* arm_UZP2 Q3 Q0 Q21 32 *)
  0x0ea12aa4;       (* arm_XTN Q4 Q21 32 *)
  0x0ea12805;       (* arm_XTN Q5 Q0 32 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9a0f02f7;       (* arm_ADC X23 X23 X15 *)
  0xa9001424;       (* arm_STP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0x3dc00034;       (* arm_LDR Q20 X1 (Immediate_Offset (word 0)) *)
  0x3dc00856;       (* arm_LDR Q22 X2 (Immediate_Offset (word 32)) *)
  0x3dc00c57;       (* arm_LDR Q23 X2 (Immediate_Offset (word 48)) *)
  0x4ea00801;       (* arm_REV64_VEC Q1 Q0 32 *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0x2ea3c087;       (* arm_UMULL_VEC Q7 Q4 Q3 32 *)
  0x4e955ab0;       (* arm_UZP2 Q16 Q21 Q21 32 *)
  0x9b087ccc;       (* arm_MUL X12 X6 X8 *)
  0xab0c0294;       (* arm_ADDS X20 X20 X12 *)
  0x4eb59c20;       (* arm_MUL_VEC Q0 Q1 Q21 32 *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x2ea3c201;       (* arm_UMULL_VEC Q1 Q16 Q3 32 *)
  0x9bc87ccc;       (* arm_UMULH X12 X6 X8 *)
  0x9b097ccd;       (* arm_MUL X13 X6 X9 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0x4e221ce2;       (* arm_AND_VEC Q2 Q7 Q2 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f605400;       (* arm_SHL_VEC Q0 Q0 32 64 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0x9bc97ccd;       (* arm_UMULH X13 X6 X9 *)
  0x6f6014e1;       (* arm_USRA_VEC Q1 Q7 32 64 128 *)
  0x2ea58080;       (* arm_UMLAL_VEC Q0 Q4 Q5 32 *)
  0x4e083c0e;       (* arm_UMOV X14 Q0 0 8 *)
  0x4e183c0f;       (* arm_UMOV X15 Q0 1 8 *)
  0x6f601441;       (* arm_USRA_VEC Q1 Q2 32 64 128 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0xba0f02f7;       (* arm_ADCS X23 X23 X15 *)
  0x4e083c2e;       (* arm_UMOV X14 Q1 0 8 *)
  0x4e183c2f;       (* arm_UMOV X15 Q1 1 8 *)
  0x9a1f03f8;       (* arm_ADC X24 XZR XZR *)
  0xab0c02b5;       (* arm_ADDS X21 X21 X12 *)
  0x9b037ea7;       (* arm_MUL X7 X21 X3 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9a0f0318;       (* arm_ADC X24 X24 X15 *)
  0xa9011c26;       (* arm_STP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0x3dc00435;       (* arm_LDR Q21 X1 (Immediate_Offset (word 16)) *)
  0x4e945ac3;       (* arm_UZP2 Q3 Q22 Q20 32 *)
  0x0ea12a84;       (* arm_XTN Q4 Q20 32 *)
  0x9b087cec;       (* arm_MUL X12 X7 X8 *)
  0x9b097ced;       (* arm_MUL X13 X7 X9 *)
  0x0ea12ac5;       (* arm_XTN Q5 Q22 32 *)
  0x4ea00ac1;       (* arm_REV64_VEC Q1 Q22 32 *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0x2ea3c087;       (* arm_UMULL_VEC Q7 Q4 Q3 32 *)
  0x9b0a7cee;       (* arm_MUL X14 X7 X10 *)
  0x9b0b7cef;       (* arm_MUL X15 X7 X11 *)
  0x4e945a90;       (* arm_UZP2 Q16 Q20 Q20 32 *)
  0x4eb49c20;       (* arm_MUL_VEC Q0 Q1 Q20 32 *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x2ea3c219;       (* arm_UMULL_VEC Q25 Q16 Q3 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0x4e221ce2;       (* arm_AND_VEC Q2 Q7 Q2 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0xab0c02b5;       (* arm_ADDS X21 X21 X12 *)
  0x9bc87cec;       (* arm_UMULH X12 X7 X8 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0x9bc97ced;       (* arm_UMULH X13 X7 X9 *)
  0x4f605418;       (* arm_SHL_VEC Q24 Q0 32 64 *)
  0x6f6014f9;       (* arm_USRA_VEC Q25 Q7 32 64 128 *)
  0x2ea58098;       (* arm_UMLAL_VEC Q24 Q4 Q5 32 *)
  0x6f601459;       (* arm_USRA_VEC Q25 Q2 32 64 128 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bca7cee;       (* arm_UMULH X14 X7 X10 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0x9bcb7cef;       (* arm_UMULH X15 X7 X11 *)
  0x4e955ae3;       (* arm_UZP2 Q3 Q23 Q21 32 *)
  0x0ea12aa4;       (* arm_XTN Q4 Q21 32 *)
  0x0ea12ae5;       (* arm_XTN Q5 Q23 32 *)
  0x4ea00ae1;       (* arm_REV64_VEC Q1 Q23 32 *)
  0xa9422448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&32))) *)
  0xa9432c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&48))) *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0x2ea3c087;       (* arm_UMULL_VEC Q7 Q4 Q3 32 *)
  0x4e955ab0;       (* arm_UZP2 Q16 Q21 Q21 32 *)
  0x4eb59c20;       (* arm_MUL_VEC Q0 Q1 Q21 32 *)
  0x9a1f03f9;       (* arm_ADC X25 XZR XZR *)
  0xab0c02cc;       (* arm_ADDS X12 X22 X12 *)
  0xba0d02ed;       (* arm_ADCS X13 X23 X13 *)
  0xba0e030e;       (* arm_ADCS X14 X24 X14 *)
  0x9a0f032f;       (* arm_ADC X15 X25 X15 *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x2ea3c21b;       (* arm_UMULL_VEC Q27 Q16 Q3 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0x4e221ce2;       (* arm_AND_VEC Q2 Q7 Q2 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f60541a;       (* arm_SHL_VEC Q26 Q0 32 64 *)
  0x6f6014fb;       (* arm_USRA_VEC Q27 Q7 32 64 128 *)
  0x2ea5809a;       (* arm_UMLAL_VEC Q26 Q4 Q5 32 *)
  0x6f60145b;       (* arm_USRA_VEC Q27 Q2 32 64 128 *)
  0xb4005120;       (* arm_CBZ X0 (word 2596) *)
  0xaa0003fb;       (* arm_MOV X27 X0 *)
  0xf100801f;       (* arm_CMP X0 (rvalue (word 32)) *)
  0x540011c1;       (* arm_BNE (word 568) *)
  0x91008042;       (* arm_ADD X2 X2 (rvalue (word 32)) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
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
  0xd100837b;       (* arm_SUB X27 X27 (rvalue (word 32)) *)
  0x140001f9;       (* arm_B (word 2020) *)
  0x4e083f30;       (* arm_UMOV X16 Q25 0 8 *)
  0x4e183f16;       (* arm_UMOV X22 Q24 1 8 *)
  0x4e183f34;       (* arm_UMOV X20 Q25 1 8 *)
  0x4e083f57;       (* arm_UMOV X23 Q26 0 8 *)
  0x4e083f75;       (* arm_UMOV X21 Q27 0 8 *)
  0x4e183f58;       (* arm_UMOV X24 Q26 1 8 *)
  0x4e183f63;       (* arm_UMOV X3 Q27 1 8 *)
  0x4e083f11;       (* arm_UMOV X17 Q24 0 8 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0xba1402f7;       (* arm_ADCS X23 X23 X20 *)
  0xba150318;       (* arm_ADCS X24 X24 X21 *)
  0x9a1f0079;       (* arm_ADC X25 X3 XZR *)
  0x3dc01056;       (* arm_LDR Q22 X2 (Immediate_Offset (word 64)) *)
  0x3dc01457;       (* arm_LDR Q23 X2 (Immediate_Offset (word 80)) *)
  0x91008042;       (* arm_ADD X2 X2 (rvalue (word 32)) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0x4e945ac3;       (* arm_UZP2 Q3 Q22 Q20 32 *)
  0x0ea12a84;       (* arm_XTN Q4 Q20 32 *)
  0x0ea12ac5;       (* arm_XTN Q5 Q22 32 *)
  0x4ea00ac1;       (* arm_REV64_VEC Q1 Q22 32 *)
  0xa9405434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&0))) *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xa9415434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0x2ea3c087;       (* arm_UMULL_VEC Q7 Q4 Q3 32 *)
  0x4e945a90;       (* arm_UZP2 Q16 Q20 Q20 32 *)
  0x4eb49c20;       (* arm_MUL_VEC Q0 Q1 Q20 32 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0x9a1f03f0;       (* arm_ADC X16 XZR XZR *)
  0xab1102d3;       (* arm_ADDS X19 X22 X17 *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x2ea3c219;       (* arm_UMULL_VEC Q25 Q16 Q3 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0xba1602f6;       (* arm_ADCS X22 X23 X22 *)
  0xba170317;       (* arm_ADCS X23 X24 X23 *)
  0xba180338;       (* arm_ADCS X24 X25 X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0x4e221ce2;       (* arm_AND_VEC Q2 Q7 Q2 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f605418;       (* arm_SHL_VEC Q24 Q0 32 64 *)
  0x6f6014f9;       (* arm_USRA_VEC Q25 Q7 32 64 128 *)
  0xab1102d4;       (* arm_ADDS X20 X22 X17 *)
  0xba1302f5;       (* arm_ADCS X21 X23 X19 *)
  0xba160316;       (* arm_ADCS X22 X24 X22 *)
  0xba170337;       (* arm_ADCS X23 X25 X23 *)
  0x2ea58098;       (* arm_UMLAL_VEC Q24 Q4 Q5 32 *)
  0x6f601459;       (* arm_USRA_VEC Q25 Q2 32 64 128 *)
  0xba1803f8;       (* arm_ADCS X24 XZR X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x4e955ae3;       (* arm_UZP2 Q3 Q23 Q21 32 *)
  0x0ea12aa4;       (* arm_XTN Q4 Q21 32 *)
  0x0ea12ae5;       (* arm_XTN Q5 Q23 32 *)
  0x4ea00ae1;       (* arm_REV64_VEC Q1 Q23 32 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0xba1002d6;       (* arm_ADCS X22 X22 X16 *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0x2ea3c087;       (* arm_UMULL_VEC Q7 Q4 Q3 32 *)
  0x4e955ab0;       (* arm_UZP2 Q16 Q21 Q21 32 *)
  0x4eb59c20;       (* arm_MUL_VEC Q0 Q1 Q21 32 *)
  0xba1f0318;       (* arm_ADCS X24 X24 XZR *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xeb0700cf;       (* arm_SUBS X15 X6 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x2ea3c21b;       (* arm_UMULL_VEC Q27 Q16 Q3 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb0a016d;       (* arm_SUBS X13 X11 X10 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x4e221ce2;       (* arm_AND_VEC Q2 Q7 Q2 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f60541a;       (* arm_SHL_VEC Q26 Q0 32 64 *)
  0x6f6014fb;       (* arm_USRA_VEC Q27 Q7 32 64 128 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0x2ea5809a;       (* arm_UMLAL_VEC Q26 Q4 Q5 32 *)
  0x6f60145b;       (* arm_USRA_VEC Q27 Q2 32 64 128 *)
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
  0xa9004c31;       (* arm_STP X17 X19 X1 (Immediate_Offset (iword (&0))) *)
  0x4e083f30;       (* arm_UMOV X16 Q25 0 8 *)
  0x4e083f7a;       (* arm_UMOV X26 Q27 0 8 *)
  0x4e183f23;       (* arm_UMOV X3 Q25 1 8 *)
  0x4e183f71;       (* arm_UMOV X17 Q27 1 8 *)
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
  0xa9015434;       (* arm_STP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0x4e183f14;       (* arm_UMOV X20 Q24 1 8 *)
  0x4e083f55;       (* arm_UMOV X21 Q26 0 8 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0c02ed;       (* arm_ADCS X13 X23 X12 *)
  0xba0c030e;       (* arm_ADCS X14 X24 X12 *)
  0x9a0c032f;       (* arm_ADC X15 X25 X12 *)
  0xaa1603ec;       (* arm_MOV X12 X22 *)
  0x4e183f58;       (* arm_UMOV X24 Q26 1 8 *)
  0xd100837b;       (* arm_SUB X27 X27 (rvalue (word 32)) *)
  0xf100837f;       (* arm_CMP X27 (rvalue (word 32)) *)
  0x540016e0;       (* arm_BEQ (word 732) *)
  0xa9422448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&32))) *)
  0xa9432c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&48))) *)
  0x3dc01056;       (* arm_LDR Q22 X2 (Immediate_Offset (word 64)) *)
  0x3dc01457;       (* arm_LDR Q23 X2 (Immediate_Offset (word 80)) *)
  0x91008042;       (* arm_ADD X2 X2 (rvalue (word 32)) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xab100296;       (* arm_ADDS X22 X20 X16 *)
  0xba0302b7;       (* arm_ADCS X23 X21 X3 *)
  0xba1a0318;       (* arm_ADCS X24 X24 X26 *)
  0x9a1f0239;       (* arm_ADC X25 X17 XZR *)
  0x4e083f11;       (* arm_UMOV X17 Q24 0 8 *)
  0x4e945ac3;       (* arm_UZP2 Q3 Q22 Q20 32 *)
  0x0ea12a84;       (* arm_XTN Q4 Q20 32 *)
  0x0ea12ac5;       (* arm_XTN Q5 Q22 32 *)
  0x4ea00ac1;       (* arm_REV64_VEC Q1 Q22 32 *)
  0xa9405434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&0))) *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xa9415434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0x2ea3c087;       (* arm_UMULL_VEC Q7 Q4 Q3 32 *)
  0x4e945a90;       (* arm_UZP2 Q16 Q20 Q20 32 *)
  0x4eb49c20;       (* arm_MUL_VEC Q0 Q1 Q20 32 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0x9a1f03f0;       (* arm_ADC X16 XZR XZR *)
  0xab1102d3;       (* arm_ADDS X19 X22 X17 *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x2ea3c219;       (* arm_UMULL_VEC Q25 Q16 Q3 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0xba1602f6;       (* arm_ADCS X22 X23 X22 *)
  0xba170317;       (* arm_ADCS X23 X24 X23 *)
  0xba180338;       (* arm_ADCS X24 X25 X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0x4e221ce2;       (* arm_AND_VEC Q2 Q7 Q2 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f605418;       (* arm_SHL_VEC Q24 Q0 32 64 *)
  0x6f6014f9;       (* arm_USRA_VEC Q25 Q7 32 64 128 *)
  0xab1102d4;       (* arm_ADDS X20 X22 X17 *)
  0xba1302f5;       (* arm_ADCS X21 X23 X19 *)
  0xba160316;       (* arm_ADCS X22 X24 X22 *)
  0xba170337;       (* arm_ADCS X23 X25 X23 *)
  0x2ea58098;       (* arm_UMLAL_VEC Q24 Q4 Q5 32 *)
  0x6f601459;       (* arm_USRA_VEC Q25 Q2 32 64 128 *)
  0xba1803f8;       (* arm_ADCS X24 XZR X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x4e955ae3;       (* arm_UZP2 Q3 Q23 Q21 32 *)
  0x0ea12aa4;       (* arm_XTN Q4 Q21 32 *)
  0x0ea12ae5;       (* arm_XTN Q5 Q23 32 *)
  0x4ea00ae1;       (* arm_REV64_VEC Q1 Q23 32 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0xba1002d6;       (* arm_ADCS X22 X22 X16 *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x2ea5c086;       (* arm_UMULL_VEC Q6 Q4 Q5 32 *)
  0x2ea3c087;       (* arm_UMULL_VEC Q7 Q4 Q3 32 *)
  0x4e955ab0;       (* arm_UZP2 Q16 Q21 Q21 32 *)
  0x4eb59c20;       (* arm_MUL_VEC Q0 Q1 Q21 32 *)
  0xba1f0318;       (* arm_ADCS X24 X24 XZR *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xeb0700cf;       (* arm_SUBS X15 X6 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x6f00e5e2;       (* arm_MOVI Q2 (word 4294967295) *)
  0x6f6014c7;       (* arm_USRA_VEC Q7 Q6 32 64 128 *)
  0x2ea3c21b;       (* arm_UMULL_VEC Q27 Q16 Q3 32 *)
  0x6ea02800;       (* arm_UADDLP Q0 Q0 32 *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb0a016d;       (* arm_SUBS X13 X11 X10 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x4e221ce2;       (* arm_AND_VEC Q2 Q7 Q2 128 *)
  0x2ea58202;       (* arm_UMLAL_VEC Q2 Q16 Q5 32 *)
  0x4f60541a;       (* arm_SHL_VEC Q26 Q0 32 64 *)
  0x6f6014fb;       (* arm_USRA_VEC Q27 Q7 32 64 128 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0x2ea5809a;       (* arm_UMLAL_VEC Q26 Q4 Q5 32 *)
  0x6f60145b;       (* arm_USRA_VEC Q27 Q2 32 64 128 *)
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
  0xa9004c31;       (* arm_STP X17 X19 X1 (Immediate_Offset (iword (&0))) *)
  0x4e083f30;       (* arm_UMOV X16 Q25 0 8 *)
  0x4e083f7a;       (* arm_UMOV X26 Q27 0 8 *)
  0x4e183f23;       (* arm_UMOV X3 Q25 1 8 *)
  0x4e183f71;       (* arm_UMOV X17 Q27 1 8 *)
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
  0xa9015434;       (* arm_STP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0x4e183f14;       (* arm_UMOV X20 Q24 1 8 *)
  0x4e083f55;       (* arm_UMOV X21 Q26 0 8 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0c02ed;       (* arm_ADCS X13 X23 X12 *)
  0xba0c030e;       (* arm_ADCS X14 X24 X12 *)
  0x9a0c032f;       (* arm_ADC X15 X25 X12 *)
  0xaa1603ec;       (* arm_MOV X12 X22 *)
  0x4e183f58;       (* arm_UMOV X24 Q26 1 8 *)
  0xd100837b;       (* arm_SUB X27 X27 (rvalue (word 32)) *)
  0xf100837f;       (* arm_CMP X27 (rvalue (word 32)) *)
  0x54ffe961;       (* arm_BNE (word 2096428) *)
  0xa9422448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&32))) *)
  0xa9432c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&48))) *)
  0x91008042;       (* arm_ADD X2 X2 (rvalue (word 32)) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xab100296;       (* arm_ADDS X22 X20 X16 *)
  0xba0302b7;       (* arm_ADCS X23 X21 X3 *)
  0xba1a0318;       (* arm_ADCS X24 X24 X26 *)
  0x9a1f0239;       (* arm_ADC X25 X17 XZR *)
  0x4e083f11;       (* arm_UMOV X17 Q24 0 8 *)
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
  0xf101037b;       (* arm_SUBS X27 X27 (rvalue (word 64)) *)
  0xa9424c31;       (* arm_LDP X17 X19 X1 (Immediate_Offset (iword (&32))) *)
  0xa9435434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&48))) *)
  0xa9417ffa;       (* arm_LDP X26 XZR SP (Immediate_Offset (iword (&16))) *)
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
  0xa9017ffa;       (* arm_STP X26 XZR SP (Immediate_Offset (iword (&16))) *)
  0x54ff9681;       (* arm_BNE (word 2093776) *)
  0xcb1c03e0;       (* arm_NEG X0 X28 *)
  0x910083ff;       (* arm_ADD SP SP (rvalue (word 32)) *)
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

(*** Load helpful lemmas and tactics for NEONs ***)

needs "arm/proofs/neon_helper.ml";;

(*** Define a few important definitions and useful functions ***)

let inner_loop_invariant =
  `\i s.  read X1 s = word_sub (word_add z (word(32 * i))) (word 32) /\
          read X2 s = word_sub (word_add m (word(32 * i))) (word 32) /\
          bignum_from_memory(m,k) s = n /\
          read X0 s = word (32 * (k4 - 1)) /\
          read SP s = word_sub stackpointer (word 32) /\
          read (memory :> bytes64 (word_sub stackpointer (word 32))) s = word w /\
          read (memory :>
            bytes64 (word_add (word_sub stackpointer (word 32)) (word 16))) s =
            wouter /\
          read X28 s = word_neg(word cout) /\
          bignum_from_memory (z,4) s = q /\
           read X4 s = word (bigdigit q 0) /\
           read X5 s = word (bigdigit q 1) /\
           read X6 s = word (bigdigit q 2) /\
           read X7 s = word (bigdigit q 3) /\
          bignum_from_memory (word_add z (word (8 * 4 * i)),
                                (k + 4) - 4 * i) s =
              highdigits a (4 * i) /\

          // induction variable
          read X27 s = word (32 * (k4 - i)) /\

          // two vector regs read during outerloop
          read Q20 s = word_join
            (word(bigdigit q 1):(64)word) (word(bigdigit q 0):(64)word) /\
          read Q21 s = word_join
            (word(bigdigit q 3):(64)word) (word(bigdigit q 2):(64)word) /\

          // pre-calculated multiplications
          read X16 s =
            word ((val (word (bigdigit q 0):(64)word) *
                   val (word (bigdigit n (4 * i)):(64)word)) DIV 2 EXP 64):(64)word /\ // hi of x4*x8
          read X26 s = word
            ((val (word (bigdigit q 2):(64)word) *
              val (word (bigdigit n (4 * i + 2)):(64)word)) DIV 2 EXP 64):(64)word /\ // hi of x6 * x10
          read X3 s  = word
            ((val (word (bigdigit q 1):(64)word) *
              val (word (bigdigit n (4 * i + 1)):(64)word)) DIV 2 EXP 64):(64)word /\ // hi of x5 * x9
          read X17 s = word
            ((val (word (bigdigit q 3):(64)word) *
              val (word (bigdigit n (4 * i + 3)):(64)word)) DIV 2 EXP 64):(64)word /\ // hi of x6 * x10
          read X20 s =
            word (0 + val (word (bigdigit q 1):(64)word)
                    * val (word (bigdigit n (4 * i + 1)):(64)word)):(64)word /\ // lo of x5 * x9
          read X21 s =
            word (0 + val (word (bigdigit q 2):(64)word)
                    * val (word (bigdigit n (4 * i + 2)):(64)word)):(64)word /\ // lo of x6 * x10
          read X24 s =
            word (0 + val (word (bigdigit q 3):(64)word)
                    * val (word (bigdigit n (4 * i + 3)):(64)word)):(64)word /\ // lo of x7 * x11
          read Q24 s = word_join
            (word (0 + val (word (bigdigit q 1):(64)word)
                     * val (word (bigdigit n (4 * i + 1)):(64)word)):(64)word)
            (word (0 + val (word (bigdigit q 0):(64)word)
                     * val (word (bigdigit n (4 * i)):(64)word)):(64)word) /\
          ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 4 * i) *
                bignum_of_wordlist
                [read X12 s; read X13 s; read X14 s; read X15 s] +
                bignum_from_memory(z,4 * i) s =
                q * lowdigits n (4 * i) + lowdigits a (4 * i) + q)`;;

let inner_loop_invariant_with_flag = mk_abs
  (`i:num`, mk_abs
    (`s:armstate`, mk_conj
      (snd (dest_abs (snd (dest_abs inner_loop_invariant))),
        `read ZF s <=> i = (k4-1)`)));;

(* Given f = \i. x, return x[n/i] *)
let apply_i f n = rhs (concl (BETA_CONV (mk_comb (f, n))));;

let get_hoare_precond (concl:term) =
  try
    let hoare_precond = rand(rator(rator(concl))) in
    hoare_precond
  with Failure _ ->
    failwith ("get_hoare_precond cannot understand " ^ string_of_term concl);;

(* Given a hoare condition that is
   `\s. aligned_bytes_loaded s (word pc) .._mc /\
       read PC s = ... /\
       BODY`,
   return `\s. BODY`. *)
let strip_mc_and_pc_conds (hoare_cond:term):term =
  let s,body = dest_abs hoare_cond in
  let aligned_load_mc, body = dest_conj body in
  let old_pc_eq, body = dest_conj body in
  let old_pc_eq_lhs, old_pc_eq_rhs = dest_eq old_pc_eq in
  if not (old_pc_eq_lhs = `read PC s`) then
    failwith ("Must be `read PC s = ...`, but got " ^ string_of_term old_pc_eq) else
  mk_abs(s, body);;

(* Given a hoare condition that is
   `\s. aligned_bytes_loaded s (word pc) .._mc /\
       read PC s = ... /\
       BODY`,
   return `\s. aligned_bytes_loaded s (word pc) .._mc /\
       read PC s = ... /\
       t /\ BODY`. *)
let mk_hoare_cond_conj (hoare_cond,t:term*term):term =
  let s,body = dest_abs hoare_cond in
  let aligned_load_mc, body = dest_conj body in
  let read_pc, body = dest_conj body in
  mk_abs(s, mk_conj(aligned_load_mc, mk_conj(read_pc, mk_conj(t, body))));;

(* A solver that targets conclusions like this:
    `2 EXP 256 * bignum_of_wordlist [sum_s179; sum_s180; sum_s181; sum_s182] +
    val sum_s53 +
    2 EXP 64 * val sum_s103 +
    2 EXP 128 * val sum_s141 +
    2 EXP 192 * val sum_s174 =
    (val (word (bigdigit q 0)) +
      2 EXP 64 * val (word (bigdigit q 1)) +
      2 EXP 128 * val (word (bigdigit q 2)) +
      2 EXP 192 * val (word (bigdigit q 3))) *
    (2 EXP (64 * 3) * bigdigit n 7 +
      2 EXP (64 * 2) * bigdigit n 6 +
      2 EXP (64 * 1) * bigdigit n 5 +
      bigdigit n 4) +
    2 EXP (64 * 3) * bigdigit a 7 +
    2 EXP (64 * 2) * bigdigit a 6 +
    2 EXP (64 * 1) * bigdigit a 5 +
    bigdigit a 4 +
    bignum_of_wordlist [g8; g9; g10; g11]` *)
let PROVE_IT = REWRITE_TAC[bignum_of_wordlist] THEN
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
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    (REAL_INTEGER_TAC ORELSE
      (PRINT_GOAL_TAC THEN
       FAIL_TAC "REAL_INTEGER failed"));;

let BIGNUM_EMONTREDC_8N_CORRECT = time prove
  (`!k z m w a n pc stackpointer.
        aligned 16 stackpointer /\
        ALLPAIRS nonoverlapping
          [(word pc,3468); (m,8 * val k)]
          [(z,8 * 2 * val k); (word_sub stackpointer (word 32), 32)] /\
        nonoverlapping (z,8 * 2 * val k) (word_sub stackpointer (word 32), 32) /\
        8 divides val k
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_8n_mc /\
                read PC s = word(pc + 0x14) /\
                read SP s = stackpointer /\
                C_ARGUMENTS [k; z; m; w] s /\
                bignum_from_memory (z,2 * val k) s = a /\
                bignum_from_memory (m,val k) s = n)
           (\s. read PC s = word(pc + 3444) /\
                ((n * val w + 1 == 0) (mod (2 EXP 64))
                 ==> n * bignum_from_memory (z,val k) s + a =
                     2 EXP (64 * val k) *
                     (2 EXP (64 * val k) * val(C_RETURN s) +
                      bignum_from_memory
                        (word_add z (word(8 * val k)),val k) s)))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
             MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`] THEN
  W64_GEN_TAC `w:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ABBREV_TAC `k4 = k DIV 4` THEN

  (*** Degenerate k/4 = 0 case ***)

  ASM_CASES_TAC `k4 = 0` THENL
   [UNDISCH_THEN `k4 = 0` SUBST_ALL_TAC THEN

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--5) THEN
    UNDISCH_TAC `read PC s5 =
      (if val (word_ushr (word k:(64)word) 2) < 1 then word (pc + 3440) else word (pc + 40))` THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`; ARITH_RULE `0 < 1`] THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC [861] THEN
    ENSURES_FINAL_STATE_TAC THEN
    UNDISCH_TAC `8 divides k` THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`;
                    DIVIDES_DIV_MULT; MULT_CLAUSES; ARITH_RULE `0 < 1`;
                    DIV_0; ARITH_RULE `k DIV 8 = k DIV 4 DIV 2`;
                    WORD_RULE `word_add (word_sub x y) y:(64)word = x`] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[ASSUME `k = 0`] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN

  (*** Restate things in terms of k' = k * k DIV 4 for naturalness ***)

  ABBREV_TAC `k' = 4 * k4` THEN
  ABBREV_TAC `a' = lowdigits a (2 * k')` THEN
  ABBREV_TAC `n' = lowdigits n k'` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x28`
   `\s. read X12 s = word(k4 - 1) /\
        read X26 s = word k4 /\
        read X1 s = z /\
        read X2 s = m /\
        read X3 s = word w /\
        read SP s = word_sub stackpointer (word 32) /\
        aligned 16 stackpointer /\
        bignum_from_memory (z,2 * k') s = a' /\
        bignum_from_memory (m,k') s = n'` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--5) THEN
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

  ENSURES_SEQUENCE_TAC `pc + 0xd74`
   `\s. ((n' * w + 1 == 0) (mod (2 EXP 64))
         ==> n' * bignum_from_memory (z,k') s + a' =
           2 EXP (64 * k') *
           (2 EXP (64 * k') * val(read X0 s) +
            bignum_from_memory (word_add z (word (8 * k')),k') s)) /\
        read SP s = stackpointer` THEN
  CONJ_TAC THENL
   [ALL_TAC;

    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
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
   `nonoverlapping (z,8 * 2 * k') (word pc,3468) /\
    nonoverlapping (z,8 * 2 * k') (m:int64,8 * k') /\
    nonoverlapping (word_sub stackpointer (word 32):int64, 32)
                   (m:int64, 8 * k') /\
    nonoverlapping (word_sub stackpointer (word 32):int64, 32)
                   (word pc, 3468) /\
    nonoverlapping (word_sub stackpointer (word 32):int64, 32)
                   (z:int64, 8 * 2 * k')`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN

  EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE [memory :> bytes (z,8 * 2 * k');
                 memory :> bytes(word_sub stackpointer (word 32),32)] ,,
      MAYCHANGE [SP]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  (* Show that 8 <= k *)
  RULE_ASSUM_TAC (REWRITE_RULE [DIVIDES_DIV_MULT]) THEN
  SUBGOAL_THEN `~(k4 = 1)` ASSUME_TAC THENL [
    DISCH_TAC THEN
    SUBST_ALL_TAC (ASSUME `k4 = 1`) THEN
    SUBGOAL_THEN `k DIV 8 = (k DIV 4) DIV 2` SUBST_ALL_TAC THENL
      [REWRITE_TAC[DIV_DIV; ARITH_RULE `4 * 2 = 8`]; ALL_TAC] THEN
    SUBGOAL_THEN `k DIV 4 DIV 2 * 8 = 0` SUBST_ALL_TAC THENL
      [REWRITE_TAC[ASSUME `k DIV 4 = 1`; ARITH_RULE `1 DIV 2 = 0`] THEN ARITH_TAC;
       ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `8 <= k'` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN

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

  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; GSYM SEQ_ASSOC] THEN
  ENSURES_WHILE_PUP_TAC `k4:num` `pc + 0x38` `pc + 0xd68`
   `\i s. (read X2 s = m /\
           bignum_from_memory (m,k) s = n /\
           read X0 s = word(32 * (k4 - 1)) /\
           read X1 s = word_add z (word(8 * 4 * i)) /\
           read SP s = word_sub stackpointer (word 32) /\
           read (memory :> bytes64 (word_add (word_sub stackpointer (word 32)) (word 16))) s = word (k4 - i) /\ // X26
           read (memory :> bytes64 (word_sub stackpointer (word 32))) s = word w /\ // X3
           aligned 16 stackpointer /\
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
  [ REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        HIGHDIGITS_BIGNUM_FROM_MEMORY) THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        LOWDIGITS_BIGNUM_FROM_MEMORY) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `MIN (2 * k) k = k /\ 2 * k - k = k`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_0; WORD_NEG_0] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; VAL_WORD_0; ADD_CLAUSES; EXP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; ARITH_RULE `2 * k - k = k`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC WORD_RULE;

    ALL_TAC; (*** This is the main loop invariant: save for later ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1];

    GHOST_INTRO_TAC `ncout:int64` `read X28` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--3) THEN CONJ_TAC THENL
    [ DISCH_TAC THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM MULT_2; WORD_SUB_LZERO] THEN
      REWRITE_TAC[MULT_SYM];
      CONV_TAC WORD_RULE
    ]
  ] THEN

  (*** Start on the main outer loop invariant, rebase at z + 32 * i = z' ***)

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

  ENSURES_SEQUENCE_TAC `pc + 0xd68`
   `\s. read X2 s = m /\
        bignum_from_memory (m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        (read ZF s <=> i + 1 = k4) /\
        read X1 s = word_add z' (word (8 * 4)) /\
        read SP s = word_sub stackpointer (word 32) /\
        read (memory :> bytes64 (word_add (word_sub stackpointer (word 32)) (word 16))) s = word (k4 - (i + 1)) /\ // X26
        read (memory :> bytes64 (word_sub stackpointer (word 32))) s = word w /\ // X3
        aligned 16 stackpointer /\
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
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28],,
    MAYCHANGE [memory :> bytes(z',8 * (k + 4))] ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 32),32)]` THEN
  (REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; GSYM SEQ_ASSOC]
   THEN CONJ_TAC) THENL
   [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (z':int64,8 * (k + 4)) (z,8 * 4 * i) /\
    nonoverlapping (z':int64,8 * (k + 4)) (word pc,3468) /\
    nonoverlapping (z':int64,8 * (k + 4)) (m,8 * k) /\
    nonoverlapping (z':int64,8 * (k + 4))
     (word_add z' (word (8 * (k + 4))),8 * (k - 4 * (i + 1))) /\
    nonoverlapping (word_sub stackpointer (word 32),32) (z,8 * 4 * i) /\
    nonoverlapping (word_sub stackpointer (word 32),32) (word pc,3468) /\
    nonoverlapping (word_sub stackpointer (word 32),32) (m,8 * k) /\
    nonoverlapping (word_sub stackpointer (word 32),32)
     (word_add z' (word (8 * (k + 4))),8 * (k - 4 * (i + 1))) /\
    nonoverlapping (word_sub stackpointer (word 32),32) (z':int64,8 * (k + 4))`
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

  ENSURES_SEQUENCE_TAC `pc + 0xd54`
   `\s. read X2 s = word_add m (word(32 * (k4 - 1))) /\
        bignum_from_memory (m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = word (k4 - i) /\
        read X1 s = word_add z' (word(32 * (k4 - 1))) /\
        read SP s = word_sub stackpointer (word 32) /\
        read (memory :> bytes64 (word_sub stackpointer (word 32))) s = word w /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             (2 EXP (64 * k) * val(word_neg (read X28 s)) +
              bignum_from_memory(word_add z' (word(8 * 4)),k) s) =
              bignum_from_memory(z',4) s * n +
              2 EXP (64 * k) * cout + z1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC (1--5)
    THEN REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      VAL_INT64_TAC `k4 - i:num` THEN ASM_REWRITE_TAC[VAL_WORD_1] THEN
      UNDISCH_TAC `i:num < k4` THEN ARITH_TAC;
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`]]] THEN

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

  ENSURES_SEQUENCE_TAC `pc + 0x304`
   `\s. read X2 s = m /\
        bignum_from_memory(m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X1 s = z /\
        read X28 s = word_neg(word cout) /\
        read SP s = word_sub stackpointer (word 32) /\
        read (memory :> bytes64 (word_sub stackpointer (word 32))) s = word w /\
        read (memory :> bytes64 (word_add
          (word_sub stackpointer (word 32)) (word 16))) s =
          wouter /\
        bignum_from_memory(word_add z (word (8 * 4)),k) s =
        highdigits a 4 /\
        read X4 s = word(bigdigit (bignum_from_memory(z,4) s) 0) /\
        read X5 s = word(bigdigit (bignum_from_memory(z,4) s) 1) /\
        read X6 s = word(bigdigit (bignum_from_memory(z,4) s) 2) /\
        read X7 s = word(bigdigit (bignum_from_memory(z,4) s) 3) /\
        read X8 s  = word(bigdigit n 4) /\
        read X9 s  = word(bigdigit n 5) /\
        read X10 s = word(bigdigit n 6) /\
        read X11 s = word(bigdigit n 7) /\
        read Q20 s = word_join
          (word(bigdigit (bignum_from_memory(z,4) s) 1):(64)word)
          (word(bigdigit (bignum_from_memory(z,4) s) 0):(64)word) /\
        read Q21 s = word_join
          (word(bigdigit (bignum_from_memory(z,4) s) 3):(64)word)
          (word(bigdigit (bignum_from_memory(z,4) s) 2):(64)word) /\
        read Q22 s = word_join
          (word(bigdigit n 5):(64)word) (word(bigdigit n 4):(64)word) /\
        read Q23 s = word_join
          (word(bigdigit n 7):(64)word) (word(bigdigit n 6):(64)word) /\
        read Q24 s = word_join
          (word(0 + val (word (bigdigit (bignum_from_memory(z,4) s) 1):(64)word) *
                    val (word (bigdigit n 5):(64)word)):(64)word)
          (word(0 + val (word (bigdigit (bignum_from_memory(z,4) s) 0):(64)word) *
                    val (word (bigdigit n 4):(64)word)):(64)word) /\
        read Q26 s = word_join
          (word(0 + val (word (bigdigit (bignum_from_memory(z,4) s) 3):(64)word) *
                    val (word (bigdigit n 7):(64)word)):(64)word)
          (word(0 + val (word (bigdigit (bignum_from_memory(z,4) s) 2):(64)word) *
                    val (word (bigdigit n 6):(64)word)):(64)word) /\
        read Q25 s = word_join
          (word((val (word (bigdigit (bignum_from_memory(z,4) s) 1):(64)word) *
                 val (word (bigdigit n 5):(64)word)) DIV 2 EXP 64):(64)word)
          (word((val (word (bigdigit (bignum_from_memory(z,4) s) 0):(64)word) *
                 val (word (bigdigit n 4):(64)word)) DIV 2 EXP 64):(64)word) /\
        read Q27 s = word_join
          (word((val (word (bigdigit (bignum_from_memory(z,4) s) 3):(64)word) *
                 val (word (bigdigit n 7):(64)word)) DIV 2 EXP 64):(64)word)
          (word((val (word (bigdigit (bignum_from_memory(z,4) s) 2):(64)word) *
                 val (word (bigdigit n 6):(64)word)) DIV 2 EXP 64):(64)word) /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             bignum_of_wordlist
              [read X12 s; read X13 s; read X14 s; read X15 s] =
             bignum_from_memory(z,4) s * lowdigits n 4 + lowdigits a 4)` THEN
  CONJ_TAC THENL
  [ REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
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
      (!i. i < 8
           ==> bigdigit (bignum_from_memory(m,k) s0) i = bigdigit n i)`
    MP_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    SUBGOAL_THEN `!i. i < 8 \/ i < 4 ==> i < k /\ i < k + 4` MP_TAC THENL
     [UNDISCH_TAC `8 <= k` THEN ARITH_TAC; SIMP_TAC[]] THEN
    DISCH_THEN(K ALL_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(BINOP_CONV EXPAND_CASES_CONV)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] THEN
    STRIP_TAC THEN

    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add m (word 16))) s0`
        `word (bigdigit n 3):(64)word` `word (bigdigit n 2):(64)word` THEN
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add m (word 32))) s0`
        `word (bigdigit n 5):(64)word` `word (bigdigit n 4):(64)word` THEN
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add m (word 48))) s0`
        `word (bigdigit n 7):(64)word` `word (bigdigit n 6):(64)word` THEN

    ARM_REWRITE_ASSUM_AND_XACCSTEPS_TAC2 BIGNUM_EMONTREDC_8N_EXEC
      [30;31;36;38;67;68;73;75] [WORD_MUL64_LO;WORD_MUL64_HI]
      (1--86) (1--86) [] THEN

    (* ldr of stp       x4, x5, [x1] *)
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 z) s86`
        `word (0 + val (sum_s40:(64)word) * w):(64)word`
        `word (0 + val (word (bigdigit a 0):(64)word) * w):(64)word` THEN
    (* ldr of ldp ... [x2, #32] *)
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add m (word 32):64 word)) s86`
        `word (bigdigit n 5):(64)word` `word (bigdigit n 4):(64)word` THEN
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add m (word 48):64 word)) s86`
        `word (bigdigit n 7):(64)word` `word (bigdigit n 6):(64)word` THEN

    ARM_REWRITE_ASSUM_AND_XACCSTEPS_TAC2 BIGNUM_EMONTREDC_8N_EXEC
      [110;111;115;116] [WORD_MUL64_LO;WORD_MUL64_HI]
      (87--123) (87--123) [] THEN

    (* ldr of stp       x6, x7, [x1, #16] *)
    BYTES128_EQ_JOIN64_TAC
        `read (memory :> bytes128 (word_add z (word 16):(64)word)) s123`
        `word (0 + val (sum_s118:(64)word) * w):(64)word`
        `word (0 + val (sum_s77:(64)word) * w):(64)word` THEN

    ARM_REWRITE_ASSUM_AND_XACCSTEPS_TAC2 BIGNUM_EMONTREDC_8N_EXEC
      [] [WORD_MUL64_LO;WORD_MUL64_HI]
      (124--179) (124--179) [] THEN

    RULE_ASSUM_TAC(REWRITE_RULE[WORD_MUL64_LO;WORD_MUL64_HI]) THEN
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

  ENSURES_SEQUENCE_TAC `pc + 0xd28`
   `\s. read X1 s = word_add z (word (32 * (k4 - 1))) /\
        read X2 s = word_add m (word (32 * (k4 - 1))) /\
        bignum_from_memory(m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read SP s = word_sub stackpointer (word 32) /\
        read (memory :> bytes64 (word_sub stackpointer (word 32))) s = word w /\
        read (memory :>
          bytes64 (word_add (word_sub stackpointer (word 32)) (word 16))) s =
          wouter /\
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
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE
       [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE [memory :> bytes (z',8 * 4)]` THEN
       REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    GSYM SEQ_ASSOC] THEN CONJ_TAC
       THENL
     [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      MAP_EVERY EXPAND_TAC ["z'"] THEN SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `nonoverlapping (z':int64,8 * 4) (word pc,3468) /\
      nonoverlapping (z':int64,8 * 4) (m,8 * k) /\
      nonoverlapping (z':int64,8 * 4) (z,8 * 4) /\
      nonoverlapping (z':int64,8 * 4) (z,8 * k) /\
      nonoverlapping (z':int64,8 * 4) ((word_sub stackpointer (word 32)),8 * 4)`
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

    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (5--8) (1--11) THEN
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
    SUBST1_TAC(SYM(ASSUME `read (memory :> bytes (z,8 * 4)) s11 = q`)) THEN
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
    REAL_ARITH_TAC
  ] THEN

  (*** The semi-degenerate case where we skip the inner loop ***)

  ASM_CASES_TAC `k4 = 1` THENL
   [UNDISCH_THEN `k4 = 1` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `4 * 1 = k ==> k = 4`)) THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN

  (***
    if (k4 = 2) {
      // straight-line code doing 256x256 mult for i = 1
      // (X27 = 32 * (2 - 1) = 32)
    } else {
      ... // straight-line code for i = 1
      for (i = 2 to k4 - 1) { .. }
      ... // straight-line code for i = k4
    }
   ***)

  ASM_CASES_TAC `k4 = 2` THENL [
    UNDISCH_THEN `k4 = 2` SUBST_ALL_TAC THEN
    SUBGOAL_THEN `k = 8` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `32 * (2 - 1) = 32`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `8 * (8 + 4) = 96`]) THEN
    (* Introduce variables storing the initial values of X12~X15 *)
    GHOST_INTRO_TAC `g8:int64` `read X12` THEN
    GHOST_INTRO_TAC `g9:int64` `read X13` THEN
    GHOST_INTRO_TAC `g10:int64` `read X14` THEN
    GHOST_INTRO_TAC `g11:int64` `read X15` THEN
    ENSURES_INIT_TAC "s0" THEN
    (* Prove [z+64..z+96] = a / 2^(64*8) from [z+32..z+96] = a / 2^(64*4). *)
    SUBGOAL_THEN
      `bignum_from_memory (word_add z (word (8 * 8)),4) s0 = highdigits a 8`
      MP_TAC THENL [
      REWRITE_TAC[WORD_RULE
        `(word_add z (word (8 * 8))) =
         (word_add (word_add z (word (8*4))) (word (8*4)))`] THEN
      REWRITE_TAC[ARITH_RULE`(_,4)=(_,8-4)` ; GSYM BIGNUM_FROM_MEMORY_DIV] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_TAC] THEN
    (* Prove that [z+32..z+64] and [z+64..z+96] are nonoverlapping *)
    SUBGOAL_THEN
        `nonoverlapping (word_add z (word 32):(64)word,32)
                        (word_add z (word 64):(64)word,32)`
      ASSUME_TAC THENL
      [REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
    (* Simplify 8*const to make nonoverlapping checks work *)
    SUBST_ALL_TAC (ARITH_RULE `8 * 8 = 64`) THEN
    SUBST_ALL_TAC (ARITH_RULE `8 * 4 = 32`) THEN

    (* Introduce byte64 version of read [z+32..z+96]. *)
    SUBGOAL_THEN
      `!j. j < 8
         ==> bigdigit (bignum_from_memory((word_add z (word 32)),8) s0) j =
             bigdigit a (4 + j)` MP_TAC THENL
      [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;ARITH_RULE`8*8=64`] THEN
       REWRITE_TAC[BIGDIGIT_HIGHDIGITS] THEN
       FAIL_TAC "unreachable";
       REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
       SIMP_TAC[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
       CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
       CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
       REWRITE_TAC [WORD_ADD_ASSOC_CONSTS] THEN
       CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV)] THEN
    STRIP_TAC THEN

    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--4) THEN
    (* jump to maddloop_x0one *)
    ARM_XACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC [`X1`; `X2`; `SP`]
      ((7--10) @ [12;14;16;18;20;21] @ (23--44) @
        [50;55;57;58;64;69] @ (71--76) @
        [82;87;89;90;91] @
        [97;102;104;105;106;107;108] @
        [114;119;121;122;123;124] @
        [130;135;137;138;139;140])
      (5--145) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    (* Discharge (n * w + 1 == 0) (mod (2 EXP 64)) and simplify an
       existing assumption using this *)
    DISCH_THEN(fun th ->
        REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
        ASSUME_TAC th) THEN
    (* Split `read (memory :> bytes (z,64)) s145` into high 32 and low 32 bytes.
       Low 32 bytes are simply q. *)
    SUBST1_TAC (ARITH_RULE `64 = 8 * 8`) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `(_,8)=(_,4+4)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE `8*4=32`] THEN

    (* Split high 32 bytes into 4 8-byte reads. *)
    REWRITE_TAC[ARITH_RULE `(_,32)=(_,8*4)`] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN

    (* Simplify .. + q = .. + q *)
    REWRITE_TAC[ARITH_RULE `p+q+x=r+s+x <=> p+q=r+s`] THEN

    (* Split lowdigits _ 8 into lowdigits _ 4 + ... *)
    ONCE_REWRITE_TAC[
      MP (SPECL [`n:num`; `8:num`] (GSYM LOWDIGITS_SELF))
         (ASSUME `n < 2 EXP (64 * 8)`)] THEN
    REWRITE_TAC[ARITH_RULE `lowdigits n 8 = lowdigits n ((((4+1)+1)+1)+1)`;
      LOWDIGITS_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ONCE_REWRITE_TAC[ARITH_RULE
      `q*(a0+a1+a2+a3+a4)+b0+b1+b2+b3+b4 =
       q*(a0+a1+a2+a3)+b0+b1+b2+b3+(q*a4+b4)`] THEN
    REWRITE_TAC[GSYM (ASSUME
      `2 EXP (64 * 4) * bignum_of_wordlist [g8; g9; g10; g11] =
       q * lowdigits n 4 + lowdigits a 4`)] THEN
    DISCARD_MATCHING_ASSUMPTIONS [
      `2 EXP (64 * 4) * bignum_of_wordlist [g8; g9; g10; g11] =
       q * lowdigits n 4 + lowdigits a 4`] THEN

    (* Expand q *)
    SUBGOAL_THEN
        `q = val(word(bigdigit q 0):(64)word)
              + 2 EXP 64 * val(word(bigdigit q 1):(64)word)
              + 2 EXP 128 * val(word(bigdigit q 2):(64)word)
              + 2 EXP 192 * val(word(bigdigit q 3):(64)word)`
        (fun thm -> ONCE_REWRITE_TAC [thm]) THENL [
      EXPAND_TAC "q" THEN
      REWRITE_TAC[ARITH_RULE `32=8*4`] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
          [GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY; ARITH_RULE `0<4/\1<4/\2<4/\3<4`;
                  WORD_VAL] THEN
      CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
      FAIL_TAC "unreachable";

      ALL_TAC] THEN

    (* Divide by 2 EXP 256 *)
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC[ARITH_RULE
      `2 EXP(64*7)*a0+2 EXP(64*6)*a1+2 EXP(64*5)*a2+2 EXP(64*4)*a3 =
       2 EXP(64*4)*(2 EXP(64*3)*a0+2 EXP(64*2)*a1+2 EXP(64*1)*a2+a3)`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 512 * a = 2 EXP (64*4) * 2 EXP 256 * a`] THEN
    REWRITE_TAC [ARITH_RULE `a * 2 EXP (64*4) * b = 2 EXP (64*4) * a * b`] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; EQ_MULT_LCANCEL;
      ARITH_RULE `~(2 EXP (64*4) = 0)`] THEN

    (* Prove it! *)
    PROVE_IT;

    ALL_TAC] THEN

  (* Jump to maddloop_neon_firstitr *)
  (fun (asl,concl) -> ENSURES_SEQUENCE_TAC `pc + 0x548`
      (strip_mc_and_pc_conds (mk_hoare_cond_conj
        (get_hoare_precond concl, `read X27 s = word (32 * (k4 - 1))`))) (asl,concl))
      THEN CONJ_TAC THENL [
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--1) THEN
    SUBGOAL_THEN `val (word (32 * (k4 - 1)):(64)word) = 0 <=> F`
        SUBST_ALL_TAC THENL
      [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN
       DISCARD_MATCHING_ASSUMPTIONS
          [`read a b = c`; `nonoverlapping_modulo x y z`;
          `bignum_from_memory a b = c`] THEN
       ASM_ARITH_TAC;
       ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [COND_CLAUSES]) THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (2--4) THEN
    SUBGOAL_THEN `val (word_sub (word (32 * (k4 - 1))) (word 32):(64)word) = 0
                    <=> F`
        SUBST_ALL_TAC THENL [
      REWRITE_TAC[VAL_WORD_SUB] THEN
      REWRITE_TAC[DIMINDEX_64; VAL_WORD] THEN
      REWRITE_TAC[ARITH_RULE `32 MOD 2 EXP 64 = 32`] THEN
      DISCARD_MATCHING_ASSUMPTIONS
        [`read a b = c`; `nonoverlapping_modulo x y z`;
         `bignum_from_memory a b = c`] THEN
      SUBGOAL_THEN `(32 * (k4 - 1)) MOD 2 EXP 64 = 32 * (k4 - 1)`
          SUBST_ALL_TAC THENL [
        IMP_REWRITE_TAC[MOD_LT] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
        `32 * (k4 - 1) + 2 EXP 64 - 32 = (32 * (k4 - 1) - 32) + 2 EXP 64`
          SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[CONJUNCT1 (SPECL
          [`32 * (k4 - 1) - 32:num`; `2 EXP 64:num`; `2 EXP 64`]
          (GSYM ADD_MOD_MOD_REFL));
          MOD_REFL; ADD_CLAUSES] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN
      ASM_ARITH_TAC;

      ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_CLAUSES]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    ALL_TAC] THEN


  (* maddloop_neon_firstitr *)
  ENSURES_SEQUENCE_TAC `pc + 0x82c` (apply_i inner_loop_invariant `2:num`)
      THEN CONJ_TAC THENL [
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    GHOST_INTRO_TAC `g8:int64` `read X12` THEN
    GHOST_INTRO_TAC `g9:int64` `read X13` THEN
    GHOST_INTRO_TAC `g10:int64` `read X14` THEN
    GHOST_INTRO_TAC `g11:int64` `read X15` THEN
    ENSURES_INIT_TAC "s0" THEN

    (* read bytes64 & bytes128 of ldr q [m + 64 ~ m + 96) *)
    (* This is for (13--14) *)
    SUBGOAL_THEN `!j. j < 4
         ==> bigdigit (bignum_from_memory(m,k) s0) (8 + j) =
             bigdigit n (8 + j)` MP_TAC THENL[
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        FAIL_TAC "unreachable";

      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      SUBGOAL_THEN `8 + 0 < k <=> T` SUBST_ALL_TAC THENL
        [DISCARD_MATCHING_ASSUMPTIONS [`read`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `8 + 1 < k <=> T` SUBST_ALL_TAC THENL
        [DISCARD_MATCHING_ASSUMPTIONS [`read`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `8 + 2 < k <=> T` SUBST_ALL_TAC THENL
        [DISCARD_MATCHING_ASSUMPTIONS [`read`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `8 + 3 < k <=> T` SUBST_ALL_TAC THENL
        [DISCARD_MATCHING_ASSUMPTIONS [`read`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[COND_CLAUSES] THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
         [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; AND_CLAUSES] THEN
      CONV_TAC (LAND_CONV NUM_REDUCE_CONV) THEN
      STRIP_TAC] THEN
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add m (word 64))) s0`
      `word (bigdigit n 9):(64)word`
      `word (bigdigit n 8):(64)word` THEN
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add m (word 80))) s0`
      `word (bigdigit n 11):(64)word`
      `word (bigdigit n 10):(64)word` THEN

    (* ldp   [z + 32 ~ z + 64) *)
    SUBGOAL_THEN `!j. j < 4
         ==> bigdigit (bignum_from_memory(word_add z (word 32),k) s0) j =
             bigdigit a (4 + j)` MP_TAC THENL [
      RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `8*4 = 32`]) THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BIGDIGIT_HIGHDIGITS] THEN
      FAIL_TAC "unreachable";

      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      SUBGOAL_THEN `0 < k <=> T` SUBST_ALL_TAC THENL
        [DISCARD_MATCHING_ASSUMPTIONS [`read`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `1 < k <=> T` SUBST_ALL_TAC THENL
        [DISCARD_MATCHING_ASSUMPTIONS [`read`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `2 < k <=> T` SUBST_ALL_TAC THENL
        [DISCARD_MATCHING_ASSUMPTIONS [`read`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `3 < k <=> T` SUBST_ALL_TAC THENL
        [DISCARD_MATCHING_ASSUMPTIONS [`read`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[COND_CLAUSES] THEN
        GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
           [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; AND_CLAUSES;
            WORD_ADD_ASSOC_CONSTS] THEN
      CONV_TAC (LAND_CONV NUM_REDUCE_CONV) THEN
      STRIP_TAC] THEN

    (* from assumption
             bignum_from_memory (word_add z (word (8 * 4)),k) s = highdigits a 4,
       make
             bignum_from_memory (word_add z (word (8 * 4 * 2)),(k + 4) - 4 * 2) s =
             highdigits a (4 * 2)
    *)
    SUBGOAL_THEN
          `bignum_from_memory (word_add z (word 64),k - 4) s0 = highdigits a 8`
        MP_TAC THENL [
      REWRITE_TAC[WORD_RULE
        `(word_add z (word 64)) =
         (word_add (word_add z (word (8*4))) (word (8*4)))`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_TAC] THEN

    (* For nonoverlapping reasoning *)
    SUBST_ALL_TAC (ARITH_RULE `8 * 4 = 32`) THEN
    (* Prove that [z+32..z+64] and [z+64..] are nonoverlapping *)
    SUBGOAL_THEN
        `nonoverlapping (word_add z (word 32):(64)word,32)
                        (word_add z (word 64):(64)word,8 * (k-4))`
      ASSUME_TAC THENL
      [REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

    ARM_REWRITE_ASSUM_AND_XACCSTEPS_TAC2 BIGNUM_EMONTREDC_8N_EXEC
      ((1--8) @ (112--115) @ [176;177;183;184])
      [WORD_MUL64_LO;WORD_MUL64_HI]
      ([2;4;6;8] @ (9--12) @ [22;23] @ (29--32) @ (37--40) @ (45--48) @ (51--54) @ (59--62)
                @ [67;68] @
                [78;89;91;92] @
                [98;103;105;106;107;108;109;110] @
                [121;126;128;129;130] @
                [136;141;143;144;145;146;147] @
                [153;158;160;161;162;163] @
                [169;174;179;180;181;182]) (1--185) [`X1`; `X2`] THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[
          ARITH_RULE `4 * 2 = 8`;
          ARITH_RULE `4 * 2 + 1 = 9`;
          ARITH_RULE `4 * 2 + 2 = 10`;
          ARITH_RULE `4 * 2 + 3 = 11`] THEN
    SUBGOAL_THEN `word_sub (word (32 * (k4 - 1))) (word 32):(64)word = word (32 * (k4 - 2))`
        SUBST_ALL_TAC THENL [
          REWRITE_TAC[ARITH_RULE `32 * (k4-2) = 32*(k4-1)-32`; WORD_SUB] THEN
          IMP_REWRITE_TAC[TAUT `(c <=> T) ==> (if c then t1 else t2) = t1`] THEN
          DISCARD_NONMATCHING_ASSUMPTIONS
          [`8 <= k`; `4 * k4 = k`] THEN ASM_ARITH_TAC;

          ALL_TAC
        ] THEN
    REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS; WORD_RULE
        `word_sub (word_add p (word (32*2):(64)word)) (word 32) =
         word_add p (word 32)`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `4*2=8`; ARITH_RULE `8*8=64`;
        ARITH_RULE `8 * ((k + 4) - 8) = 8 * (k-4)`] THEN

    (* Now the conclusion is (n * w + 1 == 0) (mod (2 EXP 64)) ==> ... . *)
    (* Discharge (n * w + 1 == 0) (mod (2 EXP 64)) and simplify an
       existing assumption using this *)
    DISCH_THEN(fun th ->
        REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
        ASSUME_TAC th) THEN
    (* Split `read (memory :> bytes (z,64)) s185` into high 32 and low 32 bytes.
       Low 32 bytes are simply q. *)
    SUBGOAL_THEN `read (memory :> bytes (z,64)) s185 =
        2 EXP (64 * 4) * bignum_from_memory (word_add z (word (8 * 4)),4) s185 +
        q` (fun thm -> ONCE_REWRITE_TAC [thm]) THENL [
      SUBST1_TAC (ARITH_RULE `64 = 8 * 8`) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[ARITH_RULE `(_,8)=(_,4+4)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ARITH_RULE `8*8=64`; ARITH_RULE `8*4=32`]
      THEN FAIL_TAC "unreachable";

      ALL_TAC] THEN

    (* Split high 32 bytes into 4 8-byte reads. *)
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC (map ARITH_RULE [`8*4=32`;`8*4+8=40`;`8*4+16=48`;`8*4+24=56`]) THEN

    (* Simplify .. + q = .. + q *)
    REWRITE_TAC[ARITH_RULE `p+q+x=r+s+x <=> p+q=r+s`] THEN

    (* Split lowdigits _ 8 into lowdigits _ 4 + ... *)
    REWRITE_TAC[ARITH_RULE `lowdigits n 8 = lowdigits n ((((4+1)+1)+1)+1)`;
        LOWDIGITS_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ONCE_REWRITE_TAC[ARITH_RULE
        `q*(a0+a1+a2+a3+a4)+b0+b1+b2+b3+b4 =
        q*(a0+a1+a2+a3)+b0+b1+b2+b3+(q*a4+b4)`] THEN
    REWRITE_TAC[GSYM (ASSUME
        `2 EXP (64 * 4) * bignum_of_wordlist [g8; g9; g10; g11] =
        q * lowdigits n 4 + lowdigits a 4`)] THEN
    DISCARD_MATCHING_ASSUMPTIONS [
        `2 EXP (64 * 4) * bignum_of_wordlist [g8; g9; g10; g11] =
        q * lowdigits n 4 + lowdigits a 4`] THEN

    (* Expand q *)
    SUBGOAL_THEN
        `q = val(word(bigdigit q 0):(64)word)
              + 2 EXP 64 * val(word(bigdigit q 1):(64)word)
              + 2 EXP 128 * val(word(bigdigit q 2):(64)word)
              + 2 EXP 192 * val(word(bigdigit q 3):(64)word)`
        (fun thm -> ONCE_REWRITE_TAC [thm]) THENL [
      EXPAND_TAC "q" THEN
      REWRITE_TAC[ARITH_RULE `32=8*4`] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
          [GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY; ARITH_RULE `0<4/\1<4/\2<4/\3<4`;
                  WORD_VAL] THEN
      CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
      FAIL_TAC "unreachable";

      ALL_TAC] THEN

    (* Divide by 2 EXP 256 *)
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC[ARITH_RULE
      `2 EXP(64*7)*a0+2 EXP(64*6)*a1+2 EXP(64*5)*a2+2 EXP(64*4)*a3 =
       2 EXP(64*4)*(2 EXP(64*3)*a0+2 EXP(64*2)*a1+2 EXP(64*1)*a2+a3)`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP (64*8) * a = 2 EXP (64*4) * 2 EXP 256 * a`] THEN
    REWRITE_TAC [ARITH_RULE `a * 2 EXP (64*4) * b = 2 EXP (64*4) * a * b`] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; EQ_MULT_LCANCEL;
      ARITH_RULE `~(2 EXP (64*4) = 0)`] THEN

    (* Prove it! *)
    PROVE_IT;

    ALL_TAC] THEN

  (* Simulate maddloop_neon_last ~ end first. *)
  ENSURES_SEQUENCE_TAC `pc + 0xb0c` (apply_i inner_loop_invariant `k4-1:num`)
      THEN CONJ_TAC THENL [
    (* 0x82c ~ 0xb0c*)
    ALL_TAC;

    (* 0xb0c ~ 0xd28 *)
    (* Use z' and m' because nonoverlapping tactic sometimes doesn't solve (z+e,z+e') *)
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_RULE `word_add z (word (8 * 4 * (k-1))) = word_add z (word(32 * (k-1)))`] THEN
    ABBREV_TAC `z':int64 = word_add z (word (32 * (k4-1)))` THEN
    ABBREV_TAC `m':int64 = word_add m (word (32 * (k4-1)))` THEN

    SUBGOAL_THEN `4 * (k4-1) < k` ASSUME_TAC THENL
      [MAP_EVERY UNDISCH_TAC [`~(k=0)`; `4 * k4 = k`] THEN ARITH_TAC; ALL_TAC] THEN
    GHOST_INTRO_TAC `g8:int64` `read X12` THEN
    GHOST_INTRO_TAC `g9:int64` `read X13` THEN
    GHOST_INTRO_TAC `g10:int64` `read X14` THEN
    GHOST_INTRO_TAC `g11:int64` `read X15` THEN

    (* Shrink the window of maychange z *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
      `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28],,
        MAYCHANGE [memory :> bytes(z',32)] ,,
        MAYCHANGE [memory :> bytes(word_sub stackpointer (word 32),32)]` THEN
      (REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; GSYM SEQ_ASSOC]
      THEN CONJ_TAC) THENL
      [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    (* nonoverlapping between (z',32) and many *)
    SUBGOAL_THEN
    `ALL (nonoverlapping (z':int64,32))
          [(z,32); (z,8 * 4 * (k4-1)); (m,8 * k); (word pc,3468);
          (m',32); (word_add z' (word 32),32);
          (word_sub stackpointer (word 32),32)]`
      MP_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THENL
      [MAP_EVERY EXPAND_TAC ["z'";"m'"] THEN
        REWRITE_TAC [WORD_RULE `word_add (word_sub x y) y = x`] THEN
        REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
        STRIP_TAC] THEN
    (* Some simplifications *)
    SUBGOAL_THEN `(k + 4) - 4 * (k4 - 1) = 8` (fun thm-> REWRITE_TAC[thm]) THENL [
      MAP_EVERY UNDISCH_TAC [`0<k4` ; `4*k4=k`] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_add z (word (8 * k)):(64)word = word_add z' (word 32)`
        (fun thm -> REWRITE_TAC[thm]) THENL [
      MAP_EVERY EXPAND_TAC ["k"; "z'"] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(k4=0)` THEN ARITH_TAC;

      ALL_TAC] THEN

    (* Start symbolic execution *)
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;ARITH_RULE`8*8=64`] THEN ENSURES_INIT_TAC "s0" THEN

    SUBGOAL_THEN
        `bignum_from_memory
            (word_add (word_sub m' (word 32)) (word 32):(64)word,
            k-4*(k4-1)) s0 =
        highdigits n (4*(k4-1))` MP_TAC THENL [
      REWRITE_TAC[WORD_RULE `word_add (word_sub x y) y = x`] THEN
      MAP_EVERY EXPAND_TAC ["n";"m'"] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_BIGNUM_FROM_MEMORY;
                    ARITH_RULE `8 * 4 * (k4-1) = 32 * (k4-1)`] THEN
      FAIL_TAC "unreachable";

      REWRITE_TAC [BIGNUM_FROM_MEMORY_BYTES] THEN STRIP_TAC] THEN

    (* ldp [x2+32 ~ x2+63] ([m' ~ m'+31]) *)
    SUBGOAL_THEN
        `!j. j < 4 ==>
          bigdigit (bignum_from_memory
            (word_add (word_sub m' (word 32)) (word 32):(64)word,
            k-4*(k4-1)) s0) j =
          bigdigit n (4*(k4-1)+j)`
        MP_TAC THENL [
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BIGDIGIT_HIGHDIGITS] THEN
      EXPAND_TAC "m'" THEN
      REWRITE_TAC[WORD_RULE `word_add (word_sub x y) y = x`] THEN
      FAIL_TAC "unreachable";

      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      (let MYTAC = MAP_EVERY UNDISCH_TAC [`4 * k4 = k`; `~(k=0)`] THEN ARITH_TAC in
        SUBGOAL_THEN `0 < k - 4 * (k4-1) <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
        SUBGOAL_THEN `1 < k - 4 * (k4-1) <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
        SUBGOAL_THEN `2 < k - 4 * (k4-1) <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
        SUBGOAL_THEN `3 < k - 4 * (k4-1) <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC]) THEN
      REWRITE_TAC[COND_CLAUSES;
          WORD_RULE `word_add (word_add x (word y)) (word z) = word_add x (word (y+z))`;
          ARITH_RULE `x+0=x`] THEN
      CONV_TAC (LAND_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[WORD_ADD_0;VAL_WORD_GALOIS;DIMINDEX_64; BIGDIGIT_BOUND] THEN STRIP_TAC] THEN

    (* ldp [x1 ~ x1 + 31] ([z' ~ z' + 31]).
        Do not use (word_add (word_sub z' 32) 32) because after line 6 we will simplify
        z'-32+32 into z' (as well as m'-32+32 to m'). *)
    SUBGOAL_THEN
          `!j. j < 4 ==>
            bigdigit (bignum_from_memory (z':(64)word, 8) s0) j =
            bigdigit a (4*(k4-1)+j)`
          MP_TAC THENL [
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BIGDIGIT_HIGHDIGITS;ARITH_RULE`8*8=64`] THEN
        EXPAND_TAC "z'" THEN
        FAIL_TAC "unreachable";

        REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
        (let MYTAC = ARITH_TAC in
          SUBGOAL_THEN `0 < 8 <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
          SUBGOAL_THEN `1 < 8 <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
          SUBGOAL_THEN `2 < 8 <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
          SUBGOAL_THEN `3 < 8 <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC]) THEN
        REWRITE_TAC[COND_CLAUSES;
            WORD_RULE `word_add (word_add x (word y)) (word z) = word_add x (word (y+z))`] THEN
        CONV_TAC (LAND_CONV NUM_REDUCE_CONV) THEN
        REWRITE_TAC[WORD_ADD_0;ARITH_RULE `x+0=x`;VAL_WORD_GALOIS;DIMINDEX_64; BIGDIGIT_BOUND] THEN STRIP_TAC] THEN

    (* From assumption
          `bignum_from_memory (z',8) s0 = highdigits a (4 * (k4-1)),
       get the highdigits of the uppermost 4 bytes.
    *)
    SUBGOAL_THEN
        `bignum_from_memory (word_add z' (word 32),4) s0 =
        highdigits a k`
        MP_TAC THENL [
      ONCE_REWRITE_TAC[ARITH_RULE `(_,4) = (_,8 - 4)`] THEN
      ONCE_REWRITE_TAC[WORD_RULE `word_add z' (word 32):64 word = word_add z' (word (8*4))`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;ARITH_RULE`8*8=64`] THEN
      REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `~(k = 0)` THEN
      EXPAND_TAC "k" THEN ARITH_TAC;

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;ARITH_RULE `8*4=32`] THEN DISCH_TAC] THEN

    (* go! *)
    ACCUMULATE_ARITH_TAC "s0" THEN CLARIFY_TAC THEN
      ARM_XACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC [`SP`;`X2`;`X1`] (1--4) (1--4) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ (* looks so dumb, but it works... *)
      WORD_RULE `word_add (word_sub x (word 32)) (word 32) = x`;
      WORD_RULE `word_add (word_sub x (word 32)) (word 40) = word_add x (word 8)`;
      WORD_RULE `word_add (word_sub x (word 32)) (word 48) = word_add x (word 16)`;
      WORD_RULE `word_add (word_sub x (word 32)) (word 56) = word_add x (word 24)`
    ]) THEN

    ARM_REWRITE_ASSUM_AND_XACCSTEPS_TAC2 BIGNUM_EMONTREDC_8N_EXEC
        [9]
        [WORD_MUL64_LO;WORD_MUL64_HI]
        [5;6;7;8;9;11;12;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;
         41;46;48;49;55;60;62;63;64;65;66;67;73;78;80;81;82;88;93;95;96;97;98;99;
         105;110;112;113;114;115;121;126;128;129;130;131]
        (5--135) [`X2`;`X1`;`X27`] THEN

    (* ENSURES_FINAL_STATE_TAC and ASM_REWRITE_TAC *)
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `8*4=32`]) THEN (* 8*4=32 for .. = q *)
    ASM_REWRITE_TAC[] THEN

    (* Discharge (n * w + 1 == 0) (mod (2 EXP 64)) and simplify an
       existing assumption using this *)
    DISCH_THEN(fun th ->
          REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
          ASSUME_TAC th) THEN

    SUBGOAL_THEN `n = lowdigits n k` (fun thm -> ONCE_REWRITE_TAC[thm]) THENL [
      MATCH_MP_TAC EQ_SYM THEN
      REWRITE_TAC[LOWDIGITS_EQ_SELF] THEN
      EXPAND_TAC "n" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
      FAIL_TAC "unreachable";

      ALL_TAC] THEN

    (* split lowdigits a(n) k *)
    SUBGOAL_THEN `!x. lowdigits x k = lowdigits x (((((4 * (k4-1) + 1) + 1) + 1) + 1))`
        (fun thm->REWRITE_TAC [thm]) THENL [
      EXPAND_TAC "k" THEN STRIP_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(k4 = 0)` THEN ARITH_TAC; ALL_TAC ] THEN
    REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
      `q*(a0+a1+a2+a3+a4)+(b0+b1+b2+b3+b4)+q =
       q*(a0+a1+a2+a3)+b0+b1+b2+b3+(q*a4+b4+q)`] THEN
    (* .. and replace q * lowdigits n .. + lowdigits a .. + q *)
    REWRITE_TAC[GSYM (ASSUME
        `2 EXP (64 * 4 * (k4 - 1)) * bignum_of_wordlist [g8; g9; g10; g11] +
         read (memory :> bytes (z,8 * 4 * (k4 - 1))) s135 =
         q * lowdigits n (4 * (k4 - 1)) + lowdigits a (4 * (k4 - 1)) + q`)] THEN

    (* split read (memory :> bytes (z,8 * k)) s135 into its high 32 bytes and low part,
      and cancel out the low parts in lhs = rhs *)
    REWRITE_TAC [GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    SUBGOAL_THEN `k = 4 * (k4 - 1) + 4`
        (fun thm -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [thm]) THENL [
      EXPAND_TAC "k" THEN UNDISCH_TAC `~(k4=0)` THEN ARITH_TAC; ALL_TAC
      ] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [BIGNUM_FROM_MEMORY_SPLIT] THEN
    REWRITE_TAC[ARITH_RULE `a0+a1+c=b0+b1+b2+b3+b4+b5+c<=>a0+a1=b0+b1+b2+b3+b4+b5`] THEN

    (* Divide by 2 EXP (64 * 4 * (k-1)) *)
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    REWRITE_TAC [ARITH_RULE `64*4*k=256*k`; ARITH_RULE `64*(4*k+k')=256*k+64*k'`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EXP_ADD] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB;
        ARITH_RULE `a * 2 EXP (256 * (k4-1)) * b = 2 EXP (256 * (k4-1)) * a * b`] THEN
    REWRITE_TAC[EQ_MULT_LCANCEL; EXP_2_NE_0] THEN

    (* Expand bignum_from_memory (z'4) *)
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC_CONSTS; ARITH_RULE `8*4*(k4-1)=32*(k4-1)`] THEN
    ASM_REWRITE_TAC[] THEN

    (* Expand q *)
    SUBGOAL_THEN
        `q = val(word(bigdigit q 0):(64)word)
              + 2 EXP 64 * val(word(bigdigit q 1):(64)word)
              + 2 EXP 128 * val(word(bigdigit q 2):(64)word)
              + 2 EXP 192 * val(word(bigdigit q 3):(64)word)`
        (fun thm -> ONCE_REWRITE_TAC [thm]) THENL [
      EXPAND_TAC "q" THEN
      REWRITE_TAC[ARITH_RULE `32=8*4`] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
          [GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY; ARITH_RULE `0<4/\1<4/\2<4/\3<4`;
                  WORD_VAL] THEN
      CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
      FAIL_TAC "unreachable";

      ALL_TAC] THEN

    (* Cleanup and prove it *)
    SUBGOAL_THEN `val (word (0 + bitval carry_s25):64 word) = bitval carry_s25`
      (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE[thm])) THENL
      [REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL]; ALL_TAC] THEN
    PROVE_IT
  ] THEN

  ASM_CASES_TAC `k4 = 3` THENL [
    SUBST_ALL_TAC (ASSUME `k4 = 3`) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE`3-1=2`];

    ALL_TAC] THEN

  (* maddloop_neon *)
  ENSURES_WHILE_PAUP_TAC `2` `k4-1:num` `pc + 0x834` `pc + 0xb08`
      inner_loop_invariant_with_flag THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
    (* 1. 2 < k-1 *)
    ASM_ARITH_TAC;

    (* 2. 0x82c -> loop begin *)
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    IMP_REWRITE_TAC[TAUT `(cond <=> F) ==> (if cond then a else b) = b`] THEN
    SUBGOAL_THEN `word_sub (word (32 * (k4 - 2))) (word 32):(64)word = word (32 * (k4 - 3))`
      SUBST_ALL_TAC THENL [
        REWRITE_TAC[ARITH_RULE `32 * (k4-3) = 32*(k4-2)-32`; WORD_SUB] THEN
        IMP_REWRITE_TAC[TAUT `(c <=> T) ==> (if c then t1 else t2) = t1`] THEN
        DISCARD_NONMATCHING_ASSUMPTIONS
        [`~(k4 = 0)`;`~(k4 = 1)`;`~(k4 = 2)`;`~(k4 = 3)`] THEN ASM_ARITH_TAC;

        ALL_TAC
      ] THEN
    VAL_INT64_TAC `32 * (k4 - 3)` THEN
    ASM_REWRITE_TAC[] THEN
    DISCARD_NONMATCHING_ASSUMPTIONS
        [`~(k4 = 0)`;`~(k4 = 1)`;`~(k4 = 2)`;`~(k4 = 3)`] THEN ASM_ARITH_TAC;

    ALL_TAC; (* 3. The main loop invariant preservation *)

    (* 4. cond br (0xb08) -> loop begin (0x834) *)
    REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1];

    (* 5. cond br (0xb08) -> 0xb0c *)
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_EXEC [1]] THEN


  (* The inner loop part. *)
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k + 4) - 4 * (i + 1) = k - 4 * i`] THEN
  REWRITE_TAC[WORD_RULE
    `word_sub (word_add m (word (32 * (i + 1)))) (word 32) = word_add m (word (32 * i))`] THEN

  (* Use z' and m' because nonoverlapping tactic sometimes doesn't solve (z+e,z+e') *)
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `4 * i + 4 = 4 * (i + 1)`] THEN
  ASM_REWRITE_TAC[
      WORD_RULE `word_add z (word (8 * 4 * i)) = word_add z (word(32 * i))`;
      WORD_RULE `word_add z (word (32 * (i + 1))) = word_add (word_add z (word(32*i))) (word 32)`] THEN
  ABBREV_TAC `z':int64 = word_add z (word (32 * i))` THEN
  ABBREV_TAC `m':int64 = word_add m (word (32 * i))` THEN

  SUBGOAL_THEN `4 * i < k` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < k4 - 1`; `4 * k4 = k`] THEN ARITH_TAC;
    ALL_TAC] THEN
  GHOST_INTRO_TAC `g8:int64` `read X12` THEN
  GHOST_INTRO_TAC `g9:int64` `read X13` THEN
  GHOST_INTRO_TAC `g10:int64` `read X14` THEN
  GHOST_INTRO_TAC `g11:int64` `read X15` THEN

  (* Shrink the window of maychange z *)
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28],,
    MAYCHANGE [memory :> bytes(z',32)] ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 32),32)]` THEN
  (REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; GSYM SEQ_ASSOC]
   THEN CONJ_TAC) THENL
   [EXPAND_TAC "z'" THEN EXPAND_TAC "m'" THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

  (* nonoverlapping between (z',32) and many *)
  SUBGOAL_THEN
   `ALL (nonoverlapping (z':int64,32))
        [(z,32); (z,8 * 4 * i); (m,8 * k); (word pc,3468);
         (m',32); (word_add z' (word 32),8 * (k - 4 * i));
         (word_sub stackpointer (word 32),32)]`
    MP_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THENL
    [MAP_EVERY EXPAND_TAC ["z'";"m'"] THEN
      REWRITE_TAC [WORD_RULE `word_add (word_sub x y) y = x`] THEN
      REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
      STRIP_TAC] THEN

  (* Start symbolic execution *)
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  SUBGOAL_THEN
      `bignum_from_memory
          (word_add (word_sub m' (word 32)) (word 32):(64)word,
           k-4*i) s0 =
       highdigits n (4*i)` MP_TAC THENL [
    REWRITE_TAC[WORD_RULE `word_add (word_sub x y) y = x`] THEN
    MAP_EVERY EXPAND_TAC ["n";"m'"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_BIGNUM_FROM_MEMORY;
                  ARITH_RULE `8 * 4 * i = 32 * i`] THEN
    FAIL_TAC "unreachable";

    REWRITE_TAC [BIGNUM_FROM_MEMORY_BYTES] THEN STRIP_TAC] THEN

  (* ldp [x2+32 ~ x2+95] ([m' ~ m'+63]) *)
  SUBGOAL_THEN
      `!j. j < 8 ==>
        bigdigit (bignum_from_memory
          (word_add (word_sub m' (word 32)) (word 32):(64)word,
           k-4*i) s0) j =
        bigdigit n (4*i+j)`
      MP_TAC THENL [
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BIGDIGIT_HIGHDIGITS] THEN
    EXPAND_TAC "m'" THEN
    REWRITE_TAC[WORD_RULE `word_add (word_sub x y) y = x`] THEN
    FAIL_TAC "unreachable";

    REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    (let MYTAC = MAP_EVERY UNDISCH_TAC [`4 * k4 = k`; `i < k4 - 1`] THEN ARITH_TAC in
      SUBGOAL_THEN `0 < k - 4 * i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `1 < k - 4 * i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `2 < k - 4 * i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `3 < k - 4 * i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `4 < k - 4 * i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `5 < k - 4 * i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `6 < k - 4 * i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `7 < k - 4 * i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC]) THEN
    REWRITE_TAC[COND_CLAUSES;
        WORD_RULE `word_add (word_add x (word y)) (word z) = word_add x (word (y+z))`;
        ARITH_RULE `x+0=x`] THEN
    CONV_TAC (LAND_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0;VAL_WORD_GALOIS;DIMINDEX_64; BIGDIGIT_BOUND] THEN STRIP_TAC] THEN

  (* ldr [x2+64~x2+95] *)
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128
        (word_add (word_sub m' (word 32)) (word 64))) s0`
      `word (bigdigit n (4*i+5)):(64)word`
      `word (bigdigit n (4*i+4)):(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128
        (word_add (word_sub m' (word 32)) (word 80))) s0`
      `word (bigdigit n (4*i+7)):(64)word`
      `word (bigdigit n (4*i+6)):(64)word` THEN

  (* ldp [x1 ~ x1 + 31] ([z' ~ z' + 31]).
     Do not use (word_add (word_sub z' 32) 32) because after line 6 we will simplify
     z'-32+32 into z' (as well as m'-32+32 to m'). *)
  SUBGOAL_THEN
      `!j. j < 4 ==>
        bigdigit (bignum_from_memory (z':(64)word, (k + 4) - 4 * i) s0) j =
        bigdigit a (4*i+j)`
      MP_TAC THENL [
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BIGDIGIT_HIGHDIGITS] THEN
    EXPAND_TAC "z'" THEN
    FAIL_TAC "unreachable";

    REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    (let MYTAC = MAP_EVERY UNDISCH_TAC [`4 * k4 = k`; `i < k4 - 1`] THEN ARITH_TAC in
      SUBGOAL_THEN `0 < (k+4)-4*i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `1 < (k+4)-4*i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `2 < (k+4)-4*i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC] THEN
      SUBGOAL_THEN `3 < (k+4)-4*i <=> T` SUBST_ALL_TAC THENL [MYTAC; ALL_TAC]) THEN
    REWRITE_TAC[COND_CLAUSES;
        WORD_RULE `word_add (word_add x (word y)) (word z) = word_add x (word (y+z))`] THEN
    CONV_TAC (LAND_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0;ARITH_RULE `x+0=x`;VAL_WORD_GALOIS;DIMINDEX_64; BIGDIGIT_BOUND] THEN STRIP_TAC] THEN

  (* From assumption
        `bignum_from_memory (z',((k + 4) - 4 * i)) s0 = highdigits a (4 * i),
     make
        `bignum_from_memory (z'+32,k - 4*i) s0 = highdigits a (4 * (i + 1))
  *)
  SUBGOAL_THEN
      `bignum_from_memory (word_add z' (word 32),k - 4*i) s0 =
       highdigits a (4 * (i + 1))`
      MP_TAC THENL [
    EXPAND_TAC "z'" THEN
    ONCE_REWRITE_TAC[
        ARITH_RULE `k - 4*i = ((k+4) - 4*i) - 4`;
        WORD_RULE `word_add (word_add z (word (32 * i))) (word 32) =
                   word_add (word_add z (word (32 * i))) (word (8*4))`] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
    REWRITE_TAC[ARITH_RULE `64*4*i+64*4=64*4*(i+1)`] THEN FAIL_TAC "unreachable";

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_TAC] THEN

  (* Cleanup + Forget the definition of z' and m' *)
  RULE_ASSUM_TAC (REWRITE_RULE [ARITH_RULE `8*4=32`]) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_add z (word (32 * i)) = z'`; `word_add m (word (32 * i)) = m'`] THEN

  (* go! *)
  ACCUMULATE_ARITH_TAC "s0" THEN CLARIFY_TAC THEN
  ARM_XACCSTEPS_TAC BIGNUM_EMONTREDC_8N_EXEC [`SP`;`X2`;`X1`] (1--4) (1--6) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [ (* looks so dumb, but it works... *)
    WORD_RULE `word_add (word_sub x (word 32)) (word 32) = x`;
    WORD_RULE `word_add (word_sub x (word 32)) (word 40) = word_add x (word 8)`;
    WORD_RULE `word_add (word_sub x (word 32)) (word 48) = word_add x (word 16)`;
    WORD_RULE `word_add (word_sub x (word 32)) (word 56) = word_add x (word 24)`;
    WORD_RULE `word_add (word_sub x (word 32)) (word 64) = word_add x (word 32)`;
    WORD_RULE `word_add (word_sub x (word 32)) (word 72) = word_add x (word 40)`;
    WORD_RULE `word_add (word_sub x (word 32)) (word 80) = word_add x (word 48)`;
    WORD_RULE `word_add (word_sub x (word 32)) (word 88) = word_add x (word 56)`
  ]) THEN

  ARM_REWRITE_ASSUM_AND_XACCSTEPS_TAC2 BIGNUM_EMONTREDC_8N_EXEC
      [11;12] [WORD_MUL64_LO;WORD_MUL64_HI]
      [7;8;9;10;11;17;18;24;25;26;27;32;33;34;35;40;41;42;43;46;47;48;49;
       54;55;56;57;62;63;73;84;86;87;93;98;100;101;102;103;104;105]
      (7--106) [`X2`;`X1`] THEN

  ARM_REWRITE_ASSUM_AND_XACCSTEPS_TAC2 BIGNUM_EMONTREDC_8N_EXEC
      [107;108;109;110;171;172;178;179] [WORD_MUL64_LO;WORD_MUL64_HI]
      [116;121;123;124;125;131;136;138;139;140;141;142;148;153;155;156;157;158;
       164;169;174;175;176;177]
      (107--181) [`X2`;`X1`;`X16`;`X26`;`X3`;`X17`] THEN

  (* ENSURES_FINAL_STATE_TAC and ASM_REWRITE_TAC *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `8*4=32`] THEN
  (* pre-calculated multiplications *)
  REWRITE_TAC ((map ARITH_RULE [
    `4 * (i + 1) + 1 = 4 * i + 5`;
    `4 * (i + 1) + 2 = 4 * i + 6`;
    `4 * (i + 1) + 3 = 4 * i + 7`;
    `4 * (i + 1) = 4 * i + 4`]) @ [WORD_BITMANIP_SIMP_LEMMAS]) THEN

  (* X27 (induction var) update *)
  SUBGOAL_THEN
      `word_sub (word (32 * (k4 - i))) (word 32):(64)word = word (32 * (k4 - (i + 1)))`
      SUBST_ALL_TAC THENL [
    REWRITE_TAC[ARITH_RULE `32 * (k4 - (i + 1)) = 32 * (k4 - i) - 32`] THEN
    REWRITE_TAC[WORD_SUB] THEN
    IMP_REWRITE_TAC [TAUT `(c <=> T) ==> (if c then t1 else t2) = t1`] THEN
    UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;

    SIMP_TAC[]] THEN
  (* Flag update *)
  SUBGOAL_THEN
      `val (word_sub (word (32 * (k4 - (i + 1)))) (word 32):(64)word) =
        (32 * (k4 - (i + 1))) - 32` SUBST_ALL_TAC THENL [
    REWRITE_TAC[VAL_WORD_SUB;VAL_WORD;DIMINDEX_64;ARITH_RULE`32 MOD 2 EXP 64 = 32`] THEN
    SUBGOAL_THEN
        `(32 * (k4 - (i + 1))) MOD 2 EXP 64 = 32 * (k4 - (i + 1))` SUBST_ALL_TAC
        THENL [
      IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 58` THEN ARITH_TAC;
      ALL_TAC ] THEN
    SUBGOAL_THEN
        `32 * (k4 - (i + 1)) + 2 EXP 64 - 32 = 32 * (k4 - (i + 1)) - 32 + 2 EXP 64`
        SUBST_ALL_TAC THENL [
      UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CONJUNCT1 (SPECL
          [`32 * (k4 - (i+1)) - 32:num`; `2 EXP 64:num`; `2 EXP 64`]
          (GSYM ADD_MOD_MOD_REFL));
          MOD_REFL; ADD_CLAUSES] THEN
    IMP_REWRITE_TAC[MOD_LT] THEN
    UNDISCH_TAC `k4 < 2 EXP 58` THEN ARITH_TAC;

    ALL_TAC] THEN

  SUBGOAL_THEN
    `32 * (k4 - (i + 1)) - 32 = 0 <=> i + 1 = k4 - 1` (fun thm -> SIMP_TAC [thm]) THENL
    [ UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC; ALL_TAC ] THEN

  (* Discharge (n * w + 1 == 0) (mod (2 EXP 64)) and simplify an
      existing assumption using this *)
  DISCH_THEN(fun th ->
        REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
        ASSUME_TAC th) THEN

  (* Expand lowdigits n(or a) (4*i+4) *)
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `4 * i + 4 = 4 * i + 1 + 1 + 1 + 1`] THEN
    REWRITE_TAC[ADD_ASSOC] THEN REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  ONCE_REWRITE_TAC[ARITH_RULE
        `(q*(a0+a1+a2+a3+a4)+b0+b1+b2+b3+b4)+q =
        q*(a0+a1+a2+a3)+b0+b1+b2+b3+(q*a4+b4+q)`] THEN
  REWRITE_TAC[GSYM (ASSUME
      `2 EXP (64 * 4 * i) * bignum_of_wordlist [g8; g9; g10; g11] +
        read (memory :> bytes (z,8 * 4 * i)) s181 =
       q * lowdigits n (4 * i) + lowdigits a (4 * i) + q`)] THEN
  (* Cancel out ... + read (memory :> bytes (z,8 * 4 * i)) s181 *)
  REWRITE_TAC[ARITH_RULE
    `a+x = b1+b2+b3+b4+b5+b6+x <=> a = b1+b2+b3+b4+b5+b6`] THEN

  (* Expand read (memory :> bytes (z',8 * 4)) s181 into 4 64-bit words *)
  REWRITE_TAC[ARITH_RULE `(_,32)=(_,8*4)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN

  (* Divide by 2 EXP 256 *)
  REWRITE_TAC(map ARITH_RULE [
      `((4 * i + 1) + 1) + 1 = 4*i+3`;
      `(4 * i + 1) + 1 = 4*i+2`
    ]) THEN
  SUBGOAL_THEN `!k. 2 EXP (64 * (4 * i + k)) = 2 EXP (64 * 4 * i) * 2 EXP (64 * k)` (fun thm -> REWRITE_TAC[thm])
    THENL [REWRITE_TAC[ARITH_RULE `64 * (a + b) = 64 * a + 64 * b`; EXP_ADD] THEN FAIL_TAC "unreachable"; ALL_TAC] THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
  REWRITE_TAC[ARITH_RULE `q*2 EXP (64*4*i)*a + p*b = 2 EXP (64*4*i)*q*a + p*b`;
      GSYM LEFT_ADD_DISTRIB] THEN
  IMP_REWRITE_TAC[EQ_MULT_LCANCEL;EXP_2_NE_0] THEN
  REWRITE_TAC(map ARITH_RULE [`64*4=256`;`64*3=192`;`64*2=128`;`64*1=64`]) THEN

  (* Expand q *)
  SUBGOAL_THEN
        `q = val(word(bigdigit q 0):(64)word)
              + 2 EXP 64 * val(word(bigdigit q 1):(64)word)
              + 2 EXP 128 * val(word(bigdigit q 2):(64)word)
              + 2 EXP 192 * val(word(bigdigit q 3):(64)word)`
        (fun thm -> ONCE_REWRITE_TAC [thm]) THENL [
      EXPAND_TAC "q" THEN
      REWRITE_TAC[ARITH_RULE `32=8*4`] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
          [GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY; ARITH_RULE `0<4/\1<4/\2<4/\3<4`;
                  WORD_VAL] THEN
      CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
      FAIL_TAC "unreachable";

      ALL_TAC] THEN

  SUBGOAL_THEN `val (word (0 + bitval carry_s25):64 word) = bitval carry_s25`
      (fun thm -> RULE_ASSUM_TAC (REWRITE_RULE[thm])) THENL
    [REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL]; ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[WORD_BITMANIP_SIMP_LEMMAS]) THEN

  DISCARD_READ_QREGS THEN
  PROVE_IT);;

let BIGNUM_EMONTREDC_8N_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALLPAIRS nonoverlapping
          [(word pc,3468); (m,8 * val k)]
          [(z,8 * 2 * val k); (word_sub stackpointer (word 112), 112)] /\
        nonoverlapping (z,8 * 2 * val k)
                       (word_sub stackpointer (word 112),112) /\
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
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                        memory :> bytes(word_sub stackpointer (word 112),112)])`,
  let execth = BIGNUM_EMONTREDC_8N_EXEC in
  let coreth = BIGNUM_EMONTREDC_8N_CORRECT in
  let regs = dest_list `[X19;X20;X21;X22;X23;X24;X25;X26;X27;X28]` in
  let sp_tm = `SP` in
  let mono2lemma = MESON[]
   `(!x. (!y. P x y) ==> (!y. Q x y)) ==> (!x y. P x y) ==> (!x y. Q x y)` in
  MP_TAC BIGNUM_EMONTREDC_8N_CORRECT THEN
  REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT(MATCH_MP_TAC mono2lemma THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC 80 THEN MP_TAC th) THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `word_add stackpointer (word 18446744073709551584):(64)word =
                word_sub stackpointer (word 32)` SUBST_ALL_TAC THENL
    [CONV_TAC WORD_BLAST;ALL_TAC] THEN
  TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN ALIGNED_16_TAC THEN
      TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN

  (* Make nonoverlapping reasoning happy *)
  ABBREV_TAC `stackpointer':64 word = word_sub stackpointer (word 32)` THEN
  SUBGOAL_THEN `stackpointer:64 word = word_add stackpointer' (word 32)`
          SUBST_ALL_TAC THENL [EXPAND_TAC "stackpointer'" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_add stackpointer' (word 32)) (word 80) =
                    word_add stackpointer' (word 112):64 word`
          SUBST_ALL_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN

  DISCH_THEN(fun th ->
      ENSURES_EXISTING_PRESERVED_TAC sp_tm THEN
      MAP_EVERY (fun c -> ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c) regs THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC execth (1--5) THEN
      MP_TAC th) THEN

  (* convert back to the original stackpointer definition to use
     ARM_BIGSTEP_TAC *)
  ABBREV_TAC `stackpointer'':64 word = word_add stackpointer' (word 32)` THEN
  SUBGOAL_THEN `stackpointer':64 word = word_sub stackpointer'' (word 32)`
          SUBST_ALL_TAC THENL [EXPAND_TAC "stackpointer''" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN

  (* ARM_BIGSTEP_TAC erases 'read (memory :> ...) = X27'.
     This replacement prevents that from happening.
     Probably this is again related to the issue in nonoverlapping... *)
  SUBGOAL_THEN
    `read (memory :> bytes64 stackpointer'') s5 =
     read (memory :> bytes64 (word_add (word_sub stackpointer'' (word 32))
                                       (word 32))) s5` SUBST_ALL_TAC THENL
    [ AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC WORD_BLAST; ALL_TAC ] THEN
  ARM_BIGSTEP_TAC execth ("s"^string_of_int(6)) THEN

  (* Again introduce the stackpointer - 32 form *)
  ABBREV_TAC `stackpointer''':64 word = word_sub stackpointer'' (word 32)` THEN
  SUBGOAL_THEN `stackpointer'':64 word = word_add stackpointer''' (word 32)`
          SUBST_ALL_TAC THENL [EXPAND_TAC "stackpointer'''" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`stackpointer''' = stackpointer''':64 word`] THEN

  REWRITE_TAC(!simulation_precanon_thms) THEN
  ARM_STEPS_TAC execth (7--12) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;
