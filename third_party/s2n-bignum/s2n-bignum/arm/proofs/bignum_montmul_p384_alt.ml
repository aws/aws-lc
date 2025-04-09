(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery multiplication modulo p_384.                                   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_montmul_p384_alt.o";;
 ****)

let bignum_montmul_p384_alt_mc =
  define_assert_from_elf "bignum_montmul_p384_alt_mc" "arm/p384/bignum_montmul_p384_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9401023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&0))) *)
  0xa9401845;       (* arm_LDP X5 X6 X2 (Immediate_Offset (iword (&0))) *)
  0x9b057c6c;       (* arm_MUL X12 X3 X5 *)
  0x9bc57c6d;       (* arm_UMULH X13 X3 X5 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0x9bc67c6e;       (* arm_UMULH X14 X3 X6 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0xa9412047;       (* arm_LDP X7 X8 X2 (Immediate_Offset (iword (&16))) *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0x9bc77c6f;       (* arm_UMULH X15 X3 X7 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0x9bc87c70;       (* arm_UMULH X16 X3 X8 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0xa9422849;       (* arm_LDP X9 X10 X2 (Immediate_Offset (iword (&32))) *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0x9bc97c71;       (* arm_UMULH X17 X3 X9 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0x9bca7c73;       (* arm_UMULH X19 X3 X10 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ad;       (* arm_ADDS X13 X13 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b01ce;       (* arm_ADCS X14 X14 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b0294;       (* arm_ADC X20 X20 X11 *)
  0xa9411023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&16))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b01ce;       (* arm_ADDS X14 X14 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b01ef;       (* arm_ADCS X15 X15 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9a9f37f5;       (* arm_CSET X21 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b01ef;       (* arm_ADDS X15 X15 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0210;       (* arm_ADCS X16 X16 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9a9f37f6;       (* arm_CSET X22 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b02d6;       (* arm_ADC X22 X22 X11 *)
  0xa9421023;       (* arm_LDP X3 X4 X1 (Immediate_Offset (iword (&32))) *)
  0x9b057c6b;       (* arm_MUL X11 X3 X5 *)
  0xab0b0210;       (* arm_ADDS X16 X16 X11 *)
  0x9b067c6b;       (* arm_MUL X11 X3 X6 *)
  0xba0b0231;       (* arm_ADCS X17 X17 X11 *)
  0x9b077c6b;       (* arm_MUL X11 X3 X7 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b087c6b;       (* arm_MUL X11 X3 X8 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b097c6b;       (* arm_MUL X11 X3 X9 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b0a7c6b;       (* arm_MUL X11 X3 X10 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9a9f37e2;       (* arm_CSET X2 Condition_CS *)
  0x9bc57c6b;       (* arm_UMULH X11 X3 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9bc67c6b;       (* arm_UMULH X11 X3 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9bc77c6b;       (* arm_UMULH X11 X3 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc87c6b;       (* arm_UMULH X11 X3 X8 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bc97c6b;       (* arm_UMULH X11 X3 X9 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9bca7c6b;       (* arm_UMULH X11 X3 X10 *)
  0x9a0b0042;       (* arm_ADC X2 X2 X11 *)
  0x9b057c8b;       (* arm_MUL X11 X4 X5 *)
  0xab0b0231;       (* arm_ADDS X17 X17 X11 *)
  0x9b067c8b;       (* arm_MUL X11 X4 X6 *)
  0xba0b0273;       (* arm_ADCS X19 X19 X11 *)
  0x9b077c8b;       (* arm_MUL X11 X4 X7 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9b087c8b;       (* arm_MUL X11 X4 X8 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9b097c8b;       (* arm_MUL X11 X4 X9 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9b0a7c8b;       (* arm_MUL X11 X4 X10 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0x9a9f37e1;       (* arm_CSET X1 Condition_CS *)
  0x9bc57c8b;       (* arm_UMULH X11 X4 X5 *)
  0xab0b0273;       (* arm_ADDS X19 X19 X11 *)
  0x9bc67c8b;       (* arm_UMULH X11 X4 X6 *)
  0xba0b0294;       (* arm_ADCS X20 X20 X11 *)
  0x9bc77c8b;       (* arm_UMULH X11 X4 X7 *)
  0xba0b02b5;       (* arm_ADCS X21 X21 X11 *)
  0x9bc87c8b;       (* arm_UMULH X11 X4 X8 *)
  0xba0b02d6;       (* arm_ADCS X22 X22 X11 *)
  0x9bc97c8b;       (* arm_UMULH X11 X4 X9 *)
  0xba0b0042;       (* arm_ADCS X2 X2 X11 *)
  0x9bca7c8b;       (* arm_UMULH X11 X4 X10 *)
  0x9a0b0021;       (* arm_ADC X1 X1 X11 *)
  0xd3607d87;       (* arm_LSL X7 X12 32 *)
  0x8b0c00ec;       (* arm_ADD X12 X7 X12 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ce7;       (* arm_UMULH X7 X7 X12 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0c7cc5;       (* arm_MUL X5 X6 X12 *)
  0x9bcc7cc6;       (* arm_UMULH X6 X6 X12 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0c00c6;       (* arm_ADCS X6 X6 X12 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ad;       (* arm_SUBS X13 X13 X7 *)
  0xfa0601ce;       (* arm_SBCS X14 X14 X6 *)
  0xfa0501ef;       (* arm_SBCS X15 X15 X5 *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da7;       (* arm_LSL X7 X13 32 *)
  0x8b0d00ed;       (* arm_ADD X13 X7 X13 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ce7;       (* arm_UMULH X7 X7 X13 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0d7cc5;       (* arm_MUL X5 X6 X13 *)
  0x9bcd7cc6;       (* arm_UMULH X6 X6 X13 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0d00c6;       (* arm_ADCS X6 X6 X13 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ce;       (* arm_SUBS X14 X14 X7 *)
  0xfa0601ef;       (* arm_SBCS X15 X15 X6 *)
  0xfa050210;       (* arm_SBCS X16 X16 X5 *)
  0xfa1f0231;       (* arm_SBCS X17 X17 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xd3607dc7;       (* arm_LSL X7 X14 32 *)
  0x8b0e00ee;       (* arm_ADD X14 X7 X14 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bce7ce7;       (* arm_UMULH X7 X7 X14 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0e7cc5;       (* arm_MUL X5 X6 X14 *)
  0x9bce7cc6;       (* arm_UMULH X6 X6 X14 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0e00c6;       (* arm_ADCS X6 X6 X14 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb0701ef;       (* arm_SUBS X15 X15 X7 *)
  0xfa060210;       (* arm_SBCS X16 X16 X6 *)
  0xfa050231;       (* arm_SBCS X17 X17 X5 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f01ce;       (* arm_SBC X14 X14 XZR *)
  0xd3607de7;       (* arm_LSL X7 X15 32 *)
  0x8b0f00ef;       (* arm_ADD X15 X7 X15 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bcf7ce7;       (* arm_UMULH X7 X7 X15 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b0f7cc5;       (* arm_MUL X5 X6 X15 *)
  0x9bcf7cc6;       (* arm_UMULH X6 X6 X15 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba0f00c6;       (* arm_ADCS X6 X6 X15 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb070210;       (* arm_SUBS X16 X16 X7 *)
  0xfa060231;       (* arm_SBCS X17 X17 X6 *)
  0xfa05018c;       (* arm_SBCS X12 X12 X5 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xda1f01ef;       (* arm_SBC X15 X15 XZR *)
  0xd3607e07;       (* arm_LSL X7 X16 32 *)
  0x8b1000f0;       (* arm_ADD X16 X7 X16 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bd07ce7;       (* arm_UMULH X7 X7 X16 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b107cc5;       (* arm_MUL X5 X6 X16 *)
  0x9bd07cc6;       (* arm_UMULH X6 X6 X16 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1000c6;       (* arm_ADCS X6 X6 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb070231;       (* arm_SUBS X17 X17 X7 *)
  0xfa06018c;       (* arm_SBCS X12 X12 X6 *)
  0xfa0501ad;       (* arm_SBCS X13 X13 X5 *)
  0xfa1f01ce;       (* arm_SBCS X14 X14 XZR *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xda1f0210;       (* arm_SBC X16 X16 XZR *)
  0xd3607e27;       (* arm_LSL X7 X17 32 *)
  0x8b1100f1;       (* arm_ADD X17 X7 X17 *)
  0xb26083e7;       (* arm_MOV X7 (rvalue (word 18446744069414584321)) *)
  0x9bd17ce7;       (* arm_UMULH X7 X7 X17 *)
  0xb2407fe6;       (* arm_MOV X6 (rvalue (word 4294967295)) *)
  0x9b117cc5;       (* arm_MUL X5 X6 X17 *)
  0x9bd17cc6;       (* arm_UMULH X6 X6 X17 *)
  0xab0500e7;       (* arm_ADDS X7 X7 X5 *)
  0xba1100c6;       (* arm_ADCS X6 X6 X17 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xeb07018c;       (* arm_SUBS X12 X12 X7 *)
  0xfa0601ad;       (* arm_SBCS X13 X13 X6 *)
  0xfa0501ce;       (* arm_SBCS X14 X14 X5 *)
  0xfa1f01ef;       (* arm_SBCS X15 X15 XZR *)
  0xfa1f0210;       (* arm_SBCS X16 X16 XZR *)
  0xda1f0231;       (* arm_SBC X17 X17 XZR *)
  0xab13018c;       (* arm_ADDS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xba1601ef;       (* arm_ADCS X15 X15 X22 *)
  0xba020210;       (* arm_ADCS X16 X16 X2 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0xb26083eb;       (* arm_MOV X11 (rvalue (word 18446744069414584321)) *)
  0xab0b0193;       (* arm_ADDS X19 X12 X11 *)
  0xb2407feb;       (* arm_MOV X11 (rvalue (word 4294967295)) *)
  0xba0b01b4;       (* arm_ADCS X20 X13 X11 *)
  0xd280002b;       (* arm_MOV X11 (rvalue (word 1)) *)
  0xba0b01d5;       (* arm_ADCS X21 X14 X11 *)
  0xba1f01f6;       (* arm_ADCS X22 X15 XZR *)
  0xba1f0202;       (* arm_ADCS X2 X16 XZR *)
  0xba1f0221;       (* arm_ADCS X1 X17 XZR *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0x9a9501ce;       (* arm_CSEL X14 X14 X21 Condition_EQ *)
  0x9a9601ef;       (* arm_CSEL X15 X15 X22 Condition_EQ *)
  0x9a820210;       (* arm_CSEL X16 X16 X2 Condition_EQ *)
  0x9a810231;       (* arm_CSEL X17 X17 X1 Condition_EQ *)
  0xa900340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&0))) *)
  0xa9013c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&16))) *)
  0xa9024410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&32))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTMUL_P384_ALT_EXEC = ARM_MK_EXEC_RULE bignum_montmul_p384_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let mmlemma = prove
 (`!h (l:int64) (x:int64).
        &2 pow 64 * &h + &(val(l:int64)):real =
        &18446744069414584321 *
        &(val(word_add (word_shl x 32) x:int64))
        ==> &2 pow 64 * &h + &(val(x:int64)):real =
            &18446744069414584321 *
            &(val(word_add (word_shl x 32) x:int64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
   MATCH_MP (NUMBER_RULE
    `p * h + l:num = y ==> (y == x) (mod p) ==> (x == l) (mod p)`)) THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_shl x 32) x:int64 = word(4294967297 * val x)`] THEN
  REWRITE_TAC[CONG; VAL_WORD; DIMINDEX_64] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod p) ==> (a * (b * x)  == x) (mod p)`) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_MONTMUL_P384_ALT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,0x450) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_alt_mc /\
                  read PC s = word(pc + 0x8) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + 0x444) /\
                  (a * b <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a * b <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a * b <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTMUL_P384_ALT_EXEC (1--271)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,6) s0` THEN

  (*** Main multiplication block ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_ALT_EXEC (1--149) (1--149) THEN

  (*** Main Montgomery reduction block ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_ALT_EXEC
   (allpairs (fun i j -> 16 * i + j) (0--5)
             [153;155;157;158;160;161;162;163;164;165] @
    (246--252))
   (150--252) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL]) THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Key properties of pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s246; sum_s247; sum_s248; sum_s249; sum_s250; sum_s251;
          word(bitval carry_s251)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a * b) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

 (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_ALT_EXEC
   [254;256;258;259;260;261;262] (253--271) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_384` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a * b) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a * b) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  MAP_EVERY EXISTS_TAC
   [`384`; `if t < p_384 then &t:real else &t - &p_384`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    REWRITE_TAC[p_384] THEN ARITH_TAC;
    ALL_TAC;
    ASM_SIMP_TAC[MOD_CASES] THEN
    GEN_REWRITE_TAC LAND_CONV [COND_RAND] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT]] THEN
  SUBGOAL_THEN
   `val(word_add (word(bitval carry_s251))
                 (word(bitval carry_s261)):int64) = 0 <=>
    t < p_384`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `carry_s251:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTMUL_P384_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,0x450) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),32))
          [(word pc,0x450); (x,8 * 6); (y,8 * 6); (z,8 * 6)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
           (\s. read PC s = returnaddress /\
                (a * b <= 2 EXP 384 * p_384
                 ==> bignum_from_memory (z,6) s =
                     (inverse_mod p_384 (2 EXP 384) * a * b) MOD p_384))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 6);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P384_ALT_EXEC BIGNUM_MONTMUL_P384_ALT_CORRECT
   `[X19;X20;X21;X22]` 32);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 384 bits, may then not be fully reduced mod p_384.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTMUL_P384_ALT_CORRECT = time prove
 (`!z x y a b pc.
        nonoverlapping (word pc,0x450) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_alt_mc /\
                  read PC s = word(pc + 0x8) /\
                  C_ARGUMENTS [z; x; y] s /\
                  bignum_from_memory (x,6) s = a /\
                  bignum_from_memory (y,6) s = b)
             (\s. read PC s = word (pc + 0x444) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9;
                         X10; X11; X12; X13; X14; X15; X16; X17; X19;
                         X20; X21; X22] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN
  BIGNUM_DIGITIZE_TAC "y_" `bignum_from_memory (y,6) s0` THEN

  (*** Main multiplication block ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_ALT_EXEC (1--149) (1--149) THEN

  (*** Main Montgomery reduction block ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_ALT_EXEC
   (allpairs (fun i j -> 16 * i + j) (0--5)
             [153;155;157;158;160;161;162;163;164;165] @
    (246--252))
   (150--252) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL]) THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Key properties of pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s246; sum_s247; sum_s248; sum_s249; sum_s250; sum_s251;
          word(bitval carry_s251)]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 384 + p_384 /\ (2 EXP 384 * t == a * b) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `2 EXP 384 * t <= (2 EXP 384 - 1) EXP 2 + (2 EXP 384 - 1) * p
        ==> t < 2 EXP 384 + p`) THEN
      REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "b"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_P384_ALT_EXEC
   [254;256;258;259;260;261;262] (253--271) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == ab) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * ab) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN

  SUBGOAL_THEN
   `val(word_add (word(bitval carry_s251))
                 (word(bitval carry_s261)):int64) = 0 <=>
    t < p_384`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `carry_s251:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
     [REWRITE_TAC[p_384] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; GSYM NOT_LE] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE `!b:num. x + b * p = y ==> (x == y) (mod p)`) THEN
  EXISTS_TAC `bitval(p_384 <= t)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b:real = c <=> c - b = a`] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 EXP 384 + p_384` THEN
    REWRITE_TAC[bitval; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
  REWRITE_TAC[bitval; GSYM NOT_LT; COND_SWAP] THEN COND_CASES_TAC THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BITVAL_CLAUSES; p_384] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTMUL_P384_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x y a b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,0x450) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),32))
          [(word pc,0x450); (x,8 * 6); (y,8 * 6); (z,8 * 6)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montmul_p384_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x; y] s /\
                bignum_from_memory (x,6) s = a /\
                bignum_from_memory (y,6) s = b)
           (\s. read PC s = returnaddress /\
                (bignum_from_memory (z,6) s ==
                 inverse_mod p_384 (2 EXP 384) * a * b) (mod p_384))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 6);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTMUL_P384_ALT_EXEC BIGNUM_AMONTMUL_P384_ALT_CORRECT
   `[X19;X20;X21;X22]` 32);;
