(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery squaring modulo p_384.                                         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

(**** print_literal_from_elf "arm/p384/unopt/bignum_montsqr_p384_base.o";;
 ****)

let bignum_montsqr_p384_unopt_mc =
  define_assert_from_elf "bignum_montsqr_p384_unopt_mc" "arm/p384/unopt/bignum_montsqr_p384_base.o"
[
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x9b037c4e;       (* arm_MUL X14 X2 X3 *)
  0x9b047c4f;       (* arm_MUL X15 X2 X4 *)
  0x9b047c70;       (* arm_MUL X16 X3 X4 *)
  0x9b027c48;       (* arm_MUL X8 X2 X2 *)
  0x9b037c6a;       (* arm_MUL X10 X3 X3 *)
  0x9b047c8c;       (* arm_MUL X12 X4 X4 *)
  0x9bc37c51;       (* arm_UMULH X17 X2 X3 *)
  0xab1101ef;       (* arm_ADDS X15 X15 X17 *)
  0x9bc47c51;       (* arm_UMULH X17 X2 X4 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc47c71;       (* arm_UMULH X17 X3 X4 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc27c49;       (* arm_UMULH X9 X2 X2 *)
  0x9bc37c6b;       (* arm_UMULH X11 X3 X3 *)
  0x9bc47c8d;       (* arm_UMULH X13 X4 X4 *)
  0xab0e01ce;       (* arm_ADDS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xab0e0129;       (* arm_ADDS X9 X9 X14 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0xd3607d10;       (* arm_LSL X16 X8 (rvalue (word 32)) *)
  0x8b080208;       (* arm_ADD X8 X16 X8 *)
  0xd360fd10;       (* arm_LSR X16 X8 (rvalue (word 32)) *)
  0xeb080210;       (* arm_SUBS X16 X16 X8 *)
  0xda1f010f;       (* arm_SBC X15 X8 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 (rvalue (word 32)) *)
  0xd360fdef;       (* arm_LSR X15 X15 (rvalue (word 32)) *)
  0xab0801ef;       (* arm_ADDS X15 X15 X8 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb100129;       (* arm_SUBS X9 X9 X16 *)
  0xfa0f014a;       (* arm_SBCS X10 X10 X15 *)
  0xfa0e016b;       (* arm_SBCS X11 X11 X14 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d30;       (* arm_LSL X16 X9 (rvalue (word 32)) *)
  0x8b090209;       (* arm_ADD X9 X16 X9 *)
  0xd360fd30;       (* arm_LSR X16 X9 (rvalue (word 32)) *)
  0xeb090210;       (* arm_SUBS X16 X16 X9 *)
  0xda1f012f;       (* arm_SBC X15 X9 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 (rvalue (word 32)) *)
  0xd360fdef;       (* arm_LSR X15 X15 (rvalue (word 32)) *)
  0xab0901ef;       (* arm_ADDS X15 X15 X9 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10014a;       (* arm_SUBS X10 X10 X16 *)
  0xfa0f016b;       (* arm_SBCS X11 X11 X15 *)
  0xfa0e018c;       (* arm_SBCS X12 X12 X14 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d50;       (* arm_LSL X16 X10 (rvalue (word 32)) *)
  0x8b0a020a;       (* arm_ADD X10 X16 X10 *)
  0xd360fd50;       (* arm_LSR X16 X10 (rvalue (word 32)) *)
  0xeb0a0210;       (* arm_SUBS X16 X16 X10 *)
  0xda1f014f;       (* arm_SBC X15 X10 XZR *)
  0x93d081f0;       (* arm_EXTR X16 X15 X16 (rvalue (word 32)) *)
  0xd360fdef;       (* arm_LSR X15 X15 (rvalue (word 32)) *)
  0xab0a01ef;       (* arm_ADDS X15 X15 X10 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0xeb10016b;       (* arm_SUBS X11 X11 X16 *)
  0xfa0f018c;       (* arm_SBCS X12 X12 X15 *)
  0xfa0e01ad;       (* arm_SBCS X13 X13 X14 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xa900300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&0))) *)
  0xa901200d;       (* arm_STP X13 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022809;       (* arm_STP X9 X10 X0 (Immediate_Offset (iword (&32))) *)
  0x9b057c48;       (* arm_MUL X8 X2 X5 *)
  0x9b067c6e;       (* arm_MUL X14 X3 X6 *)
  0x9b077c8f;       (* arm_MUL X15 X4 X7 *)
  0x9bc57c50;       (* arm_UMULH X16 X2 X5 *)
  0x9bc67c71;       (* arm_UMULH X17 X3 X6 *)
  0x9bc77c81;       (* arm_UMULH X1 X4 X7 *)
  0xab0e0210;       (* arm_ADDS X16 X16 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0x9a1f0021;       (* arm_ADC X1 X1 XZR *)
  0xab080209;       (* arm_ADDS X9 X16 X8 *)
  0xba10022a;       (* arm_ADCS X10 X17 X16 *)
  0xba11002b;       (* arm_ADCS X11 X1 X17 *)
  0x9a1f002c;       (* arm_ADC X12 X1 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba11018c;       (* arm_ADCS X12 X12 X17 *)
  0x9a1f002d;       (* arm_ADC X13 X1 XZR *)
  0xeb030051;       (* arm_SUBS X17 X2 X3 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500cf;       (* arm_SUBS X15 X6 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba100129;       (* arm_ADCS X9 X9 X16 *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba0e016b;       (* arm_ADCS X11 X11 X14 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040051;       (* arm_SUBS X17 X2 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0500ef;       (* arm_SUBS X15 X7 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba0f016b;       (* arm_ADCS X11 X11 X15 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xeb040071;       (* arm_SUBS X17 X3 X4 *)
  0xda912631;       (* arm_CNEG X17 X17 Condition_CC *)
  0xda9f23ee;       (* arm_CSETM X14 Condition_CC *)
  0xeb0600ef;       (* arm_SUBS X15 X7 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0x9b0f7e30;       (* arm_MUL X16 X17 X15 *)
  0x9bcf7e2f;       (* arm_UMULH X15 X17 X15 *)
  0xda8e21ce;       (* arm_CINV X14 X14 Condition_CC *)
  0xca0e0210;       (* arm_EOR X16 X16 X14 *)
  0xca0e01ef;       (* arm_EOR X15 X15 X14 *)
  0xb10005df;       (* arm_CMN X14 (rvalue (word 1)) *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0xba0f018c;       (* arm_ADCS X12 X12 X15 *)
  0x9a0e01ad;       (* arm_ADC X13 X13 X14 *)
  0xab080108;       (* arm_ADDS X8 X8 X8 *)
  0xba090129;       (* arm_ADCS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0x9a1f03f1;       (* arm_ADC X17 XZR XZR *)
  0xa9400c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&0))) *)
  0xab020108;       (* arm_ADDS X8 X8 X2 *)
  0xba030129;       (* arm_ADCS X9 X9 X3 *)
  0xa9410c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&16))) *)
  0xba02014a;       (* arm_ADCS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa9420c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&32))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xd3607d04;       (* arm_LSL X4 X8 (rvalue (word 32)) *)
  0x8b080088;       (* arm_ADD X8 X4 X8 *)
  0xd360fd04;       (* arm_LSR X4 X8 (rvalue (word 32)) *)
  0xeb080084;       (* arm_SUBS X4 X4 X8 *)
  0xda1f0103;       (* arm_SBC X3 X8 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 (rvalue (word 32)) *)
  0xd360fc63;       (* arm_LSR X3 X3 (rvalue (word 32)) *)
  0xab080063;       (* arm_ADDS X3 X3 X8 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb040129;       (* arm_SUBS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa02016b;       (* arm_SBCS X11 X11 X2 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0108;       (* arm_SBC X8 X8 XZR *)
  0xd3607d24;       (* arm_LSL X4 X9 (rvalue (word 32)) *)
  0x8b090089;       (* arm_ADD X9 X4 X9 *)
  0xd360fd24;       (* arm_LSR X4 X9 (rvalue (word 32)) *)
  0xeb090084;       (* arm_SUBS X4 X4 X9 *)
  0xda1f0123;       (* arm_SBC X3 X9 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 (rvalue (word 32)) *)
  0xd360fc63;       (* arm_LSR X3 X3 (rvalue (word 32)) *)
  0xab090063;       (* arm_ADDS X3 X3 X9 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04014a;       (* arm_SUBS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa02018c;       (* arm_SBCS X12 X12 X2 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d44;       (* arm_LSL X4 X10 (rvalue (word 32)) *)
  0x8b0a008a;       (* arm_ADD X10 X4 X10 *)
  0xd360fd44;       (* arm_LSR X4 X10 (rvalue (word 32)) *)
  0xeb0a0084;       (* arm_SUBS X4 X4 X10 *)
  0xda1f0143;       (* arm_SBC X3 X10 XZR *)
  0x93c48064;       (* arm_EXTR X4 X3 X4 (rvalue (word 32)) *)
  0xd360fc63;       (* arm_LSR X3 X3 (rvalue (word 32)) *)
  0xab0a0063;       (* arm_ADDS X3 X3 X10 *)
  0x9a1f03e2;       (* arm_ADC X2 XZR XZR *)
  0xeb04016b;       (* arm_SUBS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa0201ad;       (* arm_SBCS X13 X13 X2 *)
  0xfa1f0108;       (* arm_SBCS X8 X8 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xab080231;       (* arm_ADDS X17 X17 X8 *)
  0xba1f0128;       (* arm_ADCS X8 X9 XZR *)
  0xba1f0149;       (* arm_ADCS X9 X10 XZR *)
  0xba1f03ea;       (* arm_ADCS X10 XZR XZR *)
  0x9b057ca1;       (* arm_MUL X1 X5 X5 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x9b067cce;       (* arm_MUL X14 X6 X6 *)
  0x9b077cef;       (* arm_MUL X15 X7 X7 *)
  0x9bc57ca1;       (* arm_UMULH X1 X5 X5 *)
  0xba01018c;       (* arm_ADCS X12 X12 X1 *)
  0x9bc67cc1;       (* arm_UMULH X1 X6 X6 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba010231;       (* arm_ADCS X17 X17 X1 *)
  0x9bc77ce1;       (* arm_UMULH X1 X7 X7 *)
  0xba0f0108;       (* arm_ADCS X8 X8 X15 *)
  0xba010129;       (* arm_ADCS X9 X9 X1 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x9b067ca1;       (* arm_MUL X1 X5 X6 *)
  0x9b077cae;       (* arm_MUL X14 X5 X7 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0xab1001ce;       (* arm_ADDS X14 X14 X16 *)
  0x9bc77cb0;       (* arm_UMULH X16 X5 X7 *)
  0xba1001ef;       (* arm_ADCS X15 X15 X16 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0xab010021;       (* arm_ADDS X1 X1 X1 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0x9a1f03e5;       (* arm_ADC X5 XZR XZR *)
  0xab01018c;       (* arm_ADDS X12 X12 X1 *)
  0xba0e01ad;       (* arm_ADCS X13 X13 X14 *)
  0xba0f0231;       (* arm_ADCS X17 X17 X15 *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba050129;       (* arm_ADCS X9 X9 X5 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xb26083e1;       (* arm_MOV X1 (rvalue (word 18446744069414584321)) *)
  0xb2407fee;       (* arm_MOV X14 (rvalue (word 4294967295)) *)
  0xd280002f;       (* arm_MOV X15 (rvalue (word 1)) *)
  0xab01017f;       (* arm_CMN X11 X1 *)
  0xba0e019f;       (* arm_ADCS XZR X12 X14 *)
  0xba0f01bf;       (* arm_ADCS XZR X13 X15 *)
  0xba1f023f;       (* arm_ADCS XZR X17 XZR *)
  0xba1f011f;       (* arm_ADCS XZR X8 XZR *)
  0xba1f013f;       (* arm_ADCS XZR X9 XZR *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xcb0a03ea;       (* arm_NEG X10 X10 *)
  0x8a0a0021;       (* arm_AND X1 X1 X10 *)
  0xab01016b;       (* arm_ADDS X11 X11 X1 *)
  0x8a0a01ce;       (* arm_AND X14 X14 X10 *)
  0xba0e018c;       (* arm_ADCS X12 X12 X14 *)
  0x8a0a01ef;       (* arm_AND X15 X15 X10 *)
  0xba0f01ad;       (* arm_ADCS X13 X13 X15 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0108;       (* arm_ADCS X8 X8 XZR *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xa900300b;       (* arm_STP X11 X12 X0 (Immediate_Offset (iword (&0))) *)
  0xa901440d;       (* arm_STP X13 X17 X0 (Immediate_Offset (iword (&16))) *)
  0xa9022408;       (* arm_STP X8 X9 X0 (Immediate_Offset (iword (&32))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTSQR_P384_UNOPT_EXEC = ARM_MK_EXEC_RULE bignum_montsqr_p384_unopt_mc;;

(* bignum_montsqr_p384_unopt_mc without ret. *)
let bignum_montsqr_p384_unopt_core_mc_def,
    bignum_montsqr_p384_unopt_core_mc,
    BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p384_unopt_core_mc"
    bignum_montsqr_p384_unopt_mc
    (`0`,`LENGTH bignum_montsqr_p384_unopt_mc - 4`)
    (fst BIGNUM_MONTSQR_P384_UNOPT_EXEC);;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

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

let BIGNUM_MONTSQR_P384_UNOPT_CORE_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_unopt_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_unopt_core_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p384_unopt_core_mc) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (1--260)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Squaring of the lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (1--28) (1--28) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 =
    bignum_of_wordlist [mullo_s7; sum_s24; sum_s25; sum_s26; sum_s27; sum_s28]`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three short Montgomery reductions ***)

  montred_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X14;X15;X16]` 28 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X14;X15;X16]` 43 THEN
  montred_subst_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X14;X15;X16]` 58 THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Three stashing stores ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC [74;75;76] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   ([77;78;79] @ (83--93) @ [99] @ (105--109) @ [115] @
   (121--124) @ [130] @ (136--138)) (77--138) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0; x_1; x_2] * bignum_of_wordlist [x_3; x_4; x_5] =
    bignum_of_wordlist [mullo_s77; sum_s105; sum_s121;
                        sum_s136; sum_s137; sum_s138]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
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
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
       filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

 (*** Double the cross-product and add the Montgomerified lower square ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (139--155) (139--155) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
    2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                    bignum_of_wordlist [x_3; x_4; x_5] +
    p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58] =
    2 EXP 192 *
    bignum_of_wordlist
     [sum_s147; sum_s148; sum_s150; sum_s151; sum_s153; sum_s154; sum_s155]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three more Montgomery reductions on that sum ***)

  montred_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X2;X3;X4]` 155 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X2;X3;X4]` 170 THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X2;X3;X4]` 185 THEN

  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Montgomery accumulation and addition of the high square ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (201--237) (201--237) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  (*** Main pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s206; sum_s232; sum_s233;
          sum_s234; sum_s235; sum_s236; sum_s237]` THEN
  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 384 * t =
      a EXP 2 +
      p_384 * bignum_of_wordlist
        [ww_28; ww_43; ww_58; ww_155; ww_170; ww_185]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
      `(bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
        2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                        bignum_of_wordlist [x_3; x_4; x_5] +
        p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58]) +
       2 EXP 384 * bignum_of_wordlist[x_3;x_4;x_5] EXP 2 +
       2 EXP 192 * p_384 *
       bignum_of_wordlist [ww_155; ww_170; ww_185]` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_RING
         `x' - x:real = &(bignum_of_wordlist(CONS h t))
          ==> e * (&(bignum_of_wordlist(CONS h t')) -
                   &(bignum_of_wordlist(CONS h t))) = (w - e * (x' - x)) - z
              ==> w = e * &(bignum_of_wordlist(CONS h t')) + z`));
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

 (*** To make bounds reasoning more transparent, recast top as a bit ***)

  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(sum_s237:int64)` NUM_AS_BITVAL_ALT))) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN ANTS_TAC THENL
   [UNDISCH_TAC `t < 2 * p_384` THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `topc:bool` SUBST_ALL_TAC)] THEN

  (*** Final comparison ****)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (238--247) (238--247) THEN
  SUBGOAL_THEN
   `sum_s247:int64 = word(bitval(p_384 <= t))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC WORD_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THENL
     [UNDISCH_TAC `t < 2 * p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      EXPAND_TAC "t" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Corrective masked subtraction ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC [248] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word 0) x:int64 = word_neg x`]) THEN
  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (249--260) (249--260) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `t MOD p_384` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) ==> (t == i * a EXP 2) (mod p)`)) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  ASM_SIMP_TAC[MOD_CASES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `t < 2 * p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BITVAL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_MONTSQR_P384_UNOPT_CORRECT = time prove(
  `!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_unopt_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_unopt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p384_unopt_core_mc) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_CORRECT
    bignum_montsqr_p384_unopt_core_mc_def
    [fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC;
     fst BIGNUM_MONTSQR_P384_UNOPT_EXEC]);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 384 bits, may then not be fully reduced mod p_384.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTSQR_P384_UNOPT_CORE_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_unopt_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_unopt_core_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p384_unopt_core_mc) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Squaring of the lower half ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (1--28) (1--28) THEN
  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 =
    bignum_of_wordlist [mullo_s7; sum_s24; sum_s25; sum_s26; sum_s27; sum_s28]`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three short Montgomery reductions ***)

  montred_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X14;X15;X16]` 28 THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th])) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X14;X15;X16]` 43 THEN
  montred_subst_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X14;X15;X16]` 58 THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Three stashing stores ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC [74;75;76] THEN

  (*** ADK cross-product ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   ([77;78;79] @ (83--93) @ [99] @ (105--109) @ [115] @
   (121--124) @ [130] @ (136--138)) (77--138) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0; x_1; x_2] * bignum_of_wordlist [x_3; x_4; x_5] =
    bignum_of_wordlist [mullo_s77; sum_s105; sum_s121;
                        sum_s136; sum_s137; sum_s138]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`384`; `&0:real`] THEN
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
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o
       filter (is_ratconst o rand o concl) o DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

 (*** Double the cross-product and add the Montgomerified lower square ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (139--155) (139--155) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
    2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                    bignum_of_wordlist [x_3; x_4; x_5] +
    p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58] =
    2 EXP 192 *
    bignum_of_wordlist
     [sum_s147; sum_s148; sum_s150; sum_s151; sum_s153; sum_s154; sum_s155]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Three more Montgomery reductions on that sum ***)

  montred_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X8;X13;X12;X11;X10;X9;X8; X2;X3;X4]` 155 THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
                    [SYM th]) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `a:real = b + c ==> a - c = b`)) THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X9;X8;X13;X12;X11;X10;X9; X2;X3;X4]` 170 THEN

  montred_subst_tac BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
   `[X10;X9;X8;X13;X12;X11;X10; X2;X3;X4]` 185 THEN

  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word a = b`] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (rvalue a) s = b`] THEN

  (*** Montgomery accumulation and addition of the high square ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (201--237) (201--237) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  (*** Main pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s206; sum_s232; sum_s233;
          sum_s234; sum_s235; sum_s236; sum_s237]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 384 + p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `2 EXP 384 * t =
      a EXP 2 +
      p_384 * bignum_of_wordlist
        [ww_28; ww_43; ww_58; ww_155; ww_170; ww_185]`
    ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
      `(bignum_of_wordlist[x_0; x_1; x_2] EXP 2 +
        2 * 2 EXP 192 * bignum_of_wordlist [x_0; x_1; x_2] *
                        bignum_of_wordlist [x_3; x_4; x_5] +
        p_384 * bignum_of_wordlist[ww_28; ww_43; ww_58]) +
       2 EXP 384 * bignum_of_wordlist[x_3;x_4;x_5] EXP 2 +
       2 EXP 192 * p_384 *
       bignum_of_wordlist [ww_155; ww_170; ww_185]` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_RING
         `x' - x:real = &(bignum_of_wordlist(CONS h t))
          ==> e * (&(bignum_of_wordlist(CONS h t')) -
                   &(bignum_of_wordlist(CONS h t))) = (w - e * (x' - x)) - z
              ==> w = e * &(bignum_of_wordlist(CONS h t')) + z`));
        EXPAND_TAC "a" THEN REWRITE_TAC[bignum_of_wordlist] THEN
        ARITH_TAC] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC[bignum_of_wordlist; p_384; GSYM REAL_OF_NUM_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
      REWRITE_TAC[ADD_CLAUSES; VAL_WORD_BITVAL] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[NUMBER_RULE `(x + p * n:num == x) (mod p)`] THEN
      MATCH_MP_TAC(ARITH_RULE `2 EXP 384 * x < 2 EXP 384 * y ==> x < y`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word_subword a b = c`]] THEN

 (*** To make bounds reasoning more transparent, recast top as a bit ***)

  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(sum_s237:int64)` NUM_AS_BITVAL_ALT))) THEN
  REWRITE_TAC[VAL_EQ_BITVAL] THEN ANTS_TAC THENL
   [UNDISCH_TAC `t < 2 EXP 384 + p_384` THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384; bignum_of_wordlist] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `topc:bool` SUBST_ALL_TAC)] THEN

  (*** Final comparison ****)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (238--247) (238--247) THEN
  SUBGOAL_THEN
   `sum_s247:int64 = word(bitval(p_384 <= t))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC WORD_FROM_CARRY_LE THEN EXISTS_TAC `384` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THENL
     [UNDISCH_TAC `t < 2 EXP 384 + p_384` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_384] THEN REAL_ARITH_TAC;
      EXPAND_TAC "t" THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
      REWRITE_TAC[VAL_WORD_BITVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[]];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Corrective masked subtraction ***)

  ARM_STEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC [248] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word 0) x:int64 = word_neg x`]) THEN
  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC (249--260) (249--260) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE
       `(e * t == a EXP 2) (mod p)
        ==> (e * i == 1) (mod p) /\ (s == t) (mod p)
            ==> (s == i * a EXP 2) (mod p)`)) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
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
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BITVAL_CLAUSES; p_384] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_AMONTSQR_P384_UNOPT_CORRECT = time prove(
  `!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_unopt_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_unopt_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p384_unopt_core_mc) /\
                  ((bignum_from_memory (z,6) s ==
                       inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384)))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTSQR_P384_UNOPT_CORE_CORRECT
    bignum_montsqr_p384_unopt_core_mc_def
    [fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC;fst BIGNUM_MONTSQR_P384_UNOPT_EXEC]);;

(******************************************************************************
  The first program equivalence between the 'core' part of source program and
  its SIMD-vectorized but not instruction-scheduled program
******************************************************************************)

(* This is the intermediate program that is equivalent to both
   bignum_montsqr_p384_base and bignum_montsqr_p384. This is a vectorized
   version of bignum_montsqr_p384_base but instructions are unscheduled. *)

let bignum_montsqr_p384_interm1_ops:int list = [
  0xa9400829; (* ldp      x9, x2, [x1] *)
  0x3dc00032; (* ldr      q18, [x1] *)
  0x3dc00033; (* ldr      q19, [x1] *)
  0xa9411824; (* ldp      x4, x6, [x1, #16] *)
  0xa9422825; (* ldp      x5, x10, [x1, #32] *)
  0x3dc00835; (* ldr      q21, [x1, #32] *)
  0x3dc0083c; (* ldr      q28, [x1, #32] *)
  0x9b027d2c; (* mul      x12, x9, x2 *)
  0x9b047d21; (* mul      x1, x9, x4 *)
  0x9b047c4d; (* mul      x13, x2, x4 *)
  0x6f00e5e0; (* movi     v0.2d, #0xffffffff *)
  0x4e935a65; (* uzp2     v5.4s, v19.4s, v19.4s *)
  0x0ea12a59; (* xtn      v25.2s, v18.2d *)
  0x0ea12a64; (* xtn      v4.2s, v19.2d *)
  0x4ea00a77; (* rev64    v23.4s, v19.4s *)
  0x2ea4c334; (* umull    v20.2d, v25.2s, v4.2s *)
  0x2ea5c33e; (* umull    v30.2d, v25.2s, v5.2s *)
  0x4e925a53; (* uzp2     v19.4s, v18.4s, v18.4s *)
  0x4eb29ef6; (* mul      v22.4s, v23.4s, v18.4s *)
  0x6f60169e; (* usra     v30.2d, v20.2d, #32 *)
  0x2ea5c272; (* umull    v18.2d, v19.2s, v5.2s *)
  0x6ea02ad6; (* uaddlp   v22.2d, v22.4s *)
  0x4e201fd4; (* and      v20.16b, v30.16b, v0.16b *)
  0x2ea48274; (* umlal    v20.2d, v19.2s, v4.2s *)
  0x4f6056d3; (* shl      v19.2d, v22.2d, #32 *)
  0x6f6017d2; (* usra     v18.2d, v30.2d, #32 *)
  0x2ea48333; (* umlal    v19.2d, v25.2s, v4.2s *)
  0x6f601692; (* usra     v18.2d, v20.2d, #32 *)
  0x4e083e67; (* mov      x7, v19.d[0] *)
  0x4e183e71; (* mov      x17, v19.d[1] *)
  0x9b047c90; (* mul      x16, x4, x4 *)
  0x9bc27d23; (* umulh    x3, x9, x2 *)
  0xab03002f; (* adds     x15, x1, x3 *)
  0x9bc47d21; (* umulh    x1, x9, x4 *)
  0xba0101ad; (* adcs     x13, x13, x1 *)
  0x9bc47c41; (* umulh    x1, x2, x4 *)
  0xba1f0028; (* adcs     x8, x1, xzr *)
  0x4e083e4b; (* mov      x11, v18.d[0] *)
  0x4e183e4e; (* mov      x14, v18.d[1] *)
  0x9bc47c81; (* umulh    x1, x4, x4 *)
  0xab0c0183; (* adds     x3, x12, x12 *)
  0xba0f01ef; (* adcs     x15, x15, x15 *)
  0xba0d01ad; (* adcs     x13, x13, x13 *)
  0xba08010c; (* adcs     x12, x8, x8 *)
  0x9a1f0021; (* adc      x1, x1, xzr *)
  0xab03016b; (* adds     x11, x11, x3 *)
  0xba0f0223; (* adcs     x3, x17, x15 *)
  0xba0d01d1; (* adcs     x17, x14, x13 *)
  0xba0c020f; (* adcs     x15, x16, x12 *)
  0x9a1f002d; (* adc      x13, x1, xzr *)
  0xd3607ce1; (* lsl      x1, x7, #32 *)
  0x8b070030; (* add      x16, x1, x7 *)
  0xd360fe01; (* lsr      x1, x16, #32 *)
  0xeb10002c; (* subs     x12, x1, x16 *)
  0xda1f0201; (* sbc      x1, x16, xzr *)
  0x93cc802c; (* extr     x12, x1, x12, #32 *)
  0xd360fc21; (* lsr      x1, x1, #32 *)
  0xab100027; (* adds     x7, x1, x16 *)
  0x9a1f03e1; (* adc      x1, xzr, xzr *)
  0xeb0c016c; (* subs     x12, x11, x12 *)
  0xfa07006b; (* sbcs     x11, x3, x7 *)
  0xfa010231; (* sbcs     x17, x17, x1 *)
  0xfa1f01ef; (* sbcs     x15, x15, xzr *)
  0xfa1f01ad; (* sbcs     x13, x13, xzr *)
  0xda1f0203; (* sbc      x3, x16, xzr *)
  0xd3607d81; (* lsl      x1, x12, #32 *)
  0x8b0c0030; (* add      x16, x1, x12 *)
  0xd360fe01; (* lsr      x1, x16, #32 *)
  0xeb10002c; (* subs     x12, x1, x16 *)
  0xda1f0201; (* sbc      x1, x16, xzr *)
  0x93cc802c; (* extr     x12, x1, x12, #32 *)
  0xd360fc21; (* lsr      x1, x1, #32 *)
  0xab100027; (* adds     x7, x1, x16 *)
  0x9a1f03e1; (* adc      x1, xzr, xzr *)
  0xeb0c016c; (* subs     x12, x11, x12 *)
  0xfa070231; (* sbcs     x17, x17, x7 *)
  0xfa0101ef; (* sbcs     x15, x15, x1 *)
  0xfa1f01ad; (* sbcs     x13, x13, xzr *)
  0xfa1f006b; (* sbcs     x11, x3, xzr *)
  0xda1f0203; (* sbc      x3, x16, xzr *)
  0xd3607d81; (* lsl      x1, x12, #32 *)
  0x8b0c0030; (* add      x16, x1, x12 *)
  0xd360fe01; (* lsr      x1, x16, #32 *)
  0xeb10002c; (* subs     x12, x1, x16 *)
  0xda1f0201; (* sbc      x1, x16, xzr *)
  0x93cc8027; (* extr     x7, x1, x12, #32 *)
  0xd360fc21; (* lsr      x1, x1, #32 *)
  0xab10002c; (* adds     x12, x1, x16 *)
  0x9a1f03e1; (* adc      x1, xzr, xzr *)
  0xeb070231; (* subs     x17, x17, x7 *)
  0xfa0c01ef; (* sbcs     x15, x15, x12 *)
  0xfa0101ad; (* sbcs     x13, x13, x1 *)
  0xfa1f0167; (* sbcs     x7, x11, xzr *)
  0xfa1f006c; (* sbcs     x12, x3, xzr *)
  0xda1f0201; (* sbc      x1, x16, xzr *)
  0xa9003c11; (* stp      x17, x15, [x0] *)
  0xa9011c0d; (* stp      x13, x7, [x0, #16] *)
  0xa902040c; (* stp      x12, x1, [x0, #32] *)
  0x9b067d2e; (* mul      x14, x9, x6 *)
  0x9b057c4f; (* mul      x15, x2, x5 *)
  0x9b0a7c8d; (* mul      x13, x4, x10 *)
  0x9bc67d27; (* umulh    x7, x9, x6 *)
  0x9bc57c4c; (* umulh    x12, x2, x5 *)
  0x9bca7c81; (* umulh    x1, x4, x10 *)
  0xab0f00ef; (* adds     x15, x7, x15 *)
  0xba0d0190; (* adcs     x16, x12, x13 *)
  0x9a1f002d; (* adc      x13, x1, xzr *)
  0xab0e01eb; (* adds     x11, x15, x14 *)
  0xba0f0207; (* adcs     x7, x16, x15 *)
  0xba1001ac; (* adcs     x12, x13, x16 *)
  0x9a1f01a1; (* adc      x1, x13, xzr *)
  0xab0e00f1; (* adds     x17, x7, x14 *)
  0xba0f018f; (* adcs     x15, x12, x15 *)
  0xba100023; (* adcs     x3, x1, x16 *)
  0x9a1f01b0; (* adc      x16, x13, xzr *)
  0xeb020121; (* subs     x1, x9, x2 *)
  0xda81242d; (* cneg     x13, x1, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm    x7, cc  // cc = lo, ul, last *)
  0xeb0600a1; (* subs     x1, x5, x6 *)
  0xda812421; (* cneg     x1, x1, cc  // cc = lo, ul, last *)
  0x9b017dac; (* mul      x12, x13, x1 *)
  0x9bc17da1; (* umulh    x1, x13, x1 *)
  0xda8720e7; (* cinv     x7, x7, cc  // cc = lo, ul, last *)
  0xca07018c; (* eor      x12, x12, x7 *)
  0xca070021; (* eor      x1, x1, x7 *)
  0xb10004ff; (* cmn      x7, #0x1 *)
  0xba0c016b; (* adcs     x11, x11, x12 *)
  0xba010231; (* adcs     x17, x17, x1 *)
  0xba0701ef; (* adcs     x15, x15, x7 *)
  0xba070063; (* adcs     x3, x3, x7 *)
  0x9a070210; (* adc      x16, x16, x7 *)
  0xeb040129; (* subs     x9, x9, x4 *)
  0xda89252d; (* cneg     x13, x9, cc  // cc = lo, ul, last *)
  0xda9f23e7; (* csetm    x7, cc  // cc = lo, ul, last *)
  0xeb060141; (* subs     x1, x10, x6 *)
  0xda812421; (* cneg     x1, x1, cc  // cc = lo, ul, last *)
  0x9b017dac; (* mul      x12, x13, x1 *)
  0x9bc17da1; (* umulh    x1, x13, x1 *)
  0xda8720e7; (* cinv     x7, x7, cc  // cc = lo, ul, last *)
  0xca07018c; (* eor      x12, x12, x7 *)
  0xca070021; (* eor      x1, x1, x7 *)
  0xb10004ff; (* cmn      x7, #0x1 *)
  0xba0c0231; (* adcs     x17, x17, x12 *)
  0xba0101ef; (* adcs     x15, x15, x1 *)
  0xba07006d; (* adcs     x13, x3, x7 *)
  0x9a070207; (* adc      x7, x16, x7 *)
  0xeb040042; (* subs     x2, x2, x4 *)
  0xda82244c; (* cneg     x12, x2, cc  // cc = lo, ul, last *)
  0xda9f23e1; (* csetm    x1, cc  // cc = lo, ul, last *)
  0xeb050142; (* subs     x2, x10, x5 *)
  0xda822442; (* cneg     x2, x2, cc  // cc = lo, ul, last *)
  0x9b027d84; (* mul      x4, x12, x2 *)
  0x9bc27d82; (* umulh    x2, x12, x2 *)
  0xda812021; (* cinv     x1, x1, cc  // cc = lo, ul, last *)
  0xca010084; (* eor      x4, x4, x1 *)
  0xca010042; (* eor      x2, x2, x1 *)
  0xb100043f; (* cmn      x1, #0x1 *)
  0xba0401ec; (* adcs     x12, x15, x4 *)
  0xba0201a4; (* adcs     x4, x13, x2 *)
  0x9a0100e2; (* adc      x2, x7, x1 *)
  0xab0e01c1; (* adds     x1, x14, x14 *)
  0xba0b0170; (* adcs     x16, x11, x11 *)
  0xba110231; (* adcs     x17, x17, x17 *)
  0xba0c018f; (* adcs     x15, x12, x12 *)
  0xba04008d; (* adcs     x13, x4, x4 *)
  0xba020047; (* adcs     x7, x2, x2 *)
  0x9a1f03ec; (* adc      x12, xzr, xzr *)
  0xa9400804; (* ldp      x4, x2, [x0] *)
  0xab040021; (* adds     x1, x1, x4 *)
  0xba020210; (* adcs     x16, x16, x2 *)
  0xa9410804; (* ldp      x4, x2, [x0, #16] *)
  0xba040231; (* adcs     x17, x17, x4 *)
  0xba0201ef; (* adcs     x15, x15, x2 *)
  0xa9420804; (* ldp      x4, x2, [x0, #32] *)
  0xba0401ad; (* adcs     x13, x13, x4 *)
  0xba0200e7; (* adcs     x7, x7, x2 *)
  0x9a1f018b; (* adc      x11, x12, xzr *)
  0xd3607c22; (* lsl      x2, x1, #32 *)
  0x8b01004c; (* add      x12, x2, x1 *)
  0xd360fd82; (* lsr      x2, x12, #32 *)
  0xeb0c0044; (* subs     x4, x2, x12 *)
  0xda1f0182; (* sbc      x2, x12, xzr *)
  0x93c48044; (* extr     x4, x2, x4, #32 *)
  0xd360fc42; (* lsr      x2, x2, #32 *)
  0xab0c0041; (* adds     x1, x2, x12 *)
  0x9a1f03e2; (* adc      x2, xzr, xzr *)
  0xeb040204; (* subs     x4, x16, x4 *)
  0xfa010230; (* sbcs     x16, x17, x1 *)
  0xfa0201f1; (* sbcs     x17, x15, x2 *)
  0xfa1f01af; (* sbcs     x15, x13, xzr *)
  0xfa1f00ed; (* sbcs     x13, x7, xzr *)
  0xda1f0187; (* sbc      x7, x12, xzr *)
  0xd3607c82; (* lsl      x2, x4, #32 *)
  0x8b04004c; (* add      x12, x2, x4 *)
  0xd360fd82; (* lsr      x2, x12, #32 *)
  0xeb0c0044; (* subs     x4, x2, x12 *)
  0xda1f0182; (* sbc      x2, x12, xzr *)
  0x93c48044; (* extr     x4, x2, x4, #32 *)
  0xd360fc42; (* lsr      x2, x2, #32 *)
  0xab0c0041; (* adds     x1, x2, x12 *)
  0x9a1f03e2; (* adc      x2, xzr, xzr *)
  0xeb040204; (* subs     x4, x16, x4 *)
  0xfa010230; (* sbcs     x16, x17, x1 *)
  0xfa0201f1; (* sbcs     x17, x15, x2 *)
  0xfa1f01af; (* sbcs     x15, x13, xzr *)
  0xfa1f00ed; (* sbcs     x13, x7, xzr *)
  0xda1f0187; (* sbc      x7, x12, xzr *)
  0xd3607c82; (* lsl      x2, x4, #32 *)
  0x8b04004c; (* add      x12, x2, x4 *)
  0xd360fd82; (* lsr      x2, x12, #32 *)
  0xeb0c0044; (* subs     x4, x2, x12 *)
  0xda1f0182; (* sbc      x2, x12, xzr *)
  0x93c48041; (* extr     x1, x2, x4, #32 *)
  0xd360fc42; (* lsr      x2, x2, #32 *)
  0xab0c0044; (* adds     x4, x2, x12 *)
  0x9a1f03e2; (* adc      x2, xzr, xzr *)
  0xeb010203; (* subs     x3, x16, x1 *)
  0xfa040231; (* sbcs     x17, x17, x4 *)
  0xfa0201ef; (* sbcs     x15, x15, x2 *)
  0xfa1f01a1; (* sbcs     x1, x13, xzr *)
  0xfa1f00e4; (* sbcs     x4, x7, xzr *)
  0xda1f0182; (* sbc      x2, x12, xzr *)
  0xab01016d; (* adds     x13, x11, x1 *)
  0xba1f0087; (* adcs     x7, x4, xzr *)
  0xba1f004c; (* adcs     x12, x2, xzr *)
  0xba1f03f0; (* adcs     x16, xzr, xzr *)
  0x9b067cc2; (* mul      x2, x6, x6 *)
  0xab020063; (* adds     x3, x3, x2 *)
  0x0ea12b9e; (* xtn      v30.2s, v28.2d *)
  0x0f20879a; (* shrn     v26.2s, v28.2d, #32 *)
  0x2ebac3da; (* umull    v26.2d, v30.2s, v26.2s *)
  0x4f615753; (* shl      v19.2d, v26.2d, #33 *)
  0x2ebe83d3; (* umlal    v19.2d, v30.2s, v30.2s *)
  0x4e083e61; (* mov      x1, v19.d[0] *)
  0x4e183e64; (* mov      x4, v19.d[1] *)
  0x9bc67cc2; (* umulh    x2, x6, x6 *)
  0xba020231; (* adcs     x17, x17, x2 *)
  0x9bc57ca2; (* umulh    x2, x5, x5 *)
  0xba0101ef; (* adcs     x15, x15, x1 *)
  0xba0201ad; (* adcs     x13, x13, x2 *)
  0x9bca7d42; (* umulh    x2, x10, x10 *)
  0xba0400e7; (* adcs     x7, x7, x4 *)
  0xba02018c; (* adcs     x12, x12, x2 *)
  0x9a1f0210; (* adc      x16, x16, xzr *)
  0x4e080cdc; (* dup      v28.2d, x6 *)
  0x6f00e5e0; (* movi     v0.2d, #0xffffffff *)
  0x4e955aa5; (* uzp2     v5.4s, v21.4s, v21.4s *)
  0x0ea12b99; (* xtn      v25.2s, v28.2d *)
  0x0ea12aa4; (* xtn      v4.2s, v21.2d *)
  0x4ea00ab3; (* rev64    v19.4s, v21.4s *)
  0x2ea4c33e; (* umull    v30.2d, v25.2s, v4.2s *)
  0x2ea5c337; (* umull    v23.2d, v25.2s, v5.2s *)
  0x4e9c5b94; (* uzp2     v20.4s, v28.4s, v28.4s *)
  0x4ebc9e73; (* mul      v19.4s, v19.4s, v28.4s *)
  0x6f6017d7; (* usra     v23.2d, v30.2d, #32 *)
  0x2ea5c292; (* umull    v18.2d, v20.2s, v5.2s *)
  0x6ea02a73; (* uaddlp   v19.2d, v19.4s *)
  0x4e201efe; (* and      v30.16b, v23.16b, v0.16b *)
  0x2ea4829e; (* umlal    v30.2d, v20.2s, v4.2s *)
  0x4f605673; (* shl      v19.2d, v19.2d, #32 *)
  0x6f6016f2; (* usra     v18.2d, v23.2d, #32 *)
  0x2ea48333; (* umlal    v19.2d, v25.2s, v4.2s *)
  0x6f6017d2; (* usra     v18.2d, v30.2d, #32 *)
  0x4e083e66; (* mov      x6, v19.d[0] *)
  0x4e183e61; (* mov      x1, v19.d[1] *)
  0x9b0a7ca4; (* mul      x4, x5, x10 *)
  0x4e083e42; (* mov      x2, v18.d[0] *)
  0xab020021; (* adds     x1, x1, x2 *)
  0x4e183e42; (* mov      x2, v18.d[1] *)
  0xba020084; (* adcs     x4, x4, x2 *)
  0x9bca7ca5; (* umulh    x5, x5, x10 *)
  0x9a1f00a2; (* adc      x2, x5, xzr *)
  0xab0600c5; (* adds     x5, x6, x6 *)
  0xba010026; (* adcs     x6, x1, x1 *)
  0xba040081; (* adcs     x1, x4, x4 *)
  0xba020044; (* adcs     x4, x2, x2 *)
  0x9a1f03e2; (* adc      x2, xzr, xzr *)
  0xab050231; (* adds     x17, x17, x5 *)
  0xba0601ef; (* adcs     x15, x15, x6 *)
  0xba0101ad; (* adcs     x13, x13, x1 *)
  0xba0400e7; (* adcs     x7, x7, x4 *)
  0xba02018c; (* adcs     x12, x12, x2 *)
  0x9a1f0202; (* adc      x2, x16, xzr *)
  0xb26083e5; (* mov      x5, #0xffffffff00000001         // #-4294967295 *)
  0xb2407fe6; (* mov      x6, #0xffffffff                 // #4294967295 *)
  0xd2800021; (* mov      x1, #0x1                        // #1 *)
  0xab05007f; (* cmn      x3, x5 *)
  0xba06023f; (* adcs     xzr, x17, x6 *)
  0xba0101ff; (* adcs     xzr, x15, x1 *)
  0xba1f01bf; (* adcs     xzr, x13, xzr *)
  0xba1f00ff; (* adcs     xzr, x7, xzr *)
  0xba1f019f; (* adcs     xzr, x12, xzr *)
  0x9a1f0042; (* adc      x2, x2, xzr *)
  0xcb0203e4; (* neg      x4, x2 *)
  0x8a0400a2; (* and      x2, x5, x4 *)
  0xab02006a; (* adds     x10, x3, x2 *)
  0x8a0400c2; (* and      x2, x6, x4 *)
  0xba020225; (* adcs     x5, x17, x2 *)
  0x8a040022; (* and      x2, x1, x4 *)
  0xba0201e6; (* adcs     x6, x15, x2 *)
  0xba1f01a1; (* adcs     x1, x13, xzr *)
  0xba1f00e4; (* adcs     x4, x7, xzr *)
  0x9a1f0182; (* adc      x2, x12, xzr *)
  0xa900140a; (* stp      x10, x5, [x0] *)
  0xa9010406; (* stp      x6, x1, [x0, #16] *)
  0xa9020804; (* stp      x4, x2, [x0, #32] *)
  0xd65f03c0; (* ret *)
];;

let bignum_montsqr_p384_interm1_mc =
  define_mc_from_intlist "bignum_montsqr_p384_interm1_mc" bignum_montsqr_p384_interm1_ops;;

let BIGNUM_MONTSQR_P384_INTERM1_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p384_interm1_mc;;

let bignum_montsqr_p384_interm1_core_mc_def,
    bignum_montsqr_p384_interm1_core_mc,
    BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p384_interm1_core_mc"
    bignum_montsqr_p384_interm1_mc
    (`0`,`LENGTH bignum_montsqr_p384_interm1_mc - 4`)
    (fst BIGNUM_MONTSQR_P384_INTERM1_EXEC);;

let montsqr_p384_eqin = new_definition
  `!s1 s1' x z.
    (montsqr_p384_eqin:(armstate#armstate)->int64->int64->bool) (s1,s1') x z <=>
     (C_ARGUMENTS [z; x] s1 /\
      C_ARGUMENTS [z; x] s1' /\
      ?a. bignum_from_memory (x,6) s1 = a /\
          bignum_from_memory (x,6) s1' = a)`;;

let montsqr_p384_eqout = new_definition
  `!s1 s1' z.
    (montsqr_p384_eqout:(armstate#armstate)->int64->bool) (s1,s1') z <=>
    (?a.
      bignum_from_memory (z,6) s1 = a /\
      bignum_from_memory (z,6) s1' = a)`;;

(* This diff is generated by tools/gen-actions.py.
   To get this diff you will need an 'original register name'
   version of the bignum_montsqr_p384_interm1_mc. *)
let actions = [
  ("equal", 0, 1, 0, 1);
  ("insert", 1, 1, 1, 3);
  ("equal", 1, 3, 3, 5);
  ("insert", 3, 3, 5, 7);
  ("equal", 3, 6, 7, 10);
  ("replace", 6, 8, 10, 30);
  ("equal", 8, 15, 30, 37);
  ("replace", 15, 17, 37, 39);
  ("equal", 17, 206, 39, 228);
  ("replace", 206, 208, 228, 235);
  ("equal", 208, 217, 235, 244);
  ("replace", 217, 219, 244, 265);
  ("equal", 219, 220, 265, 266);
  ("replace", 220, 221, 266, 267);
  ("equal", 221, 222, 267, 268);
  ("replace", 222, 223, 268, 269);
  ("equal", 223, 260, 269, 306);
];;

let actions = break_equal_loads actions
    (snd BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC) 0x0
    (snd BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC) 0x0;;

let equiv_goal1 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montsqr_p384_unopt_core_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p384_interm1_core_mc)]`
    montsqr_p384_eqin
    montsqr_p384_eqout
    bignum_montsqr_p384_unopt_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montsqr_p384_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

let _org_extra_word_CONV = !extra_word_CONV;;
extra_word_CONV :=
  [GEN_REWRITE_CONV I [WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO; WORD_MUL64_HI;
                       WORD_SQR128_DIGIT0]]
  @ (!extra_word_CONV);;

let BIGNUM_MONTSQR_P384_CORE_EQUIV1 = time prove(equiv_goal1,

  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC;
    fst BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p384_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Start *)
  EQUIV_STEPS_TAC actions
    BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
    BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p384_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,6) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;

extra_word_CONV := _org_extra_word_CONV;;



(******************************************************************************
  The second program equivalence between the core part of intermediate
  program and fully optimized program
******************************************************************************)

let bignum_montsqr_p384_mc =
  define_from_elf "bignum_montsqr_p384_mc"
    "arm/p384/bignum_montsqr_p384.o";;

let BIGNUM_MONTSQR_P384_EXEC =
    ARM_MK_EXEC_RULE bignum_montsqr_p384_mc;;

let bignum_montsqr_p384_core_mc_def,
    bignum_montsqr_p384_core_mc,
    BIGNUM_MONTSQR_P384_CORE_EXEC =
  mk_sublist_of_mc "bignum_montsqr_p384_core_mc"
    bignum_montsqr_p384_mc
    (`0`,`LENGTH bignum_montsqr_p384_mc - 4`)
    (fst BIGNUM_MONTSQR_P384_EXEC);;


let equiv_goal2 = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montsqr_p384_interm1_core_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p384_core_mc)]`
    montsqr_p384_eqin
    montsqr_p384_eqout
    bignum_montsqr_p384_interm1_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montsqr_p384_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

(* Line numbers from the fully optimized prog. to the intermediate prog.
   The script that prints this map is being privately maintained by aqjune-aws.
   This map can be also printed from the instruction map of SLOTHY's output, but
   aqjune-aws does not have the converter. *)

let inst_map = [
3;1;2;4;15;12;32;14;19;7;13;6;18;5;34;22;16;9;17;230;229;25;21;10;27;231;20;36;11;247;33;23;35;26;245;37;29;24;8;30;232;248;250;51;253;233;28;41;40;52;254;249;42;53;43;252;44;251;38;256;45;257;246;54;255;55;46;31;260;39;47;56;48;258;49;57;259;261;50;58;262;59;60;61;66;62;67;263;63;68;64;65;69;104;70;71;72;73;74;75;76;81;103;77;82;78;83;79;80;84;85;86;87;88;89;90;102;91;92;93;100;94;96;95;101;116;97;118;117;98;99;105;106;107;119;120;123;121;122;124;108;109;110;111;112;113;114;125;115;132;134;133;147;148;149;135;139;136;126;127;137;128;129;138;130;131;150;154;151;141;142;140;152;143;144;145;171;153;146;157;155;158;168;156;159;174;160;161;271;162;163;164;165;166;167;169;170;266;172;173;238;178;179;175;265;176;180;177;181;241;182;183;184;185;186;187;188;193;189;194;190;195;191;192;196;197;199;198;200;201;202;208;203;204;209;269;210;205;267;206;207;211;212;268;270;214;213;272;215;227;216;217;218;264;219;220;221;222;273;274;234;275;236;276;277;223;224;225;226;228;235;237;285;239;240;242;243;244;278;279;280;281;284;282;286;283;287;288;289;290;291;292;293;294;295;296;297;298;299;300;304;301;302;305;303;306];;


(* (state number, (equation, fresh var)) *)
let state_to_abbrevs: (int * thm) list ref = ref [];;

let BIGNUM_MONTSQR_P384_CORE_EQUIV2 = time prove(
  equiv_goal2,

  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC;
    fst BIGNUM_MONTSQR_P384_CORE_EXEC] THEN
  REPEAT STRIP_TAC THEN
  (** Initialize **)
  EQUIV_INITIATE_TAC montsqr_p384_eqin THEN
  RULE_ASSUM_TAC (REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

  (* Left *)
  ARM_N_STEPS_AND_ABBREV_TAC BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC
    (1--(List.length inst_map)) state_to_abbrevs None THEN

  (* Right *)
  ARM_N_STEPS_AND_REWRITE_TAC BIGNUM_MONTSQR_P384_CORE_EXEC
    (1--(List.length inst_map)) inst_map state_to_abbrevs None THEN

  REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
  (* Prove remaining clauses from the postcondition *)
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    (** SUBGOAL 1. Outputs **)
    ASM_REWRITE_TAC[montsqr_p384_eqout;mk_equiv_regs;mk_equiv_bool_regs;
                    BIGNUM_EXPAND_CONV `bignum_from_memory (ptr,6) state`;
                    C_ARGUMENTS] THEN
    REPEAT (HINT_EXISTS_REFL_TAC THEN ASM_REWRITE_TAC[]);

    (** SUBGOAL 2. Maychange pair **)
    MONOTONE_MAYCHANGE_CONJ_TAC
  ]);;


(******************************************************************************
  Use transitivity of two program equivalences to prove end-to-end
  correctness
******************************************************************************)

let equiv_goal = mk_equiv_statement_simple
    `ALL (nonoverlapping (z:int64,8 * 6))
      [(word pc:int64,LENGTH bignum_montsqr_p384_unopt_core_mc);
       (word pc2:int64,LENGTH bignum_montsqr_p384_core_mc)]`
    montsqr_p384_eqin
    montsqr_p384_eqout
    bignum_montsqr_p384_unopt_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`
    bignum_montsqr_p384_core_mc
    `MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
     MAYCHANGE MODIFIABLE_SIMD_REGS ,,
     MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]`;;

let montsqr_p384_eqout_TRANS = prove(
  `!s s2 s'
    z. montsqr_p384_eqout (s,s') z /\ montsqr_p384_eqout (s',s2) z
    ==> montsqr_p384_eqout (s,s2) z`,
  MESON_TAC[montsqr_p384_eqout]);;

let BIGNUM_MONTSQR_P384_CORE_EQUIV = time prove(equiv_goal,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?pc3.
      ALL (nonoverlapping (z:int64,8 * 6))
        [(word pc:int64,LENGTH bignum_montsqr_p384_unopt_core_mc);
        (word pc3:int64,LENGTH bignum_montsqr_p384_interm1_core_mc)] /\
      ALL (nonoverlapping (z:int64,8 * 6))
        [(word pc3:int64,LENGTH bignum_montsqr_p384_interm1_core_mc);
        (word pc2:int64,LENGTH bignum_montsqr_p384_core_mc)] /\
      // Input buffers and the intermediate program don't alias
      ALL (nonoverlapping
        (word pc3:int64, LENGTH bignum_montsqr_p384_interm1_core_mc))
        [x,8 * 6] /\
      4 divides val (word pc3:int64)`
      MP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [ALL;NONOVERLAPPING_CLAUSES;
       fst BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC;
       fst BIGNUM_MONTSQR_P384_CORE_EXEC;
       GSYM CONJ_ASSOC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    FIND_HOLE_TAC;

    ALL_TAC
  ] THEN
  STRIP_TAC THEN

  EQUIV_TRANS_TAC
    (BIGNUM_MONTSQR_P384_CORE_EQUIV1,BIGNUM_MONTSQR_P384_CORE_EQUIV2)
    (montsqr_p384_eqin,montsqr_p384_eqin,montsqr_p384_eqin)
    montsqr_p384_eqout_TRANS
    (BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC,BIGNUM_MONTSQR_P384_INTERM1_CORE_EXEC,
     BIGNUM_MONTSQR_P384_CORE_EXEC));;


(******************************************************************************
          Inducing BIGNUM_MONTSQR_P384_SUBROUTINE_CORRECT
          from BIGNUM_MONTSQR_P384_UNOPT_CORE_CORRECT
******************************************************************************)

(* Prove BIGNUM_MONTSQR_P384_UNOPT_CORE_CORRECT_N first *)

let event_n_at_pc_goal = mk_eventually_n_at_pc_statement_simple
    `nonoverlapping
      (word pc:int64,
        LENGTH (APPEND bignum_montsqr_p384_unopt_core_mc barrier_inst_bytes))
      (z:int64,8 * 6)`
    [`z:int64`;`x:int64`] bignum_montsqr_p384_unopt_core_mc
    `\s0. C_ARGUMENTS [z;x] s0`;;

let BIGNUM_MONTSQR_P384_EVENTUALLY_N_AT_PC = prove(event_n_at_pc_goal,

  REWRITE_TAC[LENGTH_APPEND;fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC;BARRIER_INST_BYTES_LENGTH] THEN
  REWRITE_TAC[eventually_n_at_pc;ALL;NONOVERLAPPING_CLAUSES;C_ARGUMENTS] THEN
  SUBGOAL_THEN `4 divides (LENGTH bignum_montsqr_p384_unopt_core_mc)`
        (fun th -> REWRITE_TAC[MATCH_MP aligned_bytes_loaded_append th;
                               fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC]) THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC] THEN CONV_TAC NUM_DIVIDES_CONV;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* now start..! *)
  X_GEN_TAC `s0:armstate` THEN GEN_TAC THEN STRIP_TAC THEN
  (* eventually ==> eventually_n *)
  PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC);;


let BIGNUM_MONTSQR_P384_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTSQR_P384_UNOPT_EXEC
    BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
    BIGNUM_MONTSQR_P384_UNOPT_CORE_CORRECT
    BIGNUM_MONTSQR_P384_EVENTUALLY_N_AT_PC;;

(* This theorem is a copy of BIGNUM_MONTSQR_P384_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - bignum_montsqr_p384_unopt_core_mc with bignum_montsqr_p384_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)

let BIGNUM_MONTSQR_P384_CORE_CORRECT = prove(
  `!z x a pc2.
        nonoverlapping (word pc2,LENGTH bignum_montsqr_p384_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p384_core_mc /\
                  read PC s = word pc2 /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc2 + LENGTH bignum_montsqr_p384_core_mc) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program. This is going to be used
     for preparing an initial state by 'overwriting' bignum_montsqr_p384_unopt_mc
     at pc. *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p384_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p384_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 6) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTSQR_P384_CORE_EQUIV BIGNUM_MONTSQR_P384_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC,BIGNUM_MONTSQR_P384_CORE_EXEC)
    (montsqr_p384_eqin,montsqr_p384_eqout));;

let BIGNUM_MONTSQR_P384_CORRECT = time prove(
  `!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read PC s = word (pc) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p384_core_mc) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_MONTSQR_P384_CORE_CORRECT
    bignum_montsqr_p384_core_mc_def
    [fst BIGNUM_MONTSQR_P384_CORE_EXEC;
     fst BIGNUM_MONTSQR_P384_EXEC]);;

let BIGNUM_MONTSQR_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[fst BIGNUM_MONTSQR_P384_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P384_EXEC
    (REWRITE_RULE [fst BIGNUM_MONTSQR_P384_EXEC;
        fst BIGNUM_MONTSQR_P384_CORE_EXEC]
      BIGNUM_MONTSQR_P384_CORRECT));;

(******************************************************************************
          Inducing BIGNUM_AMONTSQR_P384_SUBROUTINE_CORRECT
          from BIGNUM_AMONTSQR_P384_CORE_CORRECT
******************************************************************************)

let BIGNUM_AMONTSQR_P384_UNOPT_CORE_CORRECT_N =
  prove_ensures_n
    BIGNUM_MONTSQR_P384_UNOPT_EXEC
    BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC
    BIGNUM_AMONTSQR_P384_UNOPT_CORE_CORRECT
    BIGNUM_MONTSQR_P384_EVENTUALLY_N_AT_PC;;

(* This theorem is a copy of BIGNUM_MONTSQR_P384_CORE_CORRECT, but with
  - 'pc' replaced with 'pc2'
  - LENGTH of bignum_montsqr_p384_unopt_core_mc with
    bignum_montsqr_p384_core_mc
  - The MAYCHANGE set replaced with the Neon version's one *)

let BIGNUM_AMONTSQR_P384_CORE_CORRECT = prove(
  `!z x a pc2.
        nonoverlapping (word pc2,LENGTH bignum_montsqr_p384_core_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc2) bignum_montsqr_p384_core_mc /\
                  read PC s = word pc2 /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc2 + LENGTH bignum_montsqr_p384_core_mc) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2)
                   (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  REPEAT GEN_TAC THEN
  (* Prepare pc for the original program. This is going to be used
     for preparing an initial state by 'overwriting' bignum_montsqr_p384_unopt_mc
     at pc. *)
  SUBGOAL_THEN
    `?pc.
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p384_unopt_core_mc barrier_inst_bytes)) (z:int64,8 * 6) /\
      nonoverlapping (word pc,
        LENGTH (APPEND bignum_montsqr_p384_unopt_core_mc barrier_inst_bytes)) (x:int64,8 * 6) /\
      4 divides val (word pc:int64)` MP_TAC THENL [
    REWRITE_TAC[fst BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC;
        NONOVERLAPPING_CLAUSES;ALL;
        LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THEN
    FIND_HOLE_TAC;

    (** SUBGOAL 2 **)
    ALL_TAC
  ] THEN

  REPEAT_N 2 STRIP_TAC THEN

  PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    BIGNUM_MONTSQR_P384_CORE_EQUIV BIGNUM_AMONTSQR_P384_UNOPT_CORE_CORRECT_N
    (BIGNUM_MONTSQR_P384_UNOPT_CORE_EXEC,BIGNUM_MONTSQR_P384_CORE_EXEC)
    (montsqr_p384_eqin,montsqr_p384_eqout));;

let BIGNUM_AMONTSQR_P384_CORRECT = time prove(
  `!z x a pc.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read PC s = word (pc) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + LENGTH bignum_montsqr_p384_core_mc) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2)
                   (mod p_384))
             (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17] ,,
              MAYCHANGE MODIFIABLE_SIMD_REGS ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,

  ARM_SUB_LIST_OF_MC_TAC BIGNUM_AMONTSQR_P384_CORE_CORRECT
    bignum_montsqr_p384_core_mc_def
    [fst BIGNUM_MONTSQR_P384_CORE_EXEC;
     fst BIGNUM_MONTSQR_P384_EXEC]);;

let BIGNUM_AMONTSQR_P384_SUBROUTINE_CORRECT = time prove
 (`!z x a pc returnaddress.
        nonoverlapping (word pc,LENGTH bignum_montsqr_p384_mc) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = returnaddress /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2)
                  (mod p_384))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)])`,
  REWRITE_TAC[fst BIGNUM_MONTSQR_P384_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTSQR_P384_EXEC
    (REWRITE_RULE [fst BIGNUM_MONTSQR_P384_EXEC;
        fst BIGNUM_MONTSQR_P384_CORE_EXEC]
      BIGNUM_AMONTSQR_P384_CORRECT));;

