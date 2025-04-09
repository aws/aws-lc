(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery squaring modulo p_384.                                         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/p384/bignum_montsqr_p384_alt.o";;
 ****)

let bignum_montsqr_p384_alt_mc =
  define_assert_from_elf "bignum_montsqr_p384_alt_mc" "arm/p384/bignum_montsqr_p384_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0x9b037c49;       (* arm_MUL X9 X2 X3 *)
  0x9bc37c4a;       (* arm_UMULH X10 X2 X3 *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0x9b047c48;       (* arm_MUL X8 X2 X4 *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0x9b057c4b;       (* arm_MUL X11 X2 X5 *)
  0x9b047c68;       (* arm_MUL X8 X3 X4 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9bc57c4c;       (* arm_UMULH X12 X2 X5 *)
  0x9b057c68;       (* arm_MUL X8 X3 X5 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0x9b077c4d;       (* arm_MUL X13 X2 X7 *)
  0x9b067c68;       (* arm_MUL X8 X3 X6 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc77c4e;       (* arm_UMULH X14 X2 X7 *)
  0x9b077c68;       (* arm_MUL X8 X3 X7 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b067caf;       (* arm_MUL X15 X5 X6 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0x9bc67cb0;       (* arm_UMULH X16 X5 X6 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9bc47c48;       (* arm_UMULH X8 X2 X4 *)
  0xab08016b;       (* arm_ADDS X11 X11 X8 *)
  0x9bc47c68;       (* arm_UMULH X8 X3 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc57c68;       (* arm_UMULH X8 X3 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9bc67c68;       (* arm_UMULH X8 X3 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc77c68;       (* arm_UMULH X8 X3 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9a1f0210;       (* arm_ADC X16 X16 XZR *)
  0x9b067c48;       (* arm_MUL X8 X2 X6 *)
  0xab08018c;       (* arm_ADDS X12 X12 X8 *)
  0x9b057c88;       (* arm_MUL X8 X4 X5 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b067c88;       (* arm_MUL X8 X4 X6 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9b077c88;       (* arm_MUL X8 X4 X7 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b077ca8;       (* arm_MUL X8 X5 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9b077cd1;       (* arm_MUL X17 X6 X7 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0x9bc77cd3;       (* arm_UMULH X19 X6 X7 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0x9bc67c48;       (* arm_UMULH X8 X2 X6 *)
  0xab0801ad;       (* arm_ADDS X13 X13 X8 *)
  0x9bc57c88;       (* arm_UMULH X8 X4 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc67c88;       (* arm_UMULH X8 X4 X6 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9bc77c88;       (* arm_UMULH X8 X4 X7 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc77ca8;       (* arm_UMULH X8 X5 X7 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9a1f0273;       (* arm_ADC X19 X19 XZR *)
  0xab090129;       (* arm_ADDS X9 X9 X9 *)
  0xba0a014a;       (* arm_ADCS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0x9a9f37f4;       (* arm_CSET X20 Condition_CS *)
  0x9bc27c48;       (* arm_UMULH X8 X2 X2 *)
  0x9b027c42;       (* arm_MUL X2 X2 X2 *)
  0xab080129;       (* arm_ADDS X9 X9 X8 *)
  0x9b037c68;       (* arm_MUL X8 X3 X3 *)
  0xba08014a;       (* arm_ADCS X10 X10 X8 *)
  0x9bc37c68;       (* arm_UMULH X8 X3 X3 *)
  0xba08016b;       (* arm_ADCS X11 X11 X8 *)
  0x9b047c88;       (* arm_MUL X8 X4 X4 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9bc47c88;       (* arm_UMULH X8 X4 X4 *)
  0xba0801ad;       (* arm_ADCS X13 X13 X8 *)
  0x9b057ca8;       (* arm_MUL X8 X5 X5 *)
  0xba0801ce;       (* arm_ADCS X14 X14 X8 *)
  0x9bc57ca8;       (* arm_UMULH X8 X5 X5 *)
  0xba0801ef;       (* arm_ADCS X15 X15 X8 *)
  0x9b067cc8;       (* arm_MUL X8 X6 X6 *)
  0xba080210;       (* arm_ADCS X16 X16 X8 *)
  0x9bc67cc8;       (* arm_UMULH X8 X6 X6 *)
  0xba080231;       (* arm_ADCS X17 X17 X8 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0xba080273;       (* arm_ADCS X19 X19 X8 *)
  0x9bc77ce8;       (* arm_UMULH X8 X7 X7 *)
  0x9a080294;       (* arm_ADC X20 X20 X8 *)
  0xd3607c45;       (* arm_LSL X5 X2 32 *)
  0x8b0200a2;       (* arm_ADD X2 X5 X2 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc27ca5;       (* arm_UMULH X5 X5 X2 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b027c83;       (* arm_MUL X3 X4 X2 *)
  0x9bc27c84;       (* arm_UMULH X4 X4 X2 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba020084;       (* arm_ADCS X4 X4 X2 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050129;       (* arm_SUBS X9 X9 X5 *)
  0xfa04014a;       (* arm_SBCS X10 X10 X4 *)
  0xfa03016b;       (* arm_SBCS X11 X11 X3 *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xda1f0042;       (* arm_SBC X2 X2 XZR *)
  0xd3607d25;       (* arm_LSL X5 X9 32 *)
  0x8b0900a9;       (* arm_ADD X9 X5 X9 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bc97ca5;       (* arm_UMULH X5 X5 X9 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b097c83;       (* arm_MUL X3 X4 X9 *)
  0x9bc97c84;       (* arm_UMULH X4 X4 X9 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba090084;       (* arm_ADCS X4 X4 X9 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05014a;       (* arm_SUBS X10 X10 X5 *)
  0xfa04016b;       (* arm_SBCS X11 X11 X4 *)
  0xfa03018c;       (* arm_SBCS X12 X12 X3 *)
  0xfa1f01ad;       (* arm_SBCS X13 X13 XZR *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xd3607d45;       (* arm_LSL X5 X10 32 *)
  0x8b0a00aa;       (* arm_ADD X10 X5 X10 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bca7ca5;       (* arm_UMULH X5 X5 X10 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0a7c83;       (* arm_MUL X3 X4 X10 *)
  0x9bca7c84;       (* arm_UMULH X4 X4 X10 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0a0084;       (* arm_ADCS X4 X4 X10 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05016b;       (* arm_SUBS X11 X11 X5 *)
  0xfa04018c;       (* arm_SBCS X12 X12 X4 *)
  0xfa0301ad;       (* arm_SBCS X13 X13 X3 *)
  0xfa1f0042;       (* arm_SBCS X2 X2 XZR *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xda1f014a;       (* arm_SBC X10 X10 XZR *)
  0xd3607d65;       (* arm_LSL X5 X11 32 *)
  0x8b0b00ab;       (* arm_ADD X11 X5 X11 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcb7ca5;       (* arm_UMULH X5 X5 X11 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0b7c83;       (* arm_MUL X3 X4 X11 *)
  0x9bcb7c84;       (* arm_UMULH X4 X4 X11 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0b0084;       (* arm_ADCS X4 X4 X11 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb05018c;       (* arm_SUBS X12 X12 X5 *)
  0xfa0401ad;       (* arm_SBCS X13 X13 X4 *)
  0xfa030042;       (* arm_SBCS X2 X2 X3 *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xda1f016b;       (* arm_SBC X11 X11 XZR *)
  0xd3607d85;       (* arm_LSL X5 X12 32 *)
  0x8b0c00ac;       (* arm_ADD X12 X5 X12 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcc7ca5;       (* arm_UMULH X5 X5 X12 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0c7c83;       (* arm_MUL X3 X4 X12 *)
  0x9bcc7c84;       (* arm_UMULH X4 X4 X12 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0c0084;       (* arm_ADCS X4 X4 X12 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb0501ad;       (* arm_SUBS X13 X13 X5 *)
  0xfa040042;       (* arm_SBCS X2 X2 X4 *)
  0xfa030129;       (* arm_SBCS X9 X9 X3 *)
  0xfa1f014a;       (* arm_SBCS X10 X10 XZR *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xda1f018c;       (* arm_SBC X12 X12 XZR *)
  0xd3607da5;       (* arm_LSL X5 X13 32 *)
  0x8b0d00ad;       (* arm_ADD X13 X5 X13 *)
  0xb26083e5;       (* arm_MOV X5 (rvalue (word 18446744069414584321)) *)
  0x9bcd7ca5;       (* arm_UMULH X5 X5 X13 *)
  0xb2407fe4;       (* arm_MOV X4 (rvalue (word 4294967295)) *)
  0x9b0d7c83;       (* arm_MUL X3 X4 X13 *)
  0x9bcd7c84;       (* arm_UMULH X4 X4 X13 *)
  0xab0300a5;       (* arm_ADDS X5 X5 X3 *)
  0xba0d0084;       (* arm_ADCS X4 X4 X13 *)
  0x9a1f03e3;       (* arm_ADC X3 XZR XZR *)
  0xeb050042;       (* arm_SUBS X2 X2 X5 *)
  0xfa040129;       (* arm_SBCS X9 X9 X4 *)
  0xfa03014a;       (* arm_SBCS X10 X10 X3 *)
  0xfa1f016b;       (* arm_SBCS X11 X11 XZR *)
  0xfa1f018c;       (* arm_SBCS X12 X12 XZR *)
  0xda1f01ad;       (* arm_SBC X13 X13 XZR *)
  0xab0e0042;       (* arm_ADDS X2 X2 X14 *)
  0xba0f0129;       (* arm_ADCS X9 X9 X15 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xba13018c;       (* arm_ADCS X12 X12 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xb26083e8;       (* arm_MOV X8 (rvalue (word 18446744069414584321)) *)
  0xab08004e;       (* arm_ADDS X14 X2 X8 *)
  0xb2407fe8;       (* arm_MOV X8 (rvalue (word 4294967295)) *)
  0xba08012f;       (* arm_ADCS X15 X9 X8 *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xba080150;       (* arm_ADCS X16 X10 X8 *)
  0xba1f0171;       (* arm_ADCS X17 X11 XZR *)
  0xba1f0193;       (* arm_ADCS X19 X12 XZR *)
  0xba1f01b4;       (* arm_ADCS X20 X13 XZR *)
  0xba1f00c6;       (* arm_ADCS X6 X6 XZR *)
  0x9a8e0042;       (* arm_CSEL X2 X2 X14 Condition_EQ *)
  0x9a8f0129;       (* arm_CSEL X9 X9 X15 Condition_EQ *)
  0x9a90014a;       (* arm_CSEL X10 X10 X16 Condition_EQ *)
  0x9a91016b;       (* arm_CSEL X11 X11 X17 Condition_EQ *)
  0x9a93018c;       (* arm_CSEL X12 X12 X19 Condition_EQ *)
  0x9a9401ad;       (* arm_CSEL X13 X13 X20 Condition_EQ *)
  0xa9002402;       (* arm_STP X2 X9 X0 (Immediate_Offset (iword (&0))) *)
  0xa9012c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&16))) *)
  0xa902340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&32))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTSQR_P384_ALT_EXEC = ARM_MK_EXEC_RULE bignum_montsqr_p384_alt_mc;;

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

let BIGNUM_MONTSQR_P384_ALT_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x368) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_alt_mc /\
                  read PC s = word(pc + 0x4) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + 0x360) /\
                  (a EXP 2 <= 2 EXP 384 * p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                         X11; X12; X13; X14; X15; X16; X17; X19; X20] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the a EXP 2 <= 2 EXP 384 * p_384  assumption ***)

  ASM_CASES_TAC `a EXP 2 <= 2 EXP 384 * p_384` THENL
   [ASM_REWRITE_TAC[]; ARM_SIM_TAC BIGNUM_MONTSQR_P384_ALT_EXEC (1--215)] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Main squaring block ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_ALT_EXEC (1--93) (1--93) THEN

  (*** Main Montgomery reduction block ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_ALT_EXEC
   (allpairs (fun i j -> 16 * i + j) (0--5)
             [97;99;101;102;104;105;106;107;108;109] @
    (190--196))
   (94--196) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL]) THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Key properties of pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s190; sum_s191; sum_s192; sum_s193; sum_s194; sum_s195;
          word(bitval carry_s195)]` THEN
  SUBGOAL_THEN
   `t < 2 * p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `ab <= 2 EXP 384 * p
         ==> 2 EXP 384 * t < ab + 2 EXP 384 * p ==> t < 2 * p`)) THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

 (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_ALT_EXEC
   [198;200;202;203;204;205;206] (197--215) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_BITVAL; COND_SWAP; REAL_BITVAL_NOT]) THEN
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
   `val(word_add (word(bitval carry_s195))
                 (word(bitval carry_s205)):int64) = 0 <=>
    t < p_384`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `carry_s195:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
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

let BIGNUM_MONTSQR_P384_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,0x368) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,0x368); (x,8 * 6); (z,8 * 6)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,6) s = a)
           (\s. read PC s = returnaddress /\
                (a EXP 2 <= 2 EXP 384 * p_384
                 ==> bignum_from_memory (z,6) s =
                     (inverse_mod p_384 (2 EXP 384) * a EXP 2) MOD p_384))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 6);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTSQR_P384_ALT_EXEC BIGNUM_MONTSQR_P384_ALT_CORRECT
   `[X19;X20]` 16);;

(* ------------------------------------------------------------------------- *)
(* Show that it also works as "almost-Montgomery" if desired. That is, even  *)
(* without the further range assumption on inputs we still get a congruence. *)
(* But the output, still 384 bits, may then not be fully reduced mod p_384.  *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_AMONTSQR_P384_ALT_CORRECT = time prove
 (`!z x a pc.
        nonoverlapping (word pc,0x368) (z,8 * 6)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_alt_mc /\
                  read PC s = word(pc + 0x4) /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = a)
             (\s. read PC s = word (pc + 0x360) /\
                  (bignum_from_memory (z,6) s ==
                   inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
             (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                         X11; X12; X13; X14; X15; X16; X17; X19; X20] ,,
              MAYCHANGE [memory :> bytes(z,8 * 6)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,6) s0` THEN

  (*** Main squaring block ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_ALT_EXEC (1--93) (1--93) THEN

  (*** Main Montgomery reduction block ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_ALT_EXEC
   (allpairs (fun i j -> 16 * i + j) (0--5)
             [97;99;101;102;104;105;106;107;108;109] @
    (190--196))
   (94--196) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; COND_SWAP; GSYM WORD_BITVAL]) THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP mmlemma th with Failure _ -> th) THEN

  (*** Key properties of pre-reduced result ***)

  ABBREV_TAC
   `t = bignum_of_wordlist
         [sum_s190; sum_s191; sum_s192; sum_s193; sum_s194; sum_s195;
          word(bitval carry_s195)]` THEN
  SUBGOAL_THEN
   `t < 2 EXP 384 + p_384 /\ (2 EXP 384 * t == a EXP 2) (mod p_384)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    ACCUMULATOR_POP_ASSUM_LIST
     (STRIP_ASSUME_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `2 EXP 384 * t <= (2 EXP 384 - 1) EXP 2 + (2 EXP 384 - 1) * p
        ==> t < 2 EXP 384 + p`) THEN
      REWRITE_TAC[p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      REWRITE_TAC[p_384; REAL_ARITH `a:real < b + c <=> a - b < c`] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN BOUNDER_TAC[];
      REWRITE_TAC[REAL_CONGRUENCE; p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MAP_EVERY EXPAND_TAC ["a"; "t"] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
      ASM_REWRITE_TAC[VAL_WORD_BITVAL] THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction stage ***)

  ARM_ACCSTEPS_TAC BIGNUM_MONTSQR_P384_ALT_EXEC
   [198;200;202;203;204;205;206] (197--215) THEN
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
   `val(word_add (word(bitval carry_s195))
                 (word(bitval carry_s205)):int64) = 0 <=>
    t < p_384`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    SIMP_TAC[ADD_EQ_0; BITVAL_EQ_0; BITVAL_BOUND; ARITH_RULE
     `a <= 1 /\ b <= 1 ==> a + b < 2 EXP 64`] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[bignum_of_wordlist; VAL_WORD_BITVAL] THEN
    ASM_CASES_TAC `carry_s195:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
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

let BIGNUM_AMONTSQR_P384_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x a pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,0x368) (z,8 * 6) /\
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,0x368); (x,8 * 6); (z,8 * 6)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montsqr_p384_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,6) s = a)
           (\s. read PC s = returnaddress /\
                (bignum_from_memory (z,6) s ==
                 inverse_mod p_384 (2 EXP 384) * a EXP 2) (mod p_384))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * 6);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MONTSQR_P384_ALT_EXEC BIGNUM_AMONTSQR_P384_ALT_CORRECT
   `[X19;X20]` 16);;
