(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiply-add mod n_25519, basepoint order for curve25519/edwards25519.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/curve25519/bignum_madd_n25519_alt.o";;
 ****)

let bignum_madd_n25519_alt_mc =
  define_assert_from_elf "bignum_madd_n25519_alt_mc" "arm/curve25519/bignum_madd_n25519_alt.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xaa0003f3;       (* arm_MOV X19 X0 *)
  0xa940382d;       (* arm_LDP X13 X14 X1 (Immediate_Offset (iword (&0))) *)
  0xa9400047;       (* arm_LDP X7 X0 X2 (Immediate_Offset (iword (&0))) *)
  0x9b077da8;       (* arm_MUL X8 X13 X7 *)
  0x9bc77da9;       (* arm_UMULH X9 X13 X7 *)
  0x9b007db0;       (* arm_MUL X16 X13 X0 *)
  0x9bc07daa;       (* arm_UMULH X10 X13 X0 *)
  0xab100129;       (* arm_ADDS X9 X9 X16 *)
  0xa9411444;       (* arm_LDP X4 X5 X2 (Immediate_Offset (iword (&16))) *)
  0x9b047db0;       (* arm_MUL X16 X13 X4 *)
  0x9bc47dab;       (* arm_UMULH X11 X13 X4 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0x9b057db0;       (* arm_MUL X16 X13 X5 *)
  0x9bc57dac;       (* arm_UMULH X12 X13 X5 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0xa940186f;       (* arm_LDP X15 X6 X3 (Immediate_Offset (iword (&0))) *)
  0xab0f0108;       (* arm_ADDS X8 X8 X15 *)
  0xba060129;       (* arm_ADCS X9 X9 X6 *)
  0xa941186f;       (* arm_LDP X15 X6 X3 (Immediate_Offset (iword (&16))) *)
  0xba0f014a;       (* arm_ADCS X10 X10 X15 *)
  0xba06016b;       (* arm_ADCS X11 X11 X6 *)
  0x9a1f018c;       (* arm_ADC X12 X12 XZR *)
  0xa941182f;       (* arm_LDP X15 X6 X1 (Immediate_Offset (iword (&16))) *)
  0x9b077dd0;       (* arm_MUL X16 X14 X7 *)
  0xab100129;       (* arm_ADDS X9 X9 X16 *)
  0x9b007dd0;       (* arm_MUL X16 X14 X0 *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0x9b047dd0;       (* arm_MUL X16 X14 X4 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0x9b057dd0;       (* arm_MUL X16 X14 X5 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0x9bc57dcd;       (* arm_UMULH X13 X14 X5 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0x9bc77dd0;       (* arm_UMULH X16 X14 X7 *)
  0xab10014a;       (* arm_ADDS X10 X10 X16 *)
  0x9bc07dd0;       (* arm_UMULH X16 X14 X0 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0x9bc47dd0;       (* arm_UMULH X16 X14 X4 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0x9a1f01ad;       (* arm_ADC X13 X13 XZR *)
  0x9b077df0;       (* arm_MUL X16 X15 X7 *)
  0xab10014a;       (* arm_ADDS X10 X10 X16 *)
  0x9b007df0;       (* arm_MUL X16 X15 X0 *)
  0xba10016b;       (* arm_ADCS X11 X11 X16 *)
  0x9b047df0;       (* arm_MUL X16 X15 X4 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0x9b057df0;       (* arm_MUL X16 X15 X5 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9bc57dee;       (* arm_UMULH X14 X15 X5 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9bc77df0;       (* arm_UMULH X16 X15 X7 *)
  0xab10016b;       (* arm_ADDS X11 X11 X16 *)
  0x9bc07df0;       (* arm_UMULH X16 X15 X0 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0x9bc47df0;       (* arm_UMULH X16 X15 X4 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x9b077cd0;       (* arm_MUL X16 X6 X7 *)
  0xab10016b;       (* arm_ADDS X11 X11 X16 *)
  0x9b007cd0;       (* arm_MUL X16 X6 X0 *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0x9b047cd0;       (* arm_MUL X16 X6 X4 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9b057cd0;       (* arm_MUL X16 X6 X5 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0x9bc57ccf;       (* arm_UMULH X15 X6 X5 *)
  0x9a1f01ef;       (* arm_ADC X15 X15 XZR *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0xab10018c;       (* arm_ADDS X12 X12 X16 *)
  0x9bc07cd0;       (* arm_UMULH X16 X6 X0 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9bc47cd0;       (* arm_UMULH X16 X6 X4 *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
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

let BIGNUM_MADD_N25519_ALT_EXEC = ARM_MK_EXEC_RULE bignum_madd_n25519_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_25519 = define `n_25519 = 7237005577332262213973186563042994240857116359379907606001950938285454250989`;;

let BIGNUM_MADD_N25519_ALT_CORRECT = time prove
 (`!z x m y n c r pc.
      nonoverlapping (word pc,0x30c) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_madd_n25519_alt_mc /\
                read PC s = word(pc + 0x4) /\
                C_ARGUMENTS [z; x; y; c] s /\
                bignum_from_memory (x,4) s = m /\
                bignum_from_memory (y,4) s = n /\
                bignum_from_memory (c,4) s = r)
           (\s. read PC s = word (pc + 0x304) /\
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

  (*** Initial schoolbook multiply-add block ***)

  ENSURES_SEQUENCE_TAC `pc + 0x130`
   `\s. read X19 s = z /\
        bignum_of_wordlist
         [read X8 s; read X9 s; read X10 s; read X11 s;
          read X12 s; read X13 s; read X14 s; read X15 s] = m * n + r` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "x_" `read(memory :> bytes(x,8 * 4)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "y_" `read(memory :> bytes(y,8 * 4)) s0` THEN
    BIGNUM_LDIGITIZE_TAC "c_" `read(memory :> bytes(c,8 * 4)) s0` THEN
    ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC (1--75) (1--75) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"; "r"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
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

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
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

  ARM_ACCSTEPS_TAC BIGNUM_MADD_N25519_ALT_EXEC
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

let BIGNUM_MADD_N25519_ALT_SUBROUTINE_CORRECT = time prove
 (`!z x m y n c r pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,0x30c); (x,8 * 4); (y,8 * 4); (c,8 * 4); (z,8 * 4)] /\
      nonoverlapping (word pc,0x30c) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_madd_n25519_alt_mc /\
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
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_MADD_N25519_ALT_EXEC BIGNUM_MADD_N25519_ALT_CORRECT
   `[X19;X20]` 16);;
