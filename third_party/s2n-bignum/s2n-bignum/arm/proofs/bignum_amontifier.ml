(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Almost-Montgomerifier computation.                                        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_amontifier.o";;
 ****)

let bignum_amontifier_mc =
  define_assert_from_elf "bignum_amontifier_mc" "arm/generic/bignum_amontifier.o"
[
  0xb40018c0;       (* arm_CBZ X0 (word 792) *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xf8647849;       (* arm_LDR X9 X2 (Shiftreg_Offset X4 3) *)
  0xf8247869;       (* arm_STR X9 X3 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xf1000404;       (* arm_SUBS X4 X0 (rvalue (word 1)) *)
  0x540001a0;       (* arm_BEQ (word 52) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xeb1f013f;       (* arm_CMP X9 XZR *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa0703e9;       (* arm_MOV X9 X7 *)
  0xf8657867;       (* arm_LDR X7 X3 (Shiftreg_Offset X5 3) *)
  0x9a870129;       (* arm_CSEL X9 X9 X7 Condition_EQ *)
  0xf8257869;       (* arm_STR X9 X3 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000ab;       (* arm_SUB X11 X5 X0 *)
  0xb5ffff4b;       (* arm_CBNZ X11 (word 2097128) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffea1;       (* arm_BNE (word 2097108) *)
  0xdac01129;       (* arm_CLZ X9 X9 *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xf240153f;       (* arm_TST X9 (rvalue (word 63)) *)
  0xda9f03e8;       (* arm_CSETM X8 Condition_NE *)
  0xcb0903eb;       (* arm_NEG X11 X9 *)
  0xf8647865;       (* arm_LDR X5 X3 (Shiftreg_Offset X4 3) *)
  0x9ac920a7;       (* arm_LSL X7 X5 X9 *)
  0xaa0a00e7;       (* arm_ORR X7 X7 X10 *)
  0x9acb24aa;       (* arm_LSR X10 X5 X11 *)
  0x8a08014a;       (* arm_AND X10 X10 X8 *)
  0xf8247867;       (* arm_STR X7 X3 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffff03;       (* arm_BCC (word 2097120) *)
  0xd1000406;       (* arm_SUB X6 X0 (rvalue (word 1)) *)
  0xf8667866;       (* arm_LDR X6 X3 (Shiftreg_Offset X6 3) *)
  0xd280002b;       (* arm_MOV X11 (rvalue (word 1)) *)
  0xcb0603ea;       (* arm_NEG X10 X6 *)
  0xd28007c4;       (* arm_MOV X4 (rvalue (word 62)) *)
  0x8b0b016b;       (* arm_ADD X11 X11 X11 *)
  0xaa0603e7;       (* arm_MOV X7 X6 *)
  0xcb0a00e7;       (* arm_SUB X7 X7 X10 *)
  0xeb07015f;       (* arm_CMP X10 X7 *)
  0xda9f33e7;       (* arm_CSETM X7 Condition_CS *)
  0xcb07016b;       (* arm_SUB X11 X11 X7 *)
  0x8b0a014a;       (* arm_ADD X10 X10 X10 *)
  0x8a0600e7;       (* arm_AND X7 X7 X6 *)
  0xcb07014a;       (* arm_SUB X10 X10 X7 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffec1;       (* arm_BNE (word 2097112) *)
  0xeb06015f;       (* arm_CMP X10 X6 *)
  0x9a8b156b;       (* arm_CSINC X11 X11 X11 Condition_NE *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xab1f03e4;       (* arm_ADDS X4 XZR XZR *)
  0xf8647867;       (* arm_LDR X7 X3 (Shiftreg_Offset X4 3) *)
  0x9b077d68;       (* arm_MUL X8 X11 X7 *)
  0xba090108;       (* arm_ADCS X8 X8 X9 *)
  0x9bc77d69;       (* arm_UMULH X9 X11 X7 *)
  0xf8247828;       (* arm_STR X8 X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xcb000087;       (* arm_SUB X7 X4 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xd2e80007;       (* arm_MOVZ X7 (word 16384) 48 *)
  0xeb070129;       (* arm_SUBS X9 X9 X7 *)
  0xda9f33eb;       (* arm_CSETM X11 Condition_CS *)
  0xeb1f03e4;       (* arm_NEGS X4 XZR *)
  0xf8647867;       (* arm_LDR X7 X3 (Shiftreg_Offset X4 3) *)
  0xf864782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X4 3) *)
  0x8a0b00e7;       (* arm_AND X7 X7 X11 *)
  0xfa0a00e7;       (* arm_SBCS X7 X7 X10 *)
  0xf8247827;       (* arm_STR X7 X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xcb000087;       (* arm_SUB X7 X4 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xeb1f03e5;       (* arm_NEGS X5 XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0x93c9fce9;       (* arm_EXTR X9 X7 X9 (rvalue (word 63)) *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0xfa0a0129;       (* arm_SBCS X9 X9 X10 *)
  0xf8257829;       (* arm_STR X9 X1 (Shiftreg_Offset X5 3) *)
  0xaa0703e9;       (* arm_MOV X9 X7 *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff07;       (* arm_CBNZ X7 (word 2097120) *)
  0xd37ffd29;       (* arm_LSR X9 X9 (rvalue (word 63)) *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xab1f03e5;       (* arm_ADDS X5 XZR XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0x8a09014a;       (* arm_AND X10 X10 X9 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0xf8257827;       (* arm_STR X7 X1 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0xaa1f03e9;       (* arm_MOV X9 XZR *)
  0xeb1f03e5;       (* arm_NEGS X5 XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0x93c9fce9;       (* arm_EXTR X9 X7 X9 (rvalue (word 63)) *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0xfa0a0129;       (* arm_SBCS X9 X9 X10 *)
  0xf8257829;       (* arm_STR X9 X1 (Shiftreg_Offset X5 3) *)
  0xaa0703e9;       (* arm_MOV X9 X7 *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff07;       (* arm_CBNZ X7 (word 2097120) *)
  0xd37ffd29;       (* arm_LSR X9 X9 (rvalue (word 63)) *)
  0xda1f0129;       (* arm_SBC X9 X9 XZR *)
  0xab1f03e5;       (* arm_ADDS X5 XZR XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0x8a09014a;       (* arm_AND X10 X10 X9 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0xf8257827;       (* arm_STR X7 X1 (Shiftreg_Offset X5 3) *)
  0xf8257867;       (* arm_STR X7 X3 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff07;       (* arm_CBNZ X7 (word 2097120) *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa0003e4;       (* arm_MOV X4 X0 *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xab1f03e9;       (* arm_ADDS X9 XZR XZR *)
  0xf8657827;       (* arm_LDR X7 X1 (Shiftreg_Offset X5 3) *)
  0x9b077cc8;       (* arm_MUL X8 X6 X7 *)
  0xba09014a;       (* arm_ADCS X10 X10 X9 *)
  0x9bc77cc9;       (* arm_UMULH X9 X6 X7 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab080148;       (* arm_ADDS X8 X10 X8 *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0xf8257868;       (* arm_STR X8 X3 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5fffec7;       (* arm_CBNZ X7 (word 2097112) *)
  0xba090146;       (* arm_ADCS X6 X10 X9 *)
  0xda9f33e8;       (* arm_CSETM X8 Condition_CS *)
  0xab1f03e5;       (* arm_ADDS X5 XZR XZR *)
  0xf8657867;       (* arm_LDR X7 X3 (Shiftreg_Offset X5 3) *)
  0xf865782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X5 3) *)
  0x8a08014a;       (* arm_AND X10 X10 X8 *)
  0xba0a00e7;       (* arm_ADCS X7 X7 X10 *)
  0xf8257867;       (* arm_STR X7 X3 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0x9a1f00c6;       (* arm_ADC X6 X6 XZR *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffca1;       (* arm_BNE (word 2097044) *)
  0xf9400047;       (* arm_LDR X7 X2 (Immediate_Offset (word 0)) *)
  0xd37ef4eb;       (* arm_LSL X11 X7 (rvalue (word 2)) *)
  0xcb0b00eb;       (* arm_SUB X11 X7 X11 *)
  0xd27f016b;       (* arm_EOR X11 X11 (rvalue (word 2)) *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0x9b0b20e9;       (* arm_MADD X9 X7 X11 X8 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0x9b0b2d2b;       (* arm_MADD X11 X9 X11 X11 *)
  0x9b0a7d49;       (* arm_MUL X9 X10 X10 *)
  0x9b0b2d4b;       (* arm_MADD X11 X10 X11 X11 *)
  0x9b097d2a;       (* arm_MUL X10 X9 X9 *)
  0x9b0b2d2b;       (* arm_MADD X11 X9 X11 X11 *)
  0x9b0b2d4b;       (* arm_MADD X11 X10 X11 X11 *)
  0xf940006a;       (* arm_LDR X10 X3 (Immediate_Offset (word 0)) *)
  0x9b0b7d4b;       (* arm_MUL X11 X10 X11 *)
  0x9b077d68;       (* arm_MUL X8 X11 X7 *)
  0x9bc77d69;       (* arm_UMULH X9 X11 X7 *)
  0xd2800025;       (* arm_MOV X5 (rvalue (word 1)) *)
  0xd1000407;       (* arm_SUB X7 X0 (rvalue (word 1)) *)
  0xab08015f;       (* arm_CMN X10 X8 *)
  0xb40001a7;       (* arm_CBZ X7 (word 52) *)
  0xf8657847;       (* arm_LDR X7 X2 (Shiftreg_Offset X5 3) *)
  0xf865786a;       (* arm_LDR X10 X3 (Shiftreg_Offset X5 3) *)
  0x9b077d68;       (* arm_MUL X8 X11 X7 *)
  0xba09014a;       (* arm_ADCS X10 X10 X9 *)
  0x9bc77d69;       (* arm_UMULH X9 X11 X7 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab08014a;       (* arm_ADDS X10 X10 X8 *)
  0xd10004a7;       (* arm_SUB X7 X5 (rvalue (word 1)) *)
  0xf827786a;       (* arm_STR X10 X3 (Shiftreg_Offset X7 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5fffea7;       (* arm_CBNZ X7 (word 2097108) *)
  0xba0900c6;       (* arm_ADCS X6 X6 X9 *)
  0xda9f33e8;       (* arm_CSETM X8 Condition_CS *)
  0xd1000407;       (* arm_SUB X7 X0 (rvalue (word 1)) *)
  0xf8277866;       (* arm_STR X6 X3 (Shiftreg_Offset X7 3) *)
  0xeb1f03e5;       (* arm_NEGS X5 XZR *)
  0xf8657867;       (* arm_LDR X7 X3 (Shiftreg_Offset X5 3) *)
  0xf865784a;       (* arm_LDR X10 X2 (Shiftreg_Offset X5 3) *)
  0x8a08014a;       (* arm_AND X10 X10 X8 *)
  0xfa0a00e7;       (* arm_SBCS X7 X7 X10 *)
  0xf8257827;       (* arm_STR X7 X1 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000a7;       (* arm_SUB X7 X5 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_AMONTIFIER_EXEC = ARM_MK_EXEC_RULE bignum_amontifier_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** This actually works mod 32 but if anything this is more convenient ***)

let WORD_NEGMODINV_SEED_LEMMA_16 = prove
 (`!a x:int64.
        ODD a /\
        word_xor (word_sub (word a) (word_shl (word a) 2)) (word 2) = x
        ==> (a * val x + 1 == 0) (mod 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONG; MOD_0] THEN
  TRANS_TAC EQ_TRANS
   `(val(word a:int64) MOD 16 * val(x:int64) MOD 16 + 1) MOD 16` THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    REWRITE_TAC[VAL_MOD; NUMSEG_LT; ARITH_EQ; ARITH]] THEN
  SUBGOAL_THEN `bit 0 (word a:int64)` MP_TAC THENL
   [ASM_REWRITE_TAC[BIT_LSB_WORD];
    EXPAND_TAC "x" THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 1 (word a:int64)`;`bit 2 (word a:int64)`;`bit 3 (word a:int64)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** Copied from bignum_shl_small proof, similar logic to bitloop ***)

let lemma1 = prove
 (`!n c. word_and (word_jushr (word n) (word_neg (word c)))
                  (word_neg (word (bitval (~(c MOD 64 = 0))))):int64 =
         word_ushr (word n) (64 - c MOD 64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_AND_MASK; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR] THEN
    REWRITE_TAC[SUB_0] THEN MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[VAL_BOUND_64];
    W(MP_TAC o PART_MATCH (lhand o rand) WORD_JUSHR_NEG o lhand o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_64; MOD_64_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC DIVIDES_CONV]);;

(*** This is for the rather specific remainder computation below ***)

let remalemma = prove
 (`!x n q b.
        (x <= q * n <=> b) /\ ~(n divides x) /\ abs(&x - &q * &n:real) <= &n
        ==> &(x MOD n):real = &(bitval b) * &n + &x - &q * &n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM int_of_num_th; GSYM int_sub_th; GSYM int_add_th;
              GSYM int_mul_th; GSYM int_add_th; GSYM int_abs_th] THEN
  REWRITE_TAC[GSYM int_le; GSYM int_eq] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; num_divides] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MUL] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THENL
   [EXISTS_TAC `&q - &1:int`; EXISTS_TAC `&q:int`] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[INT_ABS_NUM; INT_MUL_LZERO; INT_MUL_LID; INT_ADD_LID] THEN
  REWRITE_TAC[INT_ARITH `n + x - qn:int < n <=> x < qn`] THEN
  REWRITE_TAC[INT_ARITH `x - q * n:int < n <=> x < (q + &1) * n`] THEN
  REWRITE_TAC[INT_LT_LE] THEN
  (CONJ_TAC THENL [ASM_INT_ARITH_TAC; DISCH_TAC]) THEN
  UNDISCH_TAC `~((&n:int) divides (&x))` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INTEGER_RULE);;

let BIGNUM_AMONTIFIER_CORRECT = time prove
 (`!k z m t n pc.
        nonoverlapping (z,8 * val k) (t,8 * val k) /\
        ALLPAIRS nonoverlapping [(z,8 * val k); (t,8 * val k)]
                                [(word pc,0x31c); (m,8 * val k)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_amontifier_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k; z; m; t] s /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = word(pc + 0x318) /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        2 EXP (128 * val k)) (mod n)))
             (MAYCHANGE [PC; X4; X5; X6; X7; X8; X9; X10; X11] ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(t,8 * val k)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `mm:int64`; `t:int64`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `m:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ODD];
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_1)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Initial copying into temporary buffer, "copyinloop" ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x8` `pc + 0x14`
   `\i s. (read X0 s = word k /\
           read X1 s = z /\
           read X2 s = mm /\
           read X3 s = t /\
           bignum_from_memory(mm,k) s = m /\
           read X4 s = word i /\
           bignum_from_memory(word_add mm (word(8 * i)),k - i) s =
           highdigits m i /\
           bignum_from_memory(t,i) s = lowdigits m i) /\
          (read X9 s = word(bigdigit m (i - 1)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_SUB] THEN ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2);
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** The digitwise normalization "normloop" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x54`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory(mm,k) s = m /\
        m divides bignum_from_memory(t,k) s /\
        read X9 s = word(bigdigit (bignum_from_memory(t,k) s) (k - 1)) /\
        (ODD m ==> 2 EXP (64 * (k - 1)) <= bignum_from_memory(t,k) s)` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--4) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF; DIVIDES_REFL; SUB_REFL] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP (64 * 0) <= m <=> ~(m = 0)`] THEN
      MESON_TAC[ODD];
      ALL_TAC] THEN

    MP_TAC(ARITH_RULE `k - 1 = 0 <=> k = 0 \/ k = 1`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    ENSURES_WHILE_PUP_TAC `k - 1` `pc + 0x24` `pc + 0x50`
     `\i s. (read X0 s = word k /\
             read X1 s = z /\
             read X2 s = mm /\
             read X3 s = t /\
             bignum_from_memory(mm,k) s = m /\
             read X4 s = word(k - 1 - i) /\
             read X9 s = word(bigdigit (bignum_from_memory(t,k) s) (k - 1)) /\
             m divides bignum_from_memory(t,k) s /\
             (ODD m ==> 2 EXP (64 * i) <= bignum_from_memory(t,k) s)) /\
            (read ZF s <=> i = k - 1)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`word k:int64`; `word 1:int64`] VAL_WORD_SUB_CASES) THEN
      ASM_SIMP_TAC[VAL_WORD_1; LE_1] THEN DISCH_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN
      ASM_SIMP_TAC[DIVIDES_REFL; WORD_SUB; LE_1] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP (64 * 0) <= m <=> ~(m = 0)`] THEN
      MESON_TAC[ODD];
      ALL_TAC; (*** Do the main loop invariant below ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1];
      ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1]] THEN

    (*** Nested loop "shufloop" ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `n:num` `bignum_from_memory (t,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ABBREV_TAC `topz <=> bigdigit n (k - 1) = 0` THEN

    ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x30` `pc + 0x44`
     `\j s. (read X0 s = word k /\
             read X1 s = z /\
             read X2 s = mm /\
             read X3 s = t /\
             bignum_from_memory (mm,k) s = m /\
             read X4 s = word (k - 1 - i) /\
             read X5 s = word j /\
             read X7 s = (if j = 0 then word 0 else word(bigdigit n (j - 1))) /\
             (read ZF s <=> topz) /\
             bignum_from_memory(word_add t (word(8 * j)),k - j) s =
             highdigits n j /\
             bignum_from_memory(t,j) s =
             lowdigits (if topz then 2 EXP 64 * n else n) j) /\
            (read X9 s =
             word(bigdigit (bignum_from_memory(t,j) s) (j - 1)))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--3) THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_0; HIGHDIGITS_0; SUB_0] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BIGNUM_FROM_MEMORY_BYTES];

      ALL_TAC; (*** Inner loop invariant below ***)

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      VAL_INT64_TAC `k - 1` THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [3] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> s) /\ q /\ r ==> p /\ q /\ r /\ s`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < k - 1 ==> 1 <= k - 1 - i`];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [DISCH_THEN SUBST1_TAC THEN
        W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o
          lhand o lhand o snd) THEN
        REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL
         [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `i < k - 1`] THEN ARITH_TAC;
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) LOWDIGITS_SELF o
        rand o lhand o snd) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "topz" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `n = lowdigits n ((k - 1) + 1)` SUBST1_TAC THENL
         [ASM_SIMP_TAC[SUB_ADD; LE_1; LOWDIGITS_SELF];
          ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_CLAUSES; MULT_CLAUSES]] THEN
        SUBGOAL_THEN `64 * k = 64 + 64 * (k - 1)` SUBST1_TAC THENL
         [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
        SIMP_TAC[LT_MULT_LCANCEL; LOWDIGITS_BOUND; EXP_EQ_0; ARITH_EQ];
        DISCH_THEN SUBST1_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[DIVIDES_LMUL; EXP_ADD; LE_MULT_LCANCEL; EXP_EQ_0;
                     ARITH_EQ; ARITH_RULE `64 * (i + 1) = 64 + 64 * i`];
        DISCH_TAC THEN TRANS_TAC LE_TRANS `2 EXP (64 * (k - 1))`] THEN
      ASM_SIMP_TAC[LE_EXP; ARITH_EQ; ARITH_RULE
        `i < k - 1 ==> 64 * (i + 1) <= 64 * (k - 1)`] THEN
      SUBGOAL_THEN `n = lowdigits n ((k - 1) + 1)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[SUB_ADD; LE_1; LOWDIGITS_SELF];
        ASM_REWRITE_TAC[LOWDIGITS_CLAUSES; ADD_CLAUSES; MULT_CLAUSES]] THEN
      MATCH_MP_TAC(ARITH_RULE `e * 1 <= e * d ==> e <= e * d + c`) THEN
      ASM_SIMP_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; LE_1]] THEN

    X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--5) THEN
    ASM_REWRITE_TAC[ADD_SUB; GSYM WORD_ADD; ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `j < j + 1`] THEN
    UNDISCH_THEN `bigdigit n (k - 1) = 0 <=> topz` (SUBST_ALL_TAC o SYM) THEN
    ASM_CASES_TAC `bigdigit n (k - 1) = 0` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LOWDIGITS_CLAUSES; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THENL
     [ALL_TAC; ARITH_TAC] THEN
    ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; EXP] THEN
    REWRITE_TAC[LOWDIGITS_0; VAL_WORD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[REWRITE_RULE[lowdigits] (GSYM LOWDIGITS_1)] THEN
    REWRITE_TAC[MULT_CLAUSES; MOD_MULT] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    MATCH_MP_TAC(NUM_RING `x:num = y ==> a + e * x = e * y + a`) THEN
    SUBGOAL_THEN `j = SUC(j - 1)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
    THENL [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[bigdigit; EXP_ADD; ARITH_RULE `64 * SUC j = 64 + 64 * j`] THEN
    SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ];

    ALL_TAC] THEN

  (*** Bitwise stage of normalization ***)

  ENSURES_SEQUENCE_TAC `pc + 0x90`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory(mm,k) s = m /\
        m divides bignum_from_memory(t,k) s /\
        (ODD m ==> 2 EXP (64 * k - 1) <= bignum_from_memory(t,k) s)` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `n:num` `bignum_from_memory (t,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN GLOBALIZE_PRECONDITION_TAC THEN

    (*** The "bitloop" loop ***)

    ABBREV_TAC `c = 64 - bitsize(bigdigit n (k - 1))` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x6c` `pc + 0x88`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = mm /\
            read X3 s = t /\
            bignum_from_memory (mm,k) s = m /\
            read X4 s = word i /\
            read X8 s = word_neg(word(bitval(~(c MOD 64 = 0)))) /\
            read X9 s = word c /\
            read X11 s = word_neg(word c) /\
            bignum_from_memory(word_add t (word (8 * i)),k - i) s =
            highdigits n i /\
            2 EXP (64 * i) * val(read X10 s) + bignum_from_memory(t,i) s =
            2 EXP (c MOD 64) * lowdigits n i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--6) THEN
      SIMP_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[LOWDIGITS_0; DIV_0; VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES;
                  WORD_ADD_0; HIGHDIGITS_0; SUB_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[WORD_SUB_LZERO] THEN
      SUBST1_TAC(SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)) THEN
      ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN REWRITE_TAC[GSYM WORD_MASK] THEN
      SUBST1_TAC(ARITH_RULE `63 = 2 EXP 6 - 1`) THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_64_CLAUSES] THEN
      SUBGOAL_THEN `word_clz(word(bigdigit n (k - 1)):int64) = c`
        (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[WORD_CLZ_BITSIZE; DIMINDEX_64] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `b:int64` `read X10` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - i = 0 <=> ~(i < n)`] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_64_CLAUSES; LOWDIGITS_CLAUSES] THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUM_RING
       `ee * b + m:num = c * l
        ==> e * d + y = c * z + b
            ==> (ee * e) * d + m + ee * y = c * (ee * z + l)`)) THEN
      REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL; lemma1] THEN
      REWRITE_TAC[word_jshl; MOD_64_CLAUSES; DIMINDEX_64; VAL_WORD_USHR] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o
        rand o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_0; BIT_WORD_AND] THEN
        SIMP_TAC[BIT_WORD_SHL; DIMINDEX_64] THEN MATCH_MP_TAC(MESON[]
         `(!i. q i ==> ~s i) ==> !i. p i ==> ~((q i /\ r i) /\ (s i))`) THEN
        REWRITE_TAC[UPPER_BITS_ZERO] THEN
        UNDISCH_THEN
         `2 EXP (64 * i) * val(b:int64) + read (memory :> bytes (t,8 * i)) s7 =
          2 EXP (c MOD 64) * lowdigits n i`
         (MP_TAC o AP_TERM `\x. x DIV 2 EXP (64 * i)`) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
        SIMP_TAC[DIV_LT; BIGNUM_FROM_MEMORY_BOUND; ADD_CLAUSES] THEN
        DISCH_THEN SUBST1_TAC THEN
        SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
        GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
        REWRITE_TAC[LT_MULT_LCANCEL; LOWDIGITS_BOUND; EXP_EQ_0; ARITH_EQ];
        DISCH_THEN SUBST1_TAC] THEN
      SIMP_TAC[VAL_WORD_SHL; VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      SUBGOAL_THEN `2 EXP 64 = 2 EXP (c MOD 64) * 2 EXP (64 - c MOD 64)`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[MOD_MULT2; GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB]] THEN
      REWRITE_TAC[DIVISION_SIMP];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2);

      GHOST_INTRO_TAC `b:int64` `read X10` THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2)] THEN

    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `e * b + z = cn
      ==> (e * b < e * 1 ==> e * b = 0)
          ==> cn < e ==> z = cn`)) THEN
    ANTS_TAC THENL
     [SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; MULT_EQ_0] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; EXP_LT_0; ARITH_EQ] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      ASM_REWRITE_TAC[CONJUNCT1 LE; EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `64 * k = c MOD 64 + (64 * k - c MOD 64)` SUBST1_TAC THENL
       [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
        REWRITE_TAC[EXP_ADD; LT_MULT_LCANCEL; ARITH_EQ; EXP_EQ_0]] THEN
      REWRITE_TAC[GSYM BITSIZE_LE] THEN
      SUBGOAL_THEN
       `n = 2 EXP (64 * (k - 1)) * highdigits n (k - 1) + lowdigits n (k - 1)`
      SUBST1_TAC THENL [REWRITE_TAC[HIGH_LOW_DIGITS]; ALL_TAC] THEN
      ASM_SIMP_TAC[HIGHDIGITS_TOP] THEN
      UNDISCH_THEN `64 - bitsize (bigdigit n (k - 1)) = c`
       (SUBST1_TAC o SYM) THEN
      ASM_CASES_TAC `bigdigit n (k - 1) = 0` THENL
       [ASM_REWRITE_TAC[BITSIZE_0; MULT_CLAUSES; ADD_CLAUSES] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITSIZE_LE; SUB_0] THEN
        TRANS_TAC LTE_TRANS `2 EXP (64 * (k - 1))` THEN
        ASM_REWRITE_TAC[LOWDIGITS_BOUND; LE_EXP; ARITH_EQ] THEN ARITH_TAC;
        ASM_SIMP_TAC[BITSIZE_MULT_ADD; LOWDIGITS_BOUND]] THEN
      MATCH_MP_TAC(ARITH_RULE `a + c <= b ==> a <= b - c MOD 64`) THEN
      MATCH_MP_TAC(ARITH_RULE
       `~(k = 0) /\ b <= 64 ==> (64 * (k - 1) + b) + (64 - b) <= 64 * k`) THEN
      ASM_REWRITE_TAC[BITSIZE_LE; BIGDIGIT_BOUND];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[DIVIDES_LMUL] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SUBGOAL_THEN `64 * k - 1 = c MOD 64 + (64 * k - 1 - c MOD 64)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      REWRITE_TAC[EXP_ADD; LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]] THEN
    REWRITE_TAC[GSYM NOT_LT; GSYM BITSIZE_LE] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `~(b = 0) /\ a <= b + c ==> a - 1 - c < b`) THEN
    ASM_REWRITE_TAC[BITSIZE_EQ_0] THEN
    UNDISCH_THEN `64 - bitsize (bigdigit n (k - 1)) = c`
     (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; highdigits; BITSIZE_DIV] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `b < a ==> 64 - (a - b) < 64`] THEN
    UNDISCH_TAC `64 * (k - 1) < bitsize n` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Introduce the multiple n, and abbreviations for high and low parts ***)

  GHOST_INTRO_TAC `n:num` `bignum_from_memory (t,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  ABBREV_TAC `h = bigdigit n (k - 1)` THEN
  ABBREV_TAC `l = lowdigits n (k - 1)` THEN

  SUBGOAL_THEN
   `h < 2 EXP 64 /\ l < 2 EXP (64 * (k - 1)) /\
    2 EXP (64 * (k - 1)) * h + l = n /\
    (ODD m ==> 2 EXP 63 <= h)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_THEN `bigdigit n (k - 1) = h` (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN `lowdigits n (k - 1) = l` (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LOWDIGITS_BOUND; BIGDIGIT_BOUND] THEN
    ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; HIGH_LOW_DIGITS] THEN
    SIMP_TAC[highdigits; LE_RDIV_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 64 * (k - 1) + 63 = 64 * k - 1`];
    ALL_TAC] THEN

  (**** The somewhat stupid quotient loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0xd8`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = n /\
        (ODD m ==> read X11 s = word(2 EXP 126 DIV h))` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_PUP_TAC `62` `pc + 0xa4` `pc + 0xcc`
     `\i s. (read X0 s = word k /\
             read X1 s = z /\
             read X2 s = mm /\
             read X3 s = t /\
             bignum_from_memory (mm,k) s = m /\
             bignum_from_memory (t,k) s = n /\
             read X6 s = word h /\
             read X4 s = word(62 - i) /\
             val(read X11 s) < 2 EXP (i + 1) /\
             (ODD m
              ==> val(read X11 s) * h + val(read X10 s) = 2 EXP (64 + i) /\
                  val(read X10 s) <= h)) /\
            (read ZF s <=> i = 62)` THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC;

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      MP_TAC(ISPECL [`k:num`; `t:int64`; `s0:armstate`; `k - 1`]
         BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - 1 < k <=> ~(k = 0)`] THEN
      DISCH_THEN(MP_TAC o SYM) THEN
      GEN_REWRITE_TAC LAND_CONV [VAL_WORD_GALOIS] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC THEN
      SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
      ASSUME_TAC THENL [ASM_SIMP_TAC[WORD_SUB; LE_1; VAL_WORD_1]; ALL_TAC] THEN
      VAL_INT64_TAC `k - 1` THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[VAL_WORD_1; EXP_1; ADD_CLAUSES; SUB_0; ARITH_RULE `1 < 2`] THEN
      DISCH_THEN(fun th -> REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MP th))) THEN
      REWRITE_TAC[WORD_SUB_LZERO; VAL_WORD_1; MULT_CLAUSES] THEN
      REWRITE_TAC[VAL_WORD_NEG_CASES; DIMINDEX_64] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`2 EXP 63 <= h`; `h < 2 EXP 64`] THEN ARITH_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `q:num` `\s. val(read X11 s)` THEN
      GHOST_INTRO_TAC `r:num` `\s. val(read X10 s)` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(SYM(WORD_REDUCE_CONV `word_not(word 0):int64`)) THEN
      ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN REWRITE_TAC[GSYM WORD_MASK] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
        GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64;
                   ARITH_RULE `i < 62 ==> (62 - (i + 1) = 0 <=> i + 1 = 62)`;
                   ARITH_RULE `62 - i < 2 EXP 64`] THEN
      REWRITE_TAC[WORD_RULE `word_sub x (word_neg y) = word_add x y`] THEN
      REWRITE_TAC[NOT_LT; GSYM WORD_ADD] THEN CONJ_TAC THENL
       [MATCH_MP_TAC VAL_WORD_LT THEN ONCE_REWRITE_TAC[EXP_ADD] THEN
        MATCH_MP_TAC(ARITH_RULE
         `q < i /\ b <= 1 ==> (q + q) + b < i * 2 EXP 1`) THEN
        ASM_REWRITE_TAC[BITVAL_BOUND];
        DISCH_THEN(fun th ->
          REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)))] THEN
      SUBST1_TAC(ISPECL
       [`word h:int64`; `word r:int64`] VAL_WORD_SUB_CASES) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
      ASM_SIMP_TAC[ARITH_RULE `r <= h ==> (h - r <= r <=> h <= 2 * r)`] THEN
      REWRITE_TAC[WORD_AND_MASK; GSYM MULT_2] THEN

      ASM_CASES_TAC `h <= 2 * r` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
      REWRITE_TAC[WORD_SUB_0; GSYM MULT_2] THENL
       [SUBGOAL_THEN
         `word_sub (word (2 * r)) (word h):int64 = word(2 * r - h)`
        SUBST1_TAC THENL [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
        SUBGOAL_THEN `2 * r - h < 2 EXP 64` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`r:num <= h`; `h < 2 EXP 64`] THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `2 * q + 1 < 2 EXP 64` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
           `q < 2 EXP (i + 1)
            ==> 2 EXP 1 * 2 EXP (i + 1) <= 2 EXP 64
                ==> 2 * q + 1 < 2 EXP 64`)) THEN
          REWRITE_TAC[GSYM EXP_ADD; LE_EXP; ARITH_EQ] THEN
          UNDISCH_TAC `i < 62` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
        REWRITE_TAC[ADD_ASSOC] THEN ONCE_REWRITE_TAC[EXP_ADD] THEN
        SIMPLE_ARITH_TAC;

        RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
        ASM_SIMP_TAC[VAL_WORD_LE; LT_IMP_LE] THEN
        SUBGOAL_THEN `2 * r < 2 EXP 64` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`2 * r < h`; `h < 2 EXP 64`] THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `2 * q < 2 EXP 64` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
           `q < 2 EXP (i + 1)
            ==> 2 EXP 1 * 2 EXP (i + 1) <= 2 EXP 64
                ==> 2 * q  < 2 EXP 64`)) THEN
          REWRITE_TAC[GSYM EXP_ADD; LE_EXP; ARITH_EQ] THEN
          UNDISCH_TAC `i < 62` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
        ASM_REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
        REWRITE_TAC[EXP_ADD] THEN ARITH_TAC];

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1];

      GHOST_INTRO_TAC `q:num` `\s. val(read X11 s)` THEN
      GHOST_INTRO_TAC `r:num` `\s. val(read X10 s)` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--3) THEN
      DISCH_THEN(fun th ->
        REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th))) THEN
      ASM_SIMP_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_EQ; DIMINDEX_64] THEN
      REWRITE_TAC[COND_SWAP; GSYM WORD_ADD] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `if r = h then 0 else r` THEN
      UNDISCH_TAC `q * h + r = 2 EXP (64 + 62)` THEN
      UNDISCH_TAC `r:num <= h` THEN REWRITE_TAC[LE_LT] THEN
      UNDISCH_TAC `2 EXP 63 <= h` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LT_REFL] THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Ghost the quotient estimate q = floor(2^126/h) ***)

  GHOST_INTRO_TAC `q:int64` `read X11` THEN GLOBALIZE_PRECONDITION_TAC THEN

  (*** The "mulloop" doing q * n ***)

  ENSURES_SEQUENCE_TAC `pc + 0x104`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = n /\
        2 EXP (64 * k) * val(read X9 s) + bignum_from_memory(z,k) s =
        val(q:int64) * n` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `k:num` `pc + 0xe0` `pc + 0xf8`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = mm /\
            read X3 s = t /\
            bignum_from_memory (mm,k) s = m /\
            bignum_from_memory (t,k) s = n /\
            read X11 s = q /\
            read X4 s = word i /\
            bignum_from_memory(word_add t (word (8 * i)),k - i) s =
            highdigits n i /\
            2 EXP (64 * i) * (bitval(read CF s) + val(read X9 s)) +
            bignum_from_memory(z,i) s =
            val(q:int64) * lowdigits n i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_0; VAL_WORD_0] THEN
      REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; WORD_ADD_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X9` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [2;3] (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM WORD_ADD] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; MULT_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X9` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [3] [3] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ADD_SYM] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
       `ee * (e * c + s) + z = qn
        ==> (ee * e * c < ee * e * 1 ==> ee * e * c = 0) /\ qn < e * ee
            ==> ee * s + z = qn`)) THEN
      SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; MULT_EQ_0] THEN
      CONJ_TAC THENL [ARITH_TAC; MATCH_MP_TAC LT_MULT2] THEN
      ASM_REWRITE_TAC[VAL_BOUND_64]];
    ALL_TAC] THEN

  (*** The "remloop" producing remainder by sign-correction ***)
  (*** We introduce an exclusion of m = 1 temporarily here. ***)

  ENSURES_SEQUENCE_TAC `pc + 0x134`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = n /\
        (ODD m /\ ~(m = 1)
         ==> bignum_from_memory(z,k) s = 2 EXP (64 * k + 62) MOD n)` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `rhi:num` `\s. val(read X9 s)` THEN
    GHOST_INTRO_TAC `rlo:num` `bignum_from_memory (z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `rlo:num` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ABBREV_TAC `b <=> 2 EXP (64 * k + 62) <= val(q:int64) * n` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x114` `pc + 0x12c`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = mm /\
            read X3 s = t /\
            read X4 s = word i /\
            bignum_from_memory (mm,k) s = m /\
            bignum_from_memory (t,k) s = n /\
            read X11 s = word_neg(word(bitval b)) /\
            bignum_from_memory(word_add t (word (8 * i)),k - i) s =
            highdigits n i /\
            bignum_from_memory(word_add z (word (8 * i)),k - i) s =
            highdigits rlo i /\
            &(bignum_from_memory(z,i) s):real =
            &2 pow (64 * i) * &(bitval(~(read CF s))) +
            (&(bitval b) * &(lowdigits n i) - &(lowdigits rlo i))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--4) THEN
      REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0; HIGHDIGITS_0] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0; BITVAL_CLAUSES] THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; BIGNUM_FROM_MEMORY_BYTES] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[WORD_MASK] THEN
      EXPAND_TAC "b" THEN REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
      CONV_TAC WORD_REDUCE_CONV THEN AP_THM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ARITH_RULE `x = x + 0`] THEN
      ASM_SIMP_TAC[LEXICOGRAPHIC_LT; EXP_LT_0; ARITH_EQ] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM WORD_ADD] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[REAL_POW_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_0; MULT_CLAUSES] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      CONV_TAC REAL_RING;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `r:num` `bignum_from_memory (z,k)` THEN
      BIGNUM_TERMRANGE_TAC `k:num` `r:num` THEN
      REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
      DISCH_THEN(fun th -> REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MP th)))] THEN
    UNDISCH_TAC `2 EXP (64 * k - 1) <= n` THEN ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[CONJUNCT1 LE; EXP_EQ_0; ARITH_EQ] THEN DISCH_TAC THEN

    SUBGOAL_THEN `val(q:int64) = 2 EXP 126 DIV h` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN MATCH_MP_TAC(ARITH_RULE
       `x <= 2 EXP 126 DIV 2 EXP 63 ==> x < 2 EXP 64`) THEN
      MATCH_MP_TAC DIV_MONO2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      UNDISCH_THEN `q:int64 = word(2 EXP 126 DIV h)` (K ALL_TAC)] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
    MAP_EVERY EXISTS_TAC
     [`64 * k`;
      `&(bitval b) * &n +
       (&2 pow (64 * k + 62) - &(2 EXP 126 DIV h) * &n):real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      UNDISCH_THEN `2 EXP (64 * k) * rhi + rlo = 2 EXP 126 DIV h * n`
       (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_POW_ADD] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
      REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN
      SIMP_TAC[REAL_MUL_LINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      REAL_INTEGER_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC remalemma THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `m:num` o MATCH_MP (NUMBER_RULE
       `n divides x ==> !m:num. m divides n ==> m divides x`)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` (SUBST_ALL_TAC o CONJUNCT2)) THEN
      MAP_EVERY UNDISCH_TAC [`~(2 EXP i = 1)`; `ODD(2 EXP i)`] THEN
      SIMP_TAC[ODD_EXP; ARITH; EXP];
      ALL_TAC] THEN

    MP_TAC(ASSUME `2 EXP (64 * (k - 1)) * h + l = n`) THEN DISCH_THEN(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o funpow 4 RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN `64 * k + 62 = 64 * (k - 1) + 126` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; REWRITE_TAC[REAL_POW_ADD]] THEN
    REWRITE_TAC[REAL_ARITH
     `ee * e - d * (ee * h + l):real = ee * (e - d * h) - d * l`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; GSYM REAL_OF_NUM_MOD] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x y:real. &0 <= x /\ &0 <= y /\ x <= e /\ y <= e
                 ==> abs(x - y) <= e`) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `2 EXP (64 * (k - 1)) * h + l = n`) THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC(ARITH_RULE `a:num < b ==> a <= b + c`) THEN
      REWRITE_TAC[LT_MULT_LCANCEL; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      UNDISCH_TAC `2 EXP 63 <= h` THEN ARITH_TAC;

      TRANS_TAC LE_TRANS `2 EXP 63 * 2 EXP (64 * (k - 1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
        SUBST1_TAC(ARITH_RULE `2 EXP 63 = 2 EXP 126 DIV 2 EXP 63`) THEN
        MATCH_MP_TAC DIV_MONO2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        MP_TAC(ASSUME `2 EXP (64 * (k - 1)) * h + l = n`) THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        MATCH_MP_TAC(ARITH_RULE
         `ee * e:num <= ee * h ==> e * ee <= ee * h + l`) THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL]]];
    ALL_TAC] THEN

  (*** The first modular doubling, "dubloop1" and "corrloop1" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x18c`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = n /\
        (ODD m /\ ~(m = 1)
         ==> bignum_from_memory(z,k) s = 2 EXP (64 * k + 63) MOD n)` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `p62:num` `bignum_from_memory (z,k)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    BIGNUM_TERMRANGE_TAC `k:num` `p62:num` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x13c` `pc + 0x158`
      `\i s. read X0 s = word k /\
             read X1 s = z /\
             read X2 s = mm /\
             read X3 s = t /\
             bignum_from_memory (mm,k) s = m /\
             bignum_from_memory (t,k) s = n /\
             read X5 s = word i /\
             (read X9 s =
              if i = 0 then word 0 else word(bigdigit p62 (i - 1))) /\
             bignum_from_memory (word_add z (word(8 * i)),k - i) s =
             highdigits p62 i /\
             bignum_from_memory (word_add t (word(8 * i)),k - i) s =
             highdigits n i /\
             &(bignum_from_memory(z,i) s):real =
             &2 pow (64 * i) * &(bitval(~read CF s)) +
             &(lowdigits (2 * p62) i) - &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM WORD_ADD; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; REAL_POW_ADD] THEN
      MATCH_MP_TAC(REAL_RING
       `ee * y:real = w - z
        ==> --e * c + s = y ==> z + ee * s = (ee * e) * c + w`) THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ARITH
       `x - y:real = z <=> x = y + z`] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[REAL_ARITH `(x:real) * &2 pow k = &2 pow k * x`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
       [REWRITE_TAC[ARITH_RULE `(2 EXP 64 * x) DIV 2 EXP 63 = 2 * x`] THEN
        REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
        CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
        ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
       `(highdigits p62 (i - 1) DIV 2 EXP 63) MOD 2 EXP 64` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> i - 1 + 1 = i`; DIV_MOD] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CONG] THEN
        MATCH_MP_TAC(NUMBER_RULE
         `(a:num == a') (mod n)
          ==> (e * a + b == e * a' + b) (mod (n * e))`) THEN
        REWRITE_TAC[bigdigit; highdigits; CONG; MOD_MOD_EXP_MIN] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
        REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
        ASM_SIMP_TAC[bigdigit; EXP; DIV_MULT2; ARITH_EQ; ARITH_RULE
         `~(i = 0) ==> 64 * i = SUC(64 * (i - 1) + 63)`]];

       X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
       ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

       ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

    GHOST_INTRO_TAC `hi:bool` `read CF` THEN
    GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x16c` `pc + 0x184`
      `\i s. read X0 s = word k /\
             read X1 s = z /\
             read X2 s = mm /\
             read X3 s = t /\
             bignum_from_memory (mm,k) s = m /\
             bignum_from_memory (t,k) s = n /\
             read X5 s = word i  /\
             bignum_from_memory (word_add z (word(8 * i)),k - i) s =
             highdigits lo i /\
             bignum_from_memory (word_add t (word(8 * i)),k - i) s =
             highdigits n i /\
             (p62 < n
              ==> read X9 s = word_neg(word(bitval(2 * p62 < n))) /\
                  &(bignum_from_memory(z,i) s):real =
                  (&(lowdigits lo i) +
                  &(bitval(2 * p62 < n)) * &(lowdigits n i)) -
                  &2 pow (64 * i) * &(bitval(read CF s)))` THEN
     ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN
       ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (3--5) THEN
       ENSURES_FINAL_STATE_TAC THEN
       ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
       REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
       ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
       ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
       REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ADD_LID] THEN
       DISCH_TAC THEN REWRITE_TAC[WORD_RULE
        `word_sub a b = word_neg c <=> word_add c a = b`] THEN
       MP_TAC(GEN `x:int64` (ISPEC `x:int64` WORD_USHR_MSB)) THEN
       REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
       DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
       REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_BITVAL; VAL_WORD_ADD_CASES] THEN
       SIMP_TAC[DIMINDEX_64; BITVAL_BOUND; ARITH_RULE
        `b <= 1 /\ c <= 1 ==> b + c < 2 EXP 64`] THEN
       SUBGOAL_THEN `2 * p62 < 2 * n /\ 2 * p62 < 2 * 2 EXP (64 * k)`
       MP_TAC THENL
        [ASM_REWRITE_TAC[LT_MULT_LCANCEL; ARITH_EQ]; ALL_TAC] THEN
       SUBGOAL_THEN
        `2 * p62 = 2 EXP (64 * k) *
                 bitval(bit 63 (word(bigdigit p62 (k - 1)):int64)) +
                 lowdigits (2 * p62) k`
       SUBST1_TAC THENL
        [MP_TAC(SPECL [`2 * p62`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
         DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
         AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
         MP_TAC(ISPEC `word(bigdigit p62 (k - 1)):int64` WORD_USHR_MSB) THEN
         REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
         DISCH_THEN(MP_TAC o SYM o AP_TERM `val:int64->num`) THEN
         REWRITE_TAC[VAL_WORD_BITVAL; VAL_WORD_USHR] THEN
         DISCH_THEN SUBST1_TAC THEN
         SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
         ASM_SIMP_TAC[highdigits; ARITH_RULE
          `~(k = 0) ==> 64 * k = SUC(64 * (k - 1) + 63)`] THEN
         SIMP_TAC[DIV_MULT2; EXP; ARITH_EQ] THEN
         REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
         AP_THM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[bigdigit] THEN CONV_TAC SYM_CONV THEN
         MATCH_MP_TAC MOD_LT THEN
         ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
         ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 64 * (k - 1) + 64 = 64 * k`];
         ALL_TAC] THEN
       ASM_CASES_TAC `bit 63 (word(bigdigit p62 (k - 1)):int64)` THEN
       ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THENL
        [ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> ~(e + a < n)`] THEN
         UNDISCH_TAC
          `&lo:real =
            &2 pow (64 * k) * &(bitval(~hi)) +
           &(lowdigits (2 * p62) k) - &n` THEN
         UNDISCH_TAC `lo < 2 EXP (64 * k)` THEN
         REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
         BOOL_CASES_TAC `hi:bool` THEN
         ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
         REAL_ARITH_TAC;
         STRIP_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[NOT_LT; TAUT `(p <=> ~q) <=> (~p <=> q)`] THEN
         CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN
         EXISTS_TAC `64 * k` THEN REWRITE_TAC[GSYM REAL_BITVAL_NOT] THEN
         UNDISCH_THEN
          `&lo:real =
            &2 pow (64 * k) * &(bitval(~hi)) + &(lowdigits (2 * p62) k) - &n`
          (SUBST1_TAC o SYM) THEN
         ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0]];
       X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
       GHOST_INTRO_TAC `cin:bool` `read CF` THEN
       GHOST_INTRO_TAC `hi:int64` `read X9` THEN
       GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
        [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
       ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
       REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--6) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
       DISCH_THEN(fun th ->
         REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
         ASSUME_TAC th) THEN
       ASM_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
       ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
       ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
       SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
       REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                   LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
       REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
       SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
                BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
       REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
       X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
       ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
       ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)) THEN
      ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC(CONJUNCT1 th)) THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)) THEN
      ASSUME_TAC th) THEN
    SUBGOAL_THEN `2 EXP (64 * k + 63) MOD n =
                  (2 * 2 EXP (64 * k + 62) MOD n) MOD n`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n + 63 = SUC(n + 62)`; EXP] THEN
      CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p62:num < n`
     (fun th -> FIRST_X_ASSUM(MP_TAC o C MP th) THEN ASSUME_TAC th)
    THENL
     [ASM_REWRITE_TAC[MOD_LT_EQ] THEN
      UNDISCH_TAC `2 EXP (64 * k - 1) <= n` THEN
      SIMP_TAC[GSYM NOT_LT; CONTRAPOS_THM; EXP_LT_0] THEN ARITH_TAC;
      UNDISCH_THEN `p62 = 2 EXP (64 * k + 62) MOD n` (SUBST1_TAC o SYM)] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_ADD_CASES; MULT_2; ARITH_RULE
     `p62 < n ==> p62 + p62 < 2 * n`] THEN
    REWRITE_TAC[GSYM MULT_2] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`p62:num < n`; `n < 2 EXP (64 * k)`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_FIELD `inv(&2 pow n) * &2 pow n = (&1:real)`] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ARITH
     `--(&2) * e * a + e * b + c:real = e * (b - &2 * a) + c`] THEN
    MATCH_MP_TAC INTEGER_ADD THEN
    (CONJ_TAC THENL [ALL_TAC; REAL_INTEGER_TAC]) THEN
    REWRITE_TAC[REAL_ARITH `inv x * (a - b):real = (a - b) / x`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (rand o rand) REAL_CONGRUENCE o snd) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CONG; lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  (*** The second modular doubling, "dubloop2" and "corrloop2" ***)

  ENSURES_SEQUENCE_TAC `pc + 0x1e8`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory (mm,k) s = m /\
        (ODD m /\ ~(m = 1)
         ==> bignum_from_memory(z,k) s = 2 EXP (64 * k + 64) MOD n /\
             bignum_from_memory(t,k) s = 2 EXP (64 * k + 64) MOD n)` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `p63:num` `bignum_from_memory (z,k)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    BIGNUM_TERMRANGE_TAC `k:num` `p63:num` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x194` `pc + 0x1b0`
      `\i s. read X0 s = word k /\
             read X1 s = z /\
             read X2 s = mm /\
             read X3 s = t /\
             bignum_from_memory (mm,k) s = m /\
             bignum_from_memory (t,k) s = n /\
             read X5 s = word i /\
             (read X9 s =
              if i = 0 then word 0 else word(bigdigit p63 (i - 1))) /\
             bignum_from_memory (word_add z (word(8 * i)),k - i) s =
             highdigits p63 i /\
             bignum_from_memory (word_add t (word(8 * i)),k - i) s =
             highdigits n i /\
             &(bignum_from_memory(z,i) s):real =
             &2 pow (64 * i) * &(bitval(~read CF s)) +
             &(lowdigits (2 * p63) i) - &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM WORD_ADD; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; REAL_POW_ADD] THEN
      MATCH_MP_TAC(REAL_RING
       `ee * y:real = w - z
        ==> --e * c + s = y ==> z + ee * s = (ee * e) * c + w`) THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ARITH
       `x - y:real = z <=> x = y + z`] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
      REWRITE_TAC[REAL_ARITH `(x:real) * &2 pow k = &2 pow k * x`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; LE_REFL] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
       [REWRITE_TAC[ARITH_RULE `(2 EXP 64 * x) DIV 2 EXP 63 = 2 * x`] THEN
        REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
        CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
        ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
       `(highdigits p63 (i - 1) DIV 2 EXP 63) MOD 2 EXP 64` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> i - 1 + 1 = i`; DIV_MOD] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CONG] THEN
        MATCH_MP_TAC(NUMBER_RULE
         `(a:num == a') (mod n)
          ==> (e * a + b == e * a' + b) (mod (n * e))`) THEN
        REWRITE_TAC[bigdigit; highdigits; CONG; MOD_MOD_EXP_MIN] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
        REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
        ASM_SIMP_TAC[bigdigit; EXP; DIV_MULT2; ARITH_EQ; ARITH_RULE
         `~(i = 0) ==> 64 * i = SUC(64 * (i - 1) + 63)`]];

       X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
       ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

       ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

    GHOST_INTRO_TAC `hi:bool` `read CF` THEN
    GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x1c4` `pc + 0x1e0`
      `\i s. read X0 s = word k /\
             read X1 s = z /\
             read X2 s = mm /\
             read X3 s = t /\
             bignum_from_memory (mm,k) s = m /\
             read X5 s = word i  /\
             bignum_from_memory (word_add z (word(8 * i)),k - i) s =
             highdigits lo i /\
             bignum_from_memory (word_add t (word(8 * i)),k - i) s =
             highdigits n i /\
             (p63 < n
              ==> read X9 s = word_neg(word(bitval(2 * p63 < n))) /\
                  &(bignum_from_memory(z,i) s):real =
                  (&(lowdigits lo i) +
                  &(bitval(2 * p63 < n)) * &(lowdigits n i)) -
                  &2 pow (64 * i) * &(bitval(read CF s)) /\
                  &(bignum_from_memory(t,i) s):real =
                  (&(lowdigits lo i) +
                  &(bitval(2 * p63 < n)) * &(lowdigits n i)) -
                  &2 pow (64 * i) * &(bitval(read CF s)))` THEN
     ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
       RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN
       ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (3--5) THEN
       ENSURES_FINAL_STATE_TAC THEN
       ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
       REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
       ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
       ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
       REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ADD_LID] THEN
       DISCH_TAC THEN REWRITE_TAC[WORD_RULE
        `word_sub a b = word_neg c <=> word_add c a = b`] THEN
       MP_TAC(GEN `x:int64` (ISPEC `x:int64` WORD_USHR_MSB)) THEN
       REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
       DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
       REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_BITVAL; VAL_WORD_ADD_CASES] THEN
       SIMP_TAC[DIMINDEX_64; BITVAL_BOUND; ARITH_RULE
        `b <= 1 /\ c <= 1 ==> b + c < 2 EXP 64`] THEN
       SUBGOAL_THEN `2 * p63 < 2 * n /\ 2 * p63 < 2 * 2 EXP (64 * k)`
       MP_TAC THENL
        [ASM_REWRITE_TAC[LT_MULT_LCANCEL; ARITH_EQ]; ALL_TAC] THEN
       SUBGOAL_THEN
        `2 * p63 = 2 EXP (64 * k) *
                 bitval(bit 63 (word(bigdigit p63 (k - 1)):int64)) +
                 lowdigits (2 * p63) k`
       SUBST1_TAC THENL
        [MP_TAC(SPECL [`2 * p63`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
         DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
         AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
         MP_TAC(ISPEC `word(bigdigit p63 (k - 1)):int64` WORD_USHR_MSB) THEN
         REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
         DISCH_THEN(MP_TAC o SYM o AP_TERM `val:int64->num`) THEN
         REWRITE_TAC[VAL_WORD_BITVAL; VAL_WORD_USHR] THEN
         DISCH_THEN SUBST1_TAC THEN
         SIMP_TAC[VAL_WORD_EQ; BIGDIGIT_BOUND; DIMINDEX_64] THEN
         ASM_SIMP_TAC[highdigits; ARITH_RULE
          `~(k = 0) ==> 64 * k = SUC(64 * (k - 1) + 63)`] THEN
         SIMP_TAC[DIV_MULT2; EXP; ARITH_EQ] THEN
         REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
         AP_THM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[bigdigit] THEN CONV_TAC SYM_CONV THEN
         MATCH_MP_TAC MOD_LT THEN
         ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
         ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 64 * (k - 1) + 64 = 64 * k`];
         ALL_TAC] THEN
       ASM_CASES_TAC `bit 63 (word(bigdigit p63 (k - 1)):int64)` THEN
       ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THENL
        [ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> ~(e + a < n)`] THEN
         UNDISCH_TAC
          `&lo:real =
            &2 pow (64 * k) * &(bitval(~hi)) +
           &(lowdigits (2 * p63) k) - &n` THEN
         UNDISCH_TAC `lo < 2 EXP (64 * k)` THEN
         REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
         BOOL_CASES_TAC `hi:bool` THEN
         ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
         REAL_ARITH_TAC;
         STRIP_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[NOT_LT; TAUT `(p <=> ~q) <=> (~p <=> q)`] THEN
         CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN
         EXISTS_TAC `64 * k` THEN REWRITE_TAC[GSYM REAL_BITVAL_NOT] THEN
         UNDISCH_THEN
          `&lo:real =
            &2 pow (64 * k) * &(bitval(~hi)) + &(lowdigits (2 * p63) k) - &n`
          (SUBST1_TAC o SYM) THEN
         ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0]];

       X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
       GHOST_INTRO_TAC `cin:bool` `read CF` THEN
       GHOST_INTRO_TAC `hi:int64` `read X9` THEN
       GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
        [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
       ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
       REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--7) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
       DISCH_THEN(fun th ->
         REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
         ASSUME_TAC th) THEN
       ASM_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
       ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
       ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
       SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
       REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                   LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
       REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
       SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
                BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
       REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
       X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
       ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
       ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)) THEN
      ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC(CONJUNCT1 th)) THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MP th)) THEN
      ASSUME_TAC th) THEN
    SUBGOAL_THEN `2 EXP (64 * k + 64) MOD n =
                  (2 * 2 EXP (64 * k + 63) MOD n) MOD n`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n + 64 = SUC(n + 63)`; EXP] THEN
      CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p63:num < n`
     (fun th -> FIRST_X_ASSUM(MP_TAC o C MP th) THEN ASSUME_TAC th)
    THENL
     [ASM_REWRITE_TAC[MOD_LT_EQ] THEN
      UNDISCH_TAC `2 EXP (64 * k - 1) <= n` THEN
      SIMP_TAC[GSYM NOT_LT; CONTRAPOS_THM; EXP_LT_0] THEN ARITH_TAC;
      UNDISCH_THEN `p63 = 2 EXP (64 * k + 63) MOD n` (SUBST1_TAC o SYM)] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_ADD_CASES; MULT_2; ARITH_RULE
     `p63 < n ==> p63 + p63 < 2 * n`] THEN
    REWRITE_TAC[GSYM MULT_2] THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC(MESON[] `x = y /\ x = a ==> x = a /\ y = a`) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`p63:num < n`; `n < 2 EXP (64 * k)`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_FIELD `inv(&2 pow n) * &2 pow n = (&1:real)`] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REWRITE_TAC[REAL_ARITH
     `--(&2) * e * a + e * b + c:real = e * (b - &2 * a) + c`] THEN
    MATCH_MP_TAC INTEGER_ADD THEN
    (CONJ_TAC THENL [ALL_TAC; REAL_INTEGER_TAC]) THEN
    REWRITE_TAC[REAL_ARITH `inv x * (a - b):real = (a - b) / x`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (rand o rand) REAL_CONGRUENCE o snd) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CONG; lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  (*** A bit of cleanup ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `h:num` o concl))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `l:num` o concl))) THEN
  REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  GHOST_INTRO_TAC `r:num` `bignum_from_memory (z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `r:num` THEN GLOBALIZE_PRECONDITION_TAC THEN

  (*** Now the main loop "modloop" ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x1f0` `pc + 0x25c`
   `\i s. (read X0 s = word k /\
           read X1 s = z /\
           read X2 s = mm /\
           read X3 s = t /\
           read X4 s = word(k - i) /\
           bignum_from_memory (mm,k) s = m /\
           bignum_from_memory (z,k) s = r /\
           (ODD m ==> (2 EXP (64 * k) * val(read X6 s) +
                       bignum_from_memory(t,k) s ==
                       2 EXP (64 * (k + i + 1))) (mod m))) /\
          (read ZF s <=> i = k)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES; SUB_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_CASES_TAC `m = 1` THEN ASM_SIMP_TAC[CONG_MOD_1; MULT_CLAUSES] THEN
    DISCH_TAC THEN MATCH_MP_TAC(NUMBER_RULE
     `!m:num. (a == b) (mod n) /\ m divides n ==> (a == b) (mod m)`) THEN
    ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; CONG_LMOD; CONG_REFL];

    (*** The main loop invariant of "modloop" ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `h:num` `\s. val(read X6 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
    GHOST_INTRO_TAC `t1:num` `bignum_from_memory (t,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `t1:num` THEN GLOBALIZE_PRECONDITION_TAC THEN

    (*** The inner multiply-add loop "cmaloop" ***)

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x1fc` `pc + 0x220`
     `\j s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = mm /\
            read X3 s = t /\
            read X4 s = word (k - i) /\
            bignum_from_memory (mm,k) s = m /\
            bignum_from_memory (z,k) s = r /\
            read X6 s = word h /\
            read X5 s = word j /\
            bignum_from_memory (word_add z (word(8 * j)),k - j) s =
            highdigits r j /\
            bignum_from_memory (word_add t (word(8 * j)),k - j) s =
            highdigits t1 j /\
            read X10 s = word(bigdigit (2 EXP 64 * t1) j) /\
            2 EXP (64 * j) * (bitval(read CF s) + val(read X9 s)) +
            bignum_from_memory(t,j) s =
            lowdigits (2 EXP 64 * t1) j + h * lowdigits r j` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--3) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; BITVAL_CLAUSES; VAL_WORD_0] THEN
      REWRITE_TAC[WORD_ADD_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES; MOD_MULT];

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X9` THEN
      GHOST_INTRO_TAC `prd:int64` `read X10` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [2;3;5;6] (1--9) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [CONV_TAC WORD_RULE;
        AP_TERM_TAC THEN REWRITE_TAC[bigdigit] THEN
        REWRITE_TAC[ARITH_RULE `64 * (j + 1) = 64 + 64 * j`] THEN
        SIMP_TAC[EXP_ADD; DIV_MULT2; EXP_EQ_0; ARITH_EQ];
        REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `(e * d1 + d0) + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (j + 1) = 64 * j + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
       [TAUT `p /\ q /\ r /\ s <=> p /\ r /\ q /\ s`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

    (*** Additional absorption of the top digit before correction ***)

    ENSURES_SEQUENCE_TAC `pc + 0x22c`
     `\s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = mm /\
          read X3 s = t /\
          read X4 s = word (k - i) /\
          bignum_from_memory (mm,k) s = m /\
          bignum_from_memory (z,k) s = r /\
          2 EXP (64 * k) * (2 EXP 64 * bitval(read CF s) + val(read X6 s)) +
          bignum_from_memory(t,k) s =
          2 EXP 64 * t1 + h * r` THEN
    CONJ_TAC THENL
     [GHOST_INTRO_TAC `hup:int64` `read X9` THEN
      GHOST_INTRO_TAC `cup:bool` `read CF` THEN
      GHOST_INTRO_TAC `tup:num` `bignum_from_memory (t,k)` THEN
      BIGNUM_TERMRANGE_TAC `k:num` `tup:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [3] [3] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE
        `e * (a + b + c) + d:num = e * a + e * (c + b) + d`] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 LOWDIGITS_CLAUSES)] THEN
      MATCH_MP_TAC LOWDIGITS_SELF THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (j + 1) = 64 + 64 * j`] THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ];
      GHOST_INTRO_TAC `hup:int64` `read X6` THEN
      GHOST_INTRO_TAC `cup:bool` `read CF` THEN
      GHOST_INTRO_TAC `tup:num` `bignum_from_memory (t,k)` THEN
      BIGNUM_TERMRANGE_TAC `k:num` `tup:num` THEN
      GLOBALIZE_PRECONDITION_TAC] THEN

    (**** The optional addition loop "oaloop" fixing things up ***)

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x234` `pc + 0x24c`
     `\j s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = mm /\
            read X3 s = t /\
            read X4 s = word (k - i) /\
            bignum_from_memory (mm,k) s = m /\
            bignum_from_memory (z,k) s = r /\
            read X6 s = hup /\
            read X8 s = word_neg(word(bitval cup)) /\
            read X5 s = word j /\
            bignum_from_memory (word_add z (word(8 * j)),k - j) s =
            highdigits r j /\
            bignum_from_memory (word_add t (word(8 * j)),k - j) s =
            highdigits tup j /\
            2 EXP (64 * j) * bitval(read CF s) + bignum_from_memory(t,j) s =
            lowdigits tup j + bitval(cup) * lowdigits r j` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; BITVAL_CLAUSES; VAL_WORD_0] THEN
      REWRITE_TAC[WORD_ADD_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[REAL_ARITH
      `&2 pow k * c + z:real = w <=> z = w - &2 pow k * c`] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; LOWDIGITS_CLAUSES] THEN
      REWRITE_TAC[ARITH_RULE `64 * (j + 1) = 64 * j + 64`; REAL_POW_ADD] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_AND_MASK] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; BITVAL_CLAUSES] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      CONV_TAC REAL_RING;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

    (*** The final case analysis and conclusion ***)

    GHOST_INTRO_TAC `topc:bool` `read CF` THEN
    GHOST_INTRO_TAC `tout:num` `bignum_from_memory(t,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `tout:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [3] (3--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> r) /\ q ==> p /\ q /\ r `) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `a - (i + 1) = a - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> 1 <= k - i`];
      DISCH_THEN SUBST1_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o
        lhand o lhand o snd) THEN
      REWRITE_TAC[DIMINDEX_64] THEN ANTS_TAC THENL
       [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `i:num < k`] THEN ARITH_TAC;
      DISCH_THEN(fun th ->
        REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
        ASSUME_TAC th)] THEN
    REWRITE_TAC[ARITH_RULE
     `64 * (k + (i + 1) + 1) = 64 + 64 * (k + i + 1)`] THEN
    ONCE_REWRITE_TAC[EXP_ADD] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (NUMBER_RULE `(x:num == a) (mod m)
                   ==> (e * x == y) (mod m) ==> (y == e * a) (mod m)`)) THEN
    UNDISCH_TAC `ODD m /\ ~(m = 1) ==> r = 2 EXP (64 * k + 64) MOD n` THEN
    ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[CONG_MOD_1] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP(MESON[CONG_RMOD; CONG_REFL]
     `x = y MOD n ==> (y == x) (mod n)`)) THEN
    REWRITE_TAC[ARITH_RULE `e * (ee * h + t):num = e * t + (ee * e) * h`] THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `(e1:num == r) (mod n)
      ==> m divides n /\ (t + r * h == z) (mod m)
          ==> (t + e1 * h == z) (mod m)`)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(sum_s3:int64) = val(hup:int64) + bitval topc`
    SUBST1_TAC THENL
     [ALL_TAC;
      MAP_EVERY UNDISCH_TAC
       [`2 EXP (64 * k) * (2 EXP 64 * bitval cup + val(hup:int64)) + tup =
         2 EXP 64 * t1 + h * r`;
        `2 EXP (64 * k) * bitval topc + tout = tup + bitval cup * r`;
        `(2 EXP (64 * k + 64) == r) (mod n)`; `(m:num) divides n`] THEN
      REWRITE_TAC[EXP_ADD] THEN SPEC_TAC(`2 EXP (64 * k)`,`ee:num`) THEN
      SPEC_TAC(`2 EXP 64`,`e:num`) THEN
      BOOL_CASES_TAC `cup:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
      CONV_TAC NUMBER_RULE] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC(ARITH_RULE
     `(e * c < e * 1 ==> e * c = 0) /\ z < e
      ==> e * c + s:num = z ==> s = z`) THEN
    REWRITE_TAC[LT_MULT_LCANCEL; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `b < 1 ==> b = 0`] THEN
    SUBGOAL_THEN `2 EXP (64 * k) * (val(hup:int64) + bitval topc) <
                  2 EXP (64 * k) * 2 EXP 64`
    MP_TAC THENL
     [ALL_TAC; REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]] THEN
    MAP_EVERY UNDISCH_TAC
     [`2 EXP (64 * k) * (2 EXP 64 * bitval cup + val(hup:int64)) + tup =
       2 EXP 64 * t1 + h * r`;
      `2 EXP (64 * k) * bitval topc + tout = tup + bitval cup * r`] THEN
    ASM_CASES_TAC `cup:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THENL
     [SUBGOAL_THEN `2 EXP 64 * t1 < 2 EXP 64 * 2 EXP (64 * k) /\
                   (h + 1) * r <= 2 EXP 64 * 2 EXP (64 * k)`
      MP_TAC THENL [ALL_TAC; ARITH_TAC] THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
      MATCH_MP_TAC LE_MULT2 THEN
      ASM_SIMP_TAC[LT_IMP_LE; ARITH_RULE `x + 1 <= y <=> x < y`];
      ALL_TAC] THEN
    ASM_CASES_TAC `topc:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THENL
     [MAP_EVERY UNDISCH_TAC
       [`tout < 2 EXP (64 * k)`; `tup < 2 EXP (64 * k)`] THEN
      ARITH_TAC;
      SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; VAL_BOUND_64]];

    (*** Trivial loop-back ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[] THEN ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1];

    ALL_TAC] THEN

  (*** Initial word modular inverse of Montgomery tail ***)

  ENSURES_SEQUENCE_TAC `pc + 0x294`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        read X7 s = word(bigdigit m 0) /\
        bignum_from_memory (mm,k) s = m /\
        (ODD m
         ==> (2 EXP (64 * k) * val (read X6 s) +
              bignum_from_memory (t,k) s ==
              2 EXP (64 * (2 * k + 1))) (mod m)) /\
        (ODD m ==> (m * val(read X11 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
    SUBGOAL_THEN `bignum_from_memory(mm,k) s1 = highdigits m 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC LAND_CONV[BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC] THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (2--5) THEN
    SUBGOAL_THEN `ODD m ==> (m * val (read X11 s5) + 1 == 0) (mod 16)`
    MP_TAC THENL [ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16]; ALL_TAC] THEN
    REABBREV_TAC `x0 = read X11 s5` THEN DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (6--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * k + 1 = k + k + 1`] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_TAC THEN UNDISCH_TAC
     `ODD m ==> (m * val(x0:int64) + 1 == 0) (mod 16)` THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:num` `\s. val(read X11 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64]] THEN

  (*** More cleanup and setup of Montgomery multiplier ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `n:num` o concl))) THEN
  GHOST_INTRO_TAC `h:num` `\s. val(read X6 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GHOST_INTRO_TAC `z1:num` `bignum_from_memory (t,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ABBREV_TAC `q0 = (w * z1) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  (*** The prelude of the Montgomery reduction ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2b0`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory (mm,k) s = m /\
        bignum_from_memory (t,k) s = z1 /\
        read X6 s = word h /\
        read X11 s = word q0 /\
        read X5 s = word 1 /\
        read X7 s = word(k - 1) /\
        ?r0. r0 < 2 EXP 64 /\
             2 EXP 64 * (bitval(read CF s) + val(read X9 s)) + r0 =
             q0 * bigdigit m 0 + bigdigit z1 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(mm,k) s0 = highdigits m 0 /\
      bignum_from_memory(t,k) s0 = highdigits z1 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [3; 7] (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[ADD_CLAUSES; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
    EXISTS_TAC `val(sum_s7:int64)` THEN REWRITE_TAC[VAL_BOUND_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Break at "montend" to share the end reasoning ***)

  GHOST_INTRO_TAC `carin:bool` `read CF` THEN
  GHOST_INTRO_TAC `mulin:int64` `read X9` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r0:num` STRIP_ASSUME_TAC) THEN

  ENSURES_SEQUENCE_TAC `pc + 0x2e4`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory (mm,k) s = m /\
        read X6 s = word h /\
        read X11 s = word q0 /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read X9 s)) +
        2 EXP 64 * bignum_from_memory (t,k - 1) s + r0 =
        lowdigits z1 k + q0 * lowdigits m k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUB_REFL; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop "montloop" ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0x2b4` `pc + 0x2dc`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = mm /\
            read X3 s = t /\
            bignum_from_memory (mm,k) s = m /\
            read X6 s = word h /\
            read X11 s = word q0 /\
            read X5 s = word i /\
            bignum_from_memory(word_add t (word (8 * i)),k - i) s =
            highdigits z1 i /\
            bignum_from_memory(word_add mm (word (8 * i)),k - i) s =
            highdigits m i /\
            2 EXP (64 * i) * (bitval(read CF s) + val(read X9 s)) +
            2 EXP 64 * bignum_from_memory(t,i-1) s + r0 =
            lowdigits z1 i + q0 * lowdigits m i` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[GSYM highdigits; BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_1] THEN ARITH_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`i:num`; `i - 1`] THEN
      SUBGOAL_THEN `word_sub (word i) (word 1):int64 = word(i - 1)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X9` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - i:num`; `a:num`; `i:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      UNDISCH_THEN `val(word q0:int64) = q0` (K ALL_TAC) THEN
      ABBREV_TAC `i' = i - 1` THEN
      SUBGOAL_THEN `i = i' + 1` SUBST_ALL_TAC THENL
       [EXPAND_TAC "i'" THEN UNDISCH_TAC `1 <= i` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(i' + 1) + 1 = i' + 2`]) THEN
      REWRITE_TAC[ARITH_RULE `(i' + 1) + 1 = i' + 2`] THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [3;4;6;7] (1--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(m + 2) - 1 = m + 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i' + 2 = (i' + 1) + 1` MP_TAC THENL
       [ARITH_TAC; DISCH_THEN SUBST_ALL_TAC] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `(e * d1 + d0) + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
         [TAUT `p /\ q /\ r /\ s <=> p /\ r /\ q /\ s`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`i:num`; `i - 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]];
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

 (*** The final digit write ****)

  ENSURES_SEQUENCE_TAC `pc + 0x2f4`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = mm /\
        read X3 s = t /\
        bignum_from_memory (mm,k) s = m /\
        ?c. read X8 s = word_neg(word(bitval c)) /\
            2 EXP 64 * (2 EXP (64 * k) * bitval c +
                        bignum_from_memory(t,k) s) + r0 =
            (2 EXP (64 * k) * h + z1) + q0 * m` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `hin:int64` `read X9` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    VAL_INT64_TAC `k - 1` THEN
    SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`];
      ALL_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [1] (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `carry_s1:bool` THEN CONJ_TAC THENL
     [REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    SUBGOAL_THEN `64 * k = 64 * (k - 1) + 64` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; REWRITE_TAC[REAL_POW_ADD]] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN

  (*** The final correction to keep inside k digits, "osloop" ***)

  GHOST_INTRO_TAC `z2:num` `bignum_from_memory(t,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z2:num` THEN
  GHOST_INTRO_TAC `g8:int64` `read X8` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cf:bool`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x2f8` `pc + 0x310`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = mm /\
          read X3 s = t /\
          read X8 s = word_neg (word (bitval cf)) /\
          read X5 s = word i /\
          bignum_from_memory (word_add t (word(8 * i)),k - i) s =
          highdigits z2 i /\
          bignum_from_memory (word_add mm (word(8 * i)),k - i) s =
          highdigits m i /\
          &(bignum_from_memory(z,i) s):real =
          &2 pow (64 * i) * &(bitval(~read CF s)) +
          &(lowdigits z2 i) - &(bitval cf) * &(lowdigits m i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_AMONTIFIER_EXEC [1] THEN
    REWRITE_TAC[WORD_SUB_LZERO; SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BITVAL_CLAUSES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTIFIER_EXEC [4] (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
    REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
             BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_AMONTIFIER_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
      ASSUME_TAC th)] THEN

  (*** Finally deduce that the lowest digit is 0 by congruence reasoning ***)

  UNDISCH_THEN
    `2 EXP 64 * (bitval carin + val(mulin:int64)) + r0 =
     q0 * bigdigit m 0 + bigdigit z1 0`
   (MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`) THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN
  UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[MOD_LT; GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
  CONV_TAC(LAND_CONV MOD_DOWN_CONV) THEN
  REWRITE_TAC[ARITH_RULE `(w * z1) * m + z1 = z1 * (m * w + 1)`] THEN
  ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  UNDISCH_TAC `(m * w + 1 == 0) (mod (2 EXP 64))` THEN
  GEN_REWRITE_TAC LAND_CONV [CONG] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV MOD_DOWN_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; MOD_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN

  (*** The final congruence/range reasoning ***)

  MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `2 EXP 64` THEN
  ASM_REWRITE_TAC[COPRIME_LEXP; COPRIME_2] THEN
  REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `64 + 128 * k = 64 * (2 * k + 1)`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
   `(x:num == y) (mod n) ==> (z == x) (mod n) ==> (z == y) (mod n)`)) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
   `x:num = y + q * m ==> (z == x) (mod m) ==> (z == y) (mod m)`)) THEN
  MATCH_MP_TAC CONG_LMUL THEN
  SUBGOAL_THEN `~(read CF s2) <=> z2 < bitval cf * m` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `64 * k` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    UNDISCH_THEN
     `&(read (memory :> bytes (z,8 * k)) s2) =
      &2 pow (64 * k) * &(bitval (~read CF s2)) + &z2 - &(bitval cf) * &m`
     (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND; LE_0];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (vfree_in `cf:bool` o concl))) THEN
  REWRITE_TAC[GSYM int_of_num_th; GSYM int_pow_th; GSYM int_mul_th;
              GSYM int_add_th; GSYM int_sub_th; GSYM int_eq] THEN
  SIMP_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
  BOOL_CASES_TAC `cf:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT] THEN
  REWRITE_TAC[INT_CONG_REFL; INT_ADD_LID; INT_SUB_RZERO] THEN
  ASM_CASES_TAC `z2:num < m` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THENL
   [REPEAT(DISCH_THEN(K ALL_TAC)) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INTEGER_RULE;
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`)] THEN
  MATCH_MP_TAC(ARITH_RULE `b:num < a ==> ~(a = b)`) THEN
  MATCH_MP_TAC(ARITH_RULE
   `x + q * m < 2 EXP 64 * ee + 2 EXP 64 * m /\ ~(z2 < m)
    ==> x + q * m < 2 EXP 64 * (ee + z2)`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LET_ADD2 THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (MESON[ODD] `ODD m ==> ~(m = 0)`)) THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `z1:num < ee ==> (h + 1) * ee <= b ==> ee * h + z1 <= b`)) THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
  ASM_REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`]);;

let BIGNUM_AMONTIFIER_SUBROUTINE_CORRECT = time prove
 (`!k z m t n pc returnaddress.
        nonoverlapping (z,8 * val k) (t,8 * val k) /\
        ALLPAIRS nonoverlapping [(z,8 * val k); (t,8 * val k)]
                                [(word pc,0x31c); (m,8 * val k)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_amontifier_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; m; t] s /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        2 EXP (128 * val k)) (mod n)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k);
                         memory :> bytes(t,8 * val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_AMONTIFIER_EXEC BIGNUM_AMONTIFIER_CORRECT);;
