(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Montgomery multiplication of arbitrary bignums.                           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_montmul.o";;
 ****)

let bignum_montmul_mc =
  define_assert_from_elf "bignum_montmul_mc" "arm/generic/bignum_montmul.o"
[
  0xb4000a60;       (* arm_CBZ X0 (word 332) *)
  0xf940008e;       (* arm_LDR X14 X4 (Immediate_Offset (word 0)) *)
  0xd37ef5c5;       (* arm_LSL X5 X14 (rvalue (word 2)) *)
  0xcb0501c5;       (* arm_SUB X5 X14 X5 *)
  0xd27f00a5;       (* arm_EOR X5 X5 (rvalue (word 2)) *)
  0xd2800026;       (* arm_MOV X6 (rvalue (word 1)) *)
  0x9b0519c6;       (* arm_MADD X6 X14 X5 X6 *)
  0x9b067cc7;       (* arm_MUL X7 X6 X6 *)
  0x9b0514c5;       (* arm_MADD X5 X6 X5 X5 *)
  0x9b077ce6;       (* arm_MUL X6 X7 X7 *)
  0x9b0514e5;       (* arm_MADD X5 X7 X5 X5 *)
  0x9b067cc7;       (* arm_MUL X7 X6 X6 *)
  0x9b0514c5;       (* arm_MADD X5 X6 X5 X5 *)
  0x9b0514e5;       (* arm_MADD X5 X7 X5 X5 *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xf828783f;       (* arm_STR XZR X1 (Shiftreg_Offset X8 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb00011f;       (* arm_CMP X8 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xf8687849;       (* arm_LDR X9 X2 (Shiftreg_Offset X8 3) *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xab1f03eb;       (* arm_ADDS X11 XZR XZR *)
  0xf86a786e;       (* arm_LDR X14 X3 (Shiftreg_Offset X10 3) *)
  0xf86a782c;       (* arm_LDR X12 X1 (Shiftreg_Offset X10 3) *)
  0x9b0e7d2d;       (* arm_MUL X13 X9 X14 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9bce7d2b;       (* arm_UMULH X11 X9 X14 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0d018c;       (* arm_ADDS X12 X12 X13 *)
  0xf82a782c;       (* arm_STR X12 X1 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014e;       (* arm_SUB X14 X10 X0 *)
  0xb5fffece;       (* arm_CBNZ X14 (word 2097112) *)
  0xba0b00c6;       (* arm_ADCS X6 X6 X11 *)
  0x9a1f03e7;       (* arm_ADC X7 XZR XZR *)
  0xf940002c;       (* arm_LDR X12 X1 (Immediate_Offset (word 0)) *)
  0x9b057d89;       (* arm_MUL X9 X12 X5 *)
  0xf940008e;       (* arm_LDR X14 X4 (Immediate_Offset (word 0)) *)
  0x9b0e7d2d;       (* arm_MUL X13 X9 X14 *)
  0x9bce7d2b;       (* arm_UMULH X11 X9 X14 *)
  0xab0d018c;       (* arm_ADDS X12 X12 X13 *)
  0xd280002a;       (* arm_MOV X10 (rvalue (word 1)) *)
  0xd100040e;       (* arm_SUB X14 X0 (rvalue (word 1)) *)
  0xb40001ae;       (* arm_CBZ X14 (word 52) *)
  0xf86a788e;       (* arm_LDR X14 X4 (Shiftreg_Offset X10 3) *)
  0xf86a782c;       (* arm_LDR X12 X1 (Shiftreg_Offset X10 3) *)
  0x9b0e7d2d;       (* arm_MUL X13 X9 X14 *)
  0xba0b018c;       (* arm_ADCS X12 X12 X11 *)
  0x9bce7d2b;       (* arm_UMULH X11 X9 X14 *)
  0x9a1f016b;       (* arm_ADC X11 X11 XZR *)
  0xab0d018c;       (* arm_ADDS X12 X12 X13 *)
  0xd100054d;       (* arm_SUB X13 X10 (rvalue (word 1)) *)
  0xf82d782c;       (* arm_STR X12 X1 (Shiftreg_Offset X13 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014e;       (* arm_SUB X14 X10 X0 *)
  0xb5fffeae;       (* arm_CBNZ X14 (word 2097108) *)
  0xba0b00cb;       (* arm_ADCS X11 X6 X11 *)
  0x9a1f00e6;       (* arm_ADC X6 X7 XZR *)
  0xd100054d;       (* arm_SUB X13 X10 (rvalue (word 1)) *)
  0xf82d782b;       (* arm_STR X11 X1 (Shiftreg_Offset X13 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb00011f;       (* arm_CMP X8 X0 *)
  0x54fffaa3;       (* arm_BCC (word 2096980) *)
  0xeb1f03ea;       (* arm_NEGS X10 XZR *)
  0xf86a782e;       (* arm_LDR X14 X1 (Shiftreg_Offset X10 3) *)
  0xf86a788c;       (* arm_LDR X12 X4 (Shiftreg_Offset X10 3) *)
  0xfa0c01df;       (* arm_SBCS XZR X14 X12 *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014e;       (* arm_SUB X14 X10 X0 *)
  0xb5ffff6e;       (* arm_CBNZ X14 (word 2097132) *)
  0xfa1f00df;       (* arm_SBCS XZR X6 XZR *)
  0xda9f33e6;       (* arm_CSETM X6 Condition_CS *)
  0xeb1f03ea;       (* arm_NEGS X10 XZR *)
  0xf86a782e;       (* arm_LDR X14 X1 (Shiftreg_Offset X10 3) *)
  0xf86a788c;       (* arm_LDR X12 X4 (Shiftreg_Offset X10 3) *)
  0x8a06018c;       (* arm_AND X12 X12 X6 *)
  0xfa0c01ce;       (* arm_SBCS X14 X14 X12 *)
  0xf82a782e;       (* arm_STR X14 X1 (Shiftreg_Offset X10 3) *)
  0x9100054a;       (* arm_ADD X10 X10 (rvalue (word 1)) *)
  0xcb00014e;       (* arm_SUB X14 X10 X0 *)
  0xb5ffff2e;       (* arm_CBNZ X14 (word 2097124) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MONTMUL_EXEC = ARM_MK_EXEC_RULE bignum_montmul_mc;;

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

let BIGNUM_MONTMUL_CORRECT = time prove
 (`!k z x y m a b n pc.
      ALL (nonoverlapping (z,8 * val k))
          [(word pc,0x150); (x,8 * val k); (y,8 * val k); (m,8 * val k)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montmul_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [k; z; x; y; m] s /\
                bignum_from_memory (x,val k) s = a /\
                bignum_from_memory (y,val k) s = b /\
                bignum_from_memory (m,val k) s = n)
           (\s. read PC s = word(pc + 0x14c) /\
                (ODD n /\ a * b <= 2 EXP (64 * val k) * n
                 ==> bignum_from_memory (z,val k) s =
                     (inverse_mod n (2 EXP (64 * val k)) * a * b) MOD n))
           (MAYCHANGE [PC; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14] ,,
            MAYCHANGE [memory :> bytes(z,8 * val k)] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN STRIP_TAC THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`] THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ODD];
    ALL_TAC] THEN

  (*** Initial word-level modular inverse ***)

  ENSURES_SEQUENCE_TAC `pc + 0x38`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = x /\
        read X3 s = y /\
        read X4 s = m /\
        bignum_from_memory (x,k) s = a /\
        bignum_from_memory (y,k) s = b /\
        bignum_from_memory (m,k) s = n /\
        (ODD n ==> (n * val(read X5 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `bignum_from_memory(m,k) s0 = highdigits n 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC LAND_CONV[BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC] THEN
    ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--5) THEN
    SUBGOAL_THEN `ODD n ==> (n * val (read X5 s5) + 1 == 0) (mod 16)`
    MP_TAC THENL [ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16]; ALL_TAC] THEN
    REABBREV_TAC `x0 = read X5 s5` THEN DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (6--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:num` `\s. val(read X5 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64]] THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  VAL_INT64_TAC `w:num` THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_1)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Setup of the main loop with zeroing and corrective start/end ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x54` `pc + 0xfc`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = x /\
          read X3 s = y /\
          read X4 s = m /\
          read X5 s = word w /\
          read X8 s = word i /\
          bignum_from_memory(word_add x (word(8 * i)),k - i) s =
          highdigits a i /\
          bignum_from_memory (y,k) s = b /\
          bignum_from_memory (m,k) s = n /\
          ?q r. q < 2 EXP (64 * i) /\ r < 2 EXP (64 * i) /\
                2 EXP (64 * i) *
                (2 EXP (64 * k) * val(read X6 s) +
                 bignum_from_memory(z,k) s) +
                r =
                q * n + lowdigits a i * b /\
                (ODD n ==> r = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `k:num` `pc + 0x3c` `pc + 0x44`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = x /\
            read X3 s = y /\
            read X4 s = m /\
            read X5 s = word w /\
            read X8 s = word i /\
            bignum_from_memory (x,k) s = a /\
            bignum_from_memory (y,k) s = b /\
            bignum_from_memory (m,k) s = n /\
            bignum_from_memory (z,i) s = 0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      ARM_SIM_TAC BIGNUM_MONTMUL_EXEC (1--4) THEN
      ASM_REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; LOWDIGITS_0; ADD_CLAUSES;
                      SUB_0; WORD_ADD_0; HIGHDIGITS_0] THEN
      REPEAT(EXISTS_TAC `0`) THEN ARITH_TAC];

    ALL_TAC; (*** This is the main loop invariant: save for later ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** This is the corrective subtraction part.... ***)

    GHOST_INTRO_TAC `cout:num` `\s. val(read X6 s)` THEN
    GHOST_INTRO_TAC `mm:num` `bignum_from_memory(z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `mm:num` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
      STRIP_ASSUME_TAC)) THEN

    SUBGOAL_THEN `cout < 2` MP_TAC THENL
     [SUBGOAL_THEN `q * n + a * b < 2 EXP (64 * k) EXP 2 * 2` MP_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `x < e * e /\ y < e * e ==> x + y < e EXP 2 * 2`) THEN
        ASM_SIMP_TAC[LT_MULT2];
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `e * (e * c + m) + r < e EXP 2 * 2
          ==> e EXP 2 * c < e EXP 2 * 2`)) THEN
        REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
      GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT]] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:bool` SUBST_ALL_TAC) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN

    (*** Comparison operation "cmploop" ***)

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x108` `pc + 0x118`
      `\i s. read X0 s = word k /\
             read X1 s = z /\
             read X4 s = m /\
             bignum_from_memory (z,k) s = mm /\
             bignum_from_memory (m,k) s = n /\
             read X10 s = word i /\
             read X6 s = word(bitval c0) /\
             bignum_from_memory (word_add z (word(8 * i)),k - i) s =
             highdigits mm i /\
             bignum_from_memory (word_add m (word(8 * i)),k - i) s =
             highdigits n i /\
             (read CF s <=> lowdigits n i <= lowdigits mm i)` THEN
     ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
       ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--3) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; LE_REFL] THEN
       ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0];

       X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
       GHOST_INTRO_TAC `cin:bool` `read CF` THEN
       GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
        [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
       ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
       REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       ENSURES_INIT_TAC "s0" THEN
       ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--4) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[GSYM WORD_ADD; LOWDIGITS_CLAUSES] THEN
       SIMP_TAC[LEXICOGRAPHIC_LE; LOWDIGITS_BOUND] THEN
       SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
       POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN ARITH_TAC;

       X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
       ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
       ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

       ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

    (*** Corrective subtraction "corrloop" ***)

    ABBREV_TAC `c <=> n <= 2 EXP (64 * k) * bitval c0 + mm` THEN

    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x12c` `pc + 0x144`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X4 s = m /\
            read X6 s = word_neg(word(bitval c)) /\
            read X10 s = word i /\
            bignum_from_memory (word_add z (word(8 * i)),k - i) s =
            highdigits mm i /\
            bignum_from_memory (word_add m (word(8 * i)),k - i) s =
            highdigits n i /\
            &(bignum_from_memory(z,i) s):real =
            &2 pow (64 * i) * &(bitval(~read CF s)) +
            &(lowdigits mm i) - &(bitval c) * &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_REFL; VAL_WORD_0]) THEN
      ARM_VSTEPS_TAC BIGNUM_MONTMUL_EXEC (3--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB_LZERO; SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BITVAL_CLAUSES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_SUB_REFL] THEN
      ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN REWRITE_TAC[WORD_MASK] THEN
      CONV_TAC WORD_REDUCE_CONV THEN AP_THM_TAC THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN EXPAND_TAC "c" THEN
      REWRITE_TAC[ADD_CLAUSES; GSYM NOT_LE; LE_BITVAL; VAL_WORD_BITVAL] THEN
      BOOL_CASES_TAC `c0:bool` THEN
      REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
      ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> n <= e + m`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_EXEC [4] (1--6) THEN
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
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
      ASM_SIMP_TAC[BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_SELF] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      STRIP_TAC THEN UNDISCH_TAC `ODD n ==> r = 0` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (MESON[ODD] `ODD n ==> ~(n = 0)`)) THEN
    TRANS_TAC EQ_TRANS `(2 EXP (64 * k) * bitval c0 + mm) MOD n` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
      MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND; LE_0];
        REWRITE_TAC[INTEGER_CLOSED; REAL_POS]] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN TRANS_TAC LT_TRANS `n:num` THEN
        ASM_REWRITE_TAC[MOD_LT_EQ];
        ALL_TAC] THEN
      MP_TAC(SPECL [`2 EXP (64 * k) * bitval c0 + mm`; `n:num`]
        MOD_CASES) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC(MESON[LT_MULT_LCANCEL]
         `!e. ~(e = 0) /\ e * a < e * b ==> a < b`) THEN
        EXISTS_TAC `2 EXP (64 * k)` THEN
        ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
        MATCH_MP_TAC(ARITH_RULE
         `q * n < e * n /\ aa <= e * n ==> q * n + aa < e * 2 * n`) THEN
        ASM_REWRITE_TAC[LT_MULT_RCANCEL];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[GSYM NOT_LE; COND_SWAP] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
      SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_CASES_TAC `c:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
      REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_ASSOC] THEN
      SIMP_TAC[REAL_MUL_LINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      REAL_INTEGER_TAC;
      REWRITE_TAC[GSYM CONG] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
         `e * x:num = q * n + ab
          ==> (i * e == 1) (mod n)
              ==> (x == i * ab) (mod n)`)) THEN
      ASM_REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2]]] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cout:num` `\s. val(read X6 s)` THEN
  GHOST_INTRO_TAC `z1:num` `bignum_from_memory(z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[ARITH_RULE `k - i = 0 <=> ~(i < k)`] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN

  (*** The multiply-add loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0x94`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = x /\
        read X3 s = y /\
        read X4 s = m /\
        bignum_from_memory (y,k) s = b /\
        bignum_from_memory (m,k) s = n /\
        read X5 s = word w /\
        read X8 s = word i /\
        bignum_from_memory (word_add x (word (8 * (i + 1))),k - (i + 1)) s =
        highdigits a (i + 1) /\
        ?c1 c0. c0 < 2 EXP 64 /\
                read X7 s = word(bitval c1) /\
                read X6 s = word c0 /\
                2 EXP (64 * k) * (2 EXP 64 * bitval c1 + c0) +
                bignum_from_memory (z,k) s =
                (2 EXP (64 * k) * cout + z1) + bigdigit a i * b` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `k:num` `pc + 0x60` `pc + 0x84`
     `\j s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = x /\
            read X3 s = y /\
            read X4 s = m /\
            bignum_from_memory (y,k) s = b /\
            bignum_from_memory (m,k) s = n /\
            read X5 s = word w /\
            read X6 s = word cout /\
            read X8 s = word i /\
            read X9 s = word(bigdigit a i) /\
            read X10 s = word j /\
            bignum_from_memory (word_add x (word (8 * (i + 1))),k - (i + 1)) s =
            highdigits a (i + 1) /\
            bignum_from_memory(word_add z (word (8 * j)),k - j) s =
            highdigits z1 j /\
            bignum_from_memory(word_add y (word (8 * j)),k - j) s =
            highdigits b j /\
            2 EXP (64 * j) * (bitval(read CF s) + val(read X11 s)) +
            bignum_from_memory(z,j) s =
            lowdigits z1 j + bigdigit a i * lowdigits b j` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0] THEN
      REWRITE_TAC[LOWDIGITS_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0; SUB_0];

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X11` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - j:num`; `a:num`; `j:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_EXEC [3;4;6;7] (1--9) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
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
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hout:int64` `read X11` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0]) THEN
      ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_EXEC [3] (3--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`carry_s3:bool`; `val(sum_s3:int64)`] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; VAL_BOUND_64; WORD_VAL] THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
      ONCE_REWRITE_TAC[REAL_ARITH
       `e * (c + h + b) + y:real = e * c + e * (b + h) + y`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Tidying up a bit ***)

  GHOST_INTRO_TAC `z2:num` `bignum_from_memory(z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z2:num` THEN
  GHOST_INTRO_TAC `g6:int64` `read X6` THEN
  GHOST_INTRO_TAC `g7:int64` `read X7` THEN
  ASM_CASES_TAC
   `?c1 c0. c0 < 2 EXP 64 /\
            g7:int64 = word (bitval c1) /\
            g6:int64 = word c0 /\
            2 EXP (64 * k) * (2 EXP 64 * bitval c1 + c0) + z2 =
            (2 EXP (64 * k) * cout + z1) + bigdigit a i * b` THEN
  ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN FIRST_X_ASSUM(X_CHOOSE_THEN `c1:bool`
   (X_CHOOSE_THEN `c0:num` STRIP_ASSUME_TAC)) THEN
  UNDISCH_THEN `g6:int64 = word c0` SUBST_ALL_TAC THEN
  UNDISCH_THEN `g7:int64 = word(bitval c1)` SUBST_ALL_TAC THEN

  (*** The initial prelude of the Montgomery reduction ***)

  ABBREV_TAC `q0 = (w * z2) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xb4`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = x /\
        read X3 s = y /\
        read X4 s = m /\
        bignum_from_memory (y,k) s = b /\
        bignum_from_memory (m,k) s = n /\
        read X5 s = word w /\
        read X8 s = word i /\
        bignum_from_memory (word_add x (word (8 * (i + 1))),k - (i + 1)) s =
        highdigits a (i + 1) /\
        bignum_from_memory (z,k) s = z2 /\
        read X6 s = word c0 /\
        read X7 s = word (bitval c1) /\
        read X9 s = word q0 /\
        read X10 s = word 1 /\
        read X14 s = word(k - 1) /\
        2 EXP 64 * (bitval(read CF s) + val(read X11 s)) + val(read X12 s) =
        q0 * bigdigit n 0 + bigdigit z2 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(m,k) s0 = highdigits n 0 /\
      bignum_from_memory(z,k) s0 = highdigits z2 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_EXEC [4;6] (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z2) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[ADD_CLAUSES; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Break at "montend" to share the end reasoning ***)

  GHOST_INTRO_TAC `r0:num` `\s. val(read X12 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_SEQUENCE_TAC `pc + 0xe8`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = x /\
        read X3 s = y /\
        read X4 s = m /\
        bignum_from_memory (y,k) s = b /\
        bignum_from_memory (m,k) s = n /\
        read X5 s = word w /\
        read X6 s = word c0 /\
        read X7 s = word (bitval c1) /\
        read X8 s = word i /\
        read X9 s = word q0 /\
        read X10 s = word k /\
        bignum_from_memory (word_add x (word (8 * (i + 1))),k - (i + 1)) s =
        highdigits a (i + 1) /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read X11 s)) +
        2 EXP 64 * bignum_from_memory (z,k - 1) s +
        r0 =
        lowdigits z2 k + q0 * lowdigits n k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0xb8` `pc + 0xe0`
     `\j s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = x /\
            read X3 s = y /\
            read X4 s = m /\
            bignum_from_memory (y,k) s = b /\
            bignum_from_memory (m,k) s = n /\
            read X5 s = word w /\
            read X6 s = word c0 /\
            read X7 s = word (bitval c1) /\
            read X8 s = word i /\
            read X9 s = word q0 /\
            read X10 s = word j /\
            bignum_from_memory (word_add x (word (8 * (i + 1))),k - (i + 1)) s =
            highdigits a (i + 1) /\
            bignum_from_memory(word_add z (word (8 * j)),k - j) s =
            highdigits z2 j /\
            bignum_from_memory(word_add m (word (8 * j)),k - j) s =
            highdigits n j /\
            2 EXP (64 * j) * (bitval(read CF s) + val(read X11 s)) +
            2 EXP 64 * bignum_from_memory(z,j-1) s + r0 =
            lowdigits z2 j + q0 * lowdigits n j` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[GSYM highdigits; BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_1] THEN ARITH_TAC;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`j:num`; `j - 1`] THEN
      SUBGOAL_THEN `word_sub (word j) (word 1):int64 = word(j - 1)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X11` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - j:num`; `a:num`; `j:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      UNDISCH_THEN `val(word q0:int64) = q0` (K ALL_TAC) THEN
      ABBREV_TAC `j' = j - 1` THEN
      SUBGOAL_THEN `j = j' + 1` SUBST_ALL_TAC THENL
       [EXPAND_TAC "j'" THEN UNDISCH_TAC `1 <= j` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(j' + 1) + 1 = j' + 2`]) THEN
      REWRITE_TAC[ARITH_RULE `(j' + 1) + 1 = j' + 2`] THEN
      ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_EXEC [3;4;6;7] (1--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(n + 2) - 1 = n + 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `j' + 2 = (j' + 1) + 1` MP_TAC THENL
       [ARITH_TAC; DISCH_THEN SUBST_ALL_TAC] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
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

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`j:num`; `j - 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MONTMUL_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]];

    ALL_TAC] THEN

  (*** The final digit write ****)

  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read X11` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  VAL_INT64_TAC `k - 1` THEN
  SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC BIGNUM_MONTMUL_EXEC [1;2] (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN

  (*** The final mathematics of the outer loop invariant ***)

  MAP_EVERY EXISTS_TAC
   [`2 EXP (64 * i) * q0 + q`;
    `2 EXP (64 * i) * r0 + r`] THEN
  GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
     `q1 < e /\ q0 < ee /\ (q1 < e ==> (q1 + 1) * ee <= e * ee)
      ==> ee * q1 + q0 < ee * e`) THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    SUBGOAL_THEN `(i + 1) + (k - 1) = i + k` SUBST1_TAC THENL
     [UNDISCH_TAC `i:num < k` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES] THEN
    REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC REAL_RING;
    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th))) THEN
    ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
    ASM_REWRITE_TAC[EXP_LT_0; ARITH_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `ee * x + e * y + r = z
      ==> e divides ee /\ (z == 0) (mod e)
          ==> (r == 0) (mod e)`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
      UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      UNDISCH_THEN `(w * z2) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `(n * w + 1 == 0) (mod e) ==> (z + (w * z) * n == 0) (mod e)`) THEN
    ASM_REWRITE_TAC[]]);;

let BIGNUM_MONTMUL_SUBROUTINE_CORRECT = time prove
 (`!k z x y m a b n pc returnaddress.
      ALL (nonoverlapping (z,8 * val k))
          [(word pc,0x150); (x,8 * val k); (y,8 * val k); (m,8 * val k)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_montmul_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [k; z; x; y; m] s /\
                bignum_from_memory (x,val k) s = a /\
                bignum_from_memory (y,val k) s = b /\
                bignum_from_memory (m,val k) s = n)
           (\s. read PC s = returnaddress /\
                (ODD n /\ a * b <= 2 EXP (64 * val k) * n
                 ==> bignum_from_memory (z,val k) s =
                     (inverse_mod n (2 EXP (64 * val k)) * a * b) MOD n))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(z,8 * val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MONTMUL_EXEC BIGNUM_MONTMUL_CORRECT);;
