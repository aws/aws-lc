(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Helper lemmas for verifying vectorized programs                           *)
(* ========================================================================= *)

needs "common/misc.ml";;

(* Simplifies word_subword + word_join + word_zx + bitwise ops.
   Also tries to simplify word_shr. *)
let WORD_BITMANIP_SIMP_LEMMAS = prove(
  `!(x32:(32)word) (y32:(32)word) (x32_2:(32)word)
        (x64:(64)word) (y64:(64)word) (x64_2:(64)word) (y64_2:(64)word)
        (y128:(128)word).
    // word_subword
    word_subword (word_subword y128 (0,64):(64)word) (0,32):(32)word =
      word_subword y128 (0,32):(32)word /\
    word_subword (word_subword y128 (64,64):(64)word) (0,32):(32)word =
      word_subword y128 (64,32):(32)word /\
    word_subword (word_subword y128 (0,64):(64)word) (32,32):(32)word =
      word_subword y128 (32,32):(32)word /\
    word_subword (word_subword y128 (64,64):(64)word) (32,32):(32)word =
      word_subword y128 (96,32):(32)word /\
    word_subword
        (word 79228162495817593524129366015:(128)word) (64,64):(64)word =
      word 4294967295 /\
    word_subword
        (word 79228162495817593524129366015:(128)word) (0,64):(64)word =
      word 4294967295 /\
    // word_subword + word_join
    word_subword (word_join x32 y32: (64)word) (0,32) = y32 /\
    word_subword (word_join x32 y32: (64)word) (32,32) = x32 /\
    word_subword (word_join x64 y64: (128)word) (0,64) = y64 /\
    word_subword (word_join x64 y64: (128)word) (64,64) = x64 /\
    word_subword (word_join x64 y64: (128)word) (0,32):(32)word =
      word_subword y64 (0,32):(32)word /\
    word_subword (word_join x64 y64: (128)word) (32,32):(32)word =
      word_subword y64 (32,32):(32)word /\
    word_subword (word_join x64 y64: (128)word) (64,32):(32)word =
      word_subword x64 (0,32):(32)word /\
    word_subword (word_join x64 y64: (128)word) (96,32):(32)word =
      word_subword x64 (32,32):(32)word /\
    word_subword
      (word_join
        (word_join x64_2 x64: (128)word)
        (word_join y64_2 y64: (128)word): (256)word)
      (64,128):(128)word = word_join x64 y64_2 /\
    // word_subword + word_zx
    word_subword (word_zx x64:(128)word) (0,32):(32)word = word_subword x64 (0,32) /\
    word_subword (word_zx x32:(64)word) (0,32):(32)word = x32 /\
    word_subword (word_subword x64 (0,128):(128)word) (0,32):(32)word = word_subword x64 (0,32) /\
    word_subword (word_zx x64:(128)word) (32,32):(32)word = word_subword x64 (32,32) /\
    word_subword (word_subword x64 (0,128):(128)word) (32,32):(32)word = word_subword x64 (32,32) /\
    // word_subword + word_and + word_join
    word_subword (word_and y128 (word_join x64_2 x64:(128)word)) (64,64) =
      word_and (word_subword y128 (64,64):(64)word) x64_2 /\
    word_subword (word_and y128 (word_join x64_2 x64:(128)word)) (0,64) =
      word_and (word_subword y128 (0,64):(64)word) x64 /\
    // consuming word_ushrs.
    word_subword (word_ushr x64 32) (0,32):(32)word = word_subword x64 (32,32) /\
    word_ushr (word_join x32_2 x32:(64)word) 32 = word_zx x32_2`,
  CONV_TAC WORD_BLAST);;


let SPLIT_WORD64_TO_HILO: tactic =
  SUBST1_TAC (WORD_BLAST `(x:(64)word) =
        word_join (word_subword x (32,32):(32)word) (word_subword x (0,32):(32)word)`) THEN
  ABBREV_TAC `xh = word_subword (x:(64)word) (32,32):(32)word` THEN
  ABBREV_TAC `xl = word_subword (x:(64)word) (0,32):(32)word` THEN
  ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`xh:(32)word`] VAL_BOUND)) THEN
  ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`xl:(32)word`] VAL_BOUND));;

(* Low 64-bits of 64x64->128-bit squaring *)
let WORD_SQR64_LO = prove(`! (x:(64)word). word_or
      (word_shl
        (word_add
          (word_and
            (word 4294967295)
            (word_add
              (word_mul
                (word_zx (word_subword x (32,32):(32)word))
                (word_zx (word_subword x (0,32):(32)word)))
              (word_ushr
                (word_mul (word_zx (word_subword x (0,32):(32)word))
                  (word_zx (word_subword x (0,32):(32)word)))
                32)))
          (word_mul
            (word_zx (word_subword x (32,32):(32)word):(64)word)
            (word_zx (word_subword x (0,32):(32)word))))
      32)
      (word_and
        (word_mul (word_zx (word_subword x (0,32):(32)word))
        (word_zx (word_subword x (0,32):(32)word)))
      (word 4294967295)) = word (0 + val x * val x)`,
    REWRITE_TAC [WORD_RULE
      `word (0 + val (a:(64)word) * val (b:(64)word)) =
       word_mul (a:(64)word) (b:(64)word)`;
       WORD_BLAST `word_zx (word_subword x (32,32):(32)word):(64)word =
                   word_ushr x 32`] THEN
    REPEAT GEN_TAC THEN
    SPLIT_WORD64_TO_HILO THEN
    REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS] THEN
    REWRITE_TAC [GSYM VAL_EQ] THEN
    let r = REWRITE_TAC [VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
        VAL_WORD_SUBWORD; VAL_WORD; VAL_WORD_SHL; WORD_OF_BITS_32BITMASK;
        VAL_WORD_AND_MASK; VAL_WORD_USHR; VAL_WORD_JOIN; WORD_OR_ADD_DISJ] in
      (r THEN ONCE_REWRITE_TAC [WORD_AND_SYM] THEN r)
      THEN
    REWRITE_TAC[DIMINDEX_64; DIMINDEX_32;
        ARITH_RULE `MIN 32 32 = 32 /\ MIN 32 64 = 32 /\ MIN 64 32 = 32`;
        ARITH_RULE `2 EXP 0 = 1`; DIV_1; MOD_MOD_EXP_MIN] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
    (* Remove redundant MODs *)
    (* |- !m n. m < n ==> m MOD n = m *)
    IMP_REWRITE_TAC [SPECL [`val (t:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
    IMP_REWRITE_TAC [ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 32 * 2 EXP 32`] THEN
    IMP_REWRITE_TAC [SPECL
        [`val (t1:(32)word) * val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
    IMP_REWRITE_TAC [LT_MULT2] THEN
    IMP_REWRITE_TAC [SPECL
        [`2 EXP 32 * val (t1:(32)word) + val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
    IMP_REWRITE_TAC [LT_MULT_ADD_MULT; ARITH_RULE `0 < 2 EXP 32`; LE_REFL] THEN
    IMP_REWRITE_TAC [SPECL
        [`x MOD 2 EXP 32 + val (t1:(32)word) * val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
    IMP_REWRITE_TAC [LT_ADD_MULT_MULT; MOD_LT_EQ_LT; ARITH_RULE `0 < 2 EXP 32`; LE_LT] THEN
    (* |- !m n p. m MOD (n * p) = n * (m DIV n) MOD p + m MOD n *)
    REWRITE_TAC [MOD_MULT_MOD] THEN
    (* |- !m n. (m * n) MOD m = 0 *)
    REWRITE_TAC[MOD_MULT] THEN
    IMP_REWRITE_TAC[DIV_MULT] THEN
    REWRITE_TAC[ARITH_RULE `~(2 EXP 32 = 0)`; ADD_0] THEN
    IMP_REWRITE_TAC[DIV_MULT_ADD; MOD_DIV_EQ_0; ARITH_RULE `~(2 EXP 32 = 0)`; ADD_0; MOD_MOD_REFL] THEN
    REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL] THEN
    (* Now rewrite RHS *)
    REWRITE_TAC [ARITH_RULE `(x + y) * (z + w) = x * z + x * w + y * z + y * w`] THEN
    REWRITE_TAC [ARITH_RULE `(2 EXP 32 * w) * z = 2 EXP 32 * (w * z)`] THEN
    REWRITE_TAC [ARITH_RULE `val (k:(32)word) * (2 EXP 32 * z) = 2 EXP 32 * (val k * z)`] THEN
    IMP_REWRITE_TAC [DIV_MULT_ADD; MOD_MULT_ADD; ARITH_RULE `~(2 EXP 32 = 0)`] THEN
    REWRITE_TAC [ADD_MOD_MOD_REFL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC);;

let WORD_SQR64_HI = prove(`!(x:(64)word). word_add
  (word_add
    (word_mul
      (word_zx (word_subword x (32,32):(32)word):(64)word)
      (word_zx (word_subword x (32,32):(32)word):(64)word))
    (word_ushr
      (word_add
        (word_and
          (word 4294967295)
          (word_add
            (word_mul
              (word_zx (word_subword x (32,32):(32)word):(64)word)
              (word_zx (word_subword x (0,32):(32)word)))
            (word_ushr
              (word_mul (word_zx (word_subword x (0,32):(32)word))
              (word_zx (word_subword x (0,32):(32)word)))
            32)))
        (word_mul
          (word_zx (word_subword x (32,32):(32)word):(64)word)
          (word_zx (word_subword x (0,32):(32)word))))
      32))
  (word_ushr
    (word_add
      (word_mul
        (word_zx (word_subword x (32,32):(32)word):(64)word)
        (word_zx (word_subword x (0,32):(32)word)))
      (word_ushr
        (word_mul
          (word_zx (word_subword x (0,32):(32)word))
          (word_zx (word_subword x (0,32):(32)word)))
        32))
    32) =
  word ((val x * val x) DIV 2 EXP 64)`,
  GEN_TAC THEN
  SPLIT_WORD64_TO_HILO THEN
  REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS] THEN
  REWRITE_TAC [GSYM VAL_EQ] THEN
  let r = REWRITE_TAC [VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD; VAL_WORD; VAL_WORD_SHL; WORD_OF_BITS_32BITMASK; VAL_WORD_AND_MASK; VAL_WORD_USHR; VAL_WORD_JOIN; WORD_OR_ADD_DISJ] in (r THEN ONCE_REWRITE_TAC [WORD_RULE `word_and x y = word_and y x`] THEN r) THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_32; ARITH_RULE `MIN 32 32 = 32 /\ MIN 32 64 = 32 /\ MIN 64 32 = 32`; ARITH_RULE `2 EXP 0 = 1`; DIV_1; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  IMP_REWRITE_TAC [SPECL [`val (t:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 32 * 2 EXP 32`] THEN
  IMP_REWRITE_TAC [SPECL [`val (t1:(32)word) * val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_MULT2] THEN
  IMP_REWRITE_TAC [SPECL [`2 EXP 32 * val (t1:(32)word) + val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_MULT_ADD_MULT; ARITH_RULE `0 < 2 EXP 32`; LE_REFL] THEN
  IMP_REWRITE_TAC [SPECL [`x MOD 2 EXP 32 + val (t1:(32)word) * val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_ADD_MULT_MULT; MOD_LT_EQ_LT; ARITH_RULE `0 < 2 EXP 32`; LE_LT] THEN
  IMP_REWRITE_TAC [SPECL [`val (t1:(32)word) * val (t2:(32)word) + t DIV 2 EXP 32`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_MULT_ADD_MULT; ARITH_RULE `0 < 2 EXP 32`] THEN
  IMP_REWRITE_TAC[RDIV_LT_EQ; ARITH_RULE `~(2 EXP 32 = 0)`; LE_LT; LT_MULT2] THEN
  IMP_REWRITE_TAC[LT_ADD_MULT_MULT; LE_LT; MOD_LT_EQ; ARITH_RULE `~(2 EXP 32 = 0)`; ARITH_RULE `0 < 2 EXP 32`] THEN
  (* Remove the outermost MOD 2^32*2^32 *)
  AP_THM_TAC THEN AP_TERM_TAC THEN
  (* Rerwite RHS first *)
  REWRITE_TAC [ARITH_RULE `(x + y) * (z + w) = x * z + x * w + y * z + y * w`] THEN
  REWRITE_TAC [ARITH_RULE `(2 EXP 32 * w) * z = 2 EXP 32 * (w * z)`] THEN
  REWRITE_TAC [ARITH_RULE `val (k:(32)word) * (2 EXP 32 * z) = 2 EXP 32 * (val k * z)`] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD; ARITH_RULE `~(2 EXP 32 = 0)`] THEN
  (* strip 'xh * xh + ...' *)
  REWRITE_TAC[GSYM ADD_ASSOC] THEN AP_TERM_TAC THEN
  IMP_REWRITE_TAC[ADD_DIV_MOD_SIMP_LEMMA; ARITH_RULE `~(2 EXP 32 = 0)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

let WORD_MUL_64_DECOMPOSED_LEMMA = prove(`!a b c.
    ((a + 2 EXP 32 * (b MOD 2 EXP 32 + c MOD 2 EXP 32)) DIV 2 EXP 32) MOD 2 EXP 32 =
    ((a + 2 EXP 32 * (b + c)) DIV 2 EXP 32) MOD 2 EXP 32`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (thm, suffix) -> LABEL_TAC ("Ha_" ^ suffix) thm)
    (zip (CONJUNCTS ((MP
      (SPECL [`a:num`; `2 EXP 32:num`] DIVISION) (ARITH_RULE `~(2 EXP 32 = 0)`))))
      ["eq";"lt"]) THEN
  ABBREV_TAC `ahi = a DIV 2 EXP 32` THEN
  ABBREV_TAC `alo = a MOD 2 EXP 32` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE
    `(ahi * 2 EXP 32 + alo) + 2 EXP 32 * (b MOD 2 EXP 32 + c MOD 2 EXP 32) =
     (ahi + b MOD 2 EXP 32 + c MOD 2 EXP 32) * 2 EXP 32 + alo`] THEN
  REWRITE_TAC[ARITH_RULE
    `(ahi * 2 EXP 32 + alo) + 2 EXP 32 * (b + c) =
     (ahi + b + c) * 2 EXP 32 + alo`] THEN
  IMP_REWRITE_TAC[DIV_UNIQ] THEN (* (A * 2^32 + B) / 2^32 => A *)
  EXISTS_TAC `(ahi + b MOD 2 EXP 32 + c MOD 2 EXP 32)` THEN SIMP_TAC[] THEN
  EXISTS_TAC `(ahi + b + c)` THEN SIMP_TAC[] THEN
  CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[]);;

let WORD_MUL64_LO = prove(`!(x:(64)word) (y:(64)word).
    word_add
      (word_mul (word_zx (word_subword x (0,32):(32)word):(64)word)
                (word_zx (word_subword y (0,32):(32)word):(64)word))
      (word_shl
        (word_add
          (word_zx (word_mul (word_subword y (32,32):(32)word) (word_subword x (0,32):(32)word)))
          (word_zx (word_mul (word_subword y (0,32):(32)word) (word_subword x (32,32):(32)word))))
      32) =
    word (0 + val x * val y)`,
    REWRITE_TAC [WORD_RULE
      `word (0 + val (a:(64)word) * val (b:(64)word)) =
       word_mul (a:(64)word) (b:(64)word)`] THEN
    REPEAT GEN_TAC THEN
    (* word to num: step 1. x = y to val x = val y *)
    REWRITE_TAC[GSYM VAL_EQ] THEN
    (* step 2. remove all word_* *)
    REWRITE_TAC [VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD;
                VAL_WORD; VAL_WORD_SHL] THEN
    (* step 3. add x, y < 2^64 *)
    ASSUME_TAC (ISPECL [`x:(64)word`] VAL_BOUND) THEN
    ASSUME_TAC (ISPECL [`y:(64)word`] VAL_BOUND) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DIMINDEX_64]) THEN
    (* step 4. eliminate dimindex (:N) and simplify *)
    REWRITE_TAC[DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIV_1;MOD_MOD_REFL;
                MOD_MOD_EXP_MIN;ARITH_RULE `2 EXP 0 = 1`; DIV_1] THEN
    CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
    CONV_TAC MOD_DOWN_CONV THEN
    (* split x into [x0h, x0l], and divide y as well *)
    MAP_EVERY (fun (thm, suffix) -> LABEL_TAC ("Hx" ^ suffix) thm)
      (zip (CONJUNCTS ((MP (SPECL [`(val (x:(64)word)):num`; `2 EXP 32:num`] DIVISION)
        (ARITH_RULE `~(2 EXP 32 = 0)`)))) ["eq";"lt"]) THEN
    ABBREV_TAC `xhi = (val (x:(64)word)) DIV 2 EXP 32` THEN
    ABBREV_TAC `xlo = (val (x:(64)word)) MOD 2 EXP 32` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun (thm, suffix) -> LABEL_TAC ("Hy" ^ suffix) thm)
      (zip (CONJUNCTS ((MP (SPECL [`(val (y:(64)word)):num`; `2 EXP 32:num`] DIVISION)
        (ARITH_RULE `~(2 EXP 32 = 0)`)))) ["eq";"lt"]) THEN
    ABBREV_TAC `yhi = (val (y:(64)word)) DIV 2 EXP 32` THEN
    ABBREV_TAC `ylo = (val (y:(64)word)) MOD 2 EXP 32` THEN
    ASM_REWRITE_TAC[] THEN
    (* lhs *)
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC[
      ARITH_RULE `y1hi * x1hi * 2 EXP 32 = 2 EXP 32 * y1hi * x1hi`;
      ARITH_RULE `(y1hi * 2 EXP 32) * x1hi = 2 EXP 32 * y1hi * x1hi`] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN
    (* rhs *)
    REWRITE_TAC[MULT_ASSOC; ARITH_RULE `2 EXP 32 * 2 EXP 32 = 2 EXP 64`] THEN
    REWRITE_TAC[GSYM ADD_ASSOC; GSYM MULT_ASSOC] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN
    (* lhs = rhs *)
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
    REWRITE_TAC[MOD_MULT_MOD] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 32 * p + 2 EXP 32 * q = 2 EXP 32 * (p + q)`; MOD_MULT_ADD] THEN
    REWRITE_TAC [WORD_MUL_64_DECOMPOSED_LEMMA] THEN
    REWRITE_TAC [ARITH_RULE
      `(xlo * ylo + 2 EXP 32 * (yhi * xlo + ylo * xhi)) DIV 2 EXP 32 =
        (2 EXP 32 * xhi * ylo + 2 EXP 32 * xlo * yhi + xlo * ylo) DIV 2 EXP 32`]);;

let WORD_MUL64_HI = prove(`!(x: (64)word) (y: (64)word).
    word_add
      (word_add
        (word_mul
          (word_zx (word_subword x (32,32):(32)word):(64)word)
          (word_zx (word_subword y (32,32):(32)word):(64)word))
        (word_ushr
          (word_add
            (word_mul (word_zx (word_subword x (0,32):(32)word):(64)word)
              (word_zx (word_subword y (32,32):(32)word):(64)word))
            (word_ushr
              (word_mul (word_zx (word_subword x (0,32):(32)word):(64)word)
                (word_zx (word_subword y (0,32):(32)word):(64)word))
              32))
          32))
      (word_ushr
        (word_add
          (word_mul (word_zx (word_subword x (32,32):(32)word):(64)word)
            (word_zx (word_subword y (0,32):(32)word):(64)word))
          (word_and (word 4294967295:(64)word)
            (word_add
              (word_mul (word_zx (word_subword x (0,32):(32)word):(64)word)
                (word_zx (word_subword y (32,32):(32)word):(64)word))
              (word_ushr
                (word_mul (word_zx (word_subword x (0,32):(32)word):(64)word)
                  (word_zx (word_subword y (0,32):(32)word):(64)word))
                32))))
        32) =
    word ((val x * val y) DIV 2 EXP 64)`,
  REPEAT GEN_TAC THEN
  (SUBST1_TAC (WORD_BLAST `(x:(64)word) =
          word_join (word_subword x (32,32):(32)word) (word_subword x (0,32):(32)word)`) THEN
    ABBREV_TAC `xh = word_subword (x:(64)word) (32,32):(32)word` THEN
    ABBREV_TAC `xl = word_subword (x:(64)word) (0,32):(32)word` THEN
    ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`xh:(32)word`] VAL_BOUND)) THEN
    ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`xl:(32)word`] VAL_BOUND))) THEN
  (SUBST1_TAC (WORD_BLAST `(y:(64)word) =
          word_join (word_subword y (32,32):(32)word) (word_subword y (0,32):(32)word)`) THEN
    ABBREV_TAC `yh = word_subword (y:(64)word) (32,32):(32)word` THEN
    ABBREV_TAC `yl = word_subword (y:(64)word) (0,32):(32)word` THEN
    ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`yh:(32)word`] VAL_BOUND)) THEN
    ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`yl:(32)word`] VAL_BOUND))) THEN
  REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS] THEN
  REWRITE_TAC [GSYM VAL_EQ] THEN

  (let r = REWRITE_TAC [VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
      VAL_WORD_SUBWORD; VAL_WORD; VAL_WORD_SHL; WORD_OF_BITS_32BITMASK;
      VAL_WORD_AND_MASK; VAL_WORD_USHR; VAL_WORD_JOIN] in
    (r THEN ONCE_REWRITE_TAC [WORD_RULE `word_and x y = word_and y x`] THEN r)
    THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_32;
      ARITH_RULE `MIN 32 32 = 32 /\ MIN 32 64 = 32 /\ MIN 64 32 = 32`;
      ARITH_RULE `2 EXP 0 = 1`; DIV_1; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`]) THEN

  (* Remove redundant MODs in LHS *)
  IMP_REWRITE_TAC [SPECL [`val (t:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT;
                   ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 32 * 2 EXP 32`] THEN
  IMP_REWRITE_TAC [SPECL
      [`val (t1:(32)word) * val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT;
       LT_MULT2] THEN

  IMP_REWRITE_TAC [
    SPECL [`val (t1:(32)word) * val (t2:(32)word) + k`; `2 EXP 32 * 2 EXP 32`] MOD_LT;
    LT_MULT_ADD_MULT; ARITH_RULE `0 < 2 EXP 32`; LE_LT; EXP_2_MOD_LT; RDIV_LT_EQ;
    LT_MULT2; ARITH_RULE `~(2 EXP 32 = 0)`] THEN

  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  IMP_REWRITE_TAC[ADD_DIV_MOD_SIMP2_LEMMA; ARITH_RULE `~(2 EXP 32 = 0)`] THEN
  (* Simplify RHS *)

  IMP_REWRITE_TAC [SPECL
      [`2 EXP 32 * val (t1:(32)word) + val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_MULT_ADD_MULT; ARITH_RULE `0 < 2 EXP 32`; LE_REFL] THEN
  REWRITE_TAC [ARITH_RULE `(x + y) * (z + w) = x * z + x * w + y * z + y * w`] THEN
  REWRITE_TAC [ARITH_RULE `(2 EXP 32 * w) * z = 2 EXP 32 * (w * z)`] THEN
  REWRITE_TAC [ARITH_RULE `val (k:(32)word) * (2 EXP 32 * z) = 2 EXP 32 * (val k * z)`] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD; ARITH_RULE `~(2 EXP 32 = 0)`] THEN
  (* strip the outermost MOD *)
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

(* Four 64-bit words of 128x128->256-bit squaring *)
let WORD_SQR128_DIGIT0 = prove(
  `!(x:(64)word).
    word_add
      (word_mul
        (word_zx (word_subword x (0,32):(32)word):(64)word)
        (word_zx (word_subword x (0,32):(32)word):(64)word))
      (word_shl
        (word_mul (word_zx (word_subword x (0,32):(32)word):(64)word)
                  (word_zx (word_subword x (32,32):(32)word):(64)word))
        33) =
    word (0 + val x * val x) /\
    word_add
      (word_mul
        (word_zx (word_subword x (0,32):(32)word):(64)word)
        (word_zx (word_subword x (0,32):(32)word):(64)word))
      (word_shl
        (word_mul (word_zx (word_subword x (32,32):(32)word):(64)word)
                  (word_zx (word_subword x (0,32):(32)word):(64)word))
        33) =
    word (0 + val x * val x)`,

  REWRITE_TAC[GSYM WORD_MUL64_LO] THEN
  GEN_TAC THEN
  MATCH_MP_TAC (TAUT `(P /\ (P ==> Q)) ==> P /\ Q`) THEN
  CONJ_TAC THENL [
    ALL_TAC;
    CONV_TAC WORD_RULE
  ] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE`33=1+32`;GSYM WORD_SHL_COMPOSE] THEN
  REWRITE_TAC[WORD_RULE `word_shl x 1 = word_add x x`] THEN
  REWRITE_TAC[WORD_BLAST `!(x:(64)word) y.
    word_shl x 32 = word_shl y 32
    <=> word_subword x (0,32):(32)word = word_subword y (0,32)`] THEN
  IMP_REWRITE_TAC[WORD_SUBWORD_ADD] THEN
  REWRITE_TAC(ADD_0 :: map ARITH_RULE [`x EXP 0 = 1`;`x MOD 1=0`;`0<1`]) THEN
  REWRITE_TAC[DIMINDEX_32;DIMINDEX_64;ARITH_RULE`0+32<=64`] THEN
  IMP_REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS;WORD_SUBWORD_MUL] THEN
  REWRITE_TAC[DIMINDEX_32;DIMINDEX_64;ARITH_RULE`32<=64`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_MUL_SYM]
  THEN REFL_TAC);;

let WORD_SQR128_LEMMA = prove(
  `!(x:int64) (y:int64).
    (word_add
      (word_add
        (word_mul
          (word_zx (word_subword x (32,32):int32))
          (word_zx (word_subword x (32,32):int32)))
        (word_ushr
          (word_mul
            (word_zx (word_subword x (32,32):int32))
            (word_zx (word_subword x (0,32):int32)))
          31))
      (word
        (bitval
        (2 EXP 64 <=
        val
          (word_mul
            (word_zx (word_subword x (0,32):int32))
            (word_zx (word_subword x (0,32):int32)):int64) +
        val
          (word_shl
            (word_mul
              (word_zx (word_subword x (32,32):int32):int64)
              (word_zx (word_subword x (0,32):int32):int64))
            33)))):int64) =
    word ((val x * val x) DIV 2 EXP 64)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD;VAL_WORD_USHR;VAL_WORD_MUL;VAL_WORD_ZX_GEN;
    VAL_WORD_SUBWORD;VAL_WORD;DIMINDEX_64;DIMINDEX_32;VAL_WORD_BITVAL;
    VAL_WORD_SHL;ARITH_RULE `x DIV 2 EXP 0 = x`] THEN
  CONV_TAC (ONCE_DEPTH_CONV MOD_DOWN_CONV) THEN
  CONV_TAC (ONCE_DEPTH_CONV NUM_MIN_CONV) THEN

  ASSUME_TAC (ARITH_RULE `~(2 EXP 64 = 0)`) THEN
  ASSUME_TAC (ARITH_RULE `~(2 EXP 32 = 0)`) THEN

  MP_TAC (SPECL [`val (x:int64)`;`2 EXP 32`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  ABBREV_TAC `xhi = val (x:int64) DIV 2 EXP 32` THEN
  SUBGOAL_THEN `xhi < 2 EXP 32` ASSUME_TAC THENL [
    EXPAND_TAC "xhi" THEN IMP_REWRITE_TAC[RDIV_LT_EQ] THEN
    MP_TAC (SPEC `x:int64` VAL_BOUND_64) THEN ARITH_TAC;
    ALL_TAC
  ] THEN
  ABBREV_TAC `xlo = val (x:int64) MOD 2 EXP 32` THEN
  ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `xlo * xlo <2 EXP 64 /\ xhi * xlo < 2 EXP 64` MP_TAC THENL [
    REWRITE_TAC [ARITH_RULE`2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
    IMP_REWRITE_TAC[LT_MULT2];

    ALL_TAC
  ] THEN
  IMP_REWRITE_TAC[SPECL [`temp:num`;`2 EXP 32`] MOD_LT] THEN
  DISCH_THEN (fun th -> MAP_EVERY (fun th' -> REWRITE_TAC [MATCH_MP MOD_LT th'])
    (CONJUNCTS th)) THEN

  IMP_REWRITE_TAC[BITVAL_LE_DIV] THEN
  CONJ_TAC THENL [
    ALL_TAC;
    TRANS_TAC LTE_TRANS `2 EXP 32 * 2 EXP 32 + 2 EXP 32 * 2 EXP 32` THEN
    CONJ_TAC THENL [
      MATCH_MP_TAC LT_ADD2 THEN REWRITE_TAC[MOD_LT_EQ_LT] THEN
      CONJ_TAC THENL [IMP_REWRITE_TAC [LT_MULT2]; ARITH_TAC];

      ARITH_TAC
    ]
  ] THEN

  REWRITE_TAC[LEFT_ADD_DISTRIB;RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[ARITH_RULE`(x*2 EXP 32)*y*2 EXP 32 = (x*y)*2 EXP 64`;GSYM ADD_ASSOC]
    THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD] THEN
  AP_TERM_TAC THEN

  (* Use ADD_DIV_MOD_SIMP2_LEMMA *)
  REWRITE_TAC[ARITH_RULE`2 EXP 33 = 2 * 2 EXP 32`] THEN
  SUBGOAL_THEN `(xhi*xlo) DIV 2 EXP 31 = ((2 * (2 EXP 32)) * xhi*xlo) DIV 2 EXP 64` SUBST_ALL_TAC THENL [
    REWRITE_TAC[ARITH_RULE`2 EXP 64 = (2 * (2 EXP 32)) * 2 EXP 31`] THEN
    IMP_REWRITE_TAC[DIV_MULT2] THEN ARITH_TAC;
    ALL_TAC
  ] THEN
  IMP_REWRITE_TAC[ADD_DIV_MOD_SIMP2_LEMMA] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let WORD_SQR128_DIGIT1 = prove(
  `!(x:int64) (y:int64).
    word_add
      (word_add
        (word_add
          (word_mul (word_zx (word_subword x (32,32):(32)word):(64)word)
                    (word_zx (word_subword x (32,32):(32)word)))
          (word_ushr
            (word_mul
              (word_zx (word_subword x (32,32):(32)word))
              (word_zx (word_subword x (0,32):(32)word)))
            31):(64)word)
        (word
          (bitval
            (2 EXP 64 <=
              val
                (word_mul (word_zx (word_subword x (0,32):(32)word))
                          (word_zx (word_subword x (0,32):(32)word))
                          :(64)word) +
              val
                (word_shl
                  (word_mul (word_zx (word_subword x (32,32):(32)word))
                            (word_zx (word_subword x (0,32):(32)word))
                            :(64)word)
                  33)))))
      (word_shl (word (0 + val x * val y)) 1)
    = word_add
      (word_add
        (word ((val x * val x) DIV 2 EXP 64))
        (word (0 + val x * val y)))
      (word (0 + val x * val y))`,
  REWRITE_TAC [WORD_RULE `word_add (word_add x y) y = word_add x (word_shl y 1)`] THEN
  REPEAT GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_SQR128_LEMMA]);;

let WORD_SQR128_DIGIT2 = prove(
  `!(x:int64) (y:int64).
    word_add
      (word_add
        (word (0 + val y * val y))
        (word_subword
          (word_join
            (word ((val x * val y) DIV 2 EXP 64):int64)
            (word (0 + val x * val y):int64)
            :int128)
          (63,64):int64))
      (word
        (bitval
          (2 EXP 64 <=
            val
            (word_add
              (word_add
                (word_mul
                  (word_zx (word_subword x (32,32):int32))
                  (word_zx (word_subword x (32,32):int32)))
                (word_ushr
                  (word_mul
                    (word_zx (word_subword x (32,32):int32))
                    (word_zx (word_subword x (0,32):int32)))
                  31))
              (word
                (bitval
                (2 EXP 64 <=
                val
                  (word_mul
                    (word_zx (word_subword x (0,32):int32))
                    (word_zx (word_subword x (0,32):int32)):int64) +
                val
                  (word_shl
                    (word_mul
                      (word_zx (word_subword x (32,32):int32):int64)
                      (word_zx (word_subword x (0,32):int32):int64))
                    33)))):int64
              ) +
              val (word_shl (word (0 + val x * val y):int64) 1)))) =

    word_add
      (word_add
        (word_add
          (word_add
            (word (0 + val y * val y))
            (word ((val x * val y) DIV 2 EXP 64)))
          (word
            (bitval
              (2 EXP 64 <=
                val (word ((val x * val x) DIV 2 EXP 64):int64) +
                val (word (0 + val x * val y):int64)))))
        (word ((val x * val y) DIV 2 EXP 64)))
    (word
      (bitval
        (2 EXP 64 <=
          val
            (word_add
              (word ((val x * val x) DIV 2 EXP 64))
              (word (0 + val x * val y))
              :int64) +
          val (word (0 + val x * val y):int64))))`,

  REWRITE_TAC[WORD_SQR128_LEMMA] THEN
  ASSUME_TAC (ARITH_RULE`~(2 EXP 64 = 0)`) THEN

  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[ADD_CLAUSES;VAL_WORD_ADD;VAL_WORD_USHR;VAL_WORD_MUL;VAL_WORD_ZX_GEN;
    VAL_WORD_SUBWORD;VAL_WORD_JOIN;VAL_WORD;DIMINDEX_64;DIMINDEX_32;
    DIMINDEX_128;VAL_WORD_BITVAL;VAL_WORD_SHL;ARITH_RULE `x DIV 2 EXP 0 = x`] THEN
  IMP_REWRITE_TAC[BITVAL_LE_MOD_MOD_DIV] THEN
  CONV_TAC (ONCE_DEPTH_CONV MOD_DOWN_CONV) THEN
  CONV_TAC (ONCE_DEPTH_CONV NUM_MIN_CONV) THEN

  REWRITE_TAC[VAL_MUL_DIV_MOD_SIMP;DIVISION_SIMP] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  REWRITE_TAC[DIV_2_EXP_63;ARITH_RULE`2 EXP 1 = 2`] THEN
  MATCH_MP_TAC MOD_ADD_MOD_RIGHT THEN

  REWRITE_TAC[ADD_MOD_MOD_REFL] THEN
  IMP_REWRITE_TAC[ADD_DIV_MOD_SIMP2_LEMMA] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  IMP_REWRITE_TAC[ADD_DIV_MOD_SIMP2_LEMMA] THEN
  TARGET_REWRITE_TAC [ADD_SYM] ADD_DIV_MOD_SIMP2_LEMMA THEN
  ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let WORD_SQR128_DIGIT3 = prove(
 `!(x:int64) (y:int64).
  word_add
  (word_add
    (word_add
      (word_add
        (word_mul (word_zx (word_subword y (32,32):int32):int64)
          (word_zx (word_subword y (32,32):int32)))
        (word_ushr
          (word_mul (word_zx (word_subword y (32,32):int32):int64)
            (word_zx (word_subword y (0,32):int32)))
        31))
      (word
        (bitval
          (2 EXP 64 <=
            val
              (word_mul (word_zx (word_subword y (0,32):int32):int64)
                (word_zx (word_subword y (0,32):int32))) +
            val
              (word_shl
                (word_mul (word_zx (word_subword y (32,32):int32):int64)
                  (word_zx (word_subword y (0,32):int32)))
                33)))))
    (word_ushr (word ((val x * val y) DIV 2 EXP 64):int64) 63))
  (word
    (bitval
    (2 EXP 64 <=
      val (word (0 + val y * val y):int64) +
      val
      (word_subword
        (word_join
          (word ((val x * val y) DIV 2 EXP 64):int64)
          (word (0 + val x * val y):int64)
          :int128)
        (63,64):int64) +
      bitval
      (2 EXP 64 <=
      val
      (word_add
        (word_add
          (word_mul (word_zx (word_subword x (32,32):int32):int64)
            (word_zx (word_subword x (32,32):int32):int64))
        (word_ushr
          (word_mul (word_zx (word_subword x (32,32):int32):int64)
            (word_zx (word_subword x (0,32):int32):int64))
        31))
      (word
      (bitval
      (2 EXP 64 <=
        val
          (word_mul (word_zx (word_subword x (0,32):int32):int64)
            (word_zx (word_subword x (0,32):int32):int64)) +
        val
          (word_shl
            (word_mul (word_zx (word_subword x (32,32):int32))
              (word_zx (word_subword x (0,32):int32):int64))
            33))))) +
      val (word_shl (word (0 + val x * val y):int64) 1))))) =

  word_add
    (word_add
      (word ((val y * val y) DIV 2 EXP 64))
      (word
      (bitval
        (2 EXP 64 <=
          val (word (0 + val y * val y):int64) +
          val (word ((val x * val y) DIV 2 EXP 64):int64) +
          bitval
            (2 EXP 64 <=
              val (word ((val x * val x) DIV 2 EXP 64):int64) +
              val (word (0 + val x * val y):int64))))))
    (word
      (bitval
      (2 EXP 64 <=
          val
          (word_add
            (word_add (word (0 + val y * val y):int64)
              (word ((val x * val y) DIV 2 EXP 64)))
            (word
              (bitval
                (2 EXP 64 <=
                  val (word ((val x * val x) DIV 2 EXP 64):int64) +
                  val (word (0 + val x * val y):int64))))) +
        val (word ((val x * val y) DIV 2 EXP 64):int64) +
        bitval
          (2 EXP 64 <=
            val
              (word_add (word ((val x * val x) DIV 2 EXP 64):int64)
                (word (0 + val x * val y))) +
                val (word (0 + val x * val y):int64)))))`,

  REWRITE_TAC[WORD_SQR128_LEMMA] THEN
  ASSUME_TAC (ARITH_RULE`~(2 EXP 64 = 0)`) THEN
  REPEAT GEN_TAC THEN

  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[ADD_CLAUSES;VAL_WORD_ADD;VAL_WORD_USHR;VAL_WORD_MUL;VAL_WORD_ZX_GEN;
    VAL_WORD_SUBWORD;VAL_WORD_JOIN;VAL_WORD;DIMINDEX_64;DIMINDEX_32;
    DIMINDEX_128;VAL_WORD_BITVAL;VAL_WORD_SHL;ARITH_RULE `x DIV 2 EXP 0 = x`;
    ARITH_RULE`2 EXP 1 = 2`;DIV_2_EXP_63] THEN
  CONV_TAC (ONCE_DEPTH_CONV MOD_DOWN_CONV) THEN
  CONV_TAC (ONCE_DEPTH_CONV NUM_MIN_CONV) THEN

  ASM_SIMP_TAC[VAL_MUL_DIV_MOD_SIMP;DIVISION_SIMP;
              ADD_DIV_MOD_SIMP2_LEMMA;ADD_DIV_MOD_SIMP_LEMMA] THEN
  IMP_REWRITE_TAC[BITVAL_LE_MOD_MOD_DIV] THEN
  CONJ_TAC THENL [
    ALL_TAC;
    IMP_REWRITE_TAC [RDIV_LT_EQ;LT_MULT2;VAL_BOUND_64]
  ] THEN

  ASM_SIMP_TAC[GSYM ADD_ASSOC;ADD_DIV_MOD_SIMP2_LEMMA] THEN
  MATCH_MP_TAC MOD_ADD_MOD_RIGHT THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN

  (* High-level idea: for every 'bitval (2 EXP 64 <= X)', 0 <= x < 2 EXP 65. *)
  ASSUME_TAC (ARITH_RULE`1 < 2 EXP 64`) THEN
  IMP_REWRITE_TAC[BITVAL_LE_DIV] THEN
  REWRITE_TAC[ARITH_RULE`2 * 2 EXP 64 = 2 EXP 64 + 2 EXP 64`] THEN
  REPEAT CONJ_TAC THENL [
    ALL_TAC;

    MATCH_MP_TAC LT_ADD2 THEN
    ASM_REWRITE_TAC[MOD_LT_EQ] THEN
    IMP_REWRITE_TAC[MULT_ADD_DIV_LT;VAL_BOUND_64] THEN
    ASM_SIMP_TAC[LE_LT;MOD_LT_EQ];

    MATCH_MP_TAC LT_ADD2 THEN
    ASM_REWRITE_TAC[MOD_LT_EQ] THEN
    IMP_REWRITE_TAC[MULT_ADD_DIV_LT;VAL_BOUND_64] THEN
    IMP_REWRITE_TAC[LE_LT;RDIV_LT_EQ] THEN
    DISJ1_TAC THEN IMP_REWRITE_TAC[LT_MULT2;VAL_BOUND_64];

    MATCH_MP_TAC LTE_ADD2 THEN
    ASM_REWRITE_TAC[MOD_LT_EQ] THEN
    TRANS_TAC LE_TRANS `(2 EXP 64 - 1) + 1` THEN
    CONJ_TAC THENL [
      ALL_TAC; ARITH_TAC
    ] THEN
    MATCH_MP_TAC LE_ADD2 THEN
    CONJ_TAC THENL [
      REWRITE_TAC[GSYM LT_SUC_LE] THEN
      REWRITE_TAC[ARITH_RULE`SUC (2 EXP 64 - 1) = 2 EXP 64`] THEN
      ASM_REWRITE_TAC[MOD_LT_EQ];

      REWRITE_TAC[GSYM LT_SUC_LE;ARITH_RULE`SUC 1 = 1 + 1`] THEN
      IMP_REWRITE_TAC[RDIV_LT_EQ;LEFT_ADD_DISTRIB;MULT_CLAUSES] THEN
      MATCH_MP_TAC LT_ADD2 THEN CONJ_TAC THENL [
        IMP_REWRITE_TAC[RDIV_LT_EQ;LT_MULT2;VAL_BOUND_64];

        IMP_REWRITE_TAC[MOD_LT_EQ]
      ]
    ]
  ] THEN

  SUBGOAL_THEN
      `!k. (val (y:int64) * val (y:int64) + k) MOD 2 EXP 64 =
           ((val (y:int64) * val (y:int64)) MOD 2 EXP 64 + k) MOD 2 EXP 64`
      (LABEL_TAC "H") THENL [
    REWRITE_TAC[ADD_MOD_MOD_REFL]; ALL_TAC
  ] THEN
  USE_THEN "H" (fun th -> REWRITE_TAC[th]) THEN
  TARGET_REWRITE_TAC[ADD_AC] ADD_DIV_MOD_SIMP2_LEMMA THEN
  ASM_REWRITE_TAC[] THEN

  TARGET_REWRITE_TAC[ADD_AC] ADD_DIV_MOD_SIMP2_LEMMA THEN
  ASM_REWRITE_TAC[] THEN

  SUBGOAL_THEN `!(a:num) (b:num).
      (2 * (a * b) DIV 2 EXP 64) DIV 2 EXP 64 =
      ((2 * a * b) DIV 2 EXP 64) DIV 2 EXP 64`
      (fun th -> REWRITE_TAC[th]) THENL [
    ASSUME_TAC (ARITH_RULE `~(2 EXP 63 = 0)`) THEN
    REPEAT STRIP_TAC THEN
    ABBREV_TAC `c = a * b` THEN
    MP_TAC (SPECL [`c:num`;`2 EXP 64`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN (fun th -> let t1,t2 = CONJ_PAIR th in
      LABEL_TAC "HC" t1 THEN LABEL_TAC "HLT" t2) THEN
    MAP_EVERY ABBREV_TAC [`ch = c DIV 2 EXP 64`;`cl = c MOD 2 EXP 64`] THEN

    MP_TAC (SPECL [`cl:num`;`2 EXP 63`] DIVISION) THEN
    ANTS_TAC THENL [ARITH_TAC;ALL_TAC] THEN
    DISCH_THEN (fun th -> let t1,t2 = CONJ_PAIR th in
      LABEL_TAC "HCL" t1 THEN LABEL_TAC "HCLLT" t2) THEN
    MAP_EVERY ABBREV_TAC [`(clh:num) = cl DIV 2 EXP 63`;`cll = cl MOD 2 EXP 63`] THEN
    SUBGOAL_THEN `(clh:num) < 2` ASSUME_TAC THENL [
      EXPAND_TAC "clh" THEN IMP_REWRITE_TAC [RDIV_LT_EQ] THEN
      ASM_ARITH_TAC;
      ALL_TAC
    ] THEN

    USE_THEN "HC" SUBST1_TAC THEN
    USE_THEN "HCL" SUBST1_TAC THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
    TARGET_REWRITE_TAC [MULT_AC] DIV_MULT_ADD THEN
    ASM_REWRITE_TAC[] THEN
    IMP_REWRITE_TAC[ARITH_RULE`2*(x:num)*(2 EXP 63) = x*(2 EXP 64)`;DIV_MULT_ADD] THEN
    SUBGOAL_THEN `(2 * cll:num) DIV 2 EXP 64 = 0` SUBST_ALL_TAC THENL [
      IMP_REWRITE_TAC[DIV_LT] THEN ASM_ARITH_TAC; ALL_TAC
    ] THEN
    REWRITE_TAC[ADD_0] THEN

    (* now either clh is 0 or 1! *)
    MP_TAC (SPECL [`2 * ch`;`2 EXP 64`] DIVISION) THEN
    ANTS_TAC THENL [ARITH_TAC;ALL_TAC] THEN
    DISCH_THEN (fun th -> let t1,t2 = CONJ_PAIR th in
      LABEL_TAC "HCH" t1 THEN LABEL_TAC "HCHLT" t2) THEN
    MAP_EVERY ABBREV_TAC [`chh = (2 * ch) DIV 2 EXP 64`;`chl = (2 * ch) MOD 2 EXP 64`] THEN
    USE_THEN "HCH" SUBST1_TAC THEN
    TARGET_REWRITE_TAC [ADD_AC] DIV_MULT_ADD THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (ARITH_RULE`x=0 ==> a = a+x`) THEN
    ASM_SIMP_TAC[DIV_EQ_0] THEN

    SUBGOAL_THEN `EVEN chl` MP_TAC THENL [
      MP_TAC (SPEC `ch:num` EVEN_DOUBLE) THEN
      USE_THEN "HCH" SUBST1_TAC THEN
      REWRITE_TAC[EVEN_ADD] THEN
      REWRITE_TAC[ARITH_RULE`a*2 EXP 64 = 2*(a*2 EXP 63)`] THEN
      ONCE_REWRITE_TAC[EVEN_MULT] THEN
      REWRITE_TAC[ARITH_RULE`EVEN 2`];

      ALL_TAC
    ] THEN

    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `2 * m <= 2 EXP 64 - 2` MP_TAC THENL [
      USE_THEN "HCHLT" MP_TAC THEN REWRITE_TAC[
        ARITH_RULE`2 EXP 64 - 2 = 2 * (2 EXP 63 - 1)`;
        ARITH_RULE`2 EXP 64=2*2 EXP 63`] THEN
      IMP_REWRITE_TAC[LT_MULT_LCANCEL;LE_MULT_LCANCEL;ARITH_RULE`~(2=0)`] THEN
      ARITH_TAC;

      ALL_TAC
    ] THEN
    ASM_ARITH_TAC;

    ALL_TAC
  ] THEN
  TARGET_REWRITE_TAC[ADD_AC] ADD_DIV_MOD_SIMP2_LEMMA THEN
  ASM_REWRITE_TAC[] THEN

  TARGET_REWRITE_TAC[ADD_AC] ADD_DIV_MOD_SIMP2_LEMMA THEN
  ASM_REWRITE_TAC[] THEN

  ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Helpful tactics                                                           *)
(* ------------------------------------------------------------------------- *)

(* match terms of pattern `read (memory :> bytes64 addr) s = v` and
   return (addr, s, v). *)
let decompose_read_memory_bytes64 t: (term * term * term) option =
  if is_eq t
  then begin match lhs t with
    | Comb(Comb (
        Const ("read", _),
        Comb(
          Comb(Const (":>", _),Const("memory", _)),
          Comb(Const ("bytes64", _),addr))),st) ->
            Some (addr, st, rhs t)
    | _ -> None end
  else None;;

let _ = decompose_read_memory_bytes64 `read (memory :> bytes64 addr) s = v`;;

let BYTES128_EQ_JOIN64_TAC lhs128 hi64 lo64 =
  let hilo = mk_comb (mk_comb
    (`word_join:(64)word->(64)word->(128)word`,hi64),lo64) in
  SUBGOAL_THEN (mk_eq (lhs128, hilo)) ASSUME_TAC THENL [
    EVERY_ASSUM (fun thm ->
      (*let t = is_read_memory_bytes64 (concl thm) in
      let _ = printf "%s <is_read_bytes64: %b>\n" (string_of_term (concl thm)) t in*)
      if decompose_read_memory_bytes64 (concl thm) <> None
      then REWRITE_TAC[GSYM thm]
      else ALL_TAC) THEN
    REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
    (ARITH_TAC ORELSE (PRINT_GOAL_TAC THEN NO_TAC));
    ALL_TAC
  ];;

(* For s \in acc_rewrite_states_list \cap acc_states_list, apply rewrite
   acc_rewrite_rules to the assumptions before ACCSTEP *)
let ARM_REWRITE_ASSUM_AND_ACCSTEPS_TAC
    execth
    acc_rewrite_states_list (acc_rewrite_rules: thm list)
    acc_states_list states_list =
  let sl = statenames "s" acc_rewrite_states_list in
  let rls = WORD_BITMANIP_SIMP_LEMMAS::acc_rewrite_rules in
  ARM_GEN_ACCSTEPS_TAC
    (fun sname ->
      if List.mem sname sl then RULE_ASSUM_TAC (REWRITE_RULE rls)
      else RULE_ASSUM_TAC (REWRITE_RULE [WORD_BITMANIP_SIMP_LEMMAS]))
  execth acc_states_list states_list;;


let ARM_REWRITE_ASSUM_AND_XACCSTEPS_TAC2
    execth
    simp_states_list (simp_rewrite_rules: thm list)
    acc_states_list states_list
    exclude_regs =
  let acc_preproc:tactic = RULE_ASSUM_TAC
      (REWRITE_RULE [WORD_BITMANIP_SIMP_LEMMAS]) in
  MAP_EVERY
    (fun n ->
      (if List.mem n simp_states_list then
        RULE_ASSUM_TAC (REWRITE_RULE (WORD_BITMANIP_SIMP_LEMMAS::simp_rewrite_rules))
      else ALL_TAC) THEN
      let state_name = "s"^string_of_int n in
      ARM_SINGLE_STEP_TAC execth state_name THEN
      if mem n acc_states_list then
        acc_preproc THEN TRY(
          ACCUMULATEX_ARITH_TAC ([`SP`] @ exclude_regs) state_name THEN CLARIFY_TAC)
      else ALL_TAC)
    states_list;;


let contains_str (s:string) (subs:string): bool =
  let subsl = explode subs in
  let n = length subsl in
  let rec fn sl =
    if length sl < n then false
    else if fst (chop_list n sl) = subsl then true
    else match sl with | [] -> false | h::t -> fn t in
  fn (explode s);;

let DISCARD_READ_QREGS:tactic =
  DISCARD_ASSUMPTIONS_TAC (fun th ->
      contains_str (string_of_term (concl th)) "read Q");;
