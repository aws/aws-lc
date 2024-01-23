(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Helper lemmas for verifying vectorized programs                           *)
(* ========================================================================= *)

needs "common/misc.ml";;

let SPLIT_WORD64_TO_HILO: tactic =
  SUBST1_TAC (WORD_BLAST `(x:(64)word) =
        word_join (word_subword x (32,32):(32)word) (word_subword x (0,32):(32)word)`) THEN
  ABBREV_TAC `xh = word_subword (x:(64)word) (32,32):(32)word` THEN
  ABBREV_TAC `xl = word_subword (x:(64)word) (0,32):(32)word` THEN
  ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`xh:(32)word`] VAL_BOUND)) THEN
  ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`xl:(32)word`] VAL_BOUND));;

let WORD_SQR64_LO = prove(`! (x:(64)word). word_or
      (word_shl
        (word_add
        (word_and (word 4294967295)
        (word_add
          (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word)))
        (word_ushr
          (word_mul (word_zx (word_subword x (0,32):(32)word))
          (word_zx (word_subword x (0,32):(32)word)))
        32)))
        (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word))))
      32)
      (word_and
        (word_mul (word_zx (word_subword x (0,32):(32)word))
        (word_zx (word_subword x (0,32):(32)word)))
      (word 4294967295)) = word (0 + val x * val x)`,
    REWRITE_TAC [WORD_RULE
      `word (0 + val (a:(64)word) * val (b:(64)word)) =
       word_mul (a:(64)word) (b:(64)word)`] THEN
    REPEAT GEN_TAC THEN
    SPLIT_WORD64_TO_HILO THEN
    REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS] THEN
    REWRITE_TAC [GSYM VAL_EQ] THEN
    let r = REWRITE_TAC [VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
        VAL_WORD_SUBWORD; VAL_WORD; VAL_WORD_SHL; WORD_OF_BITS_32BITMASK;
        VAL_WORD_AND_MASK; VAL_WORD_USHR; VAL_WORD_JOIN; WORD_OR_ADD_DISJ] in
      (r THEN ONCE_REWRITE_TAC [WORD_RULE `word_and x y = word_and y x`] THEN r)
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
  (word_add (word_mul (word_ushr x 32) (word_ushr x 32))
  (word_ushr
    (word_add
      (word_and
        (word 4294967295)
        (word_add
          (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word)))
          (word_ushr
            (word_mul (word_zx (word_subword x (0,32):(32)word))
            (word_zx (word_subword x (0,32):(32)word)))
          32)))
      (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word))))
    32))
  (word_ushr
    (word_add
      (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word)))
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


(* ------------------------------------------------------------------------- *)
(* Helpful tactics                                                           *)
(* ------------------------------------------------------------------------- *)

(* match terms of pattern `read (memory :> bytes64 _) ) = _`. *)
let is_read_memory_bytes64 t =
  if is_eq t
  then begin match lhs t with
    | Comb(Comb (
        Const ("read", _),
        Comb(
          Comb(Const (":>", _),Const("memory", _)),
          Comb(Const ("bytes64", _),_))),_) -> true
    | _ -> false end
  else false;;

let BYTES128_EQ_JOIN64_TAC lhs128 hi64 lo64 =
  let hilo = mk_comb (mk_comb
    (`word_join:(64)word->(64)word->(128)word`,hi64),lo64) in
  SUBGOAL_THEN (mk_eq (lhs128, hilo)) ASSUME_TAC THENL [
    EVERY_ASSUM (fun thm ->
      (*let t = is_read_memory_bytes64 (concl thm) in
      let _ = printf "%s <is_read_bytes64: %b>\n" (string_of_term (concl thm)) t in*)
      if is_read_memory_bytes64 (concl thm)
      then REWRITE_TAC[GSYM thm]
      else ALL_TAC) THEN
    REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
    ARITH_TAC;
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
