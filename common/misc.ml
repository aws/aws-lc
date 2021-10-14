(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Miscellaneous theorems that don't quite fit in the main libraries.        *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/rstc.ml";;
needs "Library/floor.ml";;

(* ------------------------------------------------------------------------- *)
(* A few small general word lemmas.                                          *)
(* ------------------------------------------------------------------------- *)

let WORD_NOT_AND = prove
 (`!x y:N word. word_not(word_and x y) = word_or (word_not x) (word_not y)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_NOT_OR = prove
 (`!x y:N word. word_not(word_or x y) = word_and (word_not x) (word_not y)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_ZX_BITVAL = prove
 (`!b. (word_zx:M word->N word) (word(bitval b)) = word(bitval b)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; WORD_ZX_0; WORD_ZX_1]);;

let WORD_AND_POW2 = prove
 (`(!(x:N word) k.
        word_and x (word(2 EXP k)) = word(2 EXP k * bitval(bit k x))) /\
   (!(x:N word) k.
        word_and (word(2 EXP k)) x = word(2 EXP k * bitval(bit k x)))`,
  REWRITE_TAC[AND_FORALL_THM; bitval] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_POW2; BIT_WORD_0] THEN
  ASM_MESON_TAC[]);;

let VAL_WORD_AND_POW2 = prove
 (`(!(x:N word) k.
        val(word_and x (word(2 EXP k))) = 2 EXP k * bitval(bit k x)) /\
   (!(x:N word) k.
        val(word_and (word(2 EXP k)) x) = 2 EXP k * bitval(bit k x))`,
  REWRITE_TAC[WORD_AND_POW2] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[bitval] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES; LT_EXP; EXP_LT_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let VAL_WORD_AND_LE = prove
 (`(!x y:N word. val(word_and x y) <= val x) /\
   (!x y:N word. val(word_and x y) <= val y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[val_def] THEN MATCH_MP_TAC NSUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN X_GEN_TAC `i:num` THEN
  SIMP_TAC[IN_ELIM_THM; BIT_WORD_AND; LE_MULT_LCANCEL; LE_BITVAL]);;

let VAL_WORD_AND_WORD_LE = prove
 (`(!(x:N word) n. val(word_and x (word n)) <= n) /\
   (!(x:N word) n. val(word_and (word n) x) <= n)`,
  MESON_TAC[VAL_WORD_AND_LE; LE_TRANS; LE_REFL; VAL_WORD_LE]);;

let WORD_JOIN_NOT = prove
 (`!v w. dimindex(:P) <= dimindex(:M) + dimindex(:N)
         ==> (word_join:(M)word->(N)word->(P)word) (word_not v) (word_not w) =
             word_not(word_join v w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_JOIN; BIT_WORD_NOT; COND_SWAP] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN EQ_TAC THEN SIMP_TAC[] THEN
  ASM_ARITH_TAC);;

let WORD_SUBWORD_NOT = prove
 (`!(x:M word) pos len.
        dimindex(:N) <= len /\ pos + len <= dimindex(:M)
        ==> word_subword (word_not x) (pos,len):N word =
            word_not (word_subword x (pos,len))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_NOT] THEN
  SIMP_TAC[ARITH_RULE `i < MIN m n <=> i < m /\ i < n`] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Trivial but requires two distinct library files to be combined.           *)
(* ------------------------------------------------------------------------- *)

let RELPOW_ITER = prove
 (`!f n x y:A. RELPOW n (\a b. f a = b) x y <=> ITER n f x = y`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[RELPOW; ITER] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some specialized lemmas that come up when shifts are masked to 6 bits.    *)
(* ------------------------------------------------------------------------- *)

let MOD_64_CLAUSES = prove
 (`(!c. val(word(c MOD 64):int64) = c MOD 64) /\
   (!c. val(word(c MOD 256):byte) = c MOD 256) /\
   (!c. val(word c:int64) MOD 64 = c MOD 64) /\
   (!n. n MOD 256 MOD 64 = n MOD 64) /\
   (!n. n MOD 64 MOD 64 = n MOD 64) /\
   (!n. n MOD 2 EXP 64 MOD 64 = n MOD 64) /\
   (!n. n MOD 64 MOD 2 EXP 64 = n MOD 64)`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  ABBREV_TAC `e = 2 EXP 64` THEN
  REWRITE_TAC[ARITH_RULE `64 = 2 EXP 6 /\ 256 = 2 EXP 8`] THEN
  EXPAND_TAC "e" THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* To undo expansion of the way CSETM is done (should tweak ARM_STEP_TAC?)   *)
(* ------------------------------------------------------------------------- *)

let WORD_UNMASK_64 = prove
 (`(if p then word 18446744073709551615 else word 0):int64 =
   word_neg(word(bitval p)) /\
   (if p then word 0 else word 18446744073709551615):int64 =
   word_neg(word(bitval(~p)))`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Proving equality throwing away some other MSB multiples.                  *)
(* ------------------------------------------------------------------------- *)

let EQUAL_FROM_CONGRUENT_REAL = prove
 (`!n x y z.
        (&0 <= x /\ x < &2 pow n) /\
        (&0 <= y /\ y < &2 pow n) /\
        integer z /\ integer((x - y) / &2 pow n + z)
        ==> x = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`z:real`; `(x - y) / &2 pow n + z:real`]
        REAL_EQ_INTEGERS) THEN
  ASM_REWRITE_TAC[REAL_ARITH `z:real = x + z <=> x = &0`] THEN
  REWRITE_TAC[REAL_ARITH `abs(z - (x + z)):real = abs x`] THEN
  REWRITE_TAC[REAL_DIV_EQ_0; REAL_POW_EQ_0; REAL_SUB_0] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN ASM_REAL_ARITH_TAC);;

let EQUAL_FROM_CONGRUENT_MOD = prove
 (`!n x y z.
        &y:real < &2 pow n /\
        integer z /\ integer((&x - &y) / &2 pow n + z)
        ==> x MOD (2 EXP n) = y`,
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; MOD_UNIQUE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[num_congruent; int_congruent] THEN
  EXISTS_TAC `int_of_real(((&x - &y) / &(2 EXP n) + z) - z)` THEN
  REWRITE_TAC[int_eq; int_mul_th; int_sub_th] THEN
  ASM_SIMP_TAC[REAL_OF_INT_OF_REAL; INTEGER_CLOSED] THEN
  REWRITE_TAC[int_of_num_th; GSYM REAL_OF_NUM_POW] THEN
  CONV_TAC REAL_FIELD);;

let EQUAL_FROM_CONGRUENT_MOD_MOD = prove
 (`!n m r k r'.
        r < 2 EXP k /\ m < 2 EXP k /\ ~(m = 0) /\
        integer((&r - r') / &2 pow k) /\
        &(n MOD m) = r'
        ==> n MOD m = r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  MP_TAC(SPECL [`(&r - r') / &2 pow k`; `&0`] REAL_EQ_INTEGERS_IMP) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL [ALL_TAC; CONV_TAC REAL_FIELD] THEN
  SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_POW;
           REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x < e /\ &0 <= y /\ y < e ==> abs(x - y) < &1 * e`) THEN
  EXPAND_TAC "r'" THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LT_TRANS; MOD_LT_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Definition of limbs = general (power of 2 size) digits.                   *)
(* ------------------------------------------------------------------------- *)

let limb = new_definition
 `limb w n i = (n DIV (2 EXP (w * i)) MOD (2 EXP w))`;;

let LIMB_0 = prove
 (`!w i. limb w 0 i = 0`,
  REWRITE_TAC[limb; DIV_0; MOD_0]);;

let LIMB_BOUND = prove
 (`!w n i. limb w n i < 2 EXP w`,
  REWRITE_TAC[limb; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let DIGITSUM_WORDS_LIMB_GEN = prove
 (`!w n k. nsum {i | i < k} (\i. 2 EXP (w * i) * limb w n i) =
           n MOD (2 EXP (w * k))`,
  REWRITE_TAC[limb; EXP_MULT; DIGITSUM_WORKS_GEN]);;

let DIGITSUM_WORKS_LIMB = prove
 (`!w n k. n < 2 EXP (w * k)
           ==> nsum {i | i < k} (\i. 2 EXP (w * i) * limb w n i) = n`,
  REWRITE_TAC[limb; EXP_MULT; DIGITSUM_WORKS]);;

let LIMB_DIGITSUM = prove
 (`!w n k d.
        (!i. i < k ==> d i < 2 EXP w)
        ==> limb w (nsum {i | i < k} (\i. 2 EXP (w * i) * d i)) n =
            if n < k then d n else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[limb; EXP_MULT] THEN
  ASM_SIMP_TAC[DIGITSUM_DIV_MOD; IN_ELIM_THM; FINITE_NUMSEG_LT]);;

(* ------------------------------------------------------------------------- *)
(* More digit sum lemmas, not needed for Asm/words.ml itself so here.        *)
(* ------------------------------------------------------------------------- *)

let DIGITSUM_LT_STEP = prove
 (`!B b k n.
     0 < B /\ (!i. i < k ==> b i < B)
     ==> (nsum {i | i < k} (\i. B EXP i * b i) < B EXP n <=>
          k <= n \/
          b n = 0 /\ nsum {i | i < k} (\i. B EXP i * b i) < B EXP (n + 1))`,
  REPEAT GEN_TAC THEN SIMP_TAC[LE_1; GSYM DIV_EQ_0; EXP_LT_0] THEN
  SIMP_TAC[DIGITSUM_DIV; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{i | P i /\ Q i} = {i | i IN {j | P j} /\ Q i}`] THEN
  SIMP_TAC[NSUM_EQ_0_IFF; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[ARITH_RULE `0 < b <=> ~(b = 0)`; EXP_EQ_0; MULT_EQ_0] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(ARITH_RULE `!i. n <= i <=> i = n \/ n + 1 <= i`) THEN
  MESON_TAC[LT_REFL; NOT_LE; LE_TRANS; LT_TRANS; LET_TRANS]);;

let VAL_BOUND_64 = prove
 (`!x:int64. val x < 2 EXP 64`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64]);;

let LEXICOGRAPHIC_LT = prove
 (`!B h l h' l':num.
        l < B /\ l' < B
        ==> (B * h + l < B * h' + l' <=> h < h' \/ h = h' /\ l < l')`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `h:num = h'` THEN
  ASM_REWRITE_TAC[LT_ADD_LCANCEL; LT_REFL] THEN MATCH_MP_TAC(ARITH_RULE
   `~(x = y) /\
   (x < y ==> a + e * x < b + e * y) /\ (y < x ==> b + e * y < a + e * x)
    ==> (e * x + a:num < e * y + b <=> x < y)`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN  MATCH_MP_TAC(ARITH_RULE
   `a < e /\ b < e /\ (x < y ==> e * (x + 1) <= e * y)
    ==> x < y ==> a + e * x < b + e * y`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ARITH_TAC);;

let LEXICOGRAPHIC_LE = prove
 (`!B h l h' l':num.
        l < B /\ l' < B
        ==> (B * h + l <= B * h' + l' <=> h < h' \/ h = h' /\ l <= l')`,
  SIMP_TAC[GSYM NOT_LT; LEXICOGRAPHIC_LT] THEN ARITH_TAC);;

let LEXICOGRAPHIC_EQ = prove
 (`!B h l h' l':num.
        l < B /\ l' < B
        ==> (B * h + l = B * h' + l' <=> h = h' /\ l = l')`,
  SIMP_TAC[GSYM LE_ANTISYM; LEXICOGRAPHIC_LE] THEN ARITH_TAC);;

let LEXICOGRAPHIC_LT_64 = prove
 (`!h l h' l'.
        l < 2 EXP 64 /\ l' < 2 EXP 64
        ==> (2 EXP 64 * h + l < 2 EXP 64 * h' + l' <=>
             h < h' \/ h = h' /\ l < l')`,
  REWRITE_TAC[LEXICOGRAPHIC_LT]);;

let LEXICOGRAPHIC_LE_64 = prove
 (`!h l h' l'.
        l < 2 EXP 64 /\ l' < 2 EXP 64
        ==> (2 EXP 64 * h + l <= 2 EXP 64 * h' + l' <=>
             h < h' \/ h = h' /\ l <= l')`,
  REWRITE_TAC[LEXICOGRAPHIC_LE]);;

let LEXICOGRAPHIC_EQ_64 = prove
 (`!h l h' l'.
        l < 2 EXP 64 /\ l' < 2 EXP 64
        ==> (2 EXP 64 * h + l = 2 EXP 64 * h' + l' <=> h = h' /\ l = l')`,
  REWRITE_TAC[LEXICOGRAPHIC_EQ]);;

let LEXICOGRAPHIC_LT_INT64 = prove
 (`!h (l:int64) h' (l':int64).
        2 EXP 64 * h + val l < 2 EXP 64 * h' + val l' <=>
        h < h' \/ h = h' /\ val l < val l'`,
  SIMP_TAC[LEXICOGRAPHIC_LT_64; VAL_BOUND_64]);;

let LEXICOGRAPHIC_LE_INT64 = prove
 (`!h (l:int64) h' (l':int64).
        2 EXP 64 * h + val l <= 2 EXP 64 * h' + val l' <=>
        h < h' \/ h = h' /\ val l <= val l'`,
  SIMP_TAC[LEXICOGRAPHIC_LE_64; VAL_BOUND_64]);;

let LEXICOGRAPHIC_EQ_INT64 = prove
 (`!h (l:int64) h' (l':int64).
        2 EXP 64 * h + val l = 2 EXP 64 * h' + val l' <=> h = h' /\ l = l'`,
  SIMP_TAC[GSYM VAL_EQ; LEXICOGRAPHIC_EQ_64; VAL_BOUND_64]);;

(* ------------------------------------------------------------------------- *)
(* More word lemmas needing a few other theories so not in library.          *)
(* ------------------------------------------------------------------------- *)

let WORD_CTZ_INDEX = prove
 (`!x:N word.
        word_ctz x = if x = word 0 then dimindex(:N) else index 2 (val x)`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_CTZ_0] THEN
  MATCH_MP_TAC(MESON[LE_ANTISYM] `(!k:num. k <= m <=> k <= n) ==> m = n`) THEN
  REWRITE_TAC[LE_INDEX; WORD_LE_CTZ_VAL] THEN
  X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[ARITH_EQ; VAL_EQ_0] THEN
  REWRITE_TAC[TAUT `(p /\ q <=> q) <=> q ==> p`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[VAL_EQ_0] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[VAL_BOUND; LET_TRANS]
   `a <= val(x:N word) ==> a < 2 EXP dimindex(:N)`)) THEN
  SIMP_TAC[LT_EXP; ARITH_EQ; LT_IMP_LE]);;

let WORD_CLZ_BITSIZE = prove
 (`!x:N word. word_clz x = dimindex(:N) - bitsize(val x)`,
  REWRITE_TAC[WORD_CLZ; bitsize]);;

(* ------------------------------------------------------------------------- *)
(* More ad hoc lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

let WORD_INDEX_WRAP = prove
 (`!i. word(8 * (i + 1) + 18446744073709551608):int64 = word(8 * i)`,
  GEN_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0]);;

let MOD_UNIQ_BALANCED = prove
 (`!n p z q.
        q * p <= n + p /\ n < q * p + p /\
        q * p + z = bitval(n < q * p) * p + n
        ==> n MOD p = z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitval] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THENL
   [EXISTS_TAC `q - 1`; EXISTS_TAC `q:num` THEN ASM_ARITH_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `n + p = (q + 1) * p + z ==> n = q * p + z`) THEN
  ASM_CASES_TAC `q = 0` THENL [ASM_MESON_TAC[LT; MULT_CLAUSES]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1] THEN ASM_ARITH_TAC);;

let MOD_UNIQ_BALANCED_REAL = prove
 (`!n p z q k.
        p < 2 EXP k /\ z < 2 EXP k /\
        q * p <= n + p /\ n < q * p + p /\
        integer((&n - &z - (&q - &(bitval(n < q * p))) * &p) / &2 pow k)
        ==> n MOD p = z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ_BALANCED THEN
  EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(REAL_FIELD `!k. (y - x) / &2 pow k = &0 ==> x = y`) THEN
  EXISTS_TAC `k:num` THEN MATCH_MP_TAC REAL_EQ_INTEGERS_IMP THEN
  REWRITE_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `integer x ==> x = y ==> integer y`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_SUB_RZERO; REAL_ABS_DIV; REAL_ABS_POW] THEN
    SIMP_TAC[REAL_ABS_NUM; REAL_LT_LDIV_EQ; REAL_LT_POW2]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LT])) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let VAL_WORD_SUBWORD_JOIN_64 = prove
 (`!(h:int64) (l:int64) k.
    k <= 64
    ==> val(word_subword (word_join h l:int128) (k,64) :int64) =
        2 EXP (64 - k) * val h MOD 2 EXP k + val l DIV (2 EXP k)`,
  REWRITE_TAC[GSYM DIMINDEX_64; VAL_WORD_SUBWORD_JOIN_FULL]);;

(* ------------------------------------------------------------------------- *)
(* Alternative formulations for carry conditions as expressed abstractly.    *)
(* ------------------------------------------------------------------------- *)

let NOCARRY_WORD_ADC = prove
 (`!b x y:N word.
        val x + val y + bitval b =
        val(word_add (word_add x y) (word (bitval b))) <=>
        val x + val y + bitval b < 2 EXP dimindex(:N)`,
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_BITVAL] THEN
  REPEAT GEN_TAC THEN CONV_TAC MOD_DOWN_CONV THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  REWRITE_TAC[GSYM ADD_ASSOC; MOD_EQ_SELF] THEN
  REWRITE_TAC[ARITH_EQ; EXP_EQ_0]);;

let CARRY_WORD_ADC = prove
 (`!b x y:N word.
        ~(val x + val y + bitval b =
          val(word_add (word_add x y) (word (bitval b)))) <=>
        2 EXP dimindex(:N) <= val x + val y + bitval b`,
  REWRITE_TAC[NOCARRY_WORD_ADC; NOT_LT]);;

let NOCARRY_WORD_ADD = prove
 (`!x y:N word.
        val x + val y = val(word_add x y) <=>
        val x + val y < 2 EXP dimindex(:N)`,
  MP_TAC(SPEC `F` NOCARRY_WORD_ADC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[WORD_RULE `word_add x (word 0) = x`]);;

let CARRY_WORD_ADD = prove
 (`!x y:N word.
        ~(val x + val y = val(word_add x y)) <=>
        2 EXP dimindex(:N) <= val x + val y`,
  REWRITE_TAC[NOCARRY_WORD_ADD; NOT_LT]);;

let NOCARRY_WORD_SBB = prove
 (`!b x y:N word.
        &(val x) - (&(val y) + &(bitval b)):int =
        &(val(word_sub x (word_add y (word(bitval b))))) <=>
        if b then val y < val x else val y <= val x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_ARITH);;

let CARRY_WORD_SBB = prove
 (`!b x y:N word.
        ~(&(val x) - (&(val y) + &(bitval b)):int =
          &(val(word_sub x (word_add y (word(bitval b)))))) <=>
        if b then val x <= val y else val x < val y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_ARITH);;

let NOCARRY_WORD_SUB = prove
 (`!x y:N word.
        &(val x) - &(val y):int = &(val(word_sub x y)) <=>
        val y <= val x`,
  MP_TAC(SPEC `F` NOCARRY_WORD_SBB) THEN
  REWRITE_TAC[BITVAL_CLAUSES; INT_ADD_RID] THEN
  REWRITE_TAC[WORD_RULE `word_add x (word 0) = x`]);;

let CARRY_WORD_SUB = prove
 (`!x y:N word.
        ~(&(val x) - &(val y):int = &(val(word_sub x y))) <=>
        val x < val y`,
  REWRITE_TAC[NOCARRY_WORD_SUB; NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* More concrete versions for 64-bit words etc.                              *)
(* ------------------------------------------------------------------------- *)

let NOCARRY_THM = prove
 (`!x:int64. 2 EXP 64 <= val x <=> F`,
  GEN_TAC THEN REWRITE_TAC[NOT_LE] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC);;

let NOCARRY64_ADC = prove
 (`!b x y:int64.
        (val x + val y + bitval b =
         val(word_add (word_add x y) (word (bitval b)))) <=>
        val x + val y + bitval b < 2 EXP 64`,
  REWRITE_TAC[NOCARRY_WORD_ADC; DIMINDEX_64]);;

let CARRY64_ADC = prove
 (`!b x y:int64.
        ~(val x + val y + bitval b =
          val(word_add (word_add x y) (word (bitval b)))) <=>
        2 EXP 64 <= val x + val y + bitval b`,
  REWRITE_TAC[CARRY_WORD_ADC; DIMINDEX_64]);;

let NOCARRY64_ADD = prove
 (`!x y:int64.
        (val x + val y = val(word_add x y)) <=>
        val x + val y < 2 EXP 64`,
  REWRITE_TAC[NOCARRY_WORD_ADD; DIMINDEX_64]);;

let CARRY64_ADD = prove
 (`!x y:int64.
        ~(val x + val y = val(word_add x y)) <=>
        2 EXP 64 <= val x + val y`,
  REWRITE_TAC[CARRY_WORD_ADD; DIMINDEX_64]);;

let NOCARRY64_ADD_1 = prove
 (`!x:int64.
        (val x + 1 = val(word_add x (word 1))) <=>
        val x + 1 < 2 EXP 64`,
  METIS_TAC[NOCARRY64_ADD; VAL_WORD_1]);;

let CARRY64_ADD_1 = prove
 (`!x:int64.
        ~(val x + 1 = val(word_add x (word 1))) <=>
        2 EXP 64 <= val x + 1`,
  METIS_TAC[CARRY64_ADD; VAL_WORD_1]);;

let NOCARRY64_SBB = prove
 (`!b x y:int64.
        (&(val x) - (&(val y) + &(bitval b)):int =
         &(val(word_sub x (word_add y (word (bitval b)))))) <=>
        val y + bitval b <= val x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NOCARRY_WORD_SBB] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let CARRY64_SBB = prove
 (`!b x y:int64.
        ~(&(val x) - (&(val y) + &(bitval b)):int =
          &(val(word_sub x (word_add y (word (bitval b)))))) <=>
        val x < val y + bitval b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CARRY_WORD_SBB] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let NOCARRY64_SUB = prove
 (`!x y:int64.
        (&(val x) - &(val y):int = &(val(word_sub x y))) <=>
        val y <= val x`,
  REWRITE_TAC[NOCARRY_WORD_SUB]);;

let CARRY64_SUB = prove
 (`!x y:int64.
        ~(&(val x) - &(val y):int = &(val(word_sub x y))) <=>
        val x < val y`,
  REWRITE_TAC[CARRY_WORD_SUB]);;

let ACCUMULATE_ADC = prove
 (`!b x y:int64.
        val(x) + val(y) + val(word(bitval b):int64) =
        2 EXP 64 * bitval(2 EXP 64 <= val x + val y + bitval b) +
        val(word_add (word_add x y) (word (bitval b)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN
  SIMP_TAC[VAL_WORD_ADC_CASES; VAL_WORD_BITVAL; BITVAL_BOUND_ALT] THEN
  REWRITE_TAC[DIMINDEX_64] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_ARITH_TAC);;

let ACCUMULATE_ADC_0 = prove
 (`!b x:int64.
        val(x) + val(word(bitval b):int64) =
        2 EXP 64 * bitval(2 EXP 64 <= val x + bitval b) +
        val(word_add x (word (bitval b)))`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`b:bool`; `x:int64`; `word 0:int64`]
        ACCUMULATE_ADC) THEN
  REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; ADD_CLAUSES]);;

let ACCUMULATE_ADD = prove
 (`!x y:int64.
        val(x) + val(y) =
        2 EXP 64 * bitval(2 EXP 64 <= val x + val y) +
        val(word_add x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN
  SIMP_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; BITVAL_BOUND_ALT] THEN
  REWRITE_TAC[DIMINDEX_64] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_ARITH_TAC);;

let ACCUMULATE_SBB = prove
 (`!b x y:int64.
        2 EXP 64 * bitval(val x < val y + bitval b) + val x =
        val(word_sub x (word_add y (word (bitval b)))) + val y + bitval b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN POP_ASSUM(K ALL_TAC) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_ADD_CASES;
              VAL_WORD_0; VAL_WORD_1] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN
  MP_TAC(ISPEC `y:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let ACCUMULATE_SBB_RZERO = prove
 (`!b x:int64.
        2 EXP 64 * bitval(val x < bitval b) + val x =
        val(word_sub x (word (bitval b))) + bitval b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`b:bool`; `x:int64`; `word 0:int64`] ACCUMULATE_SBB) THEN
  REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let ACCUMULATE_SBB_LZERO = prove
 (`!b x:int64.
        2 EXP 64 * bitval(0 < val x + bitval b) =
        val(word_neg(word_add x (word (bitval b)))) + val x + bitval b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`b:bool`; `word 0:int64`; `x:int64`] ACCUMULATE_SBB) THEN
  REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let ACCUMULATE_SUB = prove
 (`!x y:int64.
        2 EXP 64 * bitval(val x < val y) + val x =
        val(word_sub x y) + val y`,
  MP_TAC(SPEC `F` ACCUMULATE_SBB) THEN
  REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; WORD_ADD_0]);;

let ACCUMULATE_MUL_GEN = prove
 (`!(x:N word) (y:N word).
        2 EXP dimindex(:N) *
        val(word_zx (word_ushr
         (word(val x * val y):(N tybit0)word) (dimindex(:N))):N word) +
        val(word_zx (word(val x * val y):(N tybit0)word):N word) =
        val x * val y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR] THEN
  REWRITE_TAC[GSYM MOD_MULT_MOD] THEN
  REWRITE_TAC[VAL_WORD; GSYM EXP_ADD; DIMINDEX_TYBIT0; MULT_2] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[EXP_ADD] THEN MATCH_MP_TAC LT_MULT2 THEN
  REWRITE_TAC[VAL_BOUND]);;

let ACCUMULATE_MUL = prove
 (`!(x:int64) (y:int64).
        2 EXP 64 *
        val(word_zx (word_ushr
         (word(val x * val y):(128)word) (dimindex(:64))):int64) +
        val(word_zx (word(val x * val y):(128)word):int64) =
        val x * val y`,
  REWRITE_TAC[GSYM DIMINDEX_64; ACCUMULATE_MUL_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Variants to express in real-number terms with error bounds.               *)
(* ------------------------------------------------------------------------- *)

let APPROXIMATE_WORD_USHR = prove
 (`!(dest:int64) a n.
        dest = word_ushr a n
        ==> ?b e. dest = b /\
                  &0 <= e /\ e <= &1 - inv(&2 pow n) /\
                  &(val b) = &(val a) / &2 pow n - e`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
  REWRITE_TAC[UNWIND_THM1; REAL_ARITH
   `&0 <= e /\ e <= u /\ x:real = y - e <=>
    y - x = e /\ x <= y /\ y <= x + u`] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
  REWRITE_TAC[REAL_FIELD
   `(x + &1 - inv(&2 pow n)) * (&2 pow n) = (x + &1) * &2 pow n - &1`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= y - x * e /\ (y - x * e) + &1 <= e
    ==> x * e <= y /\ y <= (x + &1) * e - &1`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MOD; REAL_OF_NUM_POW] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
  REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let APPROXIMATE_WORD_SHL = prove
 (`!(dest:int64) a n.
        dest = word_shl a n
        ==> &2 pow n * &(val a):real < &2 pow 64
            ==> ?c. dest = c /\
                    &(val c):real = &2 pow n * &(val a)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[VAL_WORD_SHL; REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let APPROXIMATE_WORD_ADD = prove
 (`!(dest:int64) a b.
        dest = word_add a b
        ==> &(val a) + &(val b):real < &2 pow 64
            ==> ?c. dest = c /\
                    &(val c):real = &(val a) + &(val b)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[VAL_WORD_ADD; REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let APPROXIMATE_WORD_SUB = prove
 (`!(dest:int64) a b.
        dest = word_sub a b
        ==> &0 <= &(val a) - &(val b)
            ==> ?c. dest = c /\
                    &(val c) = &(val a) - &(val b)`,
  REWRITE_TAC[REAL_SUB_LE; REAL_EQ_SUB_LADD; REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN ASM_ARITH_TAC);;

let APPROXIMATE_WORD_MUL = prove
 (`!(dest:int64) (a:int64) (b:int64).
        dest = word(0 + val a * val b)
        ==> &(val a) * &(val b):real < &2 pow 64
            ==> ?c. dest = c /\
                    &(val c):real = &(val a) * &(val b)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; UNWIND_THM1] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]);;

let APPROXIMATE_WORD_MADD = prove
 (`!(dest:int64) (a:int64) (b:int64) (c:int64).
        dest = word(val a + val b * val c)
        ==> &(val a) + &(val b) * &(val c):real < &2 pow 64
            ==> ?d. dest = d /\
                    &(val d):real = &(val a) + &(val b) * &(val c)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]);;

let APPROXIMATE_WORD_MNEG = prove
 (`!(dest:int64) (a:int64) (b:int64).
        dest = iword(&0 - ival a * ival b)
        ==> &0 < &(val a) * &(val b):real /\
            &(val a) * &(val b):real <= &2 pow 64
            ==> ?c. dest = c /\
                    &(val c):real = &2 pow 64 - &(val a) * &(val b)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[INT_SUB_LZERO; REAL_EQ_SUB_LADD] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_EQ_SUB_LADD] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN
  EXISTS_TAC `(&2:int) pow 64` THEN CONJ_TAC THENL
   [W(MP_TAC o C SPEC VAL_BOUND_64 o
      rand o rand o lhand o rand o lhand o snd) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_RULE
     `(x:int == n - y) (mod n) <=> (x == --y) (mod n)`] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ; DIMINDEX_64]
                (INST_TYPE [`:64`,`:N`] VAL_IWORD_CONG); GSYM INT_REM_EQ] THEN
    REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC(INTEGER_RULE
     `(a:int == a') (mod n) /\ (b == b') (mod n)
      ==> (--(a * b) == --(a' * b')) (mod n)`) THEN
    REWRITE_TAC[REWRITE_RULE[DIMINDEX_64]
     (INST_TYPE [`:64`,`:N`]IVAL_VAL_CONG)]]);;

let APPROXIMATE_WORD_IWORD = prove
 (`!(dest:int64) x x'.
        dest = iword x
        ==> &0 <= x' /\ x' < &2 pow 64 /\ (x == x') (mod (&2 pow 64))
            ==> ?c. dest = c /\
                    &(val c) = real_of_int x'`,
  REWRITE_TAC[UNWIND_THM1; GSYM INT_REM_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM int_of_num_th; GSYM int_eq] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 64` THEN
  REWRITE_TAC[GSYM INT_REM_EQ; GSYM DIMINDEX_64] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] VAL_IWORD_CONG] THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN MATCH_MP_TAC(INT_ARITH
   `&0 <= x /\ x < e /\ &0 <= y /\ y < e ==> abs(x - y:int) < e`) THEN
  ASM_REWRITE_TAC[INT_POS] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; VAL_BOUND_64]);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas to get a flag out of a carry setting                          *)
(* ------------------------------------------------------------------------- *)

let FLAG_FROM_CARRY_REAL_LT = prove
 (`!k x (y:real) p.
        &0 <= &2 pow k * &(bitval p) + x - y /\
        &2 pow k * &(bitval p) + x - y < &2 pow k
        ==> (p <=> x < y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN REAL_ARITH_TAC);;

let FLAG_FROM_CARRY_REAL_LE = prove
 (`!k x (y:real) p.
        &0 <= &2 pow k * (&1 - &(bitval p)) + y - x /\
        &2 pow k * (&1 - &(bitval p)) + y - x < &2 pow k
        ==> (p <=> x <= y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN REAL_ARITH_TAC);;

let FLAG_FROM_CARRY_LT = prove
 (`!k m n p.
        &0:real <= &2 pow k * &(bitval p) + &m - &n /\
        &2 pow k * &(bitval p) + &m - &n:real < &2 pow k
        ==> (p <=> m < n)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; FLAG_FROM_CARRY_REAL_LT]);;

let FLAG_FROM_CARRY_LE = prove
 (`!k m n p.
        &0:real <= &2 pow k * (&1 - &(bitval p)) + &n - &m /\
        &2 pow k * (&1 - &(bitval p)) + &n - &m:real < &2 pow k
        ==> (p <=> m <= n)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; FLAG_FROM_CARRY_REAL_LE]);;

(* ------------------------------------------------------------------------- *)
(* Getting a word in {0,1} in a similar way.                                 *)
(* ------------------------------------------------------------------------- *)

let WORD_FROM_CARRY_REAL_LT = prove
 (`!k x (y:real) (w:N word).
        y - x <= &2 pow k /\
        &0 <= &2 pow k * &(val w) + x - y /\
        &2 pow k * &(val w) + x - y < &2 pow k
        ==> w = word(bitval(x < y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(w:N word)` NUM_AS_BITVAL_ALT))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC `(&2 pow k):real` THEN REWRITE_TAC[REAL_LT_POW2] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VAL_EQ_BITVAL] THEN DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP FLAG_FROM_CARRY_REAL_LT) THEN
    REWRITE_TAC[]]);;

let WORD_FROM_CARRY_REAL_LE = prove
 (`!k x (y:real) (w:N word).
        y - x < &2 pow k /\
        &0 <= &2 pow k * (&1 - &(val w)) + y - x /\
        &2 pow k * (&1 - &(val w)) + y - x < &2 pow k
        ==> w = word(bitval(x <= y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(w:N word)` NUM_AS_BITVAL_ALT))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC `(&2 pow k):real` THEN REWRITE_TAC[REAL_LT_POW2] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VAL_EQ_BITVAL] THEN DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP FLAG_FROM_CARRY_REAL_LE) THEN
    REWRITE_TAC[]]);;

let WORD_FROM_CARRY_LT = prove
 (`!k x y (w:N word).
        y - x:real <= &2 pow k /\
        &0:real <= &2 pow k * &(val w) + x - y /\
        &2 pow k * &(val w) + x - y:real < &2 pow k
        ==> w = word(bitval(x < y))`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; WORD_FROM_CARRY_REAL_LT]);;

let WORD_FROM_CARRY_LE = prove
 (`!k x  (w:N word).
        &y - &x < &2 pow k /\
        &0 <= &2 pow k * (&1 - &(val w)) + &y - &x /\
        &2 pow k * (&1 - &(val w)) + &y - &x < &2 pow k
        ==> w = word(bitval(x <= y))`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; WORD_FROM_CARRY_REAL_LE]);;

(* ------------------------------------------------------------------------- *)
(* An elaborated version for getting a flag and a mask word.                 *)
(* ------------------------------------------------------------------------- *)

let FLAG_AND_MASK_FROM_CARRY_REAL_LT = prove
 (`!c (m:int64) k (x:real).
        --(&2 pow k) <= x /\ x < &2 pow k /\
        &0 <= x - &2 pow k * (&(val m) - &2 pow 64 * &(bitval c)) /\
        x - &2 pow k * (&(val m) - &2 pow 64 * &(bitval c)) < &2 pow k
        ==> m = word_neg(word(bitval(x < &0))) /\
            (c <=> x < &0)`,
  REPEAT GEN_TAC THEN  ASM_CASES_TAC `c:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_MUL_RZERO; REAL_MUL_RID;
                  REAL_SUB_RZERO; REAL_NOT_LT] THEN
  STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `x - p * (m - c):real < p ==> p * &1 <= p * (c - m) ==> x < &0`)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[REAL_ARITH `&1:real <= x - y <=> y + &1 <= x`] THEN
    SIMP_TAC[GSYM REAL_LT_INTEGERS; INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM DIMINDEX_64; VAL_BOUND] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM VAL_EQ_MAX_MASK; DIMINDEX_64] THEN
    MATCH_MP_TAC(ARITH_RULE `m < e /\ e < m + 2 ==> m = e - 1`) THEN
    REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `(&2:real) pow k` THEN
    REWRITE_TAC[REAL_LT_POW2] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `&0:real <= x - p ==> &0 <= p ==> &0 <= x`)) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; REAL_POS];
      SIMP_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC] THEN
    REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0] THEN
    REWRITE_TAC[GSYM VAL_EQ_0; ARITH_RULE `n = 0 <=> ~(1 <= n)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `&0 <= x - p * m ==> x < p ==> ~(p * &1 <= p * m)`)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_POW2]]);;

let FLAG_AND_MASK_FROM_CARRY_LT = prove
 (`!c (m:int64) k x y.
        --(&2 pow k):real <= &x - &y /\ &x - &y:real < &2 pow k /\
        &0:real <= &x - &y - &2 pow k * (&(val m) - &2 pow 64 * &(bitval c)) /\
        &x - &y - &2 pow k * (&(val m) - &2 pow 64 * &(bitval c)):real
        < &2 pow k
        ==> m = word_neg(word(bitval(x < y))) /\
            (c <=> x < y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x:real < y <=> x - y < &0`] THEN
  MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_REAL_LT THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Yet more general formulations of similar patterns.                        *)
(* ------------------------------------------------------------------------- *)

let MASK_AND_VALUE_FROM_CARRY_REAL_LT = prove
 (`!(m:int64) l k (x:real).
        (--(&2 pow k) <= x /\ x < &2 pow k) /\
        (&0 <= l /\ l < &2 pow k) /\
        integer(((&2 pow k * &(val m) + l) - x) / &2 pow (k + 64))
        ==> m = word_neg(word(bitval(x < &0))) /\
            l = if x < &0 then x + &2 pow k else x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (MESON[REAL_DIV_RMUL]
     `integer(x / y) ==> ~(y = &0) ==> ?n. integer n /\ x = n * y`)) THEN
  SIMP_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:real` THEN REWRITE_TAC[REAL_POW_ADD; REAL_ARITH
   `(k * m + l) - x:real = n * k * e <=> l - x = k * (n * e - m)`] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
   [REWRITE_TAC[REAL_ARITH `l:real = x + k <=> l - x - k = &0`] THEN
    SUBGOAL_THEN `abs(l - x - &2 pow k) < &2 pow k * &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC];
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    SUBGOAL_THEN `abs(l - x) < &2 pow k * &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM;
                  REAL_ARITH `k * x - k:real = k * (x - &1)`] THEN
  SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_POW2] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [GSYM REAL_EQ_INTEGERS; INTEGER_CLOSED] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_ARITH `x - y:real = &1 <=> x - &1 = y`] THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64; REAL_CONGRUENCE] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

let MASK_AND_VALUE_FROM_CARRY_LT = prove
 (`!(m:int64) l k x y.
        (--(&2 pow k):real <= &x - &y /\ &x - &y:real < &2 pow k) /\
        (&0 <= l /\ l < &2 pow k) /\
        integer(((&2 pow k * &(val m) + l) - (&x - &y)) / &2 pow (k + 64))
        ==> m = word_neg(word(bitval(x < y))) /\
            l = if x < y then (&x - &y) + &2 pow k else &x - &y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x:real < y <=> x - y < &0`] THEN
  MATCH_MP_TAC MASK_AND_VALUE_FROM_CARRY_REAL_LT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Useful for showing that a call is accessible.                             *)
(* ------------------------------------------------------------------------- *)

let WORD32_ADD_SUB_OF_LT = prove
 (`!pc tgt. pc <= 2 EXP 31 /\ tgt < 2 EXP 31 ==>
  word_add (word pc) (word_sx (iword (&tgt - &pc):int32)):int64 = word tgt`,
  IMP_REWRITE_TAC [word_sx; IVAL_IWORD; WORD_IWORD; GSYM IWORD_INT_ADD;
    INT_SUB_ADD2; DIMINDEX_32] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Transformation for a slightly different way multiplication can be done.   *)
(* ------------------------------------------------------------------------- *)

let WORD_MULTIPLICATION_LOHI = prove
 (`!(x:N word) (y:N word).
        word_mul x y = word_zx(word(val x * val y):(N tybit0)word) /\
        word((val x * val y) DIV 2 EXP dimindex(:N)):N word =
        word_zx (word_ushr (word(val x * val y):(N tybit0)word)
                (dimindex(:N)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
              VAL_WORD_USHR; VAL_WORD; DIMINDEX_TYBIT0] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `MIN (2 * n) n = n`; DIV_MOD;
              GSYM EXP_ADD; GSYM MULT_2; ARITH_RULE `MIN n n = n`]);;

(* ------------------------------------------------------------------------- *)
(* Prove non-triviality |- ?y x1 ... xn. t[x1,...,xn] = y                    *)
(* Used for non-vacuity of transitions even with undefined variables.        *)
(* ------------------------------------------------------------------------- *)

let EXISTS_NONTRIVIAL_CONV =
  let pth = prove (`!s. (?s'. s = s') <=> T`,MESON_TAC[]) in
  let elim_conv = GEN_REWRITE_CONV I [pth]
  and swap_conv = GEN_REWRITE_CONV I [SWAP_EXISTS_THM]
  and deex_conv = GEN_REWRITE_CONV I [EXISTS_SIMP] in
  let rec conv tm =
   ((swap_conv THENC BINDER_CONV conv THENC deex_conv) ORELSEC elim_conv) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Simple fix for "wraparound" of symbolics like "word(pc + n)"              *)
(* by reducing n modulo 2^64. This is used for the IP, while the             *)
(* BSID thing works more elaborately.                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_PC_PLUS_CONV =
  let pth = prove
    (`word(pc + NUMERAL n):int64 =
      word(pc + NUMERAL n MOD 18446744073709551616)`,
     REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
     CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN
     REWRITE_TAC[]) in
  let conv =
    GEN_REWRITE_CONV I [pth] THENC
    RAND_CONV
     (RAND_CONV NUM_MOD_CONV THENC
      GEN_REWRITE_CONV TRY_CONV [ARITH_RULE `n + 0 = n`]) in
  CHANGED_CONV conv;;

(* ------------------------------------------------------------------------- *)
(* Better normalize "bsid" address relative to a given offset register.      *)
(* The additive case works even for variable-containing offsets "a"/"b".     *)
(* The subtractive form only does something for constant offset pairs.       *)
(* ------------------------------------------------------------------------- *)

let NORMALIZE_ADD_SUBTRACT_WORD_CONV =
  let pth = prove
   (`word_add (word_add z (word a)) (word b) =
     word_add z (word_add (word a) (word b))`,
    CONV_TAC WORD_RULE)
  and qth = prove
   (`word_sub (word_add z (word a)) (word b) =
     word_add z (word_sub (word a) (word b))`,
    CONV_TAC WORD_RULE)
  and rth = prove
   (`word_add z (word 0) = z`,
    CONV_TAC WORD_RULE) in
  ((GEN_REWRITE_CONV I [pth] THENC RAND_CONV WORD_ADD_CONV) ORELSEC
   (GEN_REWRITE_CONV I [qth] THENC RAND_CONV WORD_SUB_CONV)) THENC
  GEN_REWRITE_CONV TRY_CONV [rth];;

let NORMALIZE_RELATIVE_ADDRESS_CONV =
  let pth = prove
   (`word_add (word_add z (word a)) (word b) = word_add z (word(a + b))`,
    CONV_TAC WORD_RULE) in
  NORMALIZE_ADD_SUBTRACT_WORD_CONV ORELSEC
  (GEN_REWRITE_CONV I [pth] THENC
   RAND_CONV(RAND_CONV(TRY_CONV NUM_ADD_CONV)) THENC
   GEN_REWRITE_CONV (RAND_CONV o RAND_CONV o TRY_CONV) [ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Reduce goal ?- !x. P[x] to ?- !x. P[word_add x (word n)]                  *)
(* ------------------------------------------------------------------------- *)

let (WORD_FORALL_OFFSET_TAC:int->tactic) =
  let lemma = prove
   (`!(P:N word->bool) a. (!x. P(word_add x (word a))) ==> (!x. P x)`,
    MESON_TAC[WORD_RULE `word_add (word_sub x a) (a:N word) = x`]) in
  fun n -> MATCH_MP_TAC lemma THEN EXISTS_TAC (mk_small_numeral n) THEN
           CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ADD_SUBTRACT_WORD_CONV);;

(* ------------------------------------------------------------------------- *)
(* Do some limited simplification in association with symbolic execution.    *)
(* ------------------------------------------------------------------------- *)

let ASSEMBLER_SIMPLIFY_TAC =
  let pth = prove
   (`!a b. a < a + bitval b <=> b`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `b:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC) in
  ASM_REWRITE_TAC[WORD_XOR_REFL; WORD_ADD_0; WORD_AND_REFL; WORD_OR_REFL;
                  WORD_ZX_BITVAL; WORD_SUB_REFL; WORD_OR_0; WORD_ZX_0; NOT_LT;
                  WORD_SX_0; SUB_EQ_0; SUB_REFL; LE_REFL; LT_REFL; NOT_LE] THEN
  CONV_TAC(LAND_CONV
   (GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [CARRY64_ADC; CARRY64_ADD; CARRY64_ADD_1;
      CARRY64_SBB; CARRY64_SUB] THENC
    DEPTH_CONV
     (GEN_REWRITE_CONV I [BITVAL_CLAUSES] ORELSEC
      WORD_RED_CONV ORELSEC
      NORMALIZE_ADD_SUBTRACT_WORD_CONV ORELSEC
      NUM_RED_CONV ORELSEC
      INT_RED_CONV) THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [WORD_RULE `word_sub x (word_add x y):int64 = word_neg y`;
      pth] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [SYM(NUM_REDUCE_CONV `2 EXP 64`)]));;

(* ------------------------------------------------------------------------- *)
(* Not much commonality to all the ISAs but we do have a uniform             *)
(* notion of code length, with consistent use of length-instruction pairs    *)
(* ------------------------------------------------------------------------- *)

let codelength = new_definition
 `codelength (code:byte list) = LENGTH code`;;

let CODELENGTH_CONV ths =
  GEN_REWRITE_CONV TRY_CONV [codelength] THENC
  GEN_REWRITE_CONV RAND_CONV ths THENC
  GEN_REWRITE_CONV I [LENGTH] THENC
  GEN_REWRITE_CONV (RAND_CONV o TOP_SWEEP_CONV) [LENGTH] THENC
  DEPTH_CONV NUM_SUC_CONV;;

(* ------------------------------------------------------------------------- *)
(* Get a list of intermediate states via numeric schema.                     *)
(* ------------------------------------------------------------------------- *)

let statenames s l = map (fun n -> s^string_of_int n) l;;

(* ------------------------------------------------------------------------- *)
(* Switch quantifier over 64-bit words to over numbers.                      *)
(* ------------------------------------------------------------------------- *)

let W64_GEN_TAC =
  let pth = prove
   (`(!x:int64. P (val x) x) <=>
     (!x. x < 2 EXP 64 /\ val(word x:int64) = x
          ==> P x (word x))`,
    GEN_REWRITE_TAC LAND_CONV [FORALL_VAL_GEN] THEN
    MESON_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64]) in
  let tac = GEN_REWRITE_TAC I [pth] in
  fun w -> tac THEN X_GEN_TAC w THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* Handy to pick out matching assumptions.                                   *)
(* ------------------------------------------------------------------------- *)

let FIND_ASM_THEN part pat ttac =
  FIRST_X_ASSUM (ttac o check (fun th -> part(concl th) = pat));;

(* ------------------------------------------------------------------------- *)
(* Re-abbreviating a state component, replacing existing expansion.          *)
(* ------------------------------------------------------------------------- *)

let REABBREV_TAC tm =
  let nv,sc = dest_eq tm in
  let tfn t = is_eq t && lhand t = nv in
    ABBREV_TAC tm THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (tfn o concl)));;

(* ------------------------------------------------------------------------- *)
(* A variant that eliminates existing *variable* for same expression.        *)
(* ------------------------------------------------------------------------- *)

let DEABBREV_TAC tm =
  let nv,sc = dest_eq tm in
  let tfn t = is_eq t && lhand t = nv
  and sfn t = is_eq t && is_var(lhand t) && rand t = nv in
    ABBREV_TAC tm THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (tfn o concl))) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (sfn o concl)));;

(* ------------------------------------------------------------------------- *)
(* A slight help for efficiency of justification in some cases.              *)
(* ------------------------------------------------------------------------- *)

let CLARIFY_TAC =
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;
