(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Additional utilities that could be part of HOL Light libraries.           *)
(* ========================================================================= *)

prioritize_num();;

let rec dest_list = function
| Const("NIL",_) -> []
| Comb(Comb(Const("CONS",_),a),t) -> a :: dest_list t
| _ -> failwith "dest_list";;

let catch f x = try Some(f x) with Failure _ -> None;;

let pinst tyin tmin =
  let iterm_fn = vsubst (map (I F_F (inst tyin)) tmin)
  and itype_fn = inst tyin in
  fun th -> try iterm_fn (itype_fn th)
            with Failure _ -> failwith "pinst";;

let SPEC1_TAC = W (curry SPEC_TAC);;
let SPECL_TAC = EVERY o map SPEC1_TAC o rev;;

let (WITH_GOAL:(term->tactic)->tactic) = fun tac (_,w as st) -> tac w st;;

let CONV_RHS_RULE (conv:conv) th = TRANS th (conv (rhs (concl th)));;

let UNETA_TAC = function
| Comb(_,(Var(_,_) as x)) as t ->
  ONCE_REWRITE_TAC [SYM (ETA_CONV (mk_abs (x, t)))]
| _ -> failwith "UNETA_TAC";;

let MATCH_CONV' =
  let ifif = prove
    (`(if p then if p then a:A else b else c) = if p then a else c`,
     COND_CASES_TAC THEN REWRITE_TAC []) in
  REDEPTH_CONV MATCH_CONV THENC REWRITE_CONV [ifif];;

let NUM_DIVIDES_CONV = REWRITE_CONV [DIVIDES_MOD] THENC NUM_REDUCE_CONV;;

let FORALL_FUN_PAIR_THM = prove
 (`!P. (!f:A#B->C. P f) <=> (!g. P(\a. g (FST a) (SND a)))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [GSYM PAIR] THEN
  PURE_ASM_REWRITE_TAC[]);;

let OPTION_DISTINCT = prove_constructors_distinct option_RECURSION;;

let OPTION_INJ = prove_constructors_injective option_RECURSION;;

let is_some = define
  `is_some (NONE:A option) = F /\ !a:A. is_some (SOME a) = T`;;

parse_as_infix(">>=",(14,"right"));;
let obind = define `NONE >>= f = NONE /\ !a:A. SOME a >>= f = f a: B option`;;

let obind_eq_some = prove
 (`!ao f b. (ao >>= f) = SOME (b:B) <=> ?a:A. ao = SOME a /\ f a = SOME b`,
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC [obind; OPTION_DISTINCT; OPTION_INJ] THEN METIS_TAC []);;

let ODD_DOUBLE = prove (`!n. ~ODD (2 * n)`,
  REWRITE_TAC [NOT_ODD; EVEN_DOUBLE]);;

let EXP_2_NE_0 = prove
  (`~(2 EXP n = 0)`, REWRITE_TAC [EXP_EQ_0; ARITH_EQ]);;

let MOD_DIV_EQ_0 = prove
  (`~(n = 0) ==> (m MOD n) DIV n = 0`, DISCH_THEN (fun th ->
    IMP_REWRITE_TAC [th; DIV_EQ_0; MOD_LT_EQ]));;

let BIT0_0 = prove (`BIT0 0 = 0`, REWRITE_TAC [NUMERAL; ARITH_ZERO]);;
let BIT1_0 = prove (`BIT1 0 = 1`, REWRITE_TAC [NUMERAL]);;

let exists_list_split = prove
 (`!l n. n <= LENGTH (l:A list) ==> ?l1 l2. l = APPEND l1 l2 /\ LENGTH l1 = n`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THENL [
    REWRITE_TAC [LE; FORALL_UNWIND_THM2] THEN
    REPEAT (EXISTS_TAC `[]:A list`) THEN REWRITE_TAC [APPEND; LENGTH];
    INDUCT_TAC THENL [DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`[]:A list`; `CONS h t:A list`] THEN
      REWRITE_TAC [APPEND; LENGTH];
      POP_ASSUM (K (POP_ASSUM (fun th1 -> DISCH_THEN (fun th2 ->
        let th = MATCH_MP th1 (REWRITE_RULE [LE_SUC] th2) in
        REPEAT_TCL CHOOSE_THEN (fun th3 ->
          MAP_EVERY EXISTS_TAC [`CONS h l1:A list`; `l2:A list`] THEN
          REWRITE_TAC [th3; APPEND; LENGTH]) th))))]]);;

(* A drop in replacement for prove that uses the interactive tactic creation
   tools so that the goalstack is displayed if the proof is not complete. *)
let start(t,tac) = let _ = g t in e tac;;

(* Like CHOOSE, but the variable is the same as the one in the existential *)
let TRIV_CHOOSE =
  let P = `P:A->bool` and Q = `Q:bool` and an = `(/\)` in
  let pth = (* `(\x:A. Q /\ P x) = P, (?) P |- Q` *)
    let th1 = AP_THM (ASSUME `(\x:A. Q /\ P x) = P`) `x:A` in
    let th1 = TRANS (SYM th1) (BETA `(\x:A. Q /\ P x) x`) in
    let th1 = CONJUNCT1 (EQ_MP th1 (ASSUME `(P:A->bool) x`)) in
    let th1 = GEN `x:A` (DISCH `(P:A->bool) x` th1) in
    let th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_DEF P) in
    MP (SPEC `Q:bool` (EQ_MP th2 (ASSUME `(?) (P:A->bool)`))) th1 in
  fun th1 th2 ->
    try let P' = rand (concl th1) in
        let v,bod = dest_abs P' in
        let Q' = concl th2 in
        let anQ = mk_comb (an, Q') in
        let th3 = DEDUCT_ANTISYM_RULE (CONJ th2 (ASSUME bod))
          (CONJUNCT2 (ASSUME (mk_comb (anQ, bod)))) in
        let th4 = AP_TERM anQ (BETA (mk_comb (P', v))) in
        let th5 = PINST [snd(dest_var v),aty] [P',P; Q',Q] pth in
        PROVE_HYP th1 (PROVE_HYP (ABS v (TRANS th4 th3)) th5)
    with Failure _ -> failwith "TRIV_CHOOSE";;

(* ------------------------------------------------------------------------- *)
(* Conversion from numerals to list bool.                                    *)
(* ------------------------------------------------------------------------- *)

let from_bitlist = define
  `from_bitlist [] = 0 /\
   (!b t. from_bitlist (CONS b t) =
     if b then BIT1 (from_bitlist t) else BIT0 (from_bitlist t))`;;

let FROM_BITLIST_CLAUSES = prove
  (`from_bitlist [] = 0 /\
    (!t. from_bitlist (CONS T t) = BIT1 (from_bitlist t)) /\
    (!t. from_bitlist (CONS F t) = BIT0 (from_bitlist t))`,
  REWRITE_TAC[from_bitlist]);;

(* ------------------------------------------------------------------------- *)
(* Given a numeral n, returns an equivalent bitlist of the given length.     *)
(* For example:                                                              *)
(*   TO_BITLIST_CONV 5 `6` = |- 6 = from_bitlist [F; T; T; F; F]             *)
(* ------------------------------------------------------------------------- *)

let TO_BITLIST_CONV: int -> conv =
  let th0 = prove (`0 = from_bitlist []`, REWRITE_TAC[from_bitlist])
  and th1 = prove
    (`!t. 0 = from_bitlist t ==> 0 = from_bitlist (CONS F t)`,
    CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[from_bitlist; ARITH_ZERO; NUMERAL])
  and thb0 = prove
    (`!n t. NUMERAL n = from_bitlist t ==>
      NUMERAL (BIT0 n) = from_bitlist (CONS F t)`,
    REWRITE_TAC[NUMERAL] THEN MESON_TAC[from_bitlist])
  and thb1 = prove
    (`!n t. NUMERAL n = from_bitlist t ==>
      NUMERAL (BIT1 n) = from_bitlist (CONS T t)`,
    REWRITE_TAC[NUMERAL] THEN MESON_TAC[from_bitlist]) in
  let rec thz i =
    if i < 0 then failwith "TO_BITLIST_CONV: numeral out of range"
    else if i = 0 then th0
    else
      let thr = thz (i - 1) in
      let t = rand (snd (dest_eq (concl thr))) in
      MP (SPEC t th1) thr in
  let rec th i n =
    match n with
      Const("_0",_) -> thz i
    | Comb(Const("BIT0",_),n) ->
        let (thr:thm) = th (i - 1) n in
        let t = rand (snd (dest_eq (concl thr))) in
        MP (SPECL [n; t] thb0) thr
    | Comb(Const("BIT1",_),n) ->
        let thr = th (i - 1) n in
        let t = rand (snd (dest_eq (concl thr))) in
        MP (SPECL [n; t] thb1) thr
    | _ -> failwith "TO_BITLIST_CONV: malformed numeral" in
  fun i tm ->
    match tm with
      Comb(Const("NUMERAL",_),n) when is_numeral n -> th i n
    | _ -> failwith "TO_BITLIST_CONV";;
