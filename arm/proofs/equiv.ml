(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reasoning program equivalence for Arm programs.                           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/relational2.ml";;

(* ------------------------------------------------------------------------- *)
(* Generic lemmas and tactics that are useful                                *)
(* ------------------------------------------------------------------------- *)

let get_bytelist_length (ls:term): int =
  try
    let th = LENGTH_CONV (mk_comb (`LENGTH:((8)word)list->num`,ls)) in
      Num.int_of_num (dest_numeral (rhs (concl th)))
  with Failure s ->
    failwith (Printf.sprintf
      "get_bytelist_length: cannot get the length of `%s`" (string_of_term ls));;

let rec takedrop (n:int) (l:'a list): 'a list * 'a list =
  if n = 0 then ([],l)
  else
    match l with
    | [] -> failwith "l too short"
    | h::t ->
      let a,b = takedrop (n-1) t in
      (h::a,b);;


let DIVIDES_4_VAL_WORD_ADD_64 = prove(
  `!pc ofs. 4 divides val (word pc:int64) /\ 4 divides ofs ==>
      4 divides val (word (pc+ofs):int64)`,
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
  (let divth = REWRITE_RULE[EQ_CLAUSES] (NUM_DIVIDES_CONV `4 divides 2 EXP 64`) in
    REWRITE_TAC[GSYM (MATCH_MP DIVIDES_MOD2 divth)]) THEN
  IMP_REWRITE_TAC[DIVIDES_ADD]);;


let EXPAND_RHS_TAC: tactic =
  fun (asl,g) ->
    let _,rhs = dest_eq g in
    let name,_ = dest_var rhs in
    EXPAND_TAC name (asl,g);;

let NONOVERLAPPING_APPEND = prove(`!(x:int64) (y:int64) code code2 n.
    nonoverlapping (x, LENGTH (APPEND code code2)) (y, n) ==>
    nonoverlapping (x, LENGTH code) (y, n)`,
  (* Converted by thenify.py *)
  REWRITE_TAC[LENGTH_APPEND;NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  NONOVERLAPPING_TAC);;

(* Given a goal whose conclusion is `read (write ...) .. = v`, apply
   COMPONENT_READ_OVER_WRITE_CONV to its LHS. *)
let COMPONENT_READ_OVER_WRITE_LHS_TAC: tactic =
  fun (asl,g) ->
    ONCE_REWRITE_TAC[COMPONENT_READ_OVER_WRITE_CONV (fst (dest_eq g))] (asl,g);;

let WRITE_ELEMENT_BYTES8 = prove(
  `!loc (z:(8)word) s. write (element loc) z s = write (bytes8 loc) z s`,
  REWRITE_TAC[bytes8;WRITE_COMPONENT_COMPOSE;asword;through;write;ARITH_RULE`1=SUC 0`;bytes;WORD_ADD_0;limb] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  IMP_REWRITE_TAC[DIV_1;MOD_LT] THEN
  REWRITE_TAC[WORD_VAL;ARITH_RULE`256=2 EXP 8`;VAL_BOUND;GSYM DIMINDEX_8]);;

let READ_OVER_WRITE_BYTELIST =
  prove(`!s (loc:int64) (l:((8)word)list).
      LENGTH l < 2 EXP 64
      ==> read (bytelist (loc,LENGTH l))
        (write (bytelist (loc,LENGTH l)) l s) = l`,
    REPEAT GEN_TAC THEN
    MAP_EVERY SPEC_TAC [
      `loc:int64`,`loc:int64`;`s:(64)word->(8)word`,`s:(64)word->(8)word`;
      `l:((8)word)list`,`l:((8)word)list`] THEN
    MATCH_MP_TAC list_INDUCT THEN
    CONJ_TAC THENL [
      REWRITE_TAC[LENGTH;READ_COMPONENT_COMPOSE;bytelist_clauses];

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[LENGTH;bytelist_clauses] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[CONS_11] THEN
      CONJ_TAC THENL [
        REWRITE_TAC[element;write];

        REWRITE_TAC[WRITE_ELEMENT_BYTES8] THEN
        IMP_REWRITE_TAC[READ_WRITE_ORTHOGONAL_COMPONENTS] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ORTHOGONAL_COMPONENTS_TAC
      ]
    ]);;

let READ_OVER_WRITE_APPEND_BYTELIST =
  prove(`!s (loc:int64) (l:((8)word)list) (l':((8)word)list).
      LENGTH (APPEND l l') < 2 EXP 64
      ==> read (bytelist (loc,LENGTH l))
        (write (bytelist (loc,LENGTH (APPEND l l'))) (APPEND l l') s) = l`,
    REPEAT GEN_TAC THEN
    MAP_EVERY SPEC_TAC [
      `loc:int64`,`loc:int64`;`s:(64)word->(8)word`,`s:(64)word->(8)word`;
      `l:((8)word)list`,`l:((8)word)list`] THEN
    MATCH_MP_TAC list_INDUCT THEN
    CONJ_TAC THENL [
      REWRITE_TAC[APPEND;LENGTH;READ_COMPONENT_COMPOSE;bytelist_clauses];

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[APPEND;LENGTH;bytelist_clauses] THEN
      REPEAT GEN_TAC THEN
      GEN_REWRITE_TAC (ONCE_DEPTH_CONV o LAND_CONV) [ARITH_RULE`SUC n=1+n`] THEN
      STRIP_TAC THEN
      REWRITE_TAC[CONS_11] THEN
      CONJ_TAC THENL [
        REWRITE_TAC[element;write];

        REWRITE_TAC[WRITE_ELEMENT_BYTES8] THEN
        IMP_REWRITE_TAC[READ_WRITE_ORTHOGONAL_COMPONENTS] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
        ORTHOGONAL_COMPONENTS_TAC
      ]
    ]);;

let READ_OVER_WRITE_MEMORY_BYTELIST =
  prove(`!s (loc:int64) (l:((8)word)list).
      LENGTH l < 2 EXP 64
      ==> read (memory :> bytelist (loc,LENGTH l))
        (write (memory :> bytelist (loc,LENGTH l)) l s) = l`,
  let read_write_mem_th =
    ISPECL [`memory:(armstate,(64)word->(8)word)component`] READ_WRITE_VALID_COMPONENT in
  REWRITE_TAC[component_compose] THEN
  REWRITE_TAC[read;write;o_THM] THEN
  IMP_REWRITE_TAC([read_write_mem_th] @ (!valid_component_thms)) THEN
  REWRITE_TAC[READ_OVER_WRITE_BYTELIST]);;


let READ_OVER_WRITE_MEMORY_APPEND_BYTELIST =
  prove(`!s (loc:int64) (l:((8)word)list) (l':((8)word)list).
      LENGTH (APPEND l l') < 2 EXP 64
      ==> read (memory :> bytelist (loc,LENGTH l))
        (write (memory :> bytelist (loc,LENGTH (APPEND l l'))) (APPEND l l') s) = l`,
  let read_write_mem_th =
    ISPECL [`memory:(armstate,(64)word->(8)word)component`] READ_WRITE_VALID_COMPONENT in
  REWRITE_TAC[component_compose] THEN
  REWRITE_TAC[read;write;o_THM] THEN
  IMP_REWRITE_TAC([read_write_mem_th] @ (!valid_component_thms)) THEN
  REWRITE_TAC[READ_OVER_WRITE_APPEND_BYTELIST]);;


(* A convenient function that proves divisibility of an expression like
    `2 EXP 64` `2 EXP 128 * a + 2 EXP 192 * b + 2 EXP 256`
  with an exponential expression such as
    `2 EXP 64`.
*)

let DIVIDES_RULE (divisor:term) (dividend:term): thm =
  let rec fn (divisor:term) (dividend:term): thm =
    if is_binary "+" dividend then
      let lhs,rhs = dest_binary "+" dividend in
      let lth = fn divisor lhs in
      let rth = fn divisor rhs in
      MATCH_MP DIVIDES_ADD (CONJ lth rth)
    else if is_binary "*" dividend then
      let lhs,rhs = dest_binary "*" dividend in
      try
        let lth = fn divisor lhs in
        ISPEC rhs (MATCH_MP DIVIDES_RMUL lth)
      with _ ->
        let lhs,rhs = dest_binary "*" dividend in
        let rth = fn divisor rhs in
        ISPEC lhs (MATCH_MP DIVIDES_LMUL rth)
    else
      let reduced_th = NUM_DIVIDES_CONV (mk_binary "num_divides" (divisor, dividend)) in
      let lhs,rhs = dest_binary "=" (concl reduced_th) in
      if rhs <> `T` then failwith
          ("DIVIDES_RULE: Could not fully reduce; got `" ^
            (string_of_thm reduced_th) ^ "` instead")
      else ONCE_REWRITE_RULE [EQ_CLAUSES] reduced_th in
  fn divisor dividend;;

(* Tests *)
let _ = DIVIDES_RULE `2 EXP 64` `2 EXP 128`;;
let _ = DIVIDES_RULE `2 EXP 64` `2 EXP 128 * a`;;
let _ = DIVIDES_RULE `2 EXP 64` `2 EXP 128 * a + 2 EXP 64`;;
let _ = DIVIDES_RULE `2 EXP 64` `2 EXP 128 * a + 2 EXP 192 * b + 2 EXP 256`;;

(* A convenient function that simplifies division of an expression like
    `2 EXP 64` `2 EXP 128 * a + 2 EXP 192 * b + 2 EXP 256`
  with an exponential expression such as
    `2 EXP 64`.
*)

let DIV_EXP_REDUCE_RULE (dividend:term) (divisor:term):thm =
  let simp_one = ARITH_RULE`2 EXP 0 = 1` in
  let rec fn (dividend:term) (divisor:term):thm =
    let _ = assert (is_binary "EXP" divisor) in
    let nbase2, nexp2 = dest_binary "EXP" divisor in
    if is_binary "EXP" dividend then
      let nbase1, nexp1 = dest_binary "EXP" dividend in
      if nbase1 <> nbase2 then failwith "Different exponent"
      else
        let base_nonzero = ARITH_RULE
          (subst [mk_eq(nbase1,`0`),`__p__:bool`] `~(__p__:bool)`) in
        let th = MATCH_MP (SPECL [nbase1;nexp1;nexp2] DIV_EXP) base_nonzero in
        (* exponent comparison *)
        let th = CONV_RULE (ONCE_DEPTH_CONV (NUM_LE_CONV ORELSEC ETA_CONV)) th in
        let th = REWRITE_RULE [COND_CLAUSES] th in
        CONV_RULE (ONCE_DEPTH_CONV NUM_SUB_CONV) th
    else if is_binary "*" dividend then
      let lhs,rhs = dest_binary "*" dividend in
      (* try the left side only. *)
      let lhs_eq = fn lhs divisor in
      (* `(lhs * rhs) DIV divisor` *)
      let expr = mk_binary "DIV" (dividend,divisor) in
      (* `(lhs * rhs) DIV divisor = (lhs DIV divisor) * rhs` *)
      let precond = DIVIDES_RULE divisor lhs in
      let expr = REWRITE_CONV[MATCH_MP (CONJUNCT1 MULT_DIV) precond] expr in
      REWRITE_RULE [lhs_eq;simp_one;MULT_CLAUSES] expr
    else if is_binary "+" dividend then
      let lhs,rhs = dest_binary "+" dividend in
      let lhs_eq = fn lhs divisor in
      let rhs_eq = fn rhs divisor in
      (* `(lhs + rhs) DIV divisor` *)
      let expr = mk_binary "DIV" (dividend,divisor) in
      (* `(lhs + rhs) DIV divisor = (lhs DIV divisor) + (rhs DIV divisor)` *)
      let precond =
        try DISJ1 (DIVIDES_RULE divisor lhs) (mk_binary "num_divides" (divisor,rhs))
        with _ -> try DISJ2 (mk_binary "num_divides" (divisor,lhs)) (DIVIDES_RULE divisor rhs)
        with _ -> failwith "Could not derive DIV_ADD's precond" in
      let expr = REWRITE_CONV[MATCH_MP DIV_ADD precond] expr in
      (* (lhs DIV divisor) + (rhs DIV divisor) = lhs' + rhs' *)
      REWRITE_RULE [lhs_eq;rhs_eq;simp_one] expr
    else failwith "Unknown dividend"
  in
  fn dividend divisor;;

let _ = DIV_EXP_REDUCE_RULE `2 EXP 128` `2 EXP 64`;;
let _ = DIV_EXP_REDUCE_RULE `2 EXP 128 + 2 EXP 64` `2 EXP 64`;;
let _ = DIV_EXP_REDUCE_RULE `2 EXP 128 * x` `2 EXP 64`;;
let _ = DIV_EXP_REDUCE_RULE `2 EXP 128 * x + 2 EXP 64 * y` `2 EXP 64`;;
let _ = DIV_EXP_REDUCE_RULE `2 EXP 192 * z + 2 EXP 128 * x + 2 EXP 64 * y` `2 EXP 64`;;

(* From
   val a + k = val a' + k' where k and k' are known to be >= 2 EXP 64,
   return a = a' /\ k = k'. *)
let PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC =
  let pth = prove(`!(k:num) (k':num).
      ((2 EXP 64) divides k) /\ ((2 EXP 64) divides k')
      ==> (!(a:int64) (a':int64). (val a + k = val a' + k')
          ==> a = a' /\ k = k')`,
    (* Converted by thenify.py *)
    REPEAT GEN_TAC THEN
    REWRITE_TAC[DIVIDES_DIV_MULT] THEN
    MAP_EVERY ABBREV_TAC [`khi = k DIV 2 EXP 64`; `k'hi = k' DIV 2 EXP 64`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["k"; "k'"] THEN
    REPEAT (FIRST_X_ASSUM (K ALL_TAC)) THEN (* clear hypotheses *)
    REPEAT GEN_TAC THEN
    MAP_EVERY (fun t -> ASSUME_TAC (SPEC t VAL_BOUND_64)) [`a:int64`;`a':int64`] THEN
    REWRITE_TAC [GSYM (ISPECL [`a:int64`;`a':int64`] VAL_EQ)] THEN
    DISCH_THEN (fun th ->
      let l = SPEC `2 EXP 64` EQ_DIVMOD in
      MP_TAC (ONCE_REWRITE_RULE[GSYM l] th)) THEN
    DISCH_THEN (fun th ->
      let lhs,rhs = CONJ_PAIR th in
      let lhs = SIMP_RULE[ARITH_RULE`~(2 EXP 64 = 0)`;DIV_MULT_ADD] lhs in
      let rhs = REWRITE_RULE[MOD_MULT_ADD] rhs in
      MP_TAC (CONJ lhs rhs)
      ) THEN
    IMP_REWRITE_TAC[DIV_LT;MOD_LT;ADD_CLAUSES]) in
  let qth = prove(`!(a:num) (b:num) (c:num).
      b = c ==> b DIV a = c DIV a`,
    MESON_TAC[EQ_DIVMOD]) in
  let rec fn th =
    let eq_lhs, eq_rhs = dest_binary "=" (concl th) in
    if is_binary "+" eq_lhs then
      let _, k = dest_binary "+" eq_lhs in
      let _, k' = dest_binary "+" eq_rhs in
      let k_divided = DIVIDES_RULE `2 EXP 64` k in
      let k'_divided = DIVIDES_RULE `2 EXP 64` k' in
      let res = MATCH_MP (MATCH_MP pth (CONJ k_divided k'_divided)) th in
      let eq_a, eq_k = CONJ_PAIR res in
      (* let's divide eq_k with 2 EXP 64 *)
      let eq_k_div_2exp64 = MATCH_MP (SPEC `2 EXP 64` qth) eq_k in
      let eq_k_lhs,eq_k_rhs = dest_eq (concl eq_k) in
      (* .. and simplify it! *)
      let eq_k_div_2exp64 = REWRITE_RULE[
        DIV_EXP_REDUCE_RULE eq_k_lhs `2 EXP 64`;
        DIV_EXP_REDUCE_RULE eq_k_rhs `2 EXP 64`] eq_k_div_2exp64 in
      (SUBST_ALL_TAC eq_a THEN fn eq_k_div_2exp64)
    else
      SUBST_ALL_TAC (REWRITE_RULE [VAL_EQ] th)
  in fn;;

let _ =  prove(`!(a0:int64) (a1:int64) (a2:int64)
      (b0:int64) (b1:int64) (b2:int64).
    val a0 + 2 EXP 64 * val a1 + 2 EXP 128 * val a2 =
    val b0 + 2 EXP 64 * val b1 + 2 EXP 128 * val b2
    ==> a0 = b0 /\ a1 = b1 /\ a2 = b2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  REPEAT CONJ_TAC THEN REFL_TAC);;

(* A variant of PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC that
   (1) works on assumptions, and
   (2) equalities must have intermediate variables:
       `val a0 + 2 EXP 64 * val a1 + 2 EXP 128 * val a2 = n`,
       `val b0 + 2 EXP 64 * val b1 + 2 EXP 128 * val b2 = n`,
       ... *)
let ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC:tactic =
  let eqeq = METIS[] `!x1 x2 y1 y2 a. (x1+x2=a /\ y1+y2=a) ==> x1+x2=y1+y2` in
  REPEAT (FIRST_X_ASSUM (fun th1 ->
    FIRST_X_ASSUM (fun th2 ->
      PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC
        (MATCH_MP eqeq (CONJ th1 th2)))));;

let _ = prove(
 `!(a0:int64) (a1:int64) (a2:int64) n (b0:int64) (b1:int64) (b2:int64).
    val a0 + 2 EXP 64 * val a1 + 2 EXP 128 * val a2 = n /\
    val b0 + 2 EXP 64 * val b1 + 2 EXP 128 * val b2 = n
    ==> a0 = b0 /\ a1 = b1 /\ a2 = b2`,
  REPEAT STRIP_TAC THEN
  ASM_PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM_TAC THEN
  REFL_TAC);;

(* Apply ENSURES2_FRAME_SUBSUMED and automatically resolve the subsumes
   relations between MAYCHANGES. *)
let ENSURES2_FRAME_SUBSUMED_TAC =
  MATCH_MP_TAC ENSURES2_FRAME_SUBSUMED THEN
  REWRITE_TAC[subsumed;FORALL_PAIR_THM;SEQ_PAIR_SPLIT;ETA_AX;SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  (* two subgoals from here *)
  (fun (asl,g) ->
      let st,st' = rand(rator g), rand g in
      (FIRST_X_ASSUM (fun th ->
        if rand(concl th) = st' then
          MP_TAC th THEN MAP_EVERY SPEC_TAC [(st',st');(st,st)]
        else NO_TAC)) (asl,g)) THEN
  REWRITE_TAC[GSYM subsumed; ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC;;

let ASSERT_NONOVERLAPPING_MODULO_TAC t core_exec =
  SUBGOAL_THEN t
    (fun th -> ASSUME_TAC (REWRITE_RULE[core_exec] th)) THENL [
    REWRITE_TAC[core_exec] THEN NONOVERLAPPING_TAC;
    ALL_TAC];;


let reads_state (c:term) (store_state_name:string ref): bool =
  match c with
  | Comb (Comb (Const ("=",_),
      Comb (Comb (Const ("read", _),_), Var (stname, _))),
      _) -> store_state_name := stname; true
  | Comb (Comb (Const
      ("read", _),_),
      Var (stname, _)) ->
    (* flags are boolean *)
    store_state_name := stname; true
  | Comb (Const ("~", _),
      Comb
        (Comb (Const ("read", _),
          _), Var (stname, _))) ->
    store_state_name := stname; true
  | Comb (Comb (Comb
    (Const ("aligned_bytes_loaded",_), Var (stname, _)),_),_) ->
    store_state_name := stname; true
  | _ ->
    maychange_term c &&
      (let s' = snd (dest_comb c) in is_var s' &&
        (store_state_name := name_of s'; true));;

(* Assumption stash/recovery tactic. *)
let stashed_asms: (string * thm) list list ref = ref [];;

(* Stash `read e s = r`, `aligned_bytes_loaded s ...` and `(MAYCHANGE ...) ... s`
   where s is a member of stnames. *)
let STASH_ASMS_OF_READ_STATES (stnames:string list): tactic =
  fun (asl,g) ->
    let matched_asms, others = List.partition (fun (name,th) ->
        let s = ref "" in
        reads_state (concl th) s && mem !s stnames)
      asl in
    stashed_asms := matched_asms::!stashed_asms;
    ALL_TAC (others,g);;

let RECOVER_ASMS_OF_READ_STATES: tactic =
  fun (asl,g) ->
    let a = List.hd !stashed_asms in
    stashed_asms := List.tl !stashed_asms;
    ALL_TAC (asl @ a, g);;

let mk_fresh_temp_name =
  let counter: int ref = ref 0 in
  fun () ->
    let i = !counter in
    counter := (i + 1);
    "temp_" ^ (string_of_int i);;

(* ------------------------------------------------------------------------- *)
(* eventually_n_at_pc states that if pre/postconditions at pc/pc2 are        *)
(* satisfied at nth step, you can 'promote' eventually to eventually_n.      *)
(* ------------------------------------------------------------------------- *)

let eventually_n_at_pc = new_definition
  `!pc_mc pc pc2 (nth:num) (mc:((8)word)list) (s0_pred:armstate->bool).
    eventually_n_at_pc pc_mc mc pc pc2 nth s0_pred
      <=>
    (!(s:armstate) (P:armstate->armstate->bool).
      aligned_bytes_loaded s (word pc_mc) mc /\ read PC s = word pc /\ s0_pred s
      ==> eventually arm (\s'. read PC s' = word pc2 /\ P s s') s
      ==> eventually_n arm nth (\s'. read PC s' = word pc2 /\ P s s') s)`;;

(* ------------------------------------------------------------------------- *)
(* A "barrier" instruction that makes Arm program stop.                      *)
(* ------------------------------------------------------------------------- *)

let barrier_inst = new_definition(`barrier_inst = (word 0:int32)`);;

let BARRIER_INST_DECODE_NONE = prove(`decode barrier_inst = NONE`,
  REWRITE_TAC[decode;barrier_inst] THEN
  (fun (asl,g) -> REWRITE_TAC[BITMATCH_SEQ_CONV (fst(dest_eq g))] (asl,g)));;

let barrier_inst_bytes = new_definition(`barrier_inst_bytes = bytelist_of_num 4 (val barrier_inst)`);;

let BARRIER_INST_BYTES_LENGTH = prove(`LENGTH barrier_inst_bytes = 4`,
    REWRITE_TAC[barrier_inst_bytes;LENGTH_BYTELIST_OF_NUM]);;

let BARRIER_INST_ARM_DECODE_NONEXIST = prove(`!s pc.
    aligned_bytes_loaded s (word pc) barrier_inst_bytes
      ==> ~(?inst. arm_decode s (word pc) inst)`,
  REWRITE_TAC[arm_decode;barrier_inst_bytes] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
      `bytelist_of_num 4 (val (i:int32)) = bytelist_of_num 4 (val barrier_inst)`
      (LABEL_TAC "HEQ") THENL [
    SUBGOAL_THEN
        `LENGTH (bytelist_of_num 4 (val (i:int32))) =
        LENGTH (bytelist_of_num 4 (val barrier_inst))` ASSUME_TAC THENL [
      REWRITE_TAC[LENGTH_BYTELIST_OF_NUM;barrier_inst] THEN
      (fun (asl,g) -> REWRITE_TAC[LENGTH_CONV (snd (dest_eq g))] (asl,g));

      ALL_TAC] THEN
    ASM_MESON_TAC[aligned_bytes_loaded_unique];

    ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[barrier_inst;VAL_WORD_0]) THEN
  SUBGOAL_THEN `num_of_bytelist(bytelist_of_num 4 (val (i:int32)))=num_of_bytelist(bytelist_of_num 4 0)`
    (LABEL_TAC "HEQ2") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "HEQ2" (MP_TAC) THEN
  IMP_REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM_EQ;ARITH_RULE`0 < 256 EXP 4`] THEN
  SIMP_TAC[REWRITE_RULE[DIMINDEX_32;ARITH_RULE`2 EXP 32 = 256 EXP 4`] (ISPECL [`i:int32`] VAL_BOUND)] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  DISCH_THEN (SUBST_ALL_TAC) THEN
  ASM_MESON_TAC[REWRITE_RULE[barrier_inst] BARRIER_INST_DECODE_NONE;OPTION_DISTINCT]);;


let ALIGNED_BYTES_LOADED_BARRIER_ARM_STUCK = prove(
  `!s s' pc. aligned_bytes_loaded s (word pc) barrier_inst_bytes /\
          read PC s = word pc /\ arm s s' ==> F`,
    ASM_REWRITE_TAC[arm;arm_decode;barrier_inst_bytes] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(bytelist_of_num 4 (val (i:int32))) =
                  (bytelist_of_num 4 (val (barrier_inst:int32)))` ASSUME_TAC THENL [
    ASM_MESON_TAC[aligned_bytes_loaded_unique;LENGTH_BYTELIST_OF_NUM];
    ALL_TAC] THEN
    SUBGOAL_THEN `num_of_bytelist(bytelist_of_num 4 (val (i:int32))) =
                  num_of_bytelist(bytelist_of_num 4 (val (barrier_inst:int32)))`
    (fun th -> LABEL_TAC "HEQ"
        (REWRITE_RULE[NUM_OF_BYTELIST_OF_NUM;ARITH_RULE`256 EXP 4=2 EXP 32`] th)) THENL [
    ASM_REWRITE_TAC[];ALL_TAC] THEN
    UNDISCH_LABEL_TAC "HEQ" THEN
    SUBGOAL_THEN `!(x:int32). val x MOD 2 EXP 32 = val x` (fun th->REWRITE_TAC[th;VAL_EQ]) THENL [
    STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN
    SIMP_TAC[VAL_BOUND;GSYM DIMINDEX_32];
    ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `decode barrier_inst = SOME instr` THEN
    REWRITE_TAC[BARRIER_INST_DECODE_NONE;OPTION_DISTINCT]);;


(* ------------------------------------------------------------------------- *)
(* Tactics for simulating a program whose postcondition is eventually_n.     *)
(* ------------------------------------------------------------------------- *)

let PRINT_TAC (s:string): tactic =
  W (fun (asl,g) -> Printf.printf "%s\n%!" s; ALL_TAC);;

(* A variant of ARM_BASIC_STEP_TAC, but
   - targets eventually_n
   - preserves 'arm s sname' at assumption *)
let ARM_BASIC_STEP'_TAC =
  let arm_tm = `arm` and arm_ty = `:armstate` and one = `1:num` in
  fun decode_th sname (asl,w) ->
    (* w = `eventually_n _ {stepn} _ {sv}` *)
    let sv = rand w and sv' = mk_var(sname,arm_ty) in
    let atm = mk_comb(mk_comb(arm_tm,sv),sv') in
    let eth = ARM_CONV decode_th (map snd asl) atm in
    let stepn = dest_numeral(rand(rator(rator w))) in
    let stepn_decr = stepn -/ num 1 in
    (* stepn = 1+{stepn-1}*)
    let stepn_thm = GSYM (NUM_ADD_CONV (mk_binary "+" (one,mk_numeral(stepn_decr)))) in
    (GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [stepn_thm] THEN
      GEN_REWRITE_TAC I [EVENTUALLY_N_STEP] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth]]) (asl,w);;

(* A variant of ARM_STEP_TAC for equivalence checking.
   If 'store_update_to' is Some ref, a list of
   (`read .. = expr`) will be stored instead of added as assumptions *)
let ARM_STEP'_TAC (mc_length_th,decode_th) subths sname
                  (store_update_to:thm list ref option) =
  (*** This does the basic decoding setup ***)

  ARM_BASIC_STEP'_TAC decode_th sname THEN

  (*** This part shows the code isn't self-modifying ***)

  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP aligned_bytes_loaded_update mc_length_th) THEN

  (*** Attempt also to show subroutines aren't modified, if applicable ***)

  MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC o
    MATCH_MP aligned_bytes_loaded_update o CONJUNCT1) subths THEN

  (*** This part produces any updated versions of existing asms ***)

  ASSUMPTION_STATE_UPDATE_TAC THEN

  (*** Produce updated "MAYCHANGE" assumption ***)

  MAYCHANGE_STATE_UPDATE_TAC THEN

  (*** This adds state component theorems for the updates ***)
  (*** Could also assume th itself but I throw it away   ***)

  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ASSEMBLER_SIMPLIFY_TAC) THEN

  begin match store_update_to with
  | None -> STRIP_TAC
  | Some r -> DISCH_THEN (fun th ->
      r := CONJUNCTS th;
      ALL_TAC)
  end;;

(* A variant of DISCARD_OLDSTATE_TAC which receives a list of state names
   to preserve, 'ss'.
   If clean_old_abbrevs is true, transitively remove assumptions that
   were using the removed variables (rhs of the removed assumptions) *)
let DISCARD_OLDSTATE'_TAC ss (clean_old_abbrevs:bool) =
  let vs = List.map (fun s -> mk_var(s,`:armstate`)) ss in
  let rec unbound_statevars_of_read bound_svars tm =
    match tm with
      Comb(Comb(Const("read",_),cmp),s) ->
        if mem s bound_svars then [] else [s]
    | Comb(a,b) -> union (unbound_statevars_of_read bound_svars a)
                         (unbound_statevars_of_read bound_svars b)
    | Abs(v,t) -> unbound_statevars_of_read (v::bound_svars) t
    | _ -> [] in
  let is_read (tm:term): bool =
    match tm with
    Comb(Comb(Const("read",_),_),s) -> true
    | _ -> false in
  let old_abbrevs: term list ref = ref [] in
  (* Erase all 'read c s' equations from assumptions whose s does not
     belong to ss. *)
  DISCARD_ASSUMPTIONS_TAC(
    fun thm ->
      let us = unbound_statevars_of_read [] (concl thm) in
      if us = [] || subset us vs then false
      else
        (* Accumulate rhses of old equalities that are abbreviations *)
        ((if clean_old_abbrevs && is_eq (concl thm) then
          let lhs, rhs = dest_eq (concl thm) in
          if is_var rhs then old_abbrevs := rhs::!old_abbrevs
          else ()
        else (); true))) THEN
  (if not clean_old_abbrevs then ALL_TAC else
   (* Transitively remove assumptions that use variables in old_abbrevs. *)
   W(fun (_,_) ->
    MAP_EVERY (fun (old_abbrev_var:term) ->
      fun (asl,g) ->
        (* If the old abbrev var is used by another 'read', don't remove it. *)
        if List.exists (fun _,asm ->
              let asm = concl asm in
              is_eq asm && is_read (fst (dest_eq asm)) && vfree_in old_abbrev_var asm)
            asl then
          ALL_TAC (asl,g)
        else
          DISCARD_ASSUMPTIONS_TAC(fun thm -> vfree_in old_abbrev_var (concl thm)) (asl,g))
      !old_abbrevs));;

let get_read_component (targ:term): term option =
  let targ = if is_eq targ then lhand targ else targ in
  match targ with
  | Comb(Comb(Const("read",_),comp),_) -> Some comp
  | _ -> None;;

(* Remove `read c s = ..` where c is a register containing a dead value. *)
let DISCARD_REGS_WITH_DEAD_VALUE_TAC (dead_regs:term list) =
  fun (asl,w) ->
    if dead_regs = [] then ALL_TAC (asl,w) else
    let asl = List.filter (fun (_,th) ->
        match (get_read_component (concl th)) with
        | None -> true
        | Some c ->
          if List.exists (fun dead_reg -> c = dead_reg) dead_regs
          then (Printf.printf "- Discarding `%s` because it will not be used\n"
                  (string_of_term (concl th)); false)
          else true)
      asl in
    ALL_TAC (asl,w);;

(* A variant of ARM_STEPS_TAC but using ARM_STEP'_TAC and DISCARD_OLDSTATE'_TAC instead.
   dead_value_info is an optional array that maps the step number - 1 to the dead
   registers. *)
let ARM_STEPS'_TAC th snums stname_suffix stnames_no_discard dead_value_info =
  MAP_EVERY (fun s ->
      let stname = "s" ^ string_of_int s ^ stname_suffix in
      time (ARM_STEP'_TAC th [] stname) None THEN
      DISCARD_OLDSTATE'_TAC (stname::stnames_no_discard) false THEN
      begin match dead_value_info with
      | None -> ALL_TAC
      | Some arr -> DISCARD_REGS_WITH_DEAD_VALUE_TAC (arr.(s-1))
      end)
    snums;;

(* A variant of ENSURES_FINAL_STATE_TAC but targets eventually_n. *)
let ENSURES_FINAL_STATE'_TAC =
  GEN_REWRITE_TAC I [EVENTUALLY_N_TRIVIAL] THEN
  GEN_REWRITE_TAC TRY_CONV [BETA_THM] THEN
  W(fun (asl,w) ->
        let onlycjs,othercjs = partition maychange_term (conjuncts w) in
        if othercjs = [] then
          TRY(REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC)
        else if onlycjs = [] then
          let w' = list_mk_conj othercjs in
          GEN_REWRITE_TAC I [CONJ_ACI_RULE(mk_eq(w,w'))]
        else
          let w' = mk_conj(list_mk_conj othercjs,list_mk_conj onlycjs) in
          (GEN_REWRITE_TAC I [CONJ_ACI_RULE(mk_eq(w,w'))] THEN
           TRY(CONJ_TAC THENL
                [ALL_TAC;
                 REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN
                 NO_TAC])));;


(* Given readth,readth2 = (`|- read c s = e1`, `|- read c' s' = e2`),
   prove e1 = e2 using WORD_RULE, abbreviate e1 and e2 as a
   fresh variable, and assumes them. If forget_expr is set, do not even
   add 'e1 = abbrev_var' as an assumption.
   For flag reads, which are simply `|- read ...`, just assumes them.
*)
let ABBREV_READS_TAC (readth,readth2:thm*thm) (forget_expr:bool):tactic =
  W(fun (asl,g) ->
    let eq,eq2 = concl readth,concl readth2 in
    if not (is_eq eq)
    then (* the flag reads case *)
      MAP_EVERY STRIP_ASSUME_TAC [readth;readth2]
    else
      (* eq is: `read elem s = e` *)
      let lhs,rhs = dest_eq eq in
      let lhs2,rhs2 = dest_eq eq2 in
      (* If lhs is PC update, don't abbrevate it. Or, if rhs is already a
        variable, don't abbreviate it again. Don't try to prove the rhs of
        eq2. *)
      if is_read_pc lhs || is_var rhs
      then MAP_EVERY STRIP_ASSUME_TAC [readth;readth2]
      else
        let vname = mk_fresh_temp_name() in
        let _ = if !arm_print_log then
          Printf.printf "Abbreviating `%s` (which is `%s`) as \"%s\".. (forget_expr: %b)\n"
            (string_of_term rhs) (string_of_term lhs) vname forget_expr
          in

        let readth2 =
          (if rhs2 = rhs then readth2 else
          try
            let r = WORD_RULE (mk_eq(rhs2,rhs)) in
            let _ = if !arm_print_log then
              Printf.printf "\t- Abbreviating `%s` as \"%s\" as well\n"
                (string_of_term rhs2) vname in
            REWRITE_RULE[r] readth2
          with _ ->
            Printf.printf "\t- Error: WORD_RULE could not prove `%s = %s`\n"
              (string_of_term rhs2) (string_of_term rhs);
            failwith "ABBREV_READS_TAC") in
        (* Now introduce abbreviated writes, eventually *)
        let fresh_var = mk_var (vname,type_of rhs) in
        let abbrev_th = prove(mk_exists(fresh_var,mk_eq(rhs,fresh_var)),
          EXISTS_TAC rhs THEN REFL_TAC) in
        CHOOSE_THEN (fun abbrev_th ->
            ASSUME_TAC (REWRITE_RULE[abbrev_th] readth) THEN
            ASSUME_TAC (REWRITE_RULE[abbrev_th] readth2) THEN
            (if forget_expr then ALL_TAC else ASSUME_TAC abbrev_th))
          abbrev_th);;



(* ------------------------------------------------------------------------- *)
(* Definitions for stating program equivalence.                              *)
(* ------------------------------------------------------------------------- *)

(* A recursive function for defining a conjunction of equality clauses *)
let mk_equiv_regs = define
  `((mk_equiv_regs:((armstate,(64)word)component)list->armstate#armstate->bool)
      [] s = T) /\
   (mk_equiv_regs (CONS reg regs) (s1,s2) =
      ?(a:int64). read reg s1 = a /\ read reg s2 = a /\
                  mk_equiv_regs regs (s1,s2))`;;

let mk_equiv_bool_regs = define
  `((mk_equiv_bool_regs:((armstate,bool)component)list->armstate#armstate->bool)
      [] s = T) /\
   (mk_equiv_bool_regs (CONS reg regs) (s1,s2) =
      ?(a:bool). read reg s1 = a /\ read reg s2 = a /\
                  mk_equiv_bool_regs regs (s1,s2))`;;

(* ------------------------------------------------------------------------- *)
(* Tactics for proving equivalence of two partially different programs.      *)
(* Renamed registers in the input programs should not affect the behavior of *)
(* these tactics.                                                            *)
(* ------------------------------------------------------------------------- *)

(* A lock-step simulation.
  This abbreviates the new expression(s) appearing on the new state
  expression(s) of the right-side program, and checks whether
  new expression(s) appearing on the left-side program are equivalent
  to it.

  It forgets abbreviations that were used in the past. *)
let ARM_LOCKSTEP_TAC =
  let update_eqs_prog1: thm list ref = ref [] in
  let update_eqs_prog2: thm list ref = ref [] in

  let the_sp = `SP` in
  let forget_expr (comp:term) = comp <> the_sp in

  fun execth execth' (snum:int) (snum':int) (stname'_suffix:string)
        (ignored_output_regs_left:term list)
        (ignored_output_regs_right:term list) ->
    let new_stname = "s" ^ (string_of_int snum) in
    let new_stname' = "s" ^ (string_of_int snum') ^ stname'_suffix in

    (* 1. One step on the left program. *)
    (* Get the right program's current state name "s'" from
       `eventually_n arm n (\s. eventually_n arm n' .. s') s`,
       and stash assumptions over the right state. *)
    (fun (asl,g) ->
      (* Print log *)
      Printf.printf "ARM_LOCKSTEP_TAC (%d,%d)\n%!" snum snum';
      Printf.printf "Running left...\n";
      let cur_stname' = name_of (rand (snd ((dest_abs o rand o rator) g))) in
      STASH_ASMS_OF_READ_STATES [cur_stname'] (asl,g)) THEN
    ARM_STEP'_TAC execth [] new_stname (Some update_eqs_prog1) THEN
    (*cleanup assumptions that use old abbrevs*)
    DISCARD_OLDSTATE'_TAC [new_stname] false THEN
    (* .. and dead registers. *)
    DISCARD_REGS_WITH_DEAD_VALUE_TAC ignored_output_regs_left THEN
    RECOVER_ASMS_OF_READ_STATES THEN

    (* 2. One step on the right program. *)
    (fun (asl,g) -> Printf.printf "Running right...\n"; ALL_TAC (asl,g)) THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    STASH_ASMS_OF_READ_STATES [new_stname] THEN
    ARM_STEP'_TAC execth' [] new_stname' (Some update_eqs_prog2) THEN
    (*cleanup assumptions that use old abbrevs*)
    DISCARD_OLDSTATE'_TAC [new_stname'] true THEN
    (* .. and dead registers. *)
    DISCARD_REGS_WITH_DEAD_VALUE_TAC ignored_output_regs_right THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN

    (* 3. Abbreviate expressions that appear in the new state expressions
          created from step 2. *)
    W (fun (asl,g) ->
      let update_eqs_prog1_list = !update_eqs_prog1 in
      let update_eqs_prog2_list = !update_eqs_prog2 in
      if List.length update_eqs_prog1_list <>
          List.length update_eqs_prog2_list
      then
        (Printf.printf "Updated components mismatch:\n";
         Printf.printf "\tprog1: ";
         List.iter (fun th -> print_qterm (concl th)) update_eqs_prog1_list;
         Printf.printf "\n\tprog2: ";
         List.iter (fun th -> print_qterm (concl th)) update_eqs_prog2_list;
         failwith "ARM_LOCKSTEP_TAC")
      else
        let eqs = zip update_eqs_prog1_list update_eqs_prog2_list in
        MAP_EVERY
          (fun (eq1,eq2) ->
            let oc1:term option = get_read_component (concl eq1) in
            let oc2:term option = get_read_component (concl eq2) in
            match oc1,oc2 with
            | Some comp1, Some comp2 ->
              if mem comp1 ignored_output_regs_left &&
                 mem comp2 ignored_output_regs_right
              then ALL_TAC
              else ABBREV_READS_TAC (eq1,eq2) (forget_expr comp1)
            | _ -> (* this can happen when writing to XZR *) ALL_TAC)
          eqs);;


let EQUIV_INITIATE_TAC input_equiv_states_th =
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  ASSUME_TAC(ISPEC (mk_var("s0'",`:armstate`)) MAYCHANGE_STARTER) THEN
  let input_pred = SPEC_ALL
      (SPECL [`s0:armstate`;`s0':armstate`] input_equiv_states_th) in
  UNDISCH_TAC (fst (dest_binary "=" (concl input_pred))) THEN
  GEN_REWRITE_TAC LAND_CONV [input_equiv_states_th] THEN
  REWRITE_TAC [C_ARGUMENTS;SOME_FLAGS;mk_equiv_regs;mk_equiv_bool_regs] THEN
  STRIP_TAC;;

(* bignum_from_memory_th: `bignum_from_memory (x,8) s0 = a` *)
let BIGNUM_EXPAND_AND_DIGITIZE_TAC (bignum_from_memory_th:thm): tactic =
  let t = concl bignum_from_memory_th in
  let lhs,rhs = dest_eq t in
  let tmp,st_var = dest_comb lhs in
  let ptr,numwords = dest_pair (snd (dest_comb tmp)) in
  let st_name,rhs_name = fst (dest_var st_var),fst (dest_var rhs) in
  let new_expr = subst [(ptr,`ptr:int64`);(numwords,`numwords:num`);(st_var,`st_var:armstate`)]
      `read (memory :> bytes(ptr,8 * numwords)) st_var` in
  let new_abbrev_prefix = rhs_name ^ (if st_name.[String.length st_name - 1] = '\'' then "'" else "") ^ "_" in

  ASSUME_TAC (CONV_RULE (LAND_CONV BIGNUM_EXPAND_CONV) bignum_from_memory_th) THEN
  BIGNUM_DIGITIZE_TAC new_abbrev_prefix new_expr;;

let ARM_STUTTER_LEFT_TAC exec_th (snames:int list)
    (dead_value_info:term list array option): tactic =
  W (fun (asl,g) ->
    (* get the state name of the 'right' program *)
    let t' = fst (dest_comb g) in
    let inner_eventually = snd (dest_abs (snd (dest_comb (t')))) in
    let sname = fst (dest_var (snd (dest_comb inner_eventually))) in
    STASH_ASMS_OF_READ_STATES [sname] THEN
    ARM_STEPS'_TAC exec_th snames "" [] dead_value_info THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    CLARIFY_TAC);;

let ARM_STUTTER_RIGHT_TAC exec_th (snames:int list) (st_suffix:string)
    (dead_value_info:term list array option): tactic =
  W (fun (asl,g) ->
    (* get the state name of the 'left' program *)
    let sname = fst (dest_var (snd (dest_comb g))) in
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    STASH_ASMS_OF_READ_STATES [sname] THEN
    ARM_STEPS'_TAC exec_th snames st_suffix [] dead_value_info THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    CLARIFY_TAC);;


(* maychanges: `(MAYCHANGE [..] ,, MAYCHANGE ...)` *)
let simplify_maychanges: term -> term =
  let maychange_const = `MAYCHANGE` and seq_const = `,,` in
  let word64ty = `:(64)word` and word128ty = `:(128)word` in
  let the_base_ptr = `base_ptr:int64` and the_ofs = `ofs:num` and
      the_len = `len:num` in
  let the_base_ptr_ofs = `(word_add base_ptr (word ofs)):int64` and
      the_memory_base_ptr = `(memory :> bytes64 base_ptr)` in
  let the_memory_base_ptr_len = `(memory :> bytes(base_ptr,len))` in
  let zero = `0` in

  fun (maychanges:term) ->
    let maychange_regs64 = ref [] and
        maychange_regs128 = ref [] and
        maychange_mems = ref [] and
        maychange_others = ref [] in
    (* t: `X1`, `PC`, `Q0`, `memory :> bytes64 (x:int64)`, ... *)
    let add_maychange (t:term): unit =
      try
        (* t is memory access, e.g., `memory :> bytes64 (x:int64)` *)
        let l,r = dest_binary ":>" t in
        let lname,_ = dest_const l in
        if lname <> "memory" then failwith "not mem" else
        let c,args = strip_comb r in
        match fst (dest_const c) with
        | "bytes64" -> (* args is just a location *)
          assert (List.length args = 1);
          maychange_mems := !maychange_mems @ [(t, (List.hd args, `8`))]
        | "bytes" -> (* args is (loc, len). *)
          assert (List.length args = 1);
          let loc, len = dest_pair (List.hd args) in
          maychange_mems := !maychange_mems @ [(t, (loc, len))]
        | _ -> (* don't know what it is *)
          maychange_others := !maychange_others @ [t]
      with _ ->
        (* t is register *)
        let _,args = dest_type (type_of t) in
        let destty = last args in
        if destty = word64ty then
          maychange_regs64 := !maychange_regs64 @ [t]
        else if destty = word128ty then
          maychange_regs128 := !maychange_regs128 @ [t]
        else
          maychange_others := !maychange_others @ [t] in

    let rec f (t:term): unit =
      if is_binary ",," t then
        let lhs,rhs = dest_binary ",," t in
        let _, args = dest_comb lhs in
        let _ = List.iter add_maychange (dest_list args) in
        f rhs
      else
        let _, args = dest_comb t in
        List.iter add_maychange (dest_list args) in

    let _ = f maychanges in

    (* now merge memory accesses. *)
    let maychange_mems_merged = ref [] in
    let add_maychange_mem (base_ptr, ofs, len): unit =
      (* if len is 8, just use bytes64. *)
      let base_ptr = if ofs = 0 then base_ptr else
        subst [base_ptr,the_base_ptr;mk_small_numeral ofs,the_ofs] the_base_ptr_ofs in
      let final_term = if len = 8 then
          subst [base_ptr,the_base_ptr] the_memory_base_ptr
        else
          subst [base_ptr,the_base_ptr;mk_small_numeral len,the_len] the_memory_base_ptr_len in
      maychange_mems_merged := !maychange_mems_merged @ [final_term] in

    let base_ptr_and_ofs (t:term): term * int =
      try (* t is "word_add baseptr (word ofs)" *)
        let baseptr,y = dest_binary "word_add" t in
        let wordc, ofs = dest_comb y in
        if name_of wordc <> "word" then failwith "not word" else
        (baseptr, dest_small_numeral ofs)
      with _ -> (t, 0) in
    while length !maychange_mems <> 0 do
      let next_term,(ptr,len) = List.hd !maychange_mems in
      if not (is_numeral len) then
        (* there is nothing we can do *)
        maychange_mems_merged := next_term::!maychange_mems_merged
      else
        let baseptr, _ = base_ptr_and_ofs ptr in

        let mems_of_interest, remaining = List.partition
          (fun _,(ptr,len) -> baseptr = fst (base_ptr_and_ofs ptr) && is_numeral len)
          !maychange_mems in
        maychange_mems := remaining;

        if List.length mems_of_interest = 1 then
          maychange_mems_merged := (fst (List.hd mems_of_interest)) :: !maychange_mems_merged
        else
          (* combine mem accesses in mems_of_interest *)
          (* get (ofs, len). len must be constant. *)
          let ranges = map
            (fun (_,(t,len)) -> snd (base_ptr_and_ofs t),dest_small_numeral len)
            mems_of_interest in
          let ranges = mergesort (<) ranges in
          let rec merge_and_update ranges =
            match ranges with
            | (ofs,len)::[] -> add_maychange_mem (baseptr,ofs,len)
            | (ofs1,len1)::(ofs2,len2)::t ->
              if ofs2 <= ofs1 + len1 then
                let len = max len1 (ofs2 + len2 - ofs1) in
                merge_and_update ((ofs1,len)::t)
              else
                let _ = add_maychange_mem (baseptr, ofs1, len1) in
                merge_and_update ((ofs2,len2)::t) in
          merge_and_update ranges
    done;

    (* now rebuild maychange terms! *)
    let result = ref zero in
    let join_result (comps:term list): unit =
      if comps = [] then () else
      let mterm = mk_icomb (maychange_const, mk_flist comps) in
      if !result = zero then result := mterm
      else result := mk_icomb(mk_icomb (seq_const,mterm),!result) in
    let _ = join_result !maychange_regs64 in
    let _ = join_result !maychange_regs128 in
    let _ = join_result !maychange_others in
    let _ = List.iter (fun t -> join_result [t]) !maychange_mems_merged in
    !result;;

(*
    simplify_maychanges `MAYCHANGE [PC] ,, MAYCHANGE [X0]`;;
    simplify_maychanges `MAYCHANGE [PC] ,, MAYCHANGE [Q0] ,, MAYCHANGE [ZF]`;;
    simplify_maychanges `MAYCHANGE [memory :> bytes64 (x:int64)] ,, MAYCHANGE [X0]`;;
    simplify_maychanges `MAYCHANGE [memory :> bytes64 (x:int64)] ,,
                         MAYCHANGE [memory :> bytes64 (word_add x (word 8))]`;;
    simplify_maychanges `MAYCHANGE [memory :> bytes64 (x:int64)] ,,
                         MAYCHANGE [memory :> bytes64 (word_add x (word 16))] ,,
                         MAYCHANGE [memory :> bytes64 (word_add x (word 24))] ,,
                         MAYCHANGE [memory :> bytes64 (word_add x (word 8))]`;;
    simplify_maychanges `MAYCHANGE [memory :> bytes64 (word_add x (word 8))] ,,
                         MAYCHANGE [memory :> bytes64 (x:int64)] ,,
                         MAYCHANGE [memory :> bytes64 (word_add y (word 24))] ,,
                         MAYCHANGE [memory :> bytes64 (word_add y (word 16))]`;;
*)

let SIMPLIFY_MAYCHANGES_TAC =
  W(fun (asl,w) ->
    let mcs = List.filter_map
      (fun (_,asm) -> if maychange_term (concl asm) then Some asm else None) asl in
    MAP_EVERY (fun asm ->
        let x, st2 = dest_comb (concl asm) in
        let mainterm, st1 = dest_comb x in
        let newterm = simplify_maychanges mainterm in
        let _ = Printf.printf "SIMPLIFY_MAYCHANGES_TAC: Simplifying `%s` to `%s`\n"
            (string_of_term (concl asm)) (string_of_term newterm) in
        if mainterm = newterm then ALL_TAC
        else
          (SUBGOAL_THEN (list_mk_comb (newterm,[st1;st2])) ASSUME_TAC THENL
          [ POP_ASSUM_LIST (K ALL_TAC) THEN ASSUME_TAC asm THEN MONOTONE_MAYCHANGE_TAC;
            ALL_TAC ] THEN
          UNDISCH_THEN (concl asm) (K ALL_TAC)))
      mcs);;

let CLEAR_UNUSED_ABBREVS =
  fun (asl,w) ->
    (* asl_with_flags: (keep it?, abbrev var, (name, th)) array *)
    let asl_with_flags = ref (Array.of_list (map
      (fun (name,th) -> true, (None, name, th)) asl)) in

    (* From assumptions, find those that abbreviates to the_var *)
    let find_indices (the_var:term): int list =
      let res = ref [] in
      for i = 0 to Array.length !asl_with_flags - 1 do
        let _,(abbrev_var,_,_) = !asl_with_flags.(i) in
        if abbrev_var = Some the_var then
          res := i::!res
      done;
      !res in

    (* do BFS to mark assumptions that must be not be cleared *)
    let alive_queue = ref [] in
    for i = 0 to Array.length !asl_with_flags - 1 do
      let _,(_,name,th) = !asl_with_flags.(i) in
      let dummy_ref = ref "" in
      if reads_state (concl th) dummy_ref then
        (* assumptions that read states should not be removed *)
        alive_queue := i::!alive_queue
      else if is_eq (concl th) && is_var (rand (concl th)) then
        (* if th is 'e = var', mark it as initially dead & extract rhs var *)
        !asl_with_flags.(i) <- (false, (Some (rand (concl th)), name, th))
      else
        (* if th is not 'e = var', don't remove this because
           we don't know what this is *)
        alive_queue := i::!alive_queue
    done;

    (* Start BFS *)
    while List.length !alive_queue <> 0 do
      let i = List.hd !alive_queue in
      alive_queue := List.tl !alive_queue;
      let itm = !asl_with_flags.(i) in
      if fst itm then begin
        (* mark i'th item as alive, and propagate this aliveness to the
           used variables *)
        !asl_with_flags.(i) <- (true, snd itm);
        let _,_,asm = snd itm in
        let freevars = frees (concl asm) in
        List.iter (fun fvar ->
            let next_asms = find_indices fvar in
            alive_queue := !alive_queue @ next_asms)
          freevars
      end
    done;

    let new_asl = ref [] in
    for i = Array.length !asl_with_flags - 1 downto 0 do
      let is_alive,(_,name,th) = !asl_with_flags.(i) in
      if is_alive then
        new_asl := (name,th)::!new_asl
    done;

    Printf.printf "CLEAR_UNUSED_ABBREVS: cleared %d/%d assumptions\n%!"
      (List.length asl - List.length !new_asl) (List.length asl);

    ALL_TAC (!new_asl,w);;


(* EQUIV_STEPS_TAC simulates two partially different programs and makes
  abbreviations of the new symbolic expressions after each step.
  Instructions are considered equivalent if they are alpha-equivalent.
  It takes a list of 'action's that describe how the symbolic execution
  engine must be run. Each action is consumed by EQUIV_STEP_TAC and
  a proper tactic is taken.

  dead_value_info_left is an array of list of registers which contain
  dead values in the left program. Same for dead_value_info_right.
  They are for optimization, and giving None to them will still functionally
  work.
*)

let EQUIV_STEP_TAC action execth1 execth2
    (dead_value_info_left:term list array option)
    (dead_value_info_right:term list array option): tactic =
  let get_or_nil i (x:term list array option) =
    match x with
    | None -> []
    | Some arr -> arr.(i) in

  match action with
  | ("equal",lstart,lend,rstart,rend) ->
    assert (lend - lstart = rend - rstart);
    REPEAT_I_N 0 (lend - lstart)
      (fun i ->
        let il,ir = (lstart+i),(rstart+i) in
        time (ARM_LOCKSTEP_TAC execth1 execth2 (il+1) (ir+1) "'"
          (get_or_nil il dead_value_info_left)
          (get_or_nil ir dead_value_info_right))
        THEN (if i mod 20 = 0 then CLEAR_UNUSED_ABBREVS else ALL_TAC)
        THEN (if i mod 50 = 0 then SIMPLIFY_MAYCHANGES_TAC else ALL_TAC)
        THEN CLARIFY_TAC)
  | ("insert",lstart,lend,rstart,rend) ->
    if lstart <> lend then failwith "insert's lstart and lend must be equal"
    else begin
      (if rend - rstart > 50 then
        Printf.printf "Warning: too many instructions: insert %d~%d\n" rstart rend);
      ARM_STUTTER_RIGHT_TAC execth2 ((rstart+1)--rend) "'" dead_value_info_right
        ORELSE (PRINT_TAC "insert failed" THEN PRINT_GOAL_TAC THEN NO_TAC)
    end
  | ("delete",lstart,lend,rstart,rend) ->
    if rstart <> rend then failwith "delete's rstart and rend must be equal"
    else begin
      (if lend - lstart > 50 then
        Printf.printf "Warning: too many instructions: delete %d~%d\n" lstart lend);
      ARM_STUTTER_LEFT_TAC execth1 ((lstart+1)--lend) dead_value_info_left
        ORELSE (PRINT_TAC "delete failed" THEN PRINT_GOAL_TAC THEN NO_TAC)
    end
  | ("replace",lstart,lend,rstart,rend) ->
    (if lend - lstart > 50 || rend - rstart > 50 then
      Printf.printf "Warning: too many instructions: replace %d~%d %d~%d\n"
          lstart lend rstart rend);
    ((ARM_STUTTER_LEFT_TAC execth1 ((lstart+1)--lend) dead_value_info_left
     ORELSE (PRINT_TAC "replace failed: stuttering left" THEN PRINT_GOAL_TAC THEN NO_TAC))
     THEN
     (ARM_STUTTER_RIGHT_TAC execth2 ((rstart+1)--rend) "'" dead_value_info_right
      ORELSE (PRINT_TAC "replace failed: stuttering right" THEN PRINT_GOAL_TAC THEN NO_TAC)))
  | (s,_,_,_,_) -> failwith ("Unknown action: " ^ s);;



let EQUIV_STEPS_TAC ?dead_value_info_left ?dead_value_info_right
    actions execth1 execth2: tactic =
  MAP_EVERY
    (fun action ->
      EQUIV_STEP_TAC action execth1 execth2 dead_value_info_left
                     dead_value_info_right)
    actions;;

(* ------------------------------------------------------------------------- *)
(* Tactics for proving equivalence of two programs that have reordered       *)
(* instructions.                                                             *)
(* ------------------------------------------------------------------------- *)

(* Given eqth = (`|- read c s = rhs`), abbreviate rhs as a fresh variable.
   assume the abbreviated eqth, and add the abbreviation `rhs = fresh_var`
   to append_to.
   append_to is a list of `rhs = fresh_var` equalities.
   The abbreviated formula `rhs = x_fresh` is not added as assumption.
*)
let ABBREV_READ_TAC (eqth:thm) (append_to:thm list ref):tactic =
  W(fun (asl,g) ->
    let eq = concl eqth in
    if not (is_eq eq) then
      (Printf.printf "ABBREV_READ_TAC: not equality, passing..: `%s`\n"
          (string_of_term eq);
       ASSUME_TAC eqth) else
    (* eq is: `read elem s = e` *)
    let lhs,rhs = dest_eq eq in
    (* If lhs is PC update, don't abbrevate it *)
    if is_read_pc lhs then ASSUME_TAC eqth
    else
      let vname = mk_fresh_temp_name() in
      Printf.printf "Abbreviating `%s` (which is `%s`) as \"%s\"..\n"
          (string_of_term rhs) (string_of_term lhs) vname;

      let fresh_var = mk_var (vname,type_of rhs) in
      let abbrev_th = prove(mk_exists(fresh_var,mk_eq(rhs,fresh_var)),
        EXISTS_TAC rhs THEN REFL_TAC) in
      CHOOSE_THEN (fun abbrev_th ->
        ASSUME_TAC (REWRITE_RULE[abbrev_th] eqth) THEN
        (fun (asl,g) ->
          append_to := abbrev_th::!append_to;
          ALL_TAC(asl,g))) abbrev_th);;

(* Simulate an instruction of the left program and assign fresh variables
    to the RHSes of new state equations (`read c s = RHS`).
    store_to is a list of `RHS = assigned_fresh_var` theorems.
    The equations on assigned fresh variables (`RHS = assigned_fresh_var`)
    do not appear as assumptions.
*)

let ARM_STEP'_AND_ABBREV_TAC =
  let update_eqs_prog: thm list ref = ref [] in
  fun execth (new_stname) (store_to:thm list ref) ->
    (* Stash the right program's state equations first *)
    (fun (asl,g) ->
      let cur_stname' = name_of (rand (snd ((dest_abs o rand o rator) g))) in
      STASH_ASMS_OF_READ_STATES [cur_stname'] (asl,g)) THEN
    (* One step on the left program *)
    ARM_STEP'_TAC execth [] new_stname (Some update_eqs_prog) THEN
    DISCARD_OLDSTATE'_TAC [new_stname] false THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    (* Abbreviate RHSes of the new state equations *)
    W (fun (asl,g) ->
      let update_eqs_prog_list = !update_eqs_prog in
      MAP_EVERY
        (fun th -> ABBREV_READ_TAC th store_to)
        update_eqs_prog_list);;

(* store_to is a reference to list of state numbers and abbreviations.
   It is initialized as empty when this tactic starts.
   Unlike ARM_STEP'_AND_ABBREV_TAC, the equations on assigned fresh variables
    (`RHS = assigned_fresh_var`) are added as assumptions. *)
let ARM_STEPS'_AND_ABBREV_TAC execth (snums:int list)
    (store_to: (int * thm) list ref):tactic =
  W (fun (asl,g) -> store_to := []; ALL_TAC) THEN
  (* Stash the right program's state equations first *)
  (fun (asl,g) ->
    let pat = term_match []
      `eventually_n arm n0 (\s'. eventually_n arm n1 P s0) s1` in
    let _,assigns,_ = pat g in
    let cur_stname = name_of
      (fst (List.find (fun a,b -> b=`s0:armstate`) assigns)) in
    STASH_ASMS_OF_READ_STATES [cur_stname] (asl,g)) THEN
  MAP_EVERY
    (fun n ->
      let stname = "s" ^ (string_of_int n) in
      let store_to_n = ref [] in
      (fun (asl,g) ->
        let _ = Printf.printf "Stepping to state %s..\n" stname in
        ALL_TAC (asl,g)) THEN
      ARM_STEP'_AND_ABBREV_TAC execth stname store_to_n THEN
      (fun (asl,g) ->
        store_to := (map (fun x -> (n,x)) !store_to_n) @ !store_to;
        Printf.printf "%d new abbreviations (%d in total)\n%!"
          (List.length !store_to_n) (List.length !store_to);
        ALL_TAC (asl,g)) THEN
      CLARIFY_TAC)
    snums THEN
  RECOVER_ASMS_OF_READ_STATES;;

let get_read_component (eq:term): term =
  let lhs = fst (dest_eq eq) in
  rand (rator lhs);;

let _ = get_read_component `read X1 s = word 0`;;

(* For the right program. abbrevs must be generated by ARM_STEPS'_AND_ABBREV_TAC. *)
let ARM_STEPS'_AND_REWRITE_TAC execth (snums:int list) (inst_map: int list)
                               (abbrevs: (int * thm) list ref): tactic =
  (* Warning: no nested call of ARM_STEPS'_AND_REWRITE_TAC *)
  let abbrevs_cpy:(int * thm) list ref = ref [] in
  (* Stash the left program's state equations first *)
  (fun (asl,g) ->
    abbrevs_cpy := !abbrevs;
    let cur_stname = name_of (rand g) in
    STASH_ASMS_OF_READ_STATES [cur_stname] (asl,g)) THEN
  MAP_EVERY
    (fun n ->
      let stname = "s'" ^ (string_of_int n) in
      let new_state_eq = ref [] in
      W (fun (asl,g) ->
        let _ = Printf.printf "Stepping to state %s.. (has %d remaining abbrevs)\n%!"
            stname (List.length !abbrevs_cpy) in
        ALL_TAC) THEN
      MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
      ARM_STEP'_TAC execth [] stname (Some new_state_eq) THEN
      DISCARD_OLDSTATE'_TAC [stname] false THEN
      MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
      (fun (asl,g) ->
        let n_at_lprog = List.nth inst_map (n-1) in
        let abbrevs_for_st_n, leftover = List.partition (fun (n',t)->n'=n_at_lprog) !abbrevs_cpy in
        let _ = abbrevs_cpy := leftover in
        (* new_state_eqs is the updated state components of the 'right' program
           instruction. *)
        let new_state_eqs = !new_state_eq in
        (* Reading flags may not have 'read flag s = ..' form, but just
            'read flag s' or '~(read flag s)'. They don't need to be rewritten.
           Also, 'read PC' should not be rewritten as well. Collect them
           separately. *)
        let new_state_eqs_norewrite,new_state_eqs =
          List.partition
            (fun th -> not (is_eq (concl th)) ||
                       (is_read_pc (fst (dest_eq (concl th)))))
          new_state_eqs in
        if List.length abbrevs_for_st_n = List.length new_state_eqs then
          (* For each `read c sn = rhs`, replace rhs with abbrev *)
          let new_state_eqs = List.filter_map
            (fun new_state_eq ->
              let rhs = snd (dest_eq (concl new_state_eq)) in
              (* Find 'rhs = abbrev' from the left program's  updates. *)
              match List.find_opt
                (fun (_,th') -> fst (dest_eq (concl th')) = rhs)
                abbrevs_for_st_n with
              | Some (_,rhs_to_abbrev) ->
                (try
                  Some (GEN_REWRITE_RULE RAND_CONV [rhs_to_abbrev] new_state_eq)
                with _ ->
                  (Printf.printf "Failed to proceed.\n";
                    Printf.printf "- rhs: `%s`\n" (string_of_term rhs);
                    Printf.printf "- rhs_to_abbrev: `%s`\n" (string_of_thm rhs_to_abbrev);
                    failwith "ARM_STEPS'_AND_REWRITE_TAC"))
              | None -> (* This case happens when new_state_eq already has abbreviated RHS *)
                None)
            new_state_eqs in
          (if !arm_print_log then begin
            Printf.printf "  updated new_state_eqs:\n";
            List.iter (fun t -> Printf.printf "    %s\n" (string_of_thm t)) new_state_eqs
          end);
          MAP_EVERY ASSUME_TAC (new_state_eqs_norewrite @ new_state_eqs) (asl,g)
        else
          (Printf.printf "State number %d: length mismatch: %d <> %d\n"
            n (List.length new_state_eqs) (List.length abbrevs_for_st_n);
          Printf.printf "  new state eq:\n";
          List.iter (fun t -> Printf.printf "    %s\n" (string_of_term (concl t))) new_state_eqs;
          Printf.printf "  old state eq:\n";
          List.iter (fun (_,t) -> Printf.printf "    %s\n" (string_of_term (concl t))) abbrevs_for_st_n;
          failwith "ARM_STEPS'_AND_REWRITE_TAC")) THEN CLARIFY_TAC)
    snums THEN
  RECOVER_ASMS_OF_READ_STATES THEN
  CLARIFY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Tactics that do not perform symbolic execution but are necessary to       *)
(* initiate/finalize program equivalence proofs.                             *)
(* ------------------------------------------------------------------------- *)

(* An ad-hoc tactic for proving a goal
    `read c1 s = .. /\ read c2 s = .. /\ ...`. This also accepts
   a clause which is a predicate 'aligned_bytes_loaded'.
   Clauses which cannot not be proven with this tactic will remain as a goal. *)
let PROVE_CONJ_OF_EQ_READS_TAC execth =
  REPEAT CONJ_TAC THEN
  let main_tac =
    (* for register updates *)
    (REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN
      (REFL_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC))) ORELSE
    (* for register updates, with rhses abbreviated *)
    (EXPAND_RHS_TAC THEN REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN REFL_TAC)
    ORELSE
    (* for memory updates *)
    (ASM_REWRITE_TAC[aligned_bytes_loaded;bytes_loaded] THEN
      (EXPAND_RHS_TAC THEN
       ((REWRITE_TAC[LENGTH_APPEND;fst execth;BARRIER_INST_BYTES_LENGTH;
                     PAIR_EQ;BIGNUM_FROM_MEMORY_BYTES] THEN
         REPEAT CONJ_TAC THEN READ_OVER_WRITE_ORTHOGONAL_TAC) ORELSE
        (* sometimes the rewrites are not necessary.. *)
        READ_OVER_WRITE_ORTHOGONAL_TAC))
      (* sometimes EXPAND_RHS_TAC is not necessary.. *)
      ORELSE
        (REWRITE_TAC[LENGTH_APPEND;fst execth;BARRIER_INST_BYTES_LENGTH;
                     PAIR_EQ;BIGNUM_FROM_MEMORY_BYTES] THEN
        REPEAT CONJ_TAC THEN READ_OVER_WRITE_ORTHOGONAL_TAC)) ORELSE
    (* for aligned_bytes_loaded *)
    (ASM_REWRITE_TAC[aligned_bytes_loaded;bytes_loaded] THEN
      (MATCH_MP_TAC READ_OVER_WRITE_MEMORY_APPEND_BYTELIST ORELSE
      MATCH_MP_TAC READ_OVER_WRITE_MEMORY_BYTELIST) THEN
      REWRITE_TAC[LENGTH_APPEND;fst execth;BARRIER_INST_BYTES_LENGTH] THEN
      ARITH_TAC) in
  TRY (main_tac ORELSE (MATCH_MP_TAC EQ_SYM THEN main_tac));;

(* Prove goals like
   `?pc. nonoverlapping_modulo (2 EXP 64) (pc,36) (val addr_out,32) /\
      nonoverlapping_modulo (2 EXP 64) (pc,36) (val addr_in,32) /\
      4 divides val (word pc)`
  by instantiating pc *)
let TRY_CONST_PC_TAC (pc:term):tactic =
  TRY (EXISTS_TAC pc THEN
    (* The last clause of conjunctions is '4 divides ...'. *)
    REWRITE_TAC[CONJ_ASSOC] THEN
    CONJ_TAC THENL [
      ALL_TAC;
      REWRITE_TAC[VAL_WORD;DIMINDEX_64;DIVIDES_DIV_MULT] THEN ARITH_TAC
    ] THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN ASM_ARITH_TAC);;

(* ts must be sorted *)
let rec SPLIT_RANGES_TAC (v:term) (ts:int list): tactic =
  let rec fn (v:term) (ts:int list) (prevth:thm option):tactic =
    begin match ts with
    | [] -> ALL_TAC
    | t::ts ->
      ASM_CASES_TAC (mk_binary "<" (v,mk_numeral (num t))) THENL
      [ ALL_TAC;
        W (fun (asl,g) ->
          (match prevth with
          | Some prevth -> UNDISCH_THEN (concl prevth) (K ALL_TAC)
          | None -> ALL_TAC) THEN
          let prevth0:thm ref = ref (EQ_REFL) in
          POP_ASSUM (fun th_save ->
            let th_save = REWRITE_RULE [ARITH_RULE`!x k. ~(x < k) <=> k <= x`] th_save in
            prevth0 := th_save;
            ASSUME_TAC th_save) THEN
          (fun (asl,g) -> fn v ts (Some !prevth0) (asl,g))) ]
    end in
  fn v ts None;;

(* Prove goals like
   `?pc. nonoverlapping_modulo (2 EXP 64) (pc,36) (val addr_out,32) /\
      nonoverlapping_modulo (2 EXP 64) (pc,36) (val addr_in,32) /\
      4 divides val (word pc)`
  by finding a 'hole' from the memory layout which can place (pc,36). *)
let FIND_HOLE_TAC: tactic =
  CONV_TAC (ONCE_DEPTH_CONV (NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  fun (asl,g) ->
    (* Sanity-check the goal *)
    let pcvar, goal_body = dest_exists g in
    let goal_conjs = conjuncts goal_body in
    let terms_nonoverlap, term_divides = (butlast goal_conjs, last goal_conjs) in
    if fst (strip_comb term_divides) <> `divides`
    then failwith ("Not 'divides' predicate: " ^ (string_of_term term_divides)) else
    let ranges:(term*int) list = List.concat_map
      (fun t ->
        let tt,ranges = strip_comb t in
        if tt <> `nonoverlapping_modulo` then
          failwith ("Not 'nonoverlapping_modulo' predicate: " ^ (string_of_term t))
        else
          let dest_range (ti:term) =
            if not (is_pair ti)
            then failwith ("Not a pair: " ^ (string_of_term ti)) else
            let ptr,size = dest_pair ti in
            if not (is_numeral size)
            then failwith ("Has non-constant size: " ^ (string_of_term t)) else
            (ptr, dest_small_numeral size) in
          List.map dest_range (List.tl ranges))
      terms_nonoverlap in
    let ranges = uniq (sort (<) ranges) in
    Printf.printf "Aggregated ranges: %s\n"
      (String.concat ", " (List.map
        (fun (t,n) -> Printf.sprintf "(%s,%d)" (string_of_term t) n) ranges));
    (* prepare val X < 2 EXP 64 *)
    let val_word_ptrs = List.map fst (List.filter
      (fun (t,_) -> fst (strip_comb t) = `val:int64 -> num`)
      ranges) in
    let word_ptrs = List.map (fun t -> snd (dest_comb t)) val_word_ptrs in
    Printf.printf "Base pointers (except PC): %s\n"
      (String.concat ", " (List.map string_of_term word_ptrs));
    let val_bound_prepare_tac =
      MAP_EVERY (fun t -> ASSUME_TAC (SPEC t VAL_BOUND_64)) word_ptrs in
    (* Now prepare case split. *)
    let segsize = List.fold_left (+) 0 (List.map snd ranges) in
    let maxlen = List.fold_left max 0 (List.map snd
      (List.filter (fun (t,n) -> t <> pcvar) ranges)) in
    Printf.printf "segsize: %d, maxlen: %d\n%!\n" segsize maxlen;

    (* MAP_EVERY (fun (v:term) ->
        ASM_CASES_TAC (mk_binary "<" (v,mk_numeral (num segsize))) THEN
        ASM_CASES_TAC (mk_binary "<" (v,mk_numeral (num (2*segsize)))))
        [`val (addr_in:int64)`;`val (addr_out:int64)`] *)
    let cases_tac = MAP_EVERY (fun (v:term) ->
        SPLIT_RANGES_TAC v
          (List.map (fun i -> i * segsize) (1--(List.length word_ptrs))))
      val_word_ptrs in

    (* Invoke TRY_CONST_PC_TAC to try each hole. *)
    let try_holes = List.fold_left then_ ALL_TAC
        (List.map
          (fun i -> TRY_CONST_PC_TAC (mk_numeral (num (i * segsize + maxlen))))
          (0--(List.length word_ptrs))) in

    ((val_bound_prepare_tac THEN
      cases_tac THEN
      try_holes THEN
      PRINT_GOAL_TAC THEN NO_TAC)
      ORELSE FAIL_TAC "Has unresolved goals") (asl,g);;


(* ------------------------------------------------------------------------- *)
(* Functions that convert a specification term of theorem into a different   *)
(* form.                                                                     *)
(* ------------------------------------------------------------------------- *)

let to_ensures_n (ensures_form:term) (numsteps_fn:term): term =
  let g = ensures_form in
  let g_quants,g_imp = strip_forall g in
  let g_asms,g_ensures = dest_imp g_imp in
  let g_ensures,g_ensures_frame = dest_comb g_ensures in
  let g_ensures,g_ensures_post = dest_comb g_ensures in
  let _,g_ensures_pre = dest_comb g_ensures in
  let g_ensures_n = subst [g_ensures_pre,`P:armstate->bool`;
          g_ensures_post,`Q:armstate->bool`;
          g_ensures_frame,`Fr:armstate->armstate->bool`;
          numsteps_fn,`fn:armstate->num`]
        `ensures_n arm P Q Fr fn` in
  list_mk_forall (g_quants,mk_imp(g_asms,g_ensures_n));;

(* prove_correct_barrier_appended replaces `core_mc` with
   `APPEND core_mc barrier_inst_bytes` inside assumption and precond.

   This is a method to prove the ensures predicate with the
   barrier_inst_bytes-appended version without manipulating its proof.
   This uses ENSURES_SUBLEMMA_THM.
   If barrier_inst_bytes was not appended, but inserted inside the program,
   then this approach cannot be used because implication between two
   preconditions will not hold.
*)
let prove_correct_barrier_appended (correct_th:thm) core_exec_th: thm =
  (* core_exec_th = `LENGTH core_mc = ..`, an array of arm_decodes *)
  let core_mc = snd (dest_comb (fst (dest_eq (concl (fst core_exec_th))))) in
  let core_mc_with_barrier =
    mk_binop `APPEND:((8)word)list->((8)word)list->((8)word)list`
             core_mc `barrier_inst_bytes` in
  let update_ensures (t:term):term =
    let pred,args = strip_comb t in
    if name_of pred <> "ensures" then failwith "prove_correct_barrier_appended" else
    let arg_step::arg_pre::arg_post::arg_frame::[] = args in
    list_mk_comb (pred,
      [arg_step; subst [core_mc_with_barrier,core_mc] arg_pre; arg_post; arg_frame])
    in
  let update_imp_ensures (g:term):term =
    if is_imp g then
      let lhs,rhs = dest_imp g in
      mk_imp (subst [core_mc_with_barrier,core_mc] lhs, update_ensures rhs)
    else
      update_ensures g
    in
  let goal =
    let g = concl correct_th in
    let args,g = strip_forall g in
    list_mk_forall (args, update_imp_ensures g)
    in
  prove(goal,
    REPEAT STRIP_TAC THEN

    MP_TAC (SPEC_ALL correct_th) THEN
    (* Prove antedecent of correct_th *)
    ANTS_TAC THENL [
      REPEAT (POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[ALL;NONOVERLAPPING_CLAUSES;LENGTH_APPEND;
                  BARRIER_INST_BYTES_LENGTH] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      (NONOVERLAPPING_TAC ORELSE
       (PRINT_TAC "prove_correct_barrier_appended failed" THEN
        PRINT_GOAL_TAC THEN NO_TAC));
      ALL_TAC
    ] THEN

    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
    REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [
      (* hyp. of aligned_bytes_loaded_append*)
      (let asm = subst [core_mc,`x:((8)word)list`] `4 divides LENGTH (x:((8)word)list)` in
      SUBGOAL_THEN asm ASSUME_TAC THENL [
        REWRITE_TAC[fst core_exec_th] THEN CONV_TAC NUM_DIVIDES_CONV;

        ALL_TAC
      ] THEN
      IMP_REWRITE_TAC[aligned_bytes_loaded_append] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      IMP_REWRITE_TAC(CONJUNCTS ALIGNED_BYTES_LOADED_SUB_LIST) THEN
      CONV_TAC NUM_DIVIDES_CONV);

      SUBSUMED_MAYCHANGE_TAC;

      MESON_TAC[]
    ]);;

let prove_correct_n execth core_execth (correct_th:thm)
                    (event_n_at_pc_th:thm): thm =
  let correct_th = prove_correct_barrier_appended correct_th core_execth in
  let to_eventually_th = REWRITE_RULE [fst execth;fst core_execth] event_n_at_pc_th in
  let to_eventually_th = CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) to_eventually_th in
  let to_eventually_th = REWRITE_RULE[
      eventually_n_at_pc;
      TAUT `(P==>(!x. Q x)) <=> (!x. P==>Q x)`;
      TAUT`(PRECOND==>(P==>Q==>R))<=>(PRECOND/\P/\Q==>R)`]
    to_eventually_th in
  (* unfold LENGTH mc and LENGTH (APPEND .. )) *)
  let eventually_form =
    (CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) o
     REWRITE_RULE[fst execth;fst core_execth;LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH]) correct_th in
  let eventually_form = REWRITE_RULE[
      ensures;
      TAUT `(P==>(!x. Q x)) <=> (!x. P==>Q x)`;
      TAUT`(P==>Q==>R)<=>(P/\Q==>R)`;
      GSYM CONJ_ASSOC] eventually_form in
  let nsteps =
    let body = snd (strip_forall (concl event_n_at_pc_th)) in
    let body = if is_imp body then snd (dest_imp body) else body in
    let pred,args = strip_comb body in
    if pred <> `eventually_n_at_pc`
    then failwith "eventually_n_at_pc expected"
    else List.nth args 4 in
  let numsteps_fn = mk_abs (`s:armstate`,nsteps) in
  prove(to_ensures_n (concl correct_th) numsteps_fn,
    (* Reduce the step function, and LENGTH *. *)
    CONV_TAC (
      REWRITE_CONV[fst execth;fst core_execth;LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THENC
      ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    (* use eventually_n_at_pc *)
    REWRITE_TAC[ensures_n] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[fst execth;fst core_execth] THEN
    MATCH_MP_TAC to_eventually_th THEN
    (* Reduce the step function, and LENGTH *. *)
    CONV_TAC (
      REWRITE_CONV[fst execth;fst core_execth;LENGTH_APPEND;BARRIER_INST_BYTES_LENGTH] THENC
      ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    (ASM_MESON_TAC[ALL;NONOVERLAPPING_CLAUSES;NONOVERLAPPING_MODULO_SYM;
                   eventually_form] ORELSE
    (PRINT_TAC ("ASM_MESON could not prove this goal. eventually_form: `" ^
        (string_of_thm eventually_form) ^ "`") THEN
     PRINT_GOAL_TAC THEN NO_TAC)));;


(* ------------------------------------------------------------------------- *)
(* Tactics for simulating a program when the goal to prove is                *)
(* created by mk_eventually_n_at_pc_statement.                               *)
(* ------------------------------------------------------------------------- *)

(* Given a goal with conclusion `steps arm 0 s s' ==> G`, remove lhs and
   replace s' with s in G. *)
let SIMPLIFY_STEPS_0_TAC: tactic =
  DISCH_THEN (fun th ->
    REWRITE_TAC[GSYM(REWRITE_RULE[STEPS_TRIVIAL] th)]);;

(* Take the name of a hypothesis which is 'arm s s2', and expand it to
   'write ... s = s2' and apply thm tactic *)
let EXPAND_ARM_THEN (h_arm_hyp:string) exec_decode_th (ttac:thm->tactic):tactic =
  REMOVE_THEN h_arm_hyp (fun th ->
    (fun (asl,g) ->
      let r = ONCE_REWRITE_RULE[ARM_CONV exec_decode_th (map snd asl) (concl th)] in
      ttac (r th) (asl,g)));;

let EXPAND_ARM_AND_UPDATE_READS_TAC (h_arm_hyp:string)
    exec_decode_th (exec_decode_len:thm):tactic =
  EXPAND_ARM_THEN h_arm_hyp exec_decode_th MP_TAC THEN
  (* Now we have state-updating writes at antedecendent of the goal. *)
  (* Mimic what ARM_STEP_TAC does from an analogous situation. *)
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP aligned_bytes_loaded_update exec_decode_len) THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP aligned_bytes_loaded_update BARRIER_INST_BYTES_LENGTH) THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  (* No need to update the MAYCHANGE predicate. *)
  (* Reconstruct 'read .. = ..'. The discharged assumption is
     'write .. (write ..) = s'. *)
  DISCH_THEN (fun th ->
    let ths = STATE_UPDATE_NEW_RULE th in
    MP_TAC(end_itlist CONJ ths) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    STRIP_TAC);;

(*   `read PC s{k} = word (pc + {pc_cur_ofs})
      -----
      eventually arm (\s'. read PC s' = word (pc + {pc_end_ofs}) /\ P s{k} s')
                 s{k}
      ==> steps arm {n-k} s{k} s' ==> P s{k} s'`
  -->
     `read PC s{k} = word (pc + {pc_cur_ofs})
      -----
      eventually arm (\s'. read PC s' = word (pc + {pc_end_ofs}) /\ P s{k+1} s')
                s{k+1}
      ==> steps arm {n-k-1} s{k+1} s' ==> P s{k+1} s'`

  arm_print_log := true prints more info.
  *)
let word_simp_lemmas = map WORD_RULE
  [`(word (x+y):int64 = word (x+z)) <=> (word y:int64 = word z)`;
    `(word x:int64 = word (x+z)) <=> (word 0:int64 = word z)`;
    `(word (x+z):int64 = word x) <=> (word z:int64 = word 0)`];;

let EVENTUALLY_TAKE_STEP_RIGHT_FORALL_TAC exec_decode (k:int):tactic =
  let exec_decode_len,exec_decode_th = exec_decode in
  (*let k4::k4p4::n4::nmk4::
      nmk::nmkmone4::nmkmone::kpcofs4::
      k4p4pcofs4::npcofs4::[] =
    List.map mk_small_numeral
       [k*4; (k+1)*4; n*4; (n-k)*4;
        n-k; (n-k-1)*4; n-k-1; pc_init_ofs+k*4;
        pc_init_ofs+(k+1)*4; pc_init_ofs+n*4] in
  let nmk_th = ARITH_RULE
    (subst [nmk,`nmk:num`;nmkmone,`nmkmone:num`] `nmk = 1 + nmkmone`) in

  let mk_lt (l:term) (r:term) =
    subst [l,`__l__:num`;r,`__r__:num`] `__l__ < __r__` in*)
  let next_st_var_name = "s" ^ (string_of_int (k+1)) in
  let next_st_var = mk_var (next_st_var_name,`:armstate`) in

  (fun (asl,g) ->
    (if k mod 50 = 0 then Printf.printf "Step %d\n%!" k);
    if !arm_print_log then
      (Printf.printf "<EVENTUALLY_TAKE_STEP_RIGHT_FORALL_TAC>\n";
      PRINT_GOAL_TAC (asl,g))
    else ALL_TAC (asl,g)) THEN
  ONCE_REWRITE_TAC[eventually_CASES] THEN
  (* Unfold steps N to steps (1+(N-1)). *)
  (fun (asl,w) ->
    (* x is `steps arm N s0 s_final` *)
    let x = lhand (rand w) in
    match x with
    | Comb (Comb (Comb (Comb(Const ("steps", _),
         Const ("arm", _)), the_N),_),_) ->
      let n = dest_small_numeral(the_N) in
      let r = ARITH_RULE(mk_eq(
        mk_small_numeral(n),
        mk_binary "+" (`1`,mk_small_numeral(n-1)))) in
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [r] (asl,w)
    | _ ->
      let _ = Printf.printf "Cannot find 'steps arm ..' from `%s`\n"
        (string_of_term w) in
      failwith "EVENTUALLY_TAKE_STEP_RIGHT_FORALL_TAC") THEN
  (* Fold PC mismatch to false *)
  ASM_REWRITE_TAC[] THEN
  (* `word (pc + X) = word (pc + Y) /\ P s0 s0 \/
      (?s'. arm s0 s') /\
      (!s'. arm s0 s' ==> eventually arm (\s'. ... ) s')
      ==> steps arm (1 + Z) s0 s_final
      ==> read PC s_final = word (pc + 616) /\ P s0 s_final`
    - target: `word (pc + X) = word (pc + Y)`  *)
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) word_simp_lemmas THEN
  CONV_TAC ((LAND_CONV o LAND_CONV o LAND_CONV) WORD_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[STEPS_STEP;STEPS_ONE] THEN

  (fun (asl,g) ->
    if !arm_print_log then
      (Printf.printf "<EVENTUALLY_TAKE_STEP_RIGHT_FORALL_TAC - after STEPS_STEP>\n";
      PRINT_GOAL_TAC (asl,g))
    else ALL_TAC (asl,g)) THEN
  DISCH_THEN (fun th ->
    try let _,th2 = CONJ_PAIR th in
      LABEL_TAC "HEVENTUALLY" th2
    with _ ->
      (Printf.printf "Not a conjunction: %s\n" (string_of_thm th);
      failwith "EVENTUALLY_TAKE_STEP_RIGHT_FORALL_TAC")) THEN
  DISCH_THEN (LABEL_TAC "HSTEPS") THEN
  (* If HSTEPS is `?s'. arm s s' /\ steps ...`, choose s'.
      Otherwise, it is `arm s s_final`; don't touch it *)
  TRY (X_CHOOSE_LABEL_TAC next_st_var "HSTEPS") THEN
  REMOVE_THEN "HSTEPS" (fun th ->
    if is_conj (concl th) then
      let th1,th2 = CONJ_PAIR th in
      LABEL_TAC "HARM" th1 THEN MP_TAC th2
    else LABEL_TAC "HARM" th) THEN
  REMOVE_THEN "HEVENTUALLY"
    (fun th -> USE_THEN "HARM" (fun th2 -> MP_TAC (MATCH_MP th th2))) THEN

  (fun (asl,g) ->
    if !arm_print_log then
      (Printf.printf "<EVENTUALLY_TAKE_STEP_RIGHT_FORALL_TAC - before updating reads>\n";
      PRINT_GOAL_TAC (asl,g))
    else ALL_TAC (asl,g)) THEN
  (* get explicit definition of the next step *)
  EXPAND_ARM_AND_UPDATE_READS_TAC "HARM" exec_decode_th exec_decode_len THEN
  DISCARD_OLDSTATE_TAC next_st_var_name;;

(*    `[ read PC sk = .. ]
       ------
       steps arm (n) sk s' ==> (?s''. arm s' s'')`
  -->
      `[ read PC sk+1 = .. ]
       ------
       steps arm (n-1) sk+1 s' ==> (?s''. arm s' s'') `

  n is either a constant or an expression '1+x'.
  *)
let EVENTUALLY_STEPS_EXISTS_STEP_TAC exec_decode (k:int): tactic =
  let exec_decode_len,exec_decode_th = exec_decode in
  let armstate_ty = `:armstate` and one = `1` in
  fun (asl,g) ->
    let lhs_steps,rhs = dest_imp g in
    let nterm = rand(rator(rator(lhs_steps))) in
    let snextname = "s" ^ (string_of_int (k+1)) in
    let snext = mk_var(snextname, armstate_ty) in
    let _ = if k mod 50 = 0 then Printf.printf "Step %d\n%!" (k+1) else () in

    ((if is_numeral nterm then
      let nminus1 = dest_small_numeral nterm - 1 in
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [
        GSYM (NUM_ADD_CONV (mk_binary "+" (one,mk_small_numeral(nminus1))))]
      else ALL_TAC) THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [STEPS_STEP] THEN
     (* deal with imp lhs: `?s''. arm sk s'' /\ steps arm (n-1) s'' s'` *)
     DISCH_THEN (X_CHOOSE_THEN snext
        (fun th -> let th_arm, th_steps = CONJ_PAIR th in
          LABEL_TAC "HARM" th_arm THEN
          MP_TAC th_steps)) THEN
     EXPAND_ARM_AND_UPDATE_READS_TAC "HARM" exec_decode_th exec_decode_len THEN
     DISCARD_OLDSTATE_TAC snextname
    )
    (asl,g);;


(* Prove `?s'. arm s s'`. *)
let SOLVE_EXISTS_ARM_TAC exec_decode_th: tactic =
  (fun (asl,g) ->
    let arm_term = snd (strip_exists g) in
    (ONCE_REWRITE_TAC[ARM_CONV exec_decode_th (map snd asl) arm_term])
    (asl,g)) THEN
  META_EXISTS_TAC THEN UNIFY_REFL_TAC;;
  (*MESON_TAC[];;*)

(* Prove:
  eventually arm (\s'. read PC s' = word (pc' + 1160) /\ P s0 s') s0
  ==> eventually_n arm n (\s'. read PC s' = word (pc' + 1160) /\ P s0 s') s0
*)
let PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC execth =
  let word_add_xy_th = WORD_RULE `word_add (word x) (word y):int64 = word (x+y)` and
      stuck_th = REWRITE_RULE[TAUT `(P/\Q/\R==>S) <=> (P==>Q==>R==>S)`]
        ALIGNED_BYTES_LOADED_BARRIER_ARM_STUCK and
      ath = ARITH_RULE`!x. 1+x<n ==> x<(n-1)` and
      ath2 = ARITH_RULE`SUC x=1+x` and
      numty = `:num` in

  W (fun (asl,w) ->
    (* get n from eventually_n's params. *)
    let x,ys = strip_comb (snd (dest_imp w)) in
    if not (is_const x) || (fst (dest_const x) <> "eventually_n" )
    then failwith "Unknown goal" else
    let nterm = List.nth ys 1 in
    if not (is_numeral nterm) then failwith "Unknown goal" else
    let n = dest_small_numeral nterm in
    let _ = Printf.printf "PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC: n: %d..\n" n in

    DISCH_THEN (LABEL_TAC "HEVENTUALLY") THEN
    REWRITE_TAC[eventually_n] THEN
    CONJ_TAC THENL [
      (** SUBGOAL 1 **)
      (* `!s'. steps arm .. s s' ==> P s s'` *)
      X_GEN_TAC `s_final:armstate` THEN UNDISCH_LABEL_TAC "HEVENTUALLY" THEN
      REPEAT_I_N 0 n
        (fun i -> EVENTUALLY_TAKE_STEP_RIGHT_FORALL_TAC execth i THEN CLARIFY_TAC) THEN
      (* match last step: utilize the barrier instruction *)
      ONCE_REWRITE_TAC[eventually_CASES] THEN
      ASM_REWRITE_TAC[STEPS_TRIVIAL] THEN
      (* prepare `~arm s<final> s` *)
      ((FIRST_X_ASSUM (fun th ->
         MP_TAC (MATCH_MP stuck_th (REWRITE_RULE [word_add_xy_th] th))) THEN
       DISCH_THEN (fun th -> FIRST_ASSUM (fun pcth ->
         ASM_REWRITE_TAC[MATCH_MP th pcth])) THEN
       ASM_MESON_TAC[]) ORELSE
       PRINT_GOAL_TAC THEN FAIL_TAC "PROVE_EVENTUALLY_IMPLIES_EVENTUALLY_N_TAC");

      (** SUBGOAL 2 **)
      ONCE_REWRITE_TAC[
        ITAUT`(!x y. P y /\ Q x y ==> R x y) <=> (!y. P y ==> !x. Q x y ==> R x y)`] THEN
      X_GEN_TAC `n0:num` THEN STRIP_TAC THEN GEN_TAC THEN
      REPEAT_I_N 0 n (fun i ->
        let n = mk_var("n" ^ (string_of_int i),numty) in
        let np1 = mk_var("n" ^ (string_of_int (i+1)),numty) in
        DISJ_CASES_THEN2
          SUBST1_TAC
          (X_CHOOSE_THEN np1
            (fun th -> SUBST_ALL_TAC (REWRITE_RULE[ath2] th)))
          (SPEC n num_CASES) THENL [
          (** SUBGOAL 1 **)
          SIMPLIFY_STEPS_0_TAC THEN
          SOLVE_EXISTS_ARM_TAC (snd execth);

          (** SUBGOAL 2 **)
          EVENTUALLY_STEPS_EXISTS_STEP_TAC execth i THEN
          FIRST_X_ASSUM (fun th ->
            let res = MATCH_MP ath th in
            ASSUME_TAC (CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) res))
        ] THEN CLARIFY_TAC) THEN
      ASM_ARITH_TAC (* last is: 'n < 0' *)
    ]);;


(* ------------------------------------------------------------------------- *)
(* Functions that create statements that are related to program equivalence. *)
(* ------------------------------------------------------------------------- *)

let mk_eventually_n_at_pc_statement
    (assum:term) (quants:term list) (mc:thm)
    (pc_from:term) (pc_to:term) (nsteps:term) (s0_pred:term) =
  let mc_barrier = mk_binop
    `APPEND:((8)word)list->((8)word)list->((8)word)list`
    (lhs(concl mc)) `barrier_inst_bytes` in
  let body = list_mk_comb
    (`eventually_n_at_pc`,[`pc:num`;mc_barrier;pc_from;pc_to;nsteps;s0_pred]) in
  list_mk_forall (`pc:num`::quants, (mk_imp (assum,body)));;


(* mk_eventually_n_at_pc_statement for a straight line code mc,
   running from its begin to end. *)
let mk_eventually_n_at_pc_statement_simple
    (assum:term) (quants:term list) (mc:thm) (s0_pred:term) =
  let mk_pc ofs =
    if ofs = 0 then `pc:num`
    else mk_binary "+" (`pc:num`,mk_small_numeral ofs) in
  let pc_from = mk_pc 0 in
  let nbytes = get_bytelist_length(rhs(concl mc)) in
  let pc_to = mk_pc nbytes in
  let nsteps = mk_small_numeral(nbytes / 4) in
  mk_eventually_n_at_pc_statement assum quants mc pc_from pc_to nsteps
    s0_pred;;


(* mk_equiv_statement creates a term
   `!pc pc2 <other quantifiers>.
      assum ==> ensures2 arm
        (\(s,s2). aligned_bytes_loaded s (word pc) mc1 /\
                  read PC s = word (pc+pc_ofs1) /\
                  aligned_bytes_loaded s2 (word pc2) mc2 /\
                  read PC s2 = word (pc2+pc_ofs2) /\
                  equiv_in (s,s2))
        (\(s,s2). aligned_bytes_loaded s (word pc) mc1 /\
                  read PC s = word (pc+pc_ofs1_to) /\
                  aligned_bytes_loaded s2 (word pc2) mc2 /\
                  read PC s2 = word (pc2+pc_ofs2_to) /\
                  equiv_out (s,s2))
        (\(s,s2) (s',s2'). maychange1 s s' /\ maychange2 s2 s2')
        fnsteps1
        fnsteps2`
*)
let mk_equiv_statement (assum:term) (equiv_in:thm) (equiv_out:thm)
    (mc1:thm) (pc_ofs1:int) (pc_ofs1_to:int) (maychange1:term)
    (mc2:thm) (pc_ofs2:int) (pc_ofs2_to:int) (maychange2:term)
    (fnsteps1:term) (fnsteps2:term):term =
  let _ = List.map2 type_check
      [assum;maychange1;maychange2]
      [`:bool`;`:armstate->armstate->bool`;`:armstate->armstate->bool`] in
  let quants_in,equiv_in_body = strip_forall (concl equiv_in) in
  let quants_out,equiv_out_body = strip_forall (concl equiv_out) in
  let _ = if !arm_print_log then
    Printf.printf "quants_in: %s\nquants_out: %s\n%!"
      (String.concat ", " (List.map string_of_term quants_in))
      (String.concat ", " (List.map string_of_term quants_out)) in
  (* equiv_in and equiv_out's first two universal quantifiers must be armstates. *)
  let quants_in_states,quants_in = takedrop 2 quants_in in
  let quants_out_states,quants_out = takedrop 2 quants_out in
  let _ = List.map2 type_check
    (quants_in_states @ quants_out_states)
    [`:armstate`;`:armstate`;`:armstate`;`:armstate`] in
  let quants = union quants_in quants_out in
  let quants = [`pc:num`;`pc2:num`] @ quants in
  (* There might be more free variables in 'assum'. Let's add them too. *)
  let quants = quants @
    (List.filter (fun t -> not (mem t quants)) (frees assum)) in
  let _ = if !arm_print_log then
    Printf.printf "quantifiers: %s\n%!" (String.concat ", "
      (List.map string_of_term quants)) in

  (* Now build 'ensures2' *)
  let mk_aligned_bytes_loaded (s:term) (pc_var:term) (mc:term) =
    let _ = List.map2 type_check [s;pc_var;mc] [`:armstate`;`:num`;`:((8)word)list`] in
    let template = `aligned_bytes_loaded s (word pc) mc` in
    subst [s,`s:armstate`;mc,`mc:((8)word)list`;pc_var,`pc:num`] template
  in
  let mk_read_pc (s:term) (pc_var:term) (pc_ofs:int):term =
    let _ = List.map2 type_check [s;pc_var] [`:armstate`;`:num`] in
    if pc_ofs = 0 then
      let template = `read PC s = word pc` in
      subst [s,`s:armstate`;pc_var,`pc:num`] template
    else
      let template = `read PC s = word (pc+pc_ofs)` in
      subst [s,`s:armstate`;pc_var,`pc:num`;mk_small_numeral(pc_ofs),`pc_ofs:num`]
            template
  in
  let s = `s:armstate` and s2 = `s2:armstate` in
  let pc = `pc:num` and pc2 = `pc2:num` in
  let equiv_in_pred = fst (strip_comb (fst (dest_eq equiv_in_body))) in
  let equiv_out_pred = fst (strip_comb (fst (dest_eq equiv_out_body))) in

  let precond = mk_gabs (`(s:armstate,s2:armstate)`,
    (list_mk_conj [
      mk_aligned_bytes_loaded s pc (lhs (concl mc1));
      mk_read_pc s pc pc_ofs1;
      mk_aligned_bytes_loaded s2 pc2 (lhs (concl mc2));
      mk_read_pc s2 pc2 pc_ofs2;
      list_mk_comb (equiv_in_pred, (`(s:armstate,s2:armstate)`::quants_in))
    ])) in
  let postcond = mk_gabs (`(s:armstate,s2:armstate)`,
    (list_mk_conj [
      mk_aligned_bytes_loaded s pc (lhs (concl mc1));
      mk_read_pc s pc pc_ofs1_to;
      mk_aligned_bytes_loaded s2 pc2 (lhs (concl mc2));
      mk_read_pc s2 pc2 pc_ofs2_to;
      list_mk_comb (equiv_out_pred, (`(s:armstate,s2:armstate)`::quants_out))
    ])) in
  let maychange = list_mk_gabs (
    [`(s:armstate,s2:armstate)`;`(s':armstate,s2':armstate)`],
    mk_conj
      (list_mk_comb (maychange1,[`s:armstate`;`s':armstate`]),
       list_mk_comb (maychange2,[`s2:armstate`;`s2':armstate`]))) in

  let _ = List.iter (fun t -> Printf.printf "\t%s\n" (string_of_term t))
    [precond;postcond;maychange;fnsteps1;fnsteps2] in
  let ensures2_pred = list_mk_comb
    (`ensures2:
      (armstate->armstate->bool)->(armstate#armstate->bool)
      ->(armstate#armstate->bool)
      ->(armstate#armstate->armstate#armstate->bool)
      ->(armstate->num)->(armstate->num)->bool`,
     [`arm`;precond;postcond;maychange;fnsteps1;fnsteps2]) in
  let imp = mk_imp (assum,ensures2_pred) in
  list_mk_forall (quants, imp);;

(* Program equivalence between two straight-line programs,
   starting from its begin to end. *)
let mk_equiv_statement_simple (assum:term) (equiv_in:thm) (equiv_out:thm)
    (mc1:thm) (maychange1:term)
    (mc2:thm) (maychange2:term):term =
  let mc1_length = get_bytelist_length (rhs (concl mc1)) in
  let mc2_length = get_bytelist_length (rhs (concl mc2)) in
  mk_equiv_statement assum equiv_in equiv_out
    mc1 0 mc1_length maychange1
    mc2 0 mc2_length maychange2
    (mk_abs (`s:armstate`,mk_small_numeral(mc1_length / 4)))
    (mk_abs (`s:armstate`,mk_small_numeral(mc2_length / 4)));;


(* ------------------------------------------------------------------------- *)
(* Tactics for high-level reasoning on program equivalence.                  *)
(* ------------------------------------------------------------------------- *)

(* Given two program equivalences, say 'equiv1 p1 p2' and 'equiv2 p2 p3',
   prove 'equiv p1 p3'. *)

let EQUIV_TRANS_TAC
    (equiv1_th,equiv2_th)
    (eq_in_state_th,eq_out_state_trans_th)
    (P1_EXEC,P2_EXEC,P3_EXEC) =
  let p2_mc =
    let len_p2_mc = fst (dest_eq (concl (fst P2_EXEC))) in
    snd (dest_comb len_p2_mc) in
  let interm_state =
    subst [p2_mc,`p2_mc:((8)word)list`]
      `write (memory :> bytelist (word pc3,LENGTH (p2_mc:((8)word)list)))
             p2_mc (write PC (word pc3) s')`
    and eq_in_const =
      let def = fst (dest_eq (snd (strip_forall (concl eq_in_state_th)))) in
      fst (strip_comb def) in

  ENSURES2_TRANS_TAC equiv1_th equiv2_th THEN

  (* break 'ALL nonoverlapping' in assumptions *)
  RULE_ASSUM_TAC (REWRITE_RULE[
      ALLPAIRS;ALL;fst P1_EXEC;fst P2_EXEC;fst P3_EXEC;NONOVERLAPPING_CLAUSES]) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN

  MATCH_MP_TAC ENSURES2_WEAKEN THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(p /\ q /\ r) /\ p /\ q /\ r' <=> p /\ q /\ r /\ r'`] THEN
    EXISTS_TAC interm_state THEN

    PROVE_CONJ_OF_EQ_READS_TAC P2_EXEC THENL [
      (* Undischarge `eq_in_state_th (s,s') (args..)`. *)
      FIRST_ASSUM (fun th ->
        if fst (strip_comb (concl th)) = eq_in_const
        then UNDISCH_TAC (concl th) else ALL_TAC) THEN
      REWRITE_TAC[eq_in_state_th;C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;fst P2_EXEC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT (TRY HINT_EXISTS_REFL_TAC THEN PROVE_CONJ_OF_EQ_READS_TAC P2_EXEC);

      FIRST_ASSUM (fun th ->
        if fst (strip_comb (concl th)) = eq_in_const
        then UNDISCH_TAC (concl th) else ALL_TAC) THEN
      REWRITE_TAC[eq_in_state_th;C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;fst P2_EXEC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT (TRY HINT_EXISTS_REFL_TAC THEN PROVE_CONJ_OF_EQ_READS_TAC P2_EXEC);
    ];

    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[eq_out_state_trans_th];

    SUBSUMED_MAYCHANGE_TAC
  ];;

(* Given a goal `ensures ..` which is a spec of program p, generate a
   verification condition from two lemmas:
  1. equiv_th: a program equivalence theorem between p and another program p2
  2. correct_n_th: a specification of p2 in `ensures_n`.
  mc_length_ths is a list of LENGTH *_mc theorems for p1 and p2 used in equiv_th's
  hypotheses, specifically the nonoverlapping predicates.
  The result of tactic is conjunction of three clauses.
  If arm_print_log is set to true, it prints more info. *)
let VCGEN_EQUIV_TAC equiv_th correct_n_th mc_length_ths =
  let stepfn =
    let b = snd (strip_forall (concl equiv_th)) in
    let b = if is_imp b then snd (dest_imp b) else b in
    snd (dest_comb b) in
  if type_of stepfn <> `:armstate->num`
  then failwith ("Not a step function: " ^ (string_of_term stepfn)) else
  MATCH_MP_TAC ENSURES_N_ENSURES THEN
  EXISTS_TAC stepfn THEN
  (* Prepare a 'conjunction' of SPEC and EQUIV *)
  MP_TAC (
      let ensures_n_part = SPEC_ALL correct_n_th in
      let equiv_part = SPEC_ALL equiv_th in
      let conj_ensures_n_equiv = CONJ ensures_n_part equiv_part in
      MATCH_MP (TAUT`((P==>Q)/\(R==>S)) ==> ((P/\R)==>(Q/\S))`) conj_ensures_n_equiv) THEN

  (* Try to prove the assumptions of equiv_th and
     correct_n_th, which are in ASSUM of
     (ASSUM ==> ensures_n) ==> ensures_n.
     If it could not be proven, it will be left as a subgoal of this tactic. *)
  W (fun (asl,g) ->
    if !arm_print_log then PRINT_GOAL_TAC
    else ALL_TAC) THEN

  let maintac =
    (* Conjunction of ensures2 and ensures_n *)
    DISCH_THEN (fun th -> LABEL_TAC "H"
      (REWRITE_RULE[] (MATCH_MP ENSURES_N_ENSURES2_CONJ th))) THEN
    (* .. and apply H as a precondition of ENSURES2_ENSURES_N *)
    REMOVE_THEN "H" (fun th ->
        let th2 = MATCH_MP
          (REWRITE_RULE [TAUT `(P/\P2/\P3==>Q) <=> P==>P2==>P3==>Q`] ENSURES2_ENSURES_N) th in
        MATCH_MP_TAC (REWRITE_RULE [TAUT`(P==>Q==>R) <=> (P/\Q==>R)`] th2)) THEN
    REWRITE_TAC[] in

  W (fun (asl,g) ->
    if is_imp g then
      let r = ([ALL;NONOVERLAPPING_CLAUSES;LENGTH_APPEND;
                BARRIER_INST_BYTES_LENGTH] @ mc_length_ths) in
      SUBGOAL_THEN (fst (dest_imp (fst (dest_imp g))))
          (fun th -> REWRITE_TAC[th]) THENL [
        (REWRITE_TAC r THEN RULE_ASSUM_TAC(REWRITE_RULE r) THEN
        REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC) ORELSE
        ALL_TAC (* Leave this as a subgoal *);

        maintac
      ]
    else maintac);;

(* From program equivalence between programs P1 and P2 as well as
   ensures_n spec of P1, prove ensures spec of P2. *)
let PROVE_ENSURES_FROM_EQUIV_AND_ENSURES_N_TAC
    equiv_th ensures_n_th (P1_EXEC,P2_EXEC) (eqin_th,eqout_th) =

  let p1_mc =
    let len_p1_mc = fst (dest_eq (concl (fst P1_EXEC))) in
    snd (dest_comb len_p1_mc) in
  let interm_state =
    subst [p1_mc,`p1_mc:((8)word)list`]
      `write (memory :> bytelist
          (word pc,LENGTH (APPEND p1_mc barrier_inst_bytes)))
          (APPEND p1_mc barrier_inst_bytes) (write PC (word pc) s2)` in

  VCGEN_EQUIV_TAC equiv_th ensures_n_th [fst P1_EXEC;fst P2_EXEC] THEN

  (* unfold definitions that may block tactics *)
  RULE_ASSUM_TAC (REWRITE_RULE[
      ALL; NONOVERLAPPING_CLAUSES; fst P1_EXEC; fst P2_EXEC]) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES] THEN
  REPEAT CONJ_TAC THENL [
    (** SUBGOAL 1. Precond **)
    X_GEN_TAC `s2:armstate` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `4 divides val (word pc2:int64)` ASSUME_TAC THENL
    [ FIRST_ASSUM (fun th ->
        MP_TAC th THEN REWRITE_TAC[DIVIDES_4_VAL_WORD_64;aligned_bytes_loaded_word]
        THEN METIS_TAC[]) THEN NO_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[eqin_th;C_ARGUMENTS] THEN
    EXISTS_TAC interm_state THEN
    (* Expand variables appearing in the equiv relation *)
    REPEAT CONJ_TAC THEN
    TRY (PROVE_CONJ_OF_EQ_READS_TAC P1_EXEC) THEN
    (* Now has only one subgoal: the equivalence! *)
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REPEAT (TRY HINT_EXISTS_REFL_TAC THEN
      CHANGED_TAC (PROVE_CONJ_OF_EQ_READS_TAC P1_EXEC));

    (** SUBGOAL 2. Postcond **)
    MESON_TAC[eqout_th;BIGNUM_FROM_MEMORY_BYTES;fst P2_EXEC];

    (** SUBGOAL 3. Frame **)
    MESON_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;MODIFIABLE_SIMD_REGS]
  ];;

(* ------------------------------------------------------------------------- *)
(* Load convenient OCaml functions for merging two lists of actions which    *)
(* are obtained from diff(file1, file2) and diff(file2, file3).              *)
(* ------------------------------------------------------------------------- *)

needs "common/actions_merger.ml";;
