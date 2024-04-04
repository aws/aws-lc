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
let PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM =
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
  DISCH_THEN PROPAGATE_DIGIT_EQS_FROM_EXPANDED_BIGNUM THEN
  REPEAT CONJ_TAC THEN REFL_TAC);;

(* A simple tactic that introduces `steps arm 0 stname stname` as an
   assumption. *)
let ASSUME_STEPS_ID stname =
  let stvar = mk_var (stname, `:armstate`) in
  SUBGOAL_THEN (subst [stvar,`s:armstate`] `steps arm 0 s s`) ASSUME_TAC THENL
  [REWRITE_TAC[STEPS_TRIVIAL];ALL_TAC];;

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


(* Assumption stash/recovery tactic. *)
let left_prog_state_asms: (string * thm) list ref = ref [];;

let STASH_ASMS_OF_READ_STATES (stnames:string list): tactic =
  fun (asl,g) ->
  let left_prog, others = List.partition (fun (name,th) ->
    let c = concl th in
    try let _,inst,_ = term_match [] `read e (s:armstate) = (r:A)` c in
      let itm = fst (List.find (fun (e,v) -> v = `s:armstate`) inst) in
      let stname = fst (dest_var itm) in
      List.exists (fun i -> i = stname) stnames
    with _ -> false) asl in
  left_prog_state_asms := left_prog;
  ALL_TAC (others,g);;

let RECOVER_ASMS_OF_READ_STATES: tactic =
  fun (asl,g) -> ALL_TAC (asl @ !left_prog_state_asms, g);;

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



(* Take the name of a hypothesis which is 'arm s s2', and expand it to
   'write ... s = s2' and apply thm tactic *)
let EXPAND_ARM_THEN (h_arm_hyp:string) (exec_decode_th:thm) (ttac:thm->tactic):tactic =
  REMOVE_THEN h_arm_hyp (fun th ->
      (fun (asl,g) ->
        let r = ONCE_REWRITE_RULE[ARM_CONV exec_decode_th (map snd asl) (concl th)] in
        ttac (r th) (asl,g)));;

let EXPAND_ARM_AND_UPDATE_BYTES_LOADED_TAC (h_arm_hyp:string)
    (exec_decode_th:thm) (exec_decode_len:thm):tactic =
  EXPAND_ARM_THEN h_arm_hyp exec_decode_th MP_TAC THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP aligned_bytes_loaded_update exec_decode_len) THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP aligned_bytes_loaded_update BARRIER_INST_BYTES_LENGTH) THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  DISCH_TAC;;

let PRINT_TAC (s:string): tactic =
  W (fun (asl,g) -> Printf.printf "%s\n" s; ALL_TAC);;

(*
  Add an assumption
    `read PC (next_st_var_name:armstate) = word (pc+next_pc_offset)`
  *)
let UPDATE_PC_TAC (pc_var_name:string) (next_st_var_name:string) (next_pc_offset:term):tactic =
  let next_st_var = mk_var(next_st_var_name, `:armstate`) and
      pc_var = mk_var(pc_var_name, `:num`) in
  SUBGOAL_THEN (subst [next_st_var,`next_st_var:armstate`;next_pc_offset,`k4p4:num`;
                       pc_var,`pc:num`]
      `read PC next_st_var = word (pc+k4p4)`)
      ASSUME_TAC THENL
  [(EXPAND_TAC next_st_var_name THEN REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN REFL_TAC)
   ORELSE PRINT_TAC "UPDATE_PC_TAC could not prove this goal" THEN PRINT_GOAL_TAC THEN NO_TAC; ALL_TAC];;

let find_pc_varname (asl:(string * thm)list) (stname:string): string =
  let st_var = mk_var (stname,`:armstate`) in
  let ls = List.map (fun (_,th) ->
      try
        let lhs,rhs = dest_eq(concl th) in
        let reg,st = dest_binary "read" lhs in
        if reg <> `PC` || st <> st_var then None
        else
          let theword,expr = dest_comb rhs in
          if theword <> `word:num->int64` then None
          else if is_var expr then Some (fst (dest_var expr))
          else try
            let lhs,rhs = dest_binary "+" expr in
            Some (fst (dest_var lhs))
          with _ ->
            (Printf.printf "Cannot understand `%s`" (string_of_term (concl th)); None)
      with _ -> None) asl in
  let (Some pcname)::[] = List.filter (fun t -> t <> None) ls in
  pcname;;

(*   `read PC s{k} = word (pc + {pc_init_ofs+4k})
      -----
      eventually arm (\s'. read PC s' = word (pc + {pc_init_ofs+4n}) /\ P s{k} s')
                 s{k}
      ==> steps arm {n-k} s{k} s' ==> P s{k} s'`
  -->
     `read PC s{k} = word (pc + {pc_init_ofs+4k})
      -----
      eventually arm (\s'. read PC s' = word (pc + {pc_init_ofs+4n}) /\ P s{k+1} s')
                s{k+1}
      ==> steps arm {n-k-1} s{k+1} s' ==> P s{k+1} s'`
  *)
let EVENTUALLY_TAKE_STEP_RIGHT_FORALL_TAC
    (exec_decode:thm) (init_st_var:term) (pc_init_ofs:int) (k:int) (n:int):tactic =
  let exec_decode_len,exec_decode_th = CONJ_PAIR exec_decode and
      k4::k4p4::n4::nmk4::nmk::nmkmone4::nmkmone::kpcofs4::k4p4pcofs4::npcofs4::[] =
    List.map (fun n -> mk_numeral (Int n))
       [k*4; (k+1)*4; n*4; (n-k)*4; n-k; (n-k-1)*4; n-k-1;
        pc_init_ofs+k*4;pc_init_ofs+(k+1)*4;pc_init_ofs+n*4] in
  let nmk_th = ARITH_RULE
    (subst [nmk,`nmk:num`;nmkmone,`nmkmone:num`] `nmk = 1 + nmkmone`) in

  let mk_lt (l:term) (r:term) =
    subst [l,`__l__:num`;r,`__r__:num`] `__l__ < __r__` in
  let next_st_var_name = "s" ^ (string_of_int (k+1)) in
  let next_st_var = mk_var (next_st_var_name,`:armstate`) in

  ONCE_REWRITE_TAC[eventually_CASES] THEN
  REWRITE_TAC[nmk_th] THEN
  (* PC mismatch *)
  ASM_SIMP_TAC[WORD64_NE_ADD;WORD64_NE_ADD2;
    ARITH_RULE(mk_lt kpcofs4 npcofs4);
    ARITH_RULE(mk_lt npcofs4 `2 EXP 64`)] THEN
  ONCE_REWRITE_TAC[STEPS_STEP;STEPS_ONE] THEN

  DISCH_THEN (fun th -> let _,th2 = CONJ_PAIR th in
      LABEL_TAC "HEVENTUALLY" th2) THEN
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

  (* get explicit definition of the next step *)
  EXPAND_ARM_AND_UPDATE_BYTES_LOADED_TAC "HARM" exec_decode_th exec_decode_len THEN
  W (fun (asl,g) ->
    (* Find the name of variable 'pc' from `read PC s = word (..pc..)` assumption *)
    let pcname = find_pc_varname asl ("s" ^ (string_of_int k)) in
    UPDATE_PC_TAC pcname (if k + 1 = n then "s_final" else next_st_var_name) k4p4pcofs4);;


(*    `[ read PC sk = .. ]
       ------
       steps arm (n) sk s' ==> (?s''. arm s' s'')`
  -->
      `[ read PC sk+1 = .. ]
       ------
       steps arm (n-1) sk+1 s' ==> (?s''. arm s' s'') `

  n is either a constant or an expression '1+x'.
  *)
let EVENTUALLY_STEPS_EXISTS_STEP_TAC (exec_decode:thm) (k:int) (next_pc_ofs:int): tactic =
  let exec_decode_len,exec_decode_th = CONJ_PAIR exec_decode in
  fun (asl,g) ->
    let lhs_steps,rhs = dest_imp g in
    let nterm = rand(rator(rator(lhs_steps))) in
    let snextname = "s" ^ (string_of_int (k+1)) in
    let snext = mk_var(snextname, `:armstate`) in
    let pcname = find_pc_varname asl ("s" ^ (string_of_int k)) in

    ((if is_numeral nterm then
      let nminus1 = (dest_numeral nterm) -/ (Num.Int 1) in
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [
        ARITH_RULE
        (mk_eq (nterm, mk_binary "+" (`1`, mk_numeral (nminus1))))]
      else ALL_TAC) THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [STEPS_STEP] THEN
     (* deal with imp lhs: `?s''. arm sk s'' /\ steps arm (n-1) s'' s'` *)
     DISCH_THEN (X_CHOOSE_THEN snext
        (fun th -> let th_arm, th_steps = CONJ_PAIR th in
          LABEL_TAC "HARM" th_arm THEN
          MP_TAC th_steps)) THEN
     EXPAND_ARM_AND_UPDATE_BYTES_LOADED_TAC "HARM" exec_decode_th exec_decode_len THEN
     UPDATE_PC_TAC pcname snextname (mk_numeral (Num.Int next_pc_ofs)) THEN
     DISCARD_OLDSTATE_TAC snextname
    )
    (asl,g);;

(* Given a goal with conclusion `steps arm 0 s s' ==> G`, remove lhs and replace s' with s in G. *)
let SIMPLIFY_STEPS_0_TAC: tactic =
  DISCH_THEN (fun th ->
    REWRITE_TAC[GSYM(REWRITE_RULE[STEPS_TRIVIAL] th)]);;

(* Prove `?s'. arm s s'`. *)
let SOLVE_EXISTS_ARM_TAC (exec_decode_th:thm): tactic =
  (fun (asl,g) ->
    let arm_term = snd (strip_exists g) in
    (ONCE_REWRITE_TAC[ARM_CONV exec_decode_th (map snd asl) arm_term])
    (asl,g)) THEN
  MESON_TAC[];;

(* A variant of ARM_BASIC_STEP_TAC, but
   - targets eventually_n
   - preserves 'arm s sname' at assumption *)
let ARM_BASIC_STEP'_TAC2 =
  let arm_tm = `arm` and arm_ty = `:armstate` in
  fun execth2 sname (asl,w) ->
    (* w = `eventually_n _ {stepn} _ {sv}` *)
    let sv = rand w and sv' = mk_var(sname,arm_ty) in
    let atm = mk_comb(mk_comb(arm_tm,sv),sv') in
    let eth = ARM_CONV execth2 (map snd asl) atm in
    let stepn = dest_numeral(rand(rator(rator w))) in
    let stepn_decr = stepn -/ Int 1 in
    (* stepn = 1+{stepn-1}*)
    let stepn_thm = ARITH_RULE(
      mk_eq(mk_numeral(stepn), mk_binary "+" (`1:num`,mk_numeral(stepn_decr)))) in
    (GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [stepn_thm] THEN
      GEN_REWRITE_TAC I [EVENTUALLY_N_STEP] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN
      DISCH_THEN (fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [eth]]) (asl,w);;

let rec filter_map f l =
  match l with
  | [] -> []
  | a::l ->
    begin match f a with
    | Some x -> x::(filter_map f l)
    | None -> filter_map f l
    end;;

(* Find `arm sprev sname` and `steps arm n s0 sprev`, and produce
   `steps arm (n+1) s0 sname` *)
let ARM_ELONGATE_STEPS:string->tactic =
  let arm_const = `arm` and arm_ty = `:armstate` in
  let steps_arm_term = `steps arm` in
  let sprev_term = mk_var("sprev", arm_ty) in
  let s0_term = mk_var("s0", arm_ty) in
  let n_term = mk_var("n", `:num`) in
  let find_mapped_term (i:instantiation) (v:term): term =
    let _,m,_ = i in
    try fst (find (fun (_,v') -> v=v') m) with _ -> v (* if v does not exist, v is mapped to itself! *) in

  fun (sname:string) (asl,g) ->
    let s = mk_var(sname,arm_ty) in
    let arm_term = mk_comb(mk_comb(arm_const,sprev_term),s) in
    (* 1. Find 'arm sprev s' where s is already given *)
    let arm_assums = filter_map (fun (_,assum) ->
      try
        let i:instantiation = term_match [s] arm_term (concl assum) in
        Some (find_mapped_term i sprev_term, assum)
      with _ -> None) asl in
    match arm_assums with
    | (sprev,arm_assum)::[] -> (* arm_assum is thm `arm sprev s` *)
      begin
      let steps_term = mk_comb(mk_comb(mk_comb(steps_arm_term,n_term),s0_term),sprev) in
      (* 2. Find 'steps arm n s0 sprev' where sprev is given *)
      let steps_assums = filter_map (fun (_,assum) ->
        try
          let i = term_match [sprev] steps_term (concl assum) in
          Some (find_mapped_term i n_term, find_mapped_term i s0_term, assum)
        with _ -> None) asl in
      match steps_assums with
      | (n,s0,steps_assum)::[] ->
        (* Make `steps arm (n+1) s0 s` *)
        let n' = mk_binary "+" (n,`1`) in
        (SUBGOAL_THEN (mk_comb(mk_comb(mk_comb(steps_arm_term,n'),s0),s)) MP_TAC THENL [
          REWRITE_TAC[STEPS_ADD] THEN
          DISCARD_ASSUMPTIONS_TAC (fun th -> not (free_in `arm` (concl th))) THEN
          ASM_MESON_TAC[STEPS_ONE];
          ALL_TAC
        ] THEN
        (* Evaluate n+1 *)
        GEN_REWRITE_TAC (ONCE_DEPTH_CONV o LAND_CONV) [NUM_REDUCE_CONV n'] THEN
        STRIP_TAC THEN
        (* Remove old `steps arm n s0 sprev` and old `arm sprev s` *)
        MAP_EVERY (fun th -> UNDISCH_THEN (concl th) (K ALL_TAC)) [steps_assum;arm_assum])
        (asl,g)
      | _ -> failwith
        (Printf.sprintf "Could not find `steps arm _ _ %s`" (string_of_term sprev))
      end
    | _ -> failwith
      (Printf.sprintf "Coud not find `arm _ %s`" sname);;

(* A variant of ARM_STEP_TAC for equivalence checking.
   If 'update' is Some ref, ref will be stored a conjunction of
   equalities over reads of the new state and values. *)
let ARM_STEP'_TAC (execth::subths) sname (store_update_to:thm ref option) =
  let execth1,execth2 = CONJ_PAIR execth in

  (*** This does the basic decoding setup ***)

  ARM_BASIC_STEP'_TAC2 execth2 sname THEN
  (* Elongate 'steps arm n ..' to 'steps arm (n+1) ..' *)
  ARM_ELONGATE_STEPS sname THEN

  (*** This part shows the code isn't self-modifying ***)

  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP aligned_bytes_loaded_update execth1) THEN

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
    ASSEMBLER_SIMPLIFY_TAC THEN
    (* At this point, the LHS of the implication of goal looks like this:
      `read X19 s1' = word ((val a' * val a''''') DIV 2 EXP 64) /\
       read PC s1' = word (pc2 + 136)
       ==> eventually_n ...`
      *)
    begin match store_update_to with
    | None -> ALL_TAC
    | Some r -> DISCH_THEN (fun th -> r := th; MP_TAC th)
    end THEN
    STRIP_TAC);;

(* A variant of DISCARD_OLDSTATE_TAC which receives a list of state names
   to preserve. *)
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
   W(fun (_,_) ->
    MAP_EVERY (fun (old_abbrev_var:term) ->
      fun (asl,g) ->
        (* If the old abbrev var is used by another 'read', don't remove it. *)
        if List.exists (fun _,asm ->
              let asm = concl asm in
              vfree_in old_abbrev_var asm && is_eq asm && is_read (fst (dest_eq asm)))
            asl then
          ALL_TAC (asl,g)
        else
          DISCARD_ASSUMPTIONS_TAC(fun thm -> vfree_in old_abbrev_var (concl thm)) (asl,g))
      !old_abbrevs));;

(* A variant of ARM_STEPS_TAC but using ARM_STEP'_TAC and DISCARD_OLDSTATE'_TAC instead. *)
let ARM_STEPS'_TAC th snums stname_suffix stnames_no_discard =
  let stnames = List.map (fun s -> s ^ stname_suffix) (statenames "s" snums) in
  MAP_EVERY (fun stname ->
    time (ARM_STEP'_TAC (th::[]) stname) None THEN
          DISCARD_OLDSTATE'_TAC (stname::stnames_no_discard) false)
          stnames;;

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


(* Given eq = `read c s = e`, abbreviate e as a fresh variable.
   Also, if there is another read `read c st' = e'`, try to
   solve `e' = e` using WORD_RULE and rewrite all e' with e in
   assumptions.
*)
let ABBREV_READ_RHS_TAC (eq:term) (st':term):tactic =
  W(fun (asl,g) ->
    if not (is_eq eq) then ALL_TAC else
    (* eq is: `read elem s = e` *)
    let lhs,rhs = dest_eq eq in
    (* If lhs is PC update, don't abbrevate it *)
    if (can (term_match [] `read PC s`) lhs) then ALL_TAC else
    (* If rhs is already a variable, don't abbreviate it again *)
    if is_var rhs then ALL_TAC else
    let vname = mk_fresh_temp_name() in
    Printf.printf "Abbreviating `%s` (which is `%s`) as \"%s\"..\n"
        (string_of_term rhs) (string_of_term lhs) vname;
    (* If `read elem s_left = e` does not appear in assumption,
        raise a warning because the lock-stepping instructions are
        not equivalent. *)
    let left_prog_read = mk_comb (fst (dest_comb lhs), st') in
    begin match (List.filter
        (fun (_,t') -> let tt = concl t' in is_eq tt && fst (dest_eq tt) = left_prog_read) asl) with
    | [] ->
      Printf.printf "\t- Warning: could not find `%s = *`\n" (string_of_term left_prog_read);
      ALL_TAC
    | h::[] ->
      let h = concl (snd h) in
      let hlhs,hrhs = dest_eq h in
      if hrhs <> rhs then
        try
          let r = WORD_RULE (mk_eq(hrhs,rhs)) in
          Printf.printf "\t- Abbreviating `%s` as \"%s\" as well\n"
              (string_of_term hrhs) vname;
          RULE_ASSUM_TAC (REWRITE_RULE[r])
        with _ ->
          Printf.printf "\t- Warning: could not find `%s = %s`, but `%s`\n"
            (string_of_term hlhs) (string_of_term rhs) (string_of_term h);
          ALL_TAC
      else ALL_TAC
    | _ ->
      Printf.printf "\t- Warning: found more than one `%s = *`\n"
        (string_of_term left_prog_read);
      ALL_TAC
    end THEN
    let fresh_var = mk_var (vname,type_of rhs) in
    ABBREV_TAC (mk_eq (fresh_var,rhs)));;

(* A lock-step simulation.
  This also abbreviates the new expressions appearing on the new state
  expressions of the right-side program, and forgets abbreviations that were
  used in the past. *)
let ARM_LOCKSTEP_TAC =
  let update_eqs_rhs: thm ref = ref (TAUT `T`) in
  fun (execth:thm) (execth':thm) (snum:int) (snum':int) (stname'_suffix:string) ->
    let new_stname = "s" ^ (string_of_int snum) in
    let new_st = mk_var (new_stname,`:armstate`) and
        new_stname' = "s" ^ (string_of_int snum') ^ stname'_suffix in
    (* 1. One step on the left program. *)
    (* Get the right program's current state name "s'" from
       `eventually_n arm n (\s. eventually_n arm n' .. s') s`,
       and stash assumptions over the right state. *)
    (fun (asl,g) ->
      (* Print log *)
      Printf.printf "ARM_LOCKSTEP_TAC (%d,%d)\n" snum snum';
      let cur_stname' = name_of (rand (snd ((dest_abs o rand o rator) g))) in
      STASH_ASMS_OF_READ_STATES [cur_stname'] (asl,g)) THEN
    ARM_STEP'_TAC (execth::[]) new_stname None THEN
    DISCARD_OLDSTATE'_TAC [new_stname] false THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    (* 2. One step on the right program. *)
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    STASH_ASMS_OF_READ_STATES [new_stname] THEN
    ARM_STEP'_TAC (execth'::[]) new_stname' (Some update_eqs_rhs) THEN
    DISCARD_OLDSTATE'_TAC [new_stname'] true(*remove assumptions using old abbrevs*) THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    (* 3. Abbreviate expressions that appear in the new state expressions
          created from step 2. *)
    W (fun (asl,g) ->
      MAP_EVERY
        (fun (eqth:thm) -> ABBREV_READ_RHS_TAC (concl eqth) new_st)
        (CONJUNCTS !update_eqs_rhs));;


let EQUIV_INITIATE_TAC input_equiv_states_th =
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  MAP_EVERY ASSUME_STEPS_ID ["s0";"s0'"] THEN
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

let ARM_STUTTER_LEFT_TAC (exec_th:thm) (snames:int list): tactic =
  W (fun (asl,g) ->
    (* get the state name of the 'right' program *)
    let t' = fst (dest_comb g) in
    let inner_eventually = snd (dest_abs (snd (dest_comb (t')))) in
    let sname = fst (dest_var (snd (dest_comb inner_eventually))) in
    STASH_ASMS_OF_READ_STATES [sname] THEN
    ARM_STEPS'_TAC exec_th snames "" [] THEN
    RECOVER_ASMS_OF_READ_STATES);;

let ARM_STUTTER_RIGHT_TAC (exec_th:thm) (snames:int list) (st_suffix:string): tactic =
  W (fun (asl,g) ->
    (* get the state name of the 'left' program *)
    let sname = fst (dest_var (snd (dest_comb g))) in
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    STASH_ASMS_OF_READ_STATES [sname] THEN
    ARM_STEPS'_TAC exec_th snames st_suffix [] THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP);;

let EQUIV_STEP_TAC action (execth1:thm) (execth2:thm): tactic =
  match action with
  | ("equal",lstart,lend,rstart,rend) ->
    assert (lend - lstart = rend - rstart);
    REPEAT_I_N 0 (lend - lstart)
      (fun i ->
        ARM_LOCKSTEP_TAC execth1 execth2 (lstart+1+i) (rstart+1+i) "'"
        THEN CLARIFY_TAC)
  | ("insert",lstart,lend,rstart,rend) ->
    if lstart <> lend then failwith "insert's lstart and lend must be equal"
    else ARM_STUTTER_RIGHT_TAC execth2 ((rstart+1)--rend) "'"
        ORELSE (PRINT_TAC "insert failed" THEN PRINT_GOAL_TAC THEN NO_TAC)
  | ("delete",lstart,lend,rstart,rend) ->
    if rstart <> rend then failwith "delete's rstart and rend must be equal"
    else ARM_STUTTER_LEFT_TAC execth1 ((lstart+1)--lend)
        ORELSE (PRINT_TAC "delete failed" THEN PRINT_GOAL_TAC THEN NO_TAC)
  | ("replace",lstart,lend,rstart,rend) ->
    ((ARM_STUTTER_LEFT_TAC execth1 ((lstart+1)--lend)
     ORELSE (PRINT_TAC "replace failed: stuttering left" THEN PRINT_GOAL_TAC THEN NO_TAC))
     THEN
     (ARM_STUTTER_RIGHT_TAC execth2 ((rstart+1)--rend) "'"
      ORELSE (PRINT_TAC "replace failed: stuttering right" THEN PRINT_GOAL_TAC THEN NO_TAC)))
  | (s,_,_,_,_) -> failwith ("Unknown action: " ^ s);;




let prove_correct_barrier_appended (correct_th:thm) (core_mc:term) (core_exec_th:thm): thm =
  let core_mc_with_barrier =
    mk_binop `APPEND:((8)word)list->((8)word)list->((8)word)list`
             core_mc `barrier_inst_bytes` in
  let goal = subst [core_mc_with_barrier,core_mc] (concl correct_th) in
  prove(goal,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP correct_th th)) THEN
    REWRITE_TAC[ensures] THEN
    DISCH_THEN (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    let asm = subst [core_mc,`x:((8)word)list`] `4 divides LENGTH (x:((8)word)list)` in
    SUBGOAL_THEN asm ASSUME_TAC THENL [
      (** SUBGOAL 1 **)
      REWRITE_TAC[core_exec_th] THEN CONV_TAC NUM_DIVIDES_CONV;

      (** SUBGOAL 2 **)
      ALL_TAC
    ] THEN
    ASM_MESON_TAC[aligned_bytes_loaded_append]);;

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

let prove_correct_n (execths:thm list) (correct_th:thm) (event_n_at_pc_th:thm) (numsteps_fn:term): thm =
  let to_eventually_th = REWRITE_RULE execths event_n_at_pc_th in
  let to_eventually_th = CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) to_eventually_th in
  let to_eventually_th = REWRITE_RULE[
      eventually_n_at_pc;
      TAUT `(P==>(!x. Q x)) <=> (!x. P==>Q x)`;
      TAUT`(PRECOND==>(P==>Q==>R))<=>(PRECOND/\P/\Q==>R)`]
    to_eventually_th in
  let eventually_form = CONV_RULE (ONCE_DEPTH_CONV NUM_REDUCE_CONV) correct_th in
  let eventually_form = REWRITE_RULE[
      ensures;
      TAUT `(P==>(!x. Q x)) <=> (!x. P==>Q x)`;
      TAUT`(P==>Q==>R)<=>(P/\Q==>R)`;
      GSYM CONJ_ASSOC] eventually_form in
  prove(to_ensures_n (concl correct_th) numsteps_fn,
    (* Reduce the step function *)
    CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    (* use eventually_n_at_pc *)
    REWRITE_TAC[ensures_n] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC to_eventually_th THEN
    (ASM_MESON_TAC[eventually_form] ORELSE
    (PRINT_TAC ("ASM_MESON could not prove this goal. eventually_form: `" ^
        (string_of_thm eventually_form) ^ "`") THEN
     PRINT_GOAL_TAC THEN NO_TAC)));;

(* Prove goals like
   `?pc. nonoverlapping_modulo (2 EXP 64) (pc,36) (val addr_out,32) /\
      nonoverlapping_modulo (2 EXP 64) (pc,36) (val addr_in,32) /\
      4 divides val (word pc)` *)
let TRY_CONST_PC_TAC (pc:term):tactic =
  TRY (EXISTS_TAC pc THEN
  REPEAT CONJ_TAC THEN
  TRY (MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN ASM_ARITH_TAC) THEN
  REWRITE_TAC[VAL_WORD;DIMINDEX_64;DIVIDES_DIV_MULT] THEN ARITH_TAC);;
