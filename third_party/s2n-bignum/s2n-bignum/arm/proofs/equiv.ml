(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reasoning program equivalence for Arm programs.                           *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/neon_helper.ml";;
needs "common/equiv.ml";;

prove_conj_of_eq_reads_unfold_rules :=
    aligned_bytes_loaded::!prove_conj_of_eq_reads_unfold_rules;;

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

(* returns true if t is `read events <state>`. *)
let is_read_events t =
  match t with
  | Comb (Comb (Const ("read", _), Const ("events", _)), _) -> true
  | _ -> false;;

let define_mc_from_intlist (newname:string) (ops:int list) =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)]) ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list newname (term_of_bytes byte_list);;

let DIVIDES_4_VAL_WORD_ADD_64 = prove(
  `!pc ofs. 4 divides val (word pc:int64) /\ 4 divides ofs ==>
      4 divides val (word (pc+ofs):int64)`,
  REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
  (let divth = REWRITE_RULE[EQ_CLAUSES] (NUM_DIVIDES_CONV `4 divides 2 EXP 64`) in
    REWRITE_TAC[GSYM (MATCH_MP DIVIDES_MOD2 divth)]) THEN
  IMP_REWRITE_TAC[DIVIDES_ADD]);;


let NONOVERLAPPING_APPEND = prove(`!(x:int64) (y:int64) code code2 n.
    nonoverlapping (x, LENGTH (APPEND code code2)) (y, n) ==>
    nonoverlapping (x, LENGTH code) (y, n)`,
  (* Converted by thenify.py *)
  REWRITE_TAC[LENGTH_APPEND;NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  NONOVERLAPPING_TAC);;

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


(* A convenient function that proves divisibility of an expression like
    `2 EXP 64` `2 EXP 128 * a + 2 EXP 192 * b + 2 EXP 256`
  with an exponential expression such as
    `2 EXP 64`.
*)

let DIVIDES_EXP_CONV (divisor:term) (dividend:term): thm =
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
          ("DIVIDES_EXP_CONV: Could not fully reduce; got `" ^
            (string_of_thm reduced_th) ^ "` instead")
      else ONCE_REWRITE_RULE [EQ_CLAUSES] reduced_th in
  fn divisor dividend;;

(* Tests *)
let _ = DIVIDES_EXP_CONV `2 EXP 64` `2 EXP 128`;;
let _ = DIVIDES_EXP_CONV `2 EXP 64` `2 EXP 128 * a`;;
let _ = DIVIDES_EXP_CONV `2 EXP 64` `2 EXP 128 * a + 2 EXP 64`;;
let _ = DIVIDES_EXP_CONV `2 EXP 64` `2 EXP 128 * a + 2 EXP 192 * b + 2 EXP 256`;;

(* A convenient function that simplifies division of an expression like
    `2 EXP 64` `2 EXP 128 * a + 2 EXP 192 * b + 2 EXP 256`
  with an exponential expression such as
    `2 EXP 64`.
*)

let DIV_EXP_REDUCE_CONV (dividend:term) (divisor:term):thm =
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
      let precond = DIVIDES_EXP_CONV divisor lhs in
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
        try DISJ1 (DIVIDES_EXP_CONV divisor lhs) (mk_binary "num_divides" (divisor,rhs))
        with _ -> try DISJ2 (mk_binary "num_divides" (divisor,lhs)) (DIVIDES_EXP_CONV divisor rhs)
        with _ -> failwith "Could not derive DIV_ADD's precond" in
      let expr = REWRITE_CONV[MATCH_MP DIV_ADD precond] expr in
      (* (lhs DIV divisor) + (rhs DIV divisor) = lhs' + rhs' *)
      REWRITE_RULE [lhs_eq;rhs_eq;simp_one] expr
    else failwith "Unknown dividend"
  in
  fn dividend divisor;;

let _ = DIV_EXP_REDUCE_CONV `2 EXP 128` `2 EXP 64`;;
let _ = DIV_EXP_REDUCE_CONV `2 EXP 128 + 2 EXP 64` `2 EXP 64`;;
let _ = DIV_EXP_REDUCE_CONV `2 EXP 128 * x` `2 EXP 64`;;
let _ = DIV_EXP_REDUCE_CONV `2 EXP 128 * x + 2 EXP 64 * y` `2 EXP 64`;;
let _ = DIV_EXP_REDUCE_CONV `2 EXP 192 * z + 2 EXP 128 * x + 2 EXP 64 * y` `2 EXP 64`;;

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
      let k_divided = DIVIDES_EXP_CONV `2 EXP 64` k in
      let k'_divided = DIVIDES_EXP_CONV `2 EXP 64` k' in
      let res = MATCH_MP (MATCH_MP pth (CONJ k_divided k'_divided)) th in
      let eq_a, eq_k = CONJ_PAIR res in
      (* let's divide eq_k with 2 EXP 64 *)
      let eq_k_div_2exp64 = MATCH_MP (SPEC `2 EXP 64` qth) eq_k in
      let eq_k_lhs,eq_k_rhs = dest_eq (concl eq_k) in
      (* .. and simplify it! *)
      let eq_k_div_2exp64 = REWRITE_RULE[
        DIV_EXP_REDUCE_CONV eq_k_lhs `2 EXP 64`;
        DIV_EXP_REDUCE_CONV eq_k_rhs `2 EXP 64`] eq_k_div_2exp64 in
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


get_memory_read_info `memory :> bytes64 x`;; (* Some (`x`,`8`,"bytes64") *)
get_memory_read_info `memory :> bytes128 x`;; (* Some (`x`,`16`,"bytes128") *)
get_memory_read_info `memory :> bytes (x, sz)`;; (* Some (`x`,`sz`,"bytes") *)
get_memory_read_info `X0`;; (* None *)


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

let ENSURES_AND_EVENTUALLY_N_AT_PC_PROVES_ENSURES_N = prove(
  `forall Pre pc_mc mc pc n.
    eventually_n_at_pc pc_mc mc pc pc2 n Pre
    ==> forall Post R.
      ensures arm
        (\s. aligned_bytes_loaded s (word pc_mc) mc /\ read PC s = word pc /\ Pre s)
        (\s. read PC s = word pc2 /\ Post s)
        R
      ==> ensures_n arm
        (\s. aligned_bytes_loaded s (word pc_mc) mc /\ read PC s = word pc /\ Pre s)
        (\s. read PC s = word pc2 /\ Post s)
        R (\s. n)`,

  REPEAT GEN_TAC THEN
  REWRITE_TAC[eventually_n_at_pc;ensures;ensures_n] THEN
  INTRO_TAC "H2" THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "H1" THEN
  GEN_TAC THEN INTRO_TAC "HA HB HC" THEN
  REMOVE_THEN "H1" (fun th -> MP_TAC (SPECL [`s:armstate`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (LABEL_TAC "H1") THEN
  REMOVE_THEN "H2" (fun th -> MP_TAC (SPECL [`s:armstate`;`(\(s:armstate) (s2:armstate). Post s2 /\ R s s2)`] th)) THEN
  ASM_REWRITE_TAC[]);;

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

prove_conj_of_eq_reads_unfold_rules :=
  BARRIER_INST_BYTES_LENGTH::!prove_conj_of_eq_reads_unfold_rules;;

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

(* A variant of ARM_BASIC_STEP_TAC, but
   - targets eventually_n
   - preserves 'arm s sname' at assumption *)
let ARM_N_BASIC_STEP_TAC =
  let arm_tm = `arm` and arm_ty = `:armstate` and one = `1:num` in
  fun decode_th sname store_inst_term_to (asl,w) ->
    (* w = `eventually_n _ {stepn} _ {sv}` *)
    let sv = rand w and sv' = mk_var(sname,arm_ty) in
    let atm = mk_comb(mk_comb(arm_tm,sv),sv') in
    let eth = ARM_CONV decode_th (map snd asl) atm in
    (* store the decoded instruction at store_inst_term_to *)
    (match store_inst_term_to with | Some r -> r := rhs (concl eth) | None -> ());
    let stepn = dest_numeral(rand(rator(rator w))) in
    let stepn_decr = stepn -/ num 1 in
    (* stepn = 1+{stepn-1}*)
    let stepn_thm = GSYM (NUM_ADD_CONV (mk_binary "+" (one,mk_numeral(stepn_decr)))) in
    (GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [stepn_thm] THEN
      GEN_REWRITE_TAC I [EVENTUALLY_N_STEP] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN
      (CONV_TAC EXISTS_NONTRIVIAL_CONV ORELSE
       (PRINT_GOAL_TAC THEN
        FAIL_TAC ("Equality between two states is ill-formed." ^
                  " Did you forget extra condition like pointer alignment?")));
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth]]) (asl,w);;



(* A variant of ARM_STEP_TAC for equivalence checking.

   If 'store_update_to' is Some ref, a list of
   (`read .. = expr`) will be stored instead of added as assumptions.
   It will store a pair of lists, where the first list is the output of
   the instruction in `read .. = expr` form, and the second list is
   auxiliary `read (memory :> reads...) = ..` equalities that were constructed
   in order to formulate the main output, not to formulate the instruction
   outputs.

   If store_inst_term_to is Some ref, store e.g., `arm_ADD _ _ _` to
   store_inst_term_to. *)
let ARM_N_STEP_TAC (mc_length_th,decode_th) subths sname
                  (store_update_to:(thm list * thm list) ref option)
                  (store_inst_term_to: term ref option) =
  (*** This does the basic decoding setup ***)

  ARM_N_BASIC_STEP_TAC decode_th sname store_inst_term_to THEN

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
    ASSEMBLER_SIMPLIFY_TAC THEN

    let has_auxmems = ref false in
    (** If there is an 'unsimplified' memory read on the right hand side,
        try to synthesize an expression using bigdigit and use it. **)
    DISCH_THEN (fun simplified_th (asl,w) ->
      let res_th,newmems_th = DIGITIZE_MEMORY_READS simplified_th th (asl,w) in
      (* MP_TAC res_th and newmems_th first, to drop their assumptions. *)
      (MP_TAC res_th THEN
      (match newmems_th with
       | None -> (has_auxmems := false; ALL_TAC)
       | Some ths -> (has_auxmems := true; MP_TAC ths))) (asl,w))
    THEN

    (* store it to a reference, or make them assumptions *)
    W (fun _ ->
      match store_update_to with
      | None -> STRIP_TAC THEN (if !has_auxmems then STRIP_TAC else ALL_TAC)
      | Some to_ref ->
        if !has_auxmems then
          DISCH_THEN (fun auxmems -> DISCH_THEN (fun res ->
            to_ref := (CONJUNCTS res, CONJUNCTS auxmems); ALL_TAC))
        else
          DISCH_THEN (fun res -> to_ref := (CONJUNCTS res, []); ALL_TAC)));;

(* Remove `read c s = ..` where c is a register containing a dead value. *)
let DISCARD_REGS_WITH_DEAD_VALUE_TAC (dead_regs:term list) =
  fun (asl,w) ->
    if dead_regs = [] then ALL_TAC (asl,w) else
    let asl = List.filter (fun (_,th) ->
        match (get_read_component (concl th)) with
        | None -> true
        | Some c ->
          if List.exists (fun dead_reg -> c = dead_reg) dead_regs
          then begin
            (if !arm_print_log then
              Printf.printf "- Discarding `%s` because it will not be used\n"
                  (string_of_term (concl th)));
            false
          end else true)
      asl in
    ALL_TAC (asl,w);;

(* A variant of ARM_STEPS_TAC but using ARM_N_STEP_TAC and DISCARD_OLDSTATE_AGGRESSIVELY_TAC instead.
   dead_value_info is an optional array that maps the step number - 1 to the dead
   registers. *)
let ARM_N_STEPS_TAC th snums stname_suffix stnames_no_discard dead_value_info =
  MAP_EVERY (fun s ->
      let stname = "s" ^ string_of_int s ^ stname_suffix in
      time (ARM_N_STEP_TAC th [] stname None) None THEN
      DISCARD_OLDSTATE_AGGRESSIVELY_TAC (stname::stnames_no_discard) false THEN
      begin match dead_value_info with
      | None -> ALL_TAC
      | Some arr -> DISCARD_REGS_WITH_DEAD_VALUE_TAC (arr.(s-1))
      end)
    snums;;

(* ------------------------------------------------------------------------- *)
(* Definitions for stating program equivalence.                              *)
(* ------------------------------------------------------------------------- *)

(* A recursive function for defining a conjunction of equality clauses *)
let mk_equiv_regs = define
  `((mk_equiv_regs:((armstate,(N)word)component)list->armstate#armstate->bool)
      [] s = true) /\
   (mk_equiv_regs (CONS reg regs) (s1,s2) =
     (mk_equiv_regs regs (s1,s2) /\
      exists (a:(N)word). read reg s1 = a /\ read reg s2 = a))`;;

let mk_equiv_regs2 = define
  `((mk_equiv_regs2
    :((armstate,(N)word)component)list->
     ((armstate,(N)word)component)list->armstate#armstate->bool)
      [] [] s = true) /\
   (mk_equiv_regs2 (CONS reg regs) (CONS reg2 regs2) (s1,s2) =
     (mk_equiv_regs2 regs regs2 (s1,s2) /\
      exists (a:(N)word). read reg s1 = a /\ read reg2 s2 = a))`;;

let mk_equiv_bool_regs = define
  `((mk_equiv_bool_regs:((armstate,bool)component)list->armstate#armstate->bool)
      [] s = true) /\
   (mk_equiv_bool_regs (CONS reg regs) (s1,s2) =
     (mk_equiv_bool_regs regs (s1,s2) /\
      exists (a:bool). read reg s1 = a /\ read reg s2 = a))`;;

(* ------------------------------------------------------------------------- *)
(* Given a range of PCs of interest, identify which registers are inputs to  *)
(* the chunk of instructions and also which registers are outputs.           *)
(* A register is considered input if there exists an instruction that reads  *)
(* the register and no previous instruction in the PCs wrote to the register.*)
(* A register is considered output if it is written by any instruction in the*)
(* PCs.                                                                      *)
(* If pc_ranges has more than one range, it is considered that instructions  *)
(* in the ranges are executed consecutively.                                 *)
(* These results will not include PC.                                        *)
(* ------------------------------------------------------------------------- *)

let get_input_output_regs
    (decode_ths:thm option array) (pc_ranges: (int*int)list)
    :term list * term list =
  let input_comps: term list ref = ref [] in
  let output_comps: term list ref = ref [] in
  let normalize_word_expr t =
    rhs (concl ((DEPTH_CONV NORMALIZE_ADD_SUBTRACT_WORD_CONV THENC REWRITE_CONV[WORD_ADD_0]) t)) in
  let is_interesting_reg t = not (is_comb t) && t <> `PC` && t <> `events` in
  let update_comps (pc_begin,pc_end) =
    (* Input and output components *)
    for i = pc_begin to pc_end do
      match decode_ths.(i) with
      | None -> ()
      | Some the_th -> begin
        let r = snd (dest_imp (snd (strip_forall (concl the_th)))) in
        (* r is something like `arm_decode s (word (pc + 4)) (arm_ADD X3 X1 X2)` *)
        let f,args = strip_comb r in
        if name_of f <> "arm_decode" then failwith "Unknown inst" else
        let the_inst = last args in
        let state_update_th = ARM_EXEC_CONV the_inst in
        let state_update:term = snd (dest_eq (concl state_update_th)) in

        (* Update input_comps. get `read ...`s first *)
        let reads = find_terms (fun t -> is_comb t &&
            let c,args = strip_comb t in
            name_of c = "read" && length args = 2)
          state_update in
        let read_comps = map (fun t -> normalize_word_expr (hd (snd (strip_comb t))))
          reads in
        let read_comps = filter is_interesting_reg read_comps in
        let intermediate_comps = intersect read_comps !output_comps in
        (* subtract reads that are already written! *)
        let read_comps = subtract read_comps intermediate_comps in
        let _ = input_comps := union !input_comps read_comps in
        (* .. from output_comps as well *)

        (* Update output_comps. *)
        let writes = find_terms (is_binary ":=") state_update in
        let write_comps = map (fun t -> normalize_word_expr (fst (dest_binary ":=" t)))
          writes in
        let write_comps = filter is_interesting_reg write_comps in
        output_comps := union !output_comps write_comps;
      end
    done in

  List.iter update_comps pc_ranges;
  (!input_comps, !output_comps);;

(* example *)
let equiv_test_ops: int list = [
  0x8b010002; (* add     x2, x0, x1 *)
  0x8b020023; (* add     x3, x1, x2 *)
  0xa9402fea; (* ldp     x10, x11, [sp] *)
  0xa900abeb; (* stp     x11, x10, [sp, #8] *)
];;

let equiv_test_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    equiv_test_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "__equiv_test_mc" (term_of_bytes byte_list);;

let EQUIV_TEST_EXEC = ARM_MK_EXEC_RULE equiv_test_mc;;

let _ = get_input_output_regs (snd EQUIV_TEST_EXEC) [(0,15)];;
let _ = get_input_output_regs (snd EQUIV_TEST_EXEC) [(0,7);(12,15)];;


(* from e.g., `arm_ADD X3 X1 X2`, return
  (instruction name ("arm_ADD"), (output reg:term, input expression) list) *)
let get_inst_info =
  let normalize_word_expr t =
    rhs (concl ((DEPTH_CONV NORMALIZE_ADD_SUBTRACT_WORD_CONV THENC REWRITE_CONV[WORD_ADD_0]) t)) in
  fun  (the_inst:term): (string * (term * term) list) ->
    let state_update_th = ARM_EXEC_CONV the_inst in
    let state_update:term = snd (dest_eq (concl state_update_th)) in

    (* Get the output components and its sym expression. *)
    let writes = find_terms (is_binary ":=") state_update in
    let write_comps = map (fun t ->
      let l,r = dest_binary ":=" t in (normalize_word_expr l, r)) writes in
    (name_of (fst (strip_comb the_inst)), write_comps);;

let _ = get_inst_info `arm_ADD X3 X1 X2`;;

let backward_taint_analysis
    (decode_ths:thm option array) (pc_ranges: (int*int)list)
    (tainted_regs: (int*(term list))list) (* (pc, tainted registers) list *)
    :(int * (term list)) list =
  (* a set of tainted registers *)
  let tainted = ref [] in
  let result = ref [] in
  let update_comps (pc_begin,pc_end) =
    (* Input and output components *)
    for i = pc_end downto pc_begin do
      (* mark tainted_regs[i] as tainted *)
      let ts = try assoc i tainted_regs with _ -> [] in
      tainted := union !tainted ts;
      match decode_ths.(i) with
      | None -> ()
      | Some the_th -> begin
        let r = snd (dest_imp (snd (strip_forall (concl the_th)))) in
        (* r is something like `arm_decode s (word (pc + 4)) (arm_ADD X3 X1 X2)` *)
        let f,args = strip_comb r in
        if name_of f <> "arm_decode" then failwith "Unknown inst" else
        let the_inst = last args in
        let _,write_comps = get_inst_info the_inst in

        let result_at_i = ref [] in
        let _ = if !arm_print_log then Printf.printf "pc=%d:\n" i in
        List.iter (fun (comp,rhs) ->
            let _ = if !arm_print_log then
              Printf.printf "write: %s := %s\n" (string_of_term comp) (string_of_term rhs) in
            if not (mem comp !tainted) then () else
            if is_comb comp then () else begin
            (* only pick aliased registers *)

            (* this is tainted. *)
            (if !arm_print_log then
              Printf.printf "%s was tainted.\n" (string_of_term comp));
            result_at_i := comp::!result_at_i;

            (* remove this register from tainted. *)
            tainted := filter (fun t -> t <> comp) !tainted;

            (* get 'read X' from rhs, and add those to tainted *)
            let reads_to_taint = find_terms (fun t -> is_comb t &&
                let c,args = strip_comb t in
                name_of c = "read" && length args = 2 &&
                (* only pick aliased registers *)
                not (is_comb (hd args)))
              rhs in
            List.iter (fun t ->
                (if !arm_print_log then
                  Printf.printf "reads_to_taint: %s\n" (string_of_term t));
                let the_reg = hd (snd (strip_comb t)) in
                if not (mem the_reg !tainted) then
                  tainted := the_reg::!tainted)
              reads_to_taint
            end
          ) write_comps;

        if !result_at_i <> [] then
          result := (i,!result_at_i)::!result
      end
    done in

  List.iter update_comps pc_ranges;
  (-1,!tainted)::!result;;

assert (backward_taint_analysis (snd EQUIV_TEST_EXEC) [(0,4)] [4,[`X3`]] = [(-1, [`X0`; `X1`]); (0, [`X2`]); (4, [`X3`])]);;
assert (backward_taint_analysis (snd EQUIV_TEST_EXEC) [(0,12)] [12,[`X11`]] = [(-1, [`SP`]); (8, [`X11`])]);;


let collect_mem_address_regs
    (decode_ths:thm option array) (pc_ranges: (int*int)list)
    :(int * term) list =
  let res = ref [] in
  let update_comps (pc_begin,pc_end) =
    (* Input and output components *)
    for i = pc_begin to pc_end do
      match decode_ths.(i) with
      | None -> ()
      | Some the_th -> begin
        let r = snd (dest_imp (snd (strip_forall (concl the_th)))) in
        (* r is something like `arm_decode s (word (pc + 4)) (arm_ADD X3 X1 X2)` *)
        let f,args = strip_comb r in
        if name_of f <> "arm_decode" then failwith "Unknown inst" else
        let the_inst = last args in
        let instconstr,instargs = strip_comb the_inst in
        match name_of instconstr with
        | "arm_LDR" | "arm_STR" | "arm_LDRB" | "arm_STRB" ->
          res := (i, List.nth instargs 1)::!res
        | "arm_LDP" | "arm_STP" ->
          res := (i, List.nth instargs 2)::!res
        | _ -> ()
      end
    done in

  List.iter update_comps pc_ranges;
  List.rev !res;;

assert (collect_mem_address_regs (snd EQUIV_TEST_EXEC) [0, 12] = [(8, `SP`); (12, `SP`)]);;

(* Given output_regs in the 'right' program, find the corresponding regs
   in the 'left' program. Scans backward from the right program.
   Ignores the case when the corresponding register in the left is
   overwritten later, because it cannot be an 'output' register. *)
let map_output_regs
    (decode_ths_left:thm option array) (pc_begin_left: int)
    (decode_ths_right:thm option array) (pc_begin_right: int)
    (right_to_left_map: int array)
    (output_regs_right:term list)
    :((int * term) option) list =
  (* is register reg_left overwritten in the left program after
     idx_left? *)
  let is_overwritten_later (reg_left:term) (idx_left:int) =
    exists (fun i ->
      match decode_ths_left.(pc_begin_left + (i-1)*4) with
      | None -> false | Some the_th -> begin
        let r = snd (dest_imp (snd (strip_forall (concl the_th)))) in
        (* r is something like `arm_decode s (word (pc + 4)) (arm_ADD X3 X1 X2)` *)
        let f,args = strip_comb r in
        if name_of f <> "arm_decode" then failwith "Unknown inst" else
        let _,comp_updates_right = get_inst_info (last args) in
        exists (fun l,_ -> l = reg_left) comp_updates_right
      end) ((idx_left+1) -- (Array.length right_to_left_map)) in

  (* Returns the index of left instruction and the matching output register *)
  let rec search_out (output_reg_right:term) (idx_right:int):
      (int * term) option =
    if idx_right = 0 then None else
    let idx_left = right_to_left_map.(idx_right-1) in
    match decode_ths_right.(pc_begin_right + (idx_right-1)*4) with
    | None -> (* next iter *)
      search_out output_reg_right (idx_right - 1)
    | Some the_th -> begin
      let r = snd (dest_imp (snd (strip_forall (concl the_th)))) in
      (* r is something like `arm_decode s (word (pc + 4)) (arm_ADD X3 X1 X2)` *)
      let f,args = strip_comb r in
      if name_of f <> "arm_decode" then failwith "Unknown inst" else
      let name_right,comp_updates_right = get_inst_info (last args) in

      let update_idx = find_index (fun l,_ -> l = output_reg_right) comp_updates_right in

      match update_idx with
      | Some update_idx -> begin
        (* found! *)
        let the_th_left = Option.get (decode_ths_left.(pc_begin_left + (idx_left-1)*4)) in
        let r_left = snd (dest_imp (snd (strip_forall (concl the_th_left)))) in
        let f,args_left = strip_comb r_left in
        if name_of f <> "arm_decode" then failwith "Unknown inst" else
        let name_left,comp_updates_left = get_inst_info (last args_left) in

        assert (name_left = name_right);
        Printf.printf "Found; left instr: %s at %d; right instr: %s at %d\n" (string_of_term (last args)) idx_left (string_of_term (last args_left)) idx_right;
        let out_reg_left = fst (List.nth comp_updates_left update_idx) in

        if is_overwritten_later out_reg_left idx_left then
          None
        else Some (idx_left, out_reg_left)
        end
      | None -> (* next iter *)
        search_out output_reg_right (idx_right - 1)
    end in
  map (fun t ->
    Printf.printf "Mapping reg %s..\n%!" (string_of_term t);
    search_out t (Array.length right_to_left_map)) output_regs_right;;


(* ------------------------------------------------------------------------- *)
(* Tactics for proving equivalence of two partially different programs.      *)
(* Renamed registers in the input programs should not affect the behavior of *)
(* these tactics.                                                            *)
(* ------------------------------------------------------------------------- *)

(* A lock-step simulation.
  This abbreviates the new expression(s) appearing on the new state
  expression(s) of the right-side program, and checks whether
  new expression(s) appearing on the left-side program are equivalent
  to it. If equal, it proceeds and adds the equality between read state
  and their abbreviated values as assumptions.

  It forgets abbreviations that were used in the past. *)
let ARM_LOCKSTEP_TAC =
  let update_eqs_prog1: (thm list * thm list) ref = ref ([],[]) in
  let update_eqs_prog2: (thm list * thm list) ref = ref ([],[]) in

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
    ARM_N_STEP_TAC execth [] new_stname (Some update_eqs_prog1) None THEN
    (*cleanup assumptions that use old abbrevs*)
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC [new_stname] false THEN
    (* .. and dead registers. *)
    DISCARD_REGS_WITH_DEAD_VALUE_TAC ignored_output_regs_left THEN
    RECOVER_ASMS_OF_READ_STATES THEN

    (* 2. One step on the right program. *)
    (fun (asl,g) -> Printf.printf "Running right...\n"; ALL_TAC (asl,g)) THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    STASH_ASMS_OF_READ_STATES [new_stname] THEN
    ARM_N_STEP_TAC execth' [] new_stname' (Some update_eqs_prog2) None THEN
    (*cleanup assumptions that use old abbrevs*)
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC [new_stname'] true THEN
    (* .. and dead registers. *)
    DISCARD_REGS_WITH_DEAD_VALUE_TAC ignored_output_regs_right THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN

    (* 3. Abbreviate expressions that appear in the new state expressions
          created from step 2. *)
    W (fun (asl,g) ->
      let update_eqs_prog1_list,aux_mem_updates_prog1_list = !update_eqs_prog1 in
      let update_eqs_prog2_list,aux_mem_updates_prog2_list = !update_eqs_prog2 in
      if List.length update_eqs_prog1_list <> List.length update_eqs_prog2_list
      then
        (Printf.printf "Updated components mismatch:\n";
         Printf.printf "\tprog1: ";
         List.iter (fun th -> print_qterm (concl th)) update_eqs_prog1_list;
         Printf.printf "\n\tprog2: ";
         List.iter (fun th -> print_qterm (concl th)) update_eqs_prog2_list;
         failwith "ARM_LOCKSTEP_TAC")
      else if List.length aux_mem_updates_prog1_list <>
              List.length aux_mem_updates_prog2_list
      then
        (Printf.printf "Updated auxiliary memory components mismatch:\n";
         Printf.printf "\tprog1: ";
         List.iter (fun th -> print_qterm (concl th)) aux_mem_updates_prog1_list;
         Printf.printf "\n\tprog2: ";
         List.iter (fun th -> print_qterm (concl th)) aux_mem_updates_prog2_list;
         failwith "ARM_LOCKSTEP_TAC")
      else
        let eqs = zip update_eqs_prog1_list update_eqs_prog2_list in
        MAP_EVERY ASSUME_TAC aux_mem_updates_prog1_list THEN
        MAP_EVERY ASSUME_TAC aux_mem_updates_prog2_list THEN
        MAP_EVERY
          (fun (eq1,eq2) ->
            let oc1:term option = get_read_component (concl eq1) in
            let oc2:term option = get_read_component (concl eq2) in
            match oc1,oc2 with
            | Some comp1, Some comp2 ->
              if mem comp1 ignored_output_regs_left &&
                 mem comp2 ignored_output_regs_right
              then ALL_TAC (* dead values *)
              else ABBREV_READS_TAC (eq1,eq2) (forget_expr comp1)
            | _ -> (* this can happen when writing to XZR *) ALL_TAC)
          eqs);;


let EQUIV_INITIATE_TAC input_equiv_states_th =
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  let input_pred = SPEC_ALL
      (SPECL [`s0:armstate`;`s0':armstate`] input_equiv_states_th) in
  UNDISCH_TAC (fst (dest_binary "=" (concl input_pred))) THEN
  GEN_REWRITE_TAC LAND_CONV [input_equiv_states_th] THEN
  REWRITE_TAC [C_ARGUMENTS;SOME_FLAGS;mk_equiv_regs;mk_equiv_regs2;mk_equiv_bool_regs] THEN
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

let ARM_N_STUTTER_LEFT_TAC exec_th (snames:int list)
    (dead_value_info:term list array option): tactic =
  W (fun (asl,g) ->
    (* get the state name of the 'right' program *)
    let t' = fst (dest_comb g) in
    let inner_eventually = snd (dest_abs (snd (dest_comb (t')))) in
    let sname = fst (dest_var (snd (dest_comb inner_eventually))) in
    STASH_ASMS_OF_READ_STATES [sname] THEN
    ARM_N_STEPS_TAC exec_th snames "" [] dead_value_info THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    CLARIFY_TAC);;

let ARM_N_STUTTER_RIGHT_TAC exec_th (snames:int list) (st_suffix:string)
    (dead_value_info:term list array option): tactic =
  W (fun (asl,g) ->
    (* get the state name of the 'left' program *)
    let sname = fst (dest_var (snd (dest_comb g))) in
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    STASH_ASMS_OF_READ_STATES [sname] THEN
    ARM_N_STEPS_TAC exec_th snames st_suffix [] dead_value_info THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    CLARIFY_TAC);;


(* Build `\(s,s'). mk_equiv_regs [...]` *)
let build_equiv_regs (regs:term list) =
  let xregsl = filter (fun t -> type_of t = `:(armstate,int64)component`) regs in
  let qregsl = filter (fun t -> type_of t = `:(armstate,int128)component`) regs in
  (* todo: flags? *)

  let xregs = list_mk_icomb "mk_equiv_regs"
      [mk_list (xregsl,`:(armstate,int64)component`); `(s1:armstate,s1':armstate)`] in
  let qregs = list_mk_icomb "mk_equiv_regs"
      [mk_list (qregsl,`:(armstate,int128)component`); `(s1:armstate,s1':armstate)`] in
  list_mk_gabs ([`(s1,s1'):armstate#armstate`], mk_conj(xregs, qregs));;

let build_equiv_regs2 (regs:term list) (regs2) =
  let xregsl = filter (fun t -> type_of t = `:(armstate,int64)component`) regs in
  let qregsl = filter (fun t -> type_of t = `:(armstate,int128)component`) regs in
  let xregs2 = filter (fun t -> type_of t = `:(armstate,int64)component`) regs2 in
  let qregs2 = filter (fun t -> type_of t = `:(armstate,int128)component`) regs2 in
  (* todo: flags? *)

  let xregs = list_mk_icomb "mk_equiv_regs2"
      [mk_list (xregsl,`:(armstate,int64)component`);
       mk_list (xregs2,`:(armstate,int64)component`);
       `(s1:armstate,s1':armstate)`] in
  let qregs = list_mk_icomb "mk_equiv_regs2"
      [mk_list (qregsl,`:(armstate,int128)component`);
       mk_list (qregs2,`:(armstate,int128)component`);
       `(s1:armstate,s1':armstate)`] in
  list_mk_gabs ([`(s1,s1'):armstate#armstate`], mk_conj(xregs, qregs));;

(* Build maychanges. *)
let build_maychanges regs extra =
  let xregs,regs2 = partition (fun t -> type_of t = `:(armstate,int64)component`) regs in
  let qregs,flags = partition (fun t -> type_of t = `:(armstate,int128)component`) regs2 in
  end_itlist (fun x y -> mk_icomb (mk_icomb (`,,`,x),y))
    [mk_icomb (`MAYCHANGE`,mk_list (xregs, `:(armstate,int64)component`));
     mk_icomb (`MAYCHANGE`,mk_list (qregs, `:(armstate,int128)component`));
     mk_icomb (`MAYCHANGE`,mk_list (flags, `:(armstate,bool)component`));
     extra;
     `MAYCHANGE [PC]`;
     `MAYCHANGE [events]`];;

(* maychanges: `(MAYCHANGE [..] ,, MAYCHANGE ...)`
   combine MAYCHANGE of fragmented memory accesses of constant sizes into
   one if contiguous. *)
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
      match get_memory_read_info t with
      | Some (ptr,len,_) -> maychange_mems := !maychange_mems @ [(t, (ptr,len))]
      | None ->
        (* t is register *)
        let _,args = dest_type (type_of t) in
        let destty = last args in
        if destty = word64ty then begin
          if not (mem t !maychange_regs64) then
            maychange_regs64 := !maychange_regs64 @ [t]
        end else if destty = word128ty then begin
          if not (mem t !maychange_regs128) then
            maychange_regs128 := !maychange_regs128 @ [t]
        end else begin
          if not (mem t !maychange_others) then
            maychange_others := !maychange_others @ [t]
        end in

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

    while length !maychange_mems <> 0 do
      let next_term,(ptr,len) = List.hd !maychange_mems in
      if not (is_numeral len) then begin
        (* if len is not a constant, be conservative and just add it
           unless it already exists *)
        (if not (mem next_term !maychange_mems_merged) then
          maychange_mems_merged := next_term::!maychange_mems_merged);
        maychange_mems := List.tl !maychange_mems
      end else
        let baseptr, _ = get_base_ptr_and_constofs ptr in

        let mems_of_interest, remaining = List.partition
          (fun _,(ptr,len) -> baseptr = fst (get_base_ptr_and_constofs ptr) && is_numeral len)
          !maychange_mems in
        maychange_mems := remaining;

        if List.length mems_of_interest = 1 then
          maychange_mems_merged := (fst (List.hd mems_of_interest)) :: !maychange_mems_merged
        else
          (* combine mem accesses in mems_of_interest *)
          (* get (ofs, len). len must be constant. *)
          let ranges = map
            (fun (_,(t,len)) -> snd (get_base_ptr_and_constofs t),dest_small_numeral len)
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
    let rec join_result (comps:term list): unit =
      match comps with
      | [] -> ()
      | first_comp::comps ->
        let fcty = type_of first_comp in
        let comps0,comps1 = List.partition (fun c -> type_of c = fcty)
          comps in
        let mterm = mk_icomb (maychange_const, mk_flist (first_comp::comps0)) in
        (if !result = zero then result := mterm
        else result := mk_icomb(mk_icomb (seq_const,mterm),!result));
        join_result comps1 in
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
    TODO:
    simplify_maychanges
       `MAYCHANGE [memory :> bytes64 (word_add z (word (8 * 4 * i)))] ,,
        MAYCHANGE [memory :> bytes64 (word_add z (word (8 * 4 * i + 8)))] ,,
        MAYCHANGE [memory :> bytes64 (word_add z (word (8 * 4 * i + 16)))] ,,
        MAYCHANGE [memory :> bytes64 (word_add z (word (8 * 4 * i + 24)))]`;;
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

  Note that this tactic may remove assumptions on abbreviations if they are
  considered unused.
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
      ARM_N_STUTTER_RIGHT_TAC execth2 ((rstart+1)--rend) "'" dead_value_info_right
        ORELSE (PRINT_TAC "insert failed" THEN PRINT_GOAL_TAC THEN NO_TAC)
    end
  | ("delete",lstart,lend,rstart,rend) ->
    if rstart <> rend then failwith "delete's rstart and rend must be equal"
    else begin
      (if lend - lstart > 50 then
        Printf.printf "Warning: too many instructions: delete %d~%d\n" lstart lend);
      ARM_N_STUTTER_LEFT_TAC execth1 ((lstart+1)--lend) dead_value_info_left
        ORELSE (PRINT_TAC "delete failed" THEN PRINT_GOAL_TAC THEN NO_TAC)
    end
  | ("replace",lstart,lend,rstart,rend) ->
    (if lend - lstart > 50 || rend - rstart > 50 then
      Printf.printf "Warning: too many instructions: replace %d~%d %d~%d\n"
          lstart lend rstart rend);
    ((ARM_N_STUTTER_LEFT_TAC execth1 ((lstart+1)--lend) dead_value_info_left
     ORELSE (PRINT_TAC "replace failed: stuttering left" THEN PRINT_GOAL_TAC THEN NO_TAC))
     THEN
     (ARM_N_STUTTER_RIGHT_TAC execth2 ((rstart+1)--rend) "'" dead_value_info_right
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

(* Simulate an instruction of the left program and assign fresh variables
    to the RHSes of new state equations (`read c s = RHS`).
    store_to is a list of `RHS = assigned_fresh_var` theorems.
    The equations on assigned fresh variables (`RHS = assigned_fresh_var`)
    do not appear as assumptions.
*)

let is_store_inst (t:term) =
  let rec is_part_of_memory t =
    if is_const t then name_of t = "memory"
    else if is_binary ":>" t then is_part_of_memory (lhand t)
    else false in
  can (find_term (fun t -> is_comb t &&
    let c,args = strip_comb t in
    name_of c = "write" && is_part_of_memory (hd args))) t;;


let ARM_N_STEP_AND_ABBREV_TAC =
  let update_eqs_prog = ref ([],[]) in
  let inst_term = ref `T` in
  fun execth (new_stname) (store_to:thm list ref)
             (regs_to_avoid_abbrev: term list)->
    (* Stash the right program's state equations first *)
    (fun (asl,g) ->
      let cur_stname' = name_of (rand (snd ((dest_abs o rand o rator) g))) in
      STASH_ASMS_OF_READ_STATES [cur_stname'] (asl,g)) THEN
    (* One step on the left program *)
    ARM_N_STEP_TAC execth [] new_stname (Some update_eqs_prog) (Some inst_term) THEN
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC [new_stname] false THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    (* Abbreviate RHSes of the new state equations *)
    W (fun (asl,g) ->
      let update_eqs_prog_list, update_aux_mem_eqs_list = !update_eqs_prog in
      (* Do not abbreviate auxiliary memory read outputs. Pretend that these
         equations were already given before simulation :) This avoids control
         flow-dependent behavior of abbreviation. *)
      MAP_EVERY ASSUME_TAC update_aux_mem_eqs_list THEN

      (* avoid abbreviation of output of registers in regs_to_avoid_abbrev *)
      let update_eqs_noabbrev_list, update_eqs_prog_list =
        partition (fun th ->  (* th: `read X s = ...` *)
            let c = concl th in is_eq c &&
              mem (hd (snd (strip_comb (lhs c)))) regs_to_avoid_abbrev)
          update_eqs_prog_list in
      MAP_EVERY ASSUME_TAC update_eqs_noabbrev_list THEN

      if is_store_inst !inst_term then
        (* Do not abbreviate the expressions of values stored to the memory;
           conceptually they are not outputs. *)
        MAP_EVERY ASSUME_TAC update_eqs_prog_list
      else
        MAP_EVERY
          (fun th -> (* th: `read X s = ...` *) ABBREV_READ_TAC th store_to)
          update_eqs_prog_list);;

(* store_to is a reference to list of state numbers and abbreviations.
   It is initialized as empty when this tactic starts.
   Unlike ARM_N_STEP_AND_ABBREV_TAC, the equations on assigned fresh variables
    (`RHS = assigned_fresh_var`) are added as assumptions. *)
let ARM_N_STEPS_AND_ABBREV_TAC execth (snums:int list)
    (store_to: (int * thm) list ref)
    (regs_to_avoid_abbrev: (term list) list option):tactic =
  let regs_to_avoid_abbrev =
    match regs_to_avoid_abbrev with
    | Some l -> l | None -> replicate [] (length snums) in
  if length regs_to_avoid_abbrev <> length snums
  then failwith "regs_to_avoid_abbrev: length of snums and regs_to_avoid_abbrev mismatch" else

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
    (fun n,regs_to_avoid_abbrev ->
      let stname = "s" ^ (string_of_int n) in
      let store_to_n = ref [] in
      (fun (asl,g) ->
        let _ = Printf.printf "Stepping to state %s..\n%!" stname in
        ALL_TAC (asl,g)) THEN
      ARM_N_STEP_AND_ABBREV_TAC execth stname store_to_n regs_to_avoid_abbrev THEN
      (fun (asl,g) ->
        store_to := (map (fun x -> (n,x)) !store_to_n) @ !store_to;
        if !arm_print_log then begin
          Printf.printf "%d new abbreviations (%d in total)\n%!"
            (List.length !store_to_n) (List.length !store_to)
        end;
        ALL_TAC (asl,g)) THEN
      CLARIFY_TAC)
    (zip snums regs_to_avoid_abbrev) THEN
  RECOVER_ASMS_OF_READ_STATES;;

(* For the right program. abbrevs must be generated by ARM_N_STEPS_AND_ABBREV_TAC. *)
let ARM_N_STEPS_AND_REWRITE_TAC execth (snums:int list) (inst_map: int list)
      (abbrevs: (int * thm) list ref)
      (regs_to_avoid_abbrev: (term list) list option)
      : tactic =
  (* Warning: no nested call of ARM_N_STEPS_AND_REWRITE_TAC *)
  let abbrevs_cpy:(int * thm) list ref = ref [] in

  let regs_to_avoid_abbrev =
    match regs_to_avoid_abbrev with
    | Some l -> l | None -> replicate [] (length snums) in
  if length regs_to_avoid_abbrev <> length snums
  then failwith "regs_to_avoid_abbrev: length of snums and regs_to_avoid_abbrev mismatch" else

  (* Stash the left program's state equations first *)
  (fun (asl,g) ->
    abbrevs_cpy := !abbrevs;
    let cur_stname = name_of (rand g) in
    STASH_ASMS_OF_READ_STATES [cur_stname] (asl,g)) THEN
  MAP_EVERY
    (fun n,regs_to_avoid_abbrev ->
      let stname = "s" ^ (string_of_int n) ^ "'" in
      let new_state_eq = ref ([],[]) in
      let inst_term = ref `T` in
      W (fun (asl,g) ->
        let _ = Printf.printf "Stepping to state %s.. (has %d remaining abbrevs)\n%!"
            stname (List.length !abbrevs_cpy) in
        ALL_TAC) THEN
      MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
      ARM_N_STEP_TAC execth [] stname (Some new_state_eq) (Some inst_term) THEN
      DISCARD_OLDSTATE_AGGRESSIVELY_TAC [stname] false THEN
      MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
      (fun (asl,g) ->
        let n_at_lprog = List.nth inst_map (n-1) in
        let abbrevs_for_st_n, leftover = List.partition (fun (n',t)->n'=n_at_lprog) !abbrevs_cpy in
        let _ = abbrevs_cpy := leftover in

        (* new_state_eqs is the updated state components of the 'right' program
           instruction, which are outputs of the instruction.
           new_aux_mem_eqs are auxiliary equations between memory read and their
           right hand sides that are automatically inferred. They are not
           outputs of the instruction. *)
        let new_state_eqs, new_aux_mem_eqs = !new_state_eq in

        (if !arm_print_log then begin
          Printf.printf "ARM_N_STEPS_AND_REWRITE_TAC: new_state_eqs:\n";
          List.iter (fun t -> Printf.printf "    `%s`\n" (string_of_term (concl t))) new_state_eqs;
          Printf.printf "ARM_N_STEPS_AND_REWRITE_TAC: new_aux_mem_eqs:\n";
          List.iter (fun t -> Printf.printf "    `%s`\n" (string_of_term (concl t))) new_aux_mem_eqs;
        end);

        (* Reading flags may not have 'read flag s = ..' form, but just
            'read flag s' or '~(read flag s)'. They don't need to be rewritten.
           Also, 'read PC' and 'read events' should not be rewritten as well. Collect them
           separately. *)
        let new_state_eqs_norewrite,new_state_eqs =
          List.partition
            (fun th -> not (is_eq (concl th))
                       || (is_read_pc (lhs (concl th)))
                       || (is_read_events (lhs (concl th))))
          new_state_eqs in

        (* filter out regs from new_state_eqs that are regs_to_avoid_abbrev.
           If the instruction is a store instruction, do not abbreviate
           expressions of values that are stored to the memory because
           they are not outputs. *)
        let new_state_eqs_noabbrev, new_state_eqs =
          if is_store_inst !inst_term then new_state_eqs,[]
          else partition
            (fun th ->
              let updating_comp = hd (snd (strip_comb (lhs (concl th)))) in
              mem updating_comp regs_to_avoid_abbrev)
            new_state_eqs in

        if List.length abbrevs_for_st_n = List.length new_state_eqs then
          (* For each `read c sn = rhs`, replace rhs with abbrev *)
          let new_state_eqs = List.filter_map
            (fun new_state_eq ->
              let rhs = rhs (concl new_state_eq) in
              (* Find 'rhs = abbrev' from the left program's  updates. *)
              match List.find_opt
                (fun (_,th') -> lhs (concl th') = rhs)
                abbrevs_for_st_n with
              | Some (_,rhs_to_abbrev) ->
                (try
                  Some (GEN_REWRITE_RULE RAND_CONV [rhs_to_abbrev] new_state_eq)
                with _ ->
                  (Printf.printf "Failed to proceed.\n";
                    Printf.printf "- rhs: `%s`\n" (string_of_term rhs);
                    Printf.printf "- rhs_to_abbrev: `%s`\n" (string_of_thm rhs_to_abbrev);
                    failwith "ARM_N_STEPS_AND_REWRITE_TAC"))
              | None -> begin
                (* This case happens when new_state_eq already has abbreviated RHS *)
                (if !arm_print_log then begin
                  Printf.printf "ARM_N_STEPS_AND_REWRITE_TAC: abbrevs_for_st_n does not have matching abbreviation for this: `%s`\n" (string_of_term rhs);
                end);
                None
              end)
            new_state_eqs in
          (if !arm_print_log then begin
            Printf.printf "ARM_N_STEPS_AND_REWRITE_TAC: updated new_state_eqs:\n";
            List.iter (fun t -> Printf.printf "    `%s`\n" (string_of_term (concl t))) new_state_eqs;
            Printf.printf "ARM_N_STEPS_AND_REWRITE_TAC: new_state_eqs_noabbrev\n";
            List.iter (fun t -> Printf.printf "    `%s`\n" (string_of_term (concl t))) new_state_eqs_noabbrev;
            Printf.printf "ARM_N_STEPS_AND_REWRITE_TAC: new_state_eqs_norewrite\n";
            List.iter (fun t -> Printf.printf "    `%s`\n" (string_of_term (concl t))) new_state_eqs_norewrite;
          end);
          MAP_EVERY ASSUME_TAC (new_aux_mem_eqs @ new_state_eqs_norewrite @
                                new_state_eqs_noabbrev @
                                new_state_eqs) (asl,g)
        else
          (Printf.printf "State number %d: length mismatch: %d <> %d\n"
            n (List.length new_state_eqs) (List.length abbrevs_for_st_n);
          Printf.printf "  new state eq:\n";
          List.iter (fun t -> Printf.printf "    %s\n" (string_of_term (concl t))) new_state_eqs;
          Printf.printf "  old state eq:\n";
          List.iter (fun (_,t) -> Printf.printf "    %s\n" (string_of_term (concl t))) abbrevs_for_st_n;
          failwith "ARM_N_STEPS_AND_REWRITE_TAC")) THEN CLARIFY_TAC)
    (zip snums regs_to_avoid_abbrev) THEN
  RECOVER_ASMS_OF_READ_STATES THEN
  CLARIFY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Tactics that do not perform symbolic execution but are necessary to       *)
(* initiate/finalize program equivalence proofs.                             *)
(* ------------------------------------------------------------------------- *)

(* Prove goals like
   `?pc. nonoverlapping_modulo (2 EXP 64) (pc,36) (val addr_out,32) /\
      nonoverlapping_modulo (2 EXP 64) (pc,36) (val addr_in,32) /\
      4 divides val (word pc)`
  by instantiating pc with the 'pc' input. *)
let TRY_CONST_PC_TAC (pc:term):tactic =
  TRY ((EXISTS_TAC pc THEN
    (* The last clause of conjunctions is '4 divides ...'. *)
    REWRITE_TAC[CONJ_ASSOC] THEN
    CONJ_TAC THENL [
      ALL_TAC;
      REWRITE_TAC[VAL_WORD;DIMINDEX_64;DIVIDES_DIV_MULT] THEN ARITH_TAC
    ] THEN

    (* the main nonoverlapping_modulo clauses *)
    DISCARD_ASSUMPTIONS_TAC (fun th ->
      can (find_term (fun t -> is_const t &&
            (name_of t = "nonoverlapping_modulo" || name_of t = "aligned")))
          (concl th)) THEN

    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN ASM_ARITH_TAC) ORELSE
    (PRINT_GOAL_TAC THEN
     PRINT_TAC ("TRY_CONST_PC_TAC did not work (pc was " ^  (string_of_term pc) ^ ")")));;

(* Smartly invokes TRY_CONST_PC_TAC, after analyzing conclusion + assumptions about ranges. *)
let TRY_CONST_PCS_TAC (pcs:int list) (val_word_ptrs:term list):tactic =
  let decomp_relop t =
    if is_binary "<" t then Some ("<",dest_binary "<" t)
    else if is_binary "<=" t then Some ("<=",dest_binary "<=" t)
    else None in
  fun (asl,w) ->
    let upper_lower_bounds = List.filter_map
      (fun _,th ->
        let c = concl th in
        match decomp_relop c with
        | Some ("<", (l, r)) when is_numeral r ->
          Some (l, "<", dest_small_numeral r)
        | Some ("<=", (l, r)) when is_numeral l ->
          Some (r, ">=", dest_small_numeral l)
        | _ -> None) asl in
    let ranges = List.map
      (fun val_word_ptr ->
        let lb = List.filter_map (fun t,comp,i ->
          if comp = ">=" && t = val_word_ptr then Some i
          else None) upper_lower_bounds in
        let lb = List.fold_left max 0 lb in
        let ub = List.filter_map (fun t,comp,i ->
          if comp = "<" && t = val_word_ptr then Some i
          else None) upper_lower_bounds in
        let ub = List.fold_left min max_int ub in
        (val_word_ptr,lb,ub))
      val_word_ptrs in
    (* exclude any pc in pcs that will fit in one of the ranges *)
    let remaining_pcs = List.filter
      (fun pc -> not (exists (fun _,lb,ub -> lb <= pc && pc < ub) ranges))
      pcs in
    (if length remaining_pcs = 0 then begin
      Printf.printf "identified ranges from assumptions:\n";
      List.iter (fun t,l,u -> Printf.printf "%s:[%d,%d)\n"
        (string_of_term t) l u);
      Printf.printf "remaining pcs: ";
      List.iter (fun d -> Printf.printf "%d " d) remaining_pcs;
      Printf.printf "\n";
      PRINT_GOAL_TAC THEN NO_TAC
    end else TRY_CONST_PC_TAC (mk_small_numeral (hd remaining_pcs))) (asl,w);;

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
  CONV_TAC (DEPTH_CONV
    (* no NUM_EXP_CONV or NUM_RED_CONV to avoid reducing 2 EXP 64 of nonoverlapping_modulo *)
    (NUM_SUB_CONV ORELSEC NUM_MULT_CONV ORELSEC NUM_ADD_CONV ORELSEC NUM_DIV_CONV)) THEN
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
    let try_holes = time (TRY_CONST_PCS_TAC
      (map (fun i -> i * segsize + maxlen)
        (0--(List.length word_ptrs))) val_word_ptrs) in

    ((val_bound_prepare_tac THEN
      cases_tac THEN
      try_holes THEN NO_TAC)
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
   `APPEND core_mc barrier_inst_bytes` inside assumption
   (e.g., nonoverlapping (pc, LENGTH core_mc) ...) and
   precondition (e.g., aligned_bytes_loaded core_mc).

   This is a method to prove the ensures predicate with the
   barrier_inst_bytes-appended version without modifying its proof.
   This uses ENSURES_SUBLEMMA_THM.
   If barrier_inst_bytes was not appended, but inserted inside the program,
   then this approach cannot be used because implication between two
   preconditions will not hold.

   Note that the resulting ensures predicate is now hard to be used for
   compositional reasoning. Since the barrier instruction is appended,
   no program (other than one starting with a barrier instruction; such a
   program is useless in practice) can come next to the code, making
   composition of two sequential programs impossible.
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
      POP_ASSUM_LIST (fun th -> MP_TAC (end_itlist CONJ th)) THEN
      REWRITE_TAC[ALL;NONOVERLAPPING_CLAUSES;LENGTH_APPEND;
                  BARRIER_INST_BYTES_LENGTH] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      (REPEAT CONJ_TAC THEN (NONOVERLAPPING_TAC ORELSE
       (PRINT_TAC "prove_correct_barrier_appended failed" THEN
        PRINT_GOAL_TAC THEN NO_TAC)));
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

(* When ASM_MESON_TAC cannot discharge the final goal state because the
   goal is `exists ...`, you can use exists_params to instantiate the
   variables. *)
let prove_ensures_n ?(exists_params:term list option)
    execth core_execth (correct_th:thm) (event_n_at_pc_th:thm): thm =
  let correct_th = prove_correct_barrier_appended correct_th core_execth in
  let to_eventually_th = REWRITE_RULE [fst execth;fst core_execth] event_n_at_pc_th in
  let to_eventually_th = CONV_RULE NUM_REDUCE_CONV to_eventually_th in
  let to_eventually_th = REWRITE_RULE[
      eventually_n_at_pc;
      TAUT `(P==>(!x. Q x)) <=> (!x. P==>Q x)`;
      TAUT`(PRECOND==>(P==>Q==>R))<=>(PRECOND/\P/\Q==>R)`]
    to_eventually_th in
  (* unfold LENGTH mc and LENGTH (APPEND .. )) *)
  let eventually_form =
    (CONV_RULE NUM_REDUCE_CONV o
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

    ((match exists_params with
     | None -> NO_TAC
     | Some ls -> MAP_EVERY EXISTS_TAC ls THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC eventually_form THEN ASM_REWRITE_TAC[] THEN
        NO_TAC) ORELSE
     (ASM_MESON_TAC[eventually_form] ORELSE
      ASM_MESON_TAC[ALL;NONOVERLAPPING_CLAUSES;NONOVERLAPPING_MODULO_SYM;
                    eventually_form]) ORELSE
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
            ASSUME_TAC (CONV_RULE NUM_REDUCE_CONV res))
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
  equiv_in and equiv_out's first two universal quantifiers must be armstates.
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


(* Given two ensures2 theorems, combine them using ENSURES2_CONJ2 and put the
   result as an antecendent. If any or both of the two theorems have assumption
   like `(assumption) ==> ensures2`, this tactic tries to prove the
   assumption(s). *)
let ENSURES2_CONJ2_TRANS_TAC ensures2th ensures2th2 =
  (* instantiate first ensures2 theorem *)
  MP_TAC (SPEC_ALL (SPECL [`pc:num`;`pc3:num`] ensures2th)) THEN
  APPLY_IF is_imp (ANTS_TAC THENL [
    ASM_REWRITE_TAC[] THEN REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[ALL;NONOVERLAPPING_CLAUSES] THEN
    REPEAT STRIP_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC]) THEN
  DISCH_THEN (LABEL_TAC "_tmp_trans1") THEN
  (* instantiate second ensures2 theorem *)
  MP_TAC (SPEC_ALL (SPECL [`pc3:num`;`pc2:num`] ensures2th2)) THEN
  APPLY_IF is_imp (ANTS_TAC THENL [
    ASM_REWRITE_TAC[] THEN REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[ALL;NONOVERLAPPING_CLAUSES;MODIFIABLE_SIMD_REGS;
                MODIFIABLE_GPRS;MODIFIABLE_UPPER_SIMD_REGS] THEN
    REPEAT STRIP_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC]) THEN
  DISCH_THEN (LABEL_TAC "_tmp_trans2") THEN

  REMOVE_THEN "_tmp_trans1" (fun c1 ->
    REMOVE_THEN "_tmp_trans2" (fun c2 ->
      MP_TAC (REWRITE_RULE [] (MATCH_MP ENSURES2_CONJ2 (CONJ c1 c2)))
    ));;

(* Given two program equivalences between three programs, say
   equiv1_th: 'equiv1 p1 p2' and equiv2_th: 'equiv2 p2 p3',
   prove 'equiv p1 p3'.
   eq1_in_state_th and eq2_in_state_th are definitions of custom predicates
   describing input program equivalences in these two cases. *)

let EQUIV_TRANS_TAC
    (equiv1_th,equiv2_th)
    (eq1_in_state_th,eq2_in_state_th,eq_main_in_state_th)
    eq_out_state_trans_th
    (P1_EXEC,P2_EXEC,P3_EXEC) =
  let p2_mc =
    let len_p2_mc = fst (dest_eq (concl (fst P2_EXEC))) in
    snd (dest_comb len_p2_mc) in
  let interm_state =
    subst [p2_mc,`p2_mc:((8)word)list`]
      `write (memory :> bytelist (word pc3,LENGTH (p2_mc:((8)word)list)))
             p2_mc (write PC (word pc3) s')`
    and eq_main_in_const =
      let def = fst (dest_eq (snd (strip_forall (concl eq_main_in_state_th)))) in
      fst (strip_comb def) in

  ENSURES2_CONJ2_TRANS_TAC equiv1_th equiv2_th THEN

  (* break 'ALL nonoverlapping' in assumptions *)
  RULE_ASSUM_TAC (REWRITE_RULE[
      ALLPAIRS;ALL;fst P1_EXEC;fst P2_EXEC;fst P3_EXEC;NONOVERLAPPING_CLAUSES]) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN

  MATCH_MP_TAC ENSURES2_WEAKEN THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (* Prove that, from the main goal equivalence's precondition,
       the existential form of the combined preconditions
       (generated by ENSURES2_CONJ2_TRANS_TAC) is true. *)
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(p /\ q /\ r) /\ p /\ q /\ r' <=> p /\ q /\ r /\ r'`] THEN
    EXISTS_TAC interm_state THEN

    PROVE_CONJ_OF_EQ_READS_TAC P2_EXEC THENL [
      (* Undischarge `eq_main_in_state_th (s,s') (args..)`. *)
      FIRST_ASSUM (fun th ->
        if fst (strip_comb (concl th)) = eq_main_in_const
        then UNDISCH_TAC (concl th) else ALL_TAC) THEN
      REWRITE_TAC[eq1_in_state_th;C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;fst P2_EXEC;
                  mk_equiv_regs] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT (TRY HINT_EXISTS_REFL_TAC THEN
              CHANGED_TAC (PROVE_CONJ_OF_EQ_READS_TAC P2_EXEC))
      THEN PRINT_GOAL_TAC THEN NO_TAC;

      (* Undischarge `eq2_in_state_th (s,s') (args..)`. *)
      FIRST_ASSUM (fun th ->
        if fst (strip_comb (concl th)) = eq_main_in_const
        then UNDISCH_TAC (concl th) else ALL_TAC) THEN
      REWRITE_TAC[eq_main_in_state_th;eq2_in_state_th;C_ARGUMENTS;
                  BIGNUM_FROM_MEMORY_BYTES;fst P2_EXEC;
                  mk_equiv_regs] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT (TRY HINT_EXISTS_REFL_TAC THEN
              CHANGED_TAC (PROVE_CONJ_OF_EQ_READS_TAC P2_EXEC))
      THEN PRINT_GOAL_TAC THEN NO_TAC;
    ];

    (* Prove that the main postcondition can be proven. *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[eq_out_state_trans_th];

    SUBSUMED_MAYCHANGE_TAC
  ];;


let EQUIV_TRANS_GEN_TAC
    (equiv1_th,equiv2_th)
    (eq1_in_state_th,eq2_in_state_th,eq_main_in_state_th)
    eq_out_state_trans_th
    (P1_EXEC,P2_EXEC,P3_EXEC) =
  let p2_mc =
    let len_p2_mc = fst (dest_eq (concl (fst P2_EXEC))) in
    snd (dest_comb len_p2_mc) in
  let interm_state =
    subst [p2_mc,`p2_mc:((8)word)list`]
      `write (memory :> bytelist (word pc3,LENGTH (p2_mc:((8)word)list)))
             p2_mc (write PC (word pc3) s')`
    and eq_main_in_const =
      let def = fst (dest_eq (snd (strip_forall (concl eq_main_in_state_th)))) in
      fst (strip_comb def) in

  ENSURES2_CONJ2_TRANS_TAC equiv1_th equiv2_th THEN

  (* break 'ALL nonoverlapping' in assumptions *)
  RULE_ASSUM_TAC (REWRITE_RULE[
      ALLPAIRS;ALL;fst P1_EXEC;fst P2_EXEC;fst P3_EXEC;NONOVERLAPPING_CLAUSES]) THEN
  REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN

  MATCH_MP_TAC ENSURES2_WEAKEN THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [
    (* Prove that, from the main goal equivalence's precondition,
       the existential form of the combined preconditions
       (generated by ENSURES2_CONJ2_TRANS_TAC) is true. *)
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(p /\ q /\ r) /\ p /\ q /\ r' <=> p /\ q /\ r /\ r'`] THEN
    EXISTS_TAC interm_state THEN

    PROVE_CONJ_OF_EQ_READS_TAC P2_EXEC THENL [
      (* Undischarge `eq_main_in_state_th (s,s') (args..)`. *)
      FIRST_ASSUM (fun th ->
        if fst (strip_comb (concl th)) = eq_main_in_const
        then UNDISCH_TAC (concl th) else ALL_TAC) THEN
      REWRITE_TAC[eq1_in_state_th;eq_main_in_state_th;C_ARGUMENTS;BIGNUM_FROM_MEMORY_BYTES;fst P2_EXEC;
                  mk_equiv_regs] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT (TRY HINT_EXISTS_REFL_TAC THEN
              CHANGED_TAC (PROVE_CONJ_OF_EQ_READS_TAC P2_EXEC))
      THEN PRINT_GOAL_TAC THEN NO_TAC;

      (* Undischarge `eq2_in_state_th (s,s') (args..)`. *)
      FIRST_ASSUM (fun th ->
        if fst (strip_comb (concl th)) = eq_main_in_const
        then UNDISCH_TAC (concl th) else ALL_TAC) THEN
      REWRITE_TAC[eq_main_in_state_th;eq2_in_state_th;C_ARGUMENTS;
                  BIGNUM_FROM_MEMORY_BYTES;fst P2_EXEC;
                  mk_equiv_regs] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT (TRY HINT_EXISTS_REFL_TAC THEN
              CHANGED_TAC (PROVE_CONJ_OF_EQ_READS_TAC P2_EXEC))
      THEN PRINT_GOAL_TAC THEN NO_TAC;
    ];

    (* Prove that the main postcondition can be proven. *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[eq_out_state_trans_th];

    SUBSUMED_MAYCHANGE_TAC
  ];;

(* Given a goal `ensures ..` which is a spec of program p, generate a
   verification condition from two lemmas:
  1. equiv_th: a program equivalence theorem between p and another program p2
  2. ensures_n_th: a specification of p2 in `ensures_n`.
  mc_length_ths is a list of LENGTH *_mc theorems for p1 and p2 used in equiv_th's
  hypotheses, specifically the nonoverlapping predicates.
  The result of tactic is conjunction of three clauses.
  If arm_print_log is set to true, it prints more info. *)
let VCGEN_EQUIV_TAC equiv_th ensures_n_th mc_length_ths =
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
      let ensures_n_part = SPEC_ALL ensures_n_th in
      let equiv_part = SPEC_ALL equiv_th in
      let conj_ensures_n_equiv = CONJ ensures_n_part equiv_part in
      MATCH_MP (TAUT`((P==>Q)/\(R==>S)) ==> ((P/\R)==>(Q/\S))`) conj_ensures_n_equiv) THEN

  (* Try to prove the assumptions of equiv_th and
     ensures_n_th, which are in ASSUM of
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

  W (fun (asl,w) ->
    if is_imp w then
      let r = ([ALL;NONOVERLAPPING_CLAUSES;LENGTH_APPEND;
                BARRIER_INST_BYTES_LENGTH] @ mc_length_ths) in
      SUBGOAL_THEN (fst (dest_imp (fst (dest_imp w))))
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
   ensures_n spec of P1, prove ensures spec of P2.
   ensures_n_th must have the barrier instruction appended after
   the main machine code. *)
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
(* Sequentially composing two program equivalences and making a theorem      *)
(* on a larger program equivalence between the two composed programs.        *)
(* ------------------------------------------------------------------------- *)

let prove_equiv_seq_composition (equivth1:thm) (equivth2:thm)
    (prog1_out_implies_prog2_in_thm:thm) =
  (* step 1. let's make a goal. *)
  let quants1,body1 = strip_forall (concl equivth1) and
      quants2,body2 = strip_forall (concl equivth2) in
  (* check that there is no quantified variable with same name but different types. *)
  if List.exists2 (fun t1 t2 -> name_of t1 = name_of t2 && type_of t1 <> type_of t2)
                  quants1 quants2
  then failwith "has quantified variable with same name but different types" else
  let quants = union quants1 quants2 in

  (* break '(assums) ==> ensures ...' *)
  let assums1,body1 = if is_imp body1 then dest_imp body1 else `T`,body1 and
      assums2,body2 = if is_imp body2 then dest_imp body2 else `T`,body2 in
  let assums =
    if assums1 = assums2 then assums1 else begin
    Printf.printf "assumptions are different.. breaking conjunctions & merging";
    let cjs1 = conjuncts assums1 and cjs2 = conjuncts assums2 in
    list_mk_conj (union cjs1 cjs2) end in

  (* get pre/post/frame/steps *)
  let ensures_const,[arm_const;precond1;postcond1;frame1;step11;step12] =
      strip_comb body1 in
  if name_of ensures_const <> "ensures2"
  then failwith "equivth1 is not ensures2" else
  if name_of arm_const <> "arm"
  then failwith "equivth1 is not ensures2 arm" else
  let ensures_const,[arm_const;precond2;postcond2;frame2;step21;step22] =
      strip_comb body2 in
  if name_of ensures_const <> "ensures2"
  then failwith "equivth2 is not ensures2" else
  if name_of arm_const <> "arm"
  then failwith "equivth1 is not ensures2 arm" else

  let postcond1_vars, postcond1_body = dest_gabs postcond1 and
      precond2_vars, precond2_body = dest_gabs precond2 in
  let postcond1_var1,postcond1_var2 = dest_pair postcond1_vars and
      precond2_var1,precond2_var2 = dest_pair precond2_vars in
  let [frame1_vars1;frame1_vars2], frame1_body = strip_gabs frame1 and
      [frame2_vars1;frame2_vars2], frame2_body = strip_gabs frame2 and
      step11_var,step11_body = dest_abs step11 and
      step12_var,step12_body = dest_abs step12 and
      step21_var,step21_body = dest_abs step21 and
      step22_var,step22_body = dest_abs step22 in
  if frame1_vars1 <> frame2_vars1 || frame1_vars2 <> frame2_vars2
  then failwith "lambda variables of frames mismatch" else
  if step11_var <> step21_var || step12_var <> step22_var
  then failwith "lambda variables of steps mismatch" else

  (* simplify maychange first, then make the maychange term *)
  let frame1_body_left,frame1_body_right = dest_conj frame1_body and
      frame2_body_left,frame2_body_right = dest_conj frame2_body in
  let combine_maychanges t1 t2 =
      let t1' = fst (dest_comb (fst (dest_comb t1))) and
          t2' = fst (dest_comb (fst (dest_comb t2))) in
      let res = mk_icomb (mk_icomb (`,,`,t1'),t2') in
      let res' = REWRITE_CONV[GSYM SEQ_ASSOC] res in
      snd (dest_eq (concl res')) in
  let new_maychange1 =
      simplify_maychanges (combine_maychanges frame1_body_left frame2_body_left) in
  let new_maychange1 = list_mk_comb (new_maychange1,
    let s,s' = fst (dest_pair frame1_vars1),fst (dest_pair frame1_vars2) in [s;s']) in
  let new_maychange2 =
      simplify_maychanges (combine_maychanges frame1_body_right frame2_body_right) in
  let new_maychange2 = list_mk_comb (new_maychange2,
    let s2,s2' = snd (dest_pair frame1_vars1),snd (dest_pair frame1_vars2) in [s2;s2']) in
  let new_maychange = list_mk_gabs ([frame1_vars1;frame1_vars2],
    mk_conj(new_maychange1,new_maychange2)) in

  (* make a new step. *)
  let new_step1 = mk_abs (step11_var,(mk_binary "+" (step11_body,step21_body))) and
      new_step2 = mk_abs (step12_var,(mk_binary "+" (step12_body,step22_body))) in

  (* build a new ensures2 *)
  let new_ensures2 = list_mk_icomb "ensures2"
      [`arm`;precond1;postcond2;new_maychange;new_step1;new_step2] in
  (* finally, make a goal! *)
  let new_goal = list_mk_forall (quants,
    if assums = `T` then new_ensures2 else mk_imp (assums,new_ensures2)) in
  prove(new_goal,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES2_TRANS_GEN THEN
    MAP_EVERY EXISTS_TAC [postcond1;precond2;frame1;frame2] THEN
    REPEAT CONJ_TAC THENL [
      (* First ensures2 *)
      ASM_MESON_TAC[equivth1];

      (* Second ensures2 *)
      ASM_MESON_TAC[equivth2];

      (* The implication between postcond1 and precond2 *)
      REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      (ASM_MESON_TAC[prog1_out_implies_prog2_in_thm] ORELSE PRINT_GOAL_TAC);

      (* Maychanges: copid from ENSURES2_FRAME_SUBSUMED_TAC modulo its first line *)
      REWRITE_TAC[subsumed;FORALL_PAIR_THM;SEQ_PAIR_SPLIT;ETA_AX;SOME_FLAGS] THEN
      REPEAT STRIP_TAC THENL
      (* two subgoals from here *)
      replicate
        ((fun (asl,g) ->
          let st,st' = rand(rator g), rand g in
          (FIRST_X_ASSUM (fun th ->
            if rand(concl th) = st' then
              MP_TAC th THEN MAP_EVERY SPEC_TAC [(st',st');(st,st)]
            else NO_TAC)) (asl,g)) THEN
        REWRITE_TAC[GSYM subsumed; ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC)
        2
    ]);;

(* ------------------------------------------------------------------------- *)
(* Load convenient OCaml functions for merging two lists of actions which    *)
(* are obtained from diff(file1, file2) and diff(file2, file3).              *)
(* ------------------------------------------------------------------------- *)

needs "common/actions_merger.ml";;

(* ------------------------------------------------------------------------- *)
(* Replace loads in actions that are marked as 'equal' with 'replace'.       *)
(* 'actions' is the input of EQUIV_STEPS_TAC. The loads are instructions     *)
(* starting with 'arm_LD'.                                                   *)
(* This prevents EQUIV_STEPS_TAC from abbreviating the expressions represen- *)
(* ting the output of load. A main use case (2024) is vectorization involving*)
(* memory loads. It loads a same memory location using one ldp to a pair of  *)
(* X registers and one ldr to one Q register. If one of these loads is       *)
(* abbreviated, then we lose the fact that ldr to Q is word_join of the ldp  *)
(* Xs.                                                                       *)
(* For example, let's assume that read memory from x3 by some large (n)      *)
(* bytes is a. The output of ARM_N_STEP_TAC of ldp x1, x2, [x3] will be:     *)
(*   read X1 s = bigdigit 0 a /\ read X2 s = bigdigit 1 a /\                 *)
(*   read (memory :> bytes64 X3) = bigdigit 0 a /\                           *)
(*   read (memory :> bytes64 (word_add X3 (word 8)) = bigdigit 1 a           *)
(* The former two equations will be abbreivated by ABBREV_READS_TAC whereas  *)
(* the latter two equations will be unchanged and kept as assumptions when   *)
(* "equiv" was its action. break_equal_loads will change this action to      *)
(* "replace" so that the former two equations are not abbreviated.           *)
(* ------------------------------------------------------------------------- *)

let rec break_equal_loads actions (decodeth1:thm option array) pcbegin1
                                 (decodeth2:thm option array) pcbegin2 =
  let get_opname_from_decode (th:thm option):string =
    let th = Option.get th in
    (* th is: `|- forall s pc.
           aligned_bytes_loaded s (word pc) bignum_montsqr_p256_mc
           ==> arm_decode s (word (pc + 216)) (arm_ADC X8 X8 XZR)` *)
    let rhs = snd (dest_imp (snd (strip_forall (concl th)))) in
    let arm_blah = last (snd (strip_comb rhs)) in
    name_of (fst (strip_comb arm_blah)) in
  match actions with
  | [] -> []
  | ("equal",beg1,end1,beg2,end2)::tail ->
    let _ = assert (end1 - beg1 = end2 - beg2) in
    let numinsts = end1 - beg1 in
    let actions_expanded = ref [] in
    (* the range of "equal". *)
    let eq_start_i = ref 0 in
    (* the range of "arm_LD*". *)
    let ld_start_i = ref (-1) in

    let add_action_equal i = begin
      assert (!eq_start_i <> -1);
      actions_expanded := !actions_expanded @
        [("equal", beg1+ !eq_start_i, beg1+i, beg2+ !eq_start_i, beg2+i)];
      eq_start_i := -1
    end in
    let add_action_replace i = begin
      assert (!ld_start_i <> -1);
      actions_expanded := !actions_expanded @
        [("replace", beg1+ !ld_start_i, beg1+i, beg2+ !ld_start_i, beg2+i)];
      ld_start_i := -1
    end in

    for i = 0 to numinsts - 1 do
      let opname1 = get_opname_from_decode decodeth1.(pcbegin1 + 4 * (beg1 + i)) in
      let opname2 = get_opname_from_decode decodeth2.(pcbegin2 + 4 * (beg2 + i)) in
      if opname1 <> opname2 then failwith
        (Printf.sprintf "Op not equal: %s vs. %s" opname1 opname2) else
      if String.starts_with ~prefix:"arm_LD" opname1 then
        if !ld_start_i = -1 then begin
          (* first load *)
          (* flush ("equal", eq_start_i ~ i-1) *)
          (if i <> 0 then add_action_equal i else eq_start_i := -1);
          ld_start_i := i
        end else
          (* keep growing.. *)
          ()
      else
        if !eq_start_i = -1 then begin
          (* first non-load *)
          (* flush ("replace", ld_start_i ~ i-1) *)
          add_action_replace i;
          eq_start_i := i
        end else
          ()
    done;
    if !eq_start_i <> -1 then add_action_equal numinsts
    else (assert (!ld_start_i <> -1); add_action_replace numinsts);
    !actions_expanded @ break_equal_loads tail decodeth1 pcbegin1 decodeth2 pcbegin2
  | head::tail -> head::(break_equal_loads tail decodeth1 pcbegin1 decodeth2 pcbegin2);;
