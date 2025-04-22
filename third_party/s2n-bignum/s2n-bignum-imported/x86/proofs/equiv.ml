(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reasoning program equivalence for X86 programs.                           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/equiv.ml";;


(* ------------------------------------------------------------------------- *)
(* eventually_n_at_pc states that if pre/postconditions at pc/pc2 are        *)
(* satisfied at nth step, you can 'promote' eventually to eventually_n.      *)
(* ------------------------------------------------------------------------- *)

let eventually_n_at_pc = new_definition
  `!pc_mc pc pc2 (nth:num) (mc:((8)word)list) (s0_pred:x86state->bool).
    eventually_n_at_pc pc_mc mc pc pc2 nth s0_pred
      <=>
    (!s (P:x86state->x86state->bool).
      bytes_loaded s (word pc_mc) mc /\ read RIP s = word pc /\
      s0_pred s ==>
      eventually x86 (\s'. read RIP s' = word pc2 /\ P s s') s ==>
      eventually_n x86 nth (\s'. read RIP s' = word pc2 /\ P s s') s)`;;

let ENSURES_AND_EVENTUALLY_N_AT_PC_PROVES_ENSURES_N = prove(
  `forall Pre pc_mc mc pc n.
    eventually_n_at_pc pc_mc mc pc pc2 n Pre
    ==> forall Post R.
      ensures x86
        (\s. bytes_loaded s (word pc_mc) mc /\ read RIP s = word pc /\
             Pre s)
        (\s. read RIP s = word pc2 /\ Post s)
        R
      ==> ensures_n x86
        (\s. bytes_loaded s (word pc_mc) mc /\ read RIP s = word pc /\
             Pre s)
        (\s. read RIP s = word pc2 /\ Post s)
        R (\s. n)`,

  REPEAT GEN_TAC THEN
  REWRITE_TAC[eventually_n_at_pc;ensures;ensures_n] THEN
  INTRO_TAC "H2" THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "H1" THEN
  GEN_TAC THEN INTRO_TAC "HA HB HC" THEN
  REMOVE_THEN "H1" (fun th -> MP_TAC (SPECL [`s:x86state`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (LABEL_TAC "H1") THEN
  REMOVE_THEN "H2" (fun th -> MP_TAC (SPECL
    [`s:x86state`;`(\(s:x86state) (s2:x86state). Post s2 /\ R s s2)`] th)) THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* A "barrier" instruction that makes x86 program stop.                      *)
(* ------------------------------------------------------------------------- *)

(* A "barrier" instruction that cannot be decoded in x86.
   It is UD2 (Undefined instruction). https://www.felixcloutier.com/x86/ud
   ADD1's hoare triple must hold on a program that ends with this
   barrier_inst, and this is due to an interesting property of
   the underlying theory of hoare logic for machine codes.
   https://www.cl.cam.ac.uk/~mom22/mc-hoare-logic.pdf
*)
let barrier_inst_bytes = new_definition(`barrier_inst_bytes = [word 0x0F; word 0x0B]:((8)word)list`);;

let DECODE_TO_NONE_CONV:conv =
  REWRITE_CONV[decode;barrier_inst_bytes;APPEND] THENC
  ONCE_REWRITE_CONV[read_prefixes] THENC
  ONCE_DEPTH_CONV BITMATCH_SEQ_CONV THENC
  REWRITE_CONV[obind;read_REX_prefix] THENC
  ONCE_DEPTH_CONV BITMATCH_SEQ_CONV THENC
  ONCE_DEPTH_CONV let_CONV THENC
  REWRITE_CONV[decode_aux;read_byte_val;obind] THENC
  ONCE_DEPTH_CONV BITMATCH_SEQ_CONV THENC
  REWRITE_CONV[read_byte_val;obind] THENC
  ONCE_DEPTH_CONV BITMATCH_SEQ_CONV;;

let BARRIER_INST_DECODE_NONE = prove(`!l. decode (APPEND barrier_inst_bytes l) = NONE`,
  GEN_TAC THEN
  CONV_TAC (LAND_CONV DECODE_TO_NONE_CONV) THEN
  REFL_TAC);;

let BARRIER_INST_BYTES_LENGTH = prove(`LENGTH barrier_inst_bytes = 2`,
    REWRITE_TAC[barrier_inst_bytes;LENGTH] THEN ARITH_TAC);;

prove_conj_of_eq_reads_unfold_rules :=
  BARRIER_INST_BYTES_LENGTH::!prove_conj_of_eq_reads_unfold_rules;;

let BYTES_LOADED_BARRIER_X86_STUCK = prove(
  `!s s' pc. bytes_loaded s (word pc) barrier_inst_bytes /\
          read RIP s = word pc /\ x86 s s' ==> F`,
    REWRITE_TAC[x86;x86_decode;barrier_inst_bytes] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `read RIP s = word pc` SUBST_ALL_TAC THEN
    (* There are three cases for l: [], [15], APPEND([15;11], l') *)
    DISJ_CASES_TAC (ISPEC `l:((8)word)list` list_CASES) THENL
    (** empty list **)
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     UNDISCH_TAC `decode [] = SOME (instr,[])` THEN
     CONV_TAC (LAND_CONV DECODE_TO_NONE_CONV) THEN
     REWRITE_TAC[OPTION_DISTINCT]; ALL_TAC] THEN
    (** list with >=1 elem **)
    REPEAT_N 2 (FIRST_X_ASSUM CHOOSE_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    DISJ_CASES_TAC (ISPEC `t:((8)word)list` list_CASES) THENL
    (** list with 1 elem **)
    [ FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `[word 15;word 11]:((8)word)list = APPEND [word 15] [word 11]` SUBST_ALL_TAC THENL
      [REWRITE_TAC[APPEND] THEN FAIL_TAC "unfinished"; ALL_TAC] THEN
      (* show that h is 15 *)
      RULE_ASSUM_TAC (REWRITE_RULE [bytes_loaded_append]) THEN
      SPLIT_FIRST_CONJ_ASSUM_TAC THEN
      SUBGOAL_THEN `[h]:((8)word)list = [word 15]` SUBST_ALL_TAC THENL
      [ SUBGOAL_THEN `LENGTH ([word 15]:((8)word)list) = LENGTH ([h]:((8)word)list)` ASSUME_TAC THENL
        [REWRITE_TAC[LENGTH] THEN ARITH_TAC;ALL_TAC] THEN
        ASM_MESON_TAC[bytes_loaded_unique];
        ALL_TAC] THEN
      (* now unfold decode [15] *)
      UNDISCH_TAC `decode ([word 15]:((8)word)list) = SOME (instr,[])` THEN
      CONV_TAC (LAND_CONV DECODE_TO_NONE_CONV) THEN
      REWRITE_TAC[OPTION_DISTINCT] THEN FAIL_TAC "unfinished";

      ALL_TAC
    ] THEN
    (** list with >=2 elems **)
    REPEAT_N 2 (FIRST_X_ASSUM CHOOSE_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(CONS h (CONS h' t')):((8)word)list = APPEND [h;h'] t'` SUBST_ALL_TAC THENL
    [ REWRITE_TAC[APPEND] THEN FAIL_TAC "unfinished"; ALL_TAC ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [bytes_loaded_append]) THEN
    SPLIT_FIRST_CONJ_ASSUM_TAC THEN
    SUBGOAL_THEN `[h;h']:((8)word)list = [word 15; word 11]` SUBST_ALL_TAC THENL
    [ SUBGOAL_THEN `LENGTH ([word 15;word 11]:((8)word)list) = LENGTH ([h;h']:((8)word)list)` ASSUME_TAC THENL
      [REWRITE_TAC[LENGTH] THEN ARITH_TAC;ALL_TAC] THEN
      ASM_MESON_TAC[bytes_loaded_unique];
      ALL_TAC
    ] THEN
    UNDISCH_TAC `decode (APPEND ([word 15;word 11]:((8)word)list) t') = SOME (instr,[])` THEN
    CONV_TAC (LAND_CONV DECODE_TO_NONE_CONV) THEN
    REWRITE_TAC[OPTION_DISTINCT]
  );;


(* ------------------------------------------------------------------------- *)
(* Tactics for simulating a program whose postcondition is eventually_n.     *)
(* ------------------------------------------------------------------------- *)

(* A variant of X86_BASIC_STEP_TAC, but
   - targets eventually_n
   - preserves 'x86 s sname' at assumption *)
let X86_N_BASIC_STEP_TAC =
  let x86_tm = `x86` and x86_ty = `:x86state` and one = `1:num` in
  fun decode_th sname store_inst_term_to (asl,w) ->
    (* w = `eventually_n _ {stepn} _ {sv}` *)
    let sv = rand w and sv' = mk_var(sname,x86_ty) in
    let atm = mk_comb(mk_comb(x86_tm,sv),sv') in
    let eth = X86_CONV decode_th (map snd asl) atm in
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
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth] THEN
      REPEAT X86_UNDEFINED_CHOOSE_TAC]) (asl,w);;


(* A variant of X86_STEP_TAC for equivalence checking.

   If 'store_update_to' is Some ref, a list of
   (`read .. = expr`) will be stored instead of added as assumptions.
   It will store a pair of lists, where the first list is the output of
   the instruction in `read .. = expr` form, and the second list is
   auxiliary `read (memory :> reads...) = ..` equalities that were constructed
   in order to formulate the main output, not to formulate the instruction
   outputs. *)
let X86_N_STEP_TAC (mc_length_th,decode_ths) subths sname
                  (store_update_to:(thm list * thm list) ref option)
                  (store_inst_term_to: term ref option)  =
  (*** This does the basic decoding setup ***)

  X86_N_BASIC_STEP_TAC decode_ths sname store_inst_term_to THEN

  (*** This part shows the code isn't self-modifying ***)

  NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update mc_length_th) THEN

  (*** Attempt also to show subroutines aren't modified, if applicable ***)

  MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC o
    MATCH_MP bytes_loaded_update o CONJUNCT1) subths THEN

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

(* A variant of X86_STEPS_TAC but uses DISCARD_OLDSTATE_AGGRESSIVELY_TAC
   instead.
   TODO: receive dead value info & use it, as X86_N_STEPS_TAC does *)
let X86_N_STEPS_TAC th snums stname_suffix stnames_no_discard =
  let stnames = List.map (fun s -> s ^ stname_suffix) (statenames "s" snums) in
  MAP_EVERY (fun stname ->
    time (X86_N_STEP_TAC th [] stname None) None THEN
          DISCARD_OLDSTATE_AGGRESSIVELY_TAC (stname::stnames_no_discard)
            false)
          stnames;;


(* ------------------------------------------------------------------------- *)
(* Definitions for stating program equivalence.                              *)
(* ------------------------------------------------------------------------- *)

(* A recursive function for defining a conjunction of equality clauses *)
let mk_equiv_regs = define
  `((mk_equiv_regs:((x86state,(N)word)component)list->x86state#x86state->bool)
      [] s = true) /\
   (mk_equiv_regs (CONS reg regs) (s1,s2) =
     (mk_equiv_regs regs (s1,s2) /\
      exists (a:(N)word). read reg s1 = a /\ read reg s2 = a))`;;

let mk_equiv_regs2 = define
  `((mk_equiv_regs2
    :((x86state,(N)word)component)list->
     ((x86state,(N)word)component)list->x86state#x86state->bool)
      [] [] s = true) /\
   (mk_equiv_regs2 (CONS reg regs) (CONS reg2 regs2) (s1,s2) =
     (mk_equiv_regs2 regs regs2 (s1,s2) /\
      exists (a:(N)word). read reg s1 = a /\ read reg2 s2 = a))`;;

let mk_equiv_bool_regs = define
  `((mk_equiv_bool_regs:((x86state,bool)component)list->x86state#x86state->bool)
      [] s = true) /\
   (mk_equiv_bool_regs (CONS reg regs) (s1,s2) =
     (mk_equiv_bool_regs regs (s1,s2) /\
      exists (a:bool). read reg s1 = a /\ read reg s2 = a))`;;


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
let X86_LOCKSTEP_TAC =
  let update_eqs_prog1: (thm list * thm list) ref = ref ([],[]) in
  let update_eqs_prog2: (thm list * thm list) ref = ref ([],[]) in

  let the_sp = `RSP` in
  let forget_expr (comp:term) = comp <> the_sp in

  fun execth execth' (snum:int) (snum':int) (stname'_suffix:string) ->
    let new_stname = "s" ^ (string_of_int snum) in
    let new_stname' = "s" ^ (string_of_int snum') ^ stname'_suffix in

    (* 1. One step on the left program. *)
    (* Get the right program's current state name "s'" from
       `eventually_n x86 n (\s. eventually_n x86 n' .. s') s`,
       and stash assumptions over the right state. *)
    (fun (asl,g) ->
      (* Print log *)
      Printf.printf "X86_LOCKSTEP_TAC (%d,%d)\n%!" snum snum';
      Printf.printf "Running left...\n";
      let cur_stname' = name_of (rand (snd ((dest_abs o rand o rator) g))) in
      STASH_ASMS_OF_READ_STATES [cur_stname'] (asl,g)) THEN
    X86_N_STEP_TAC execth [] new_stname (Some update_eqs_prog1) None THEN
    (*cleanup assumptions that use old abbrevs*)
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC [new_stname] false THEN
    RECOVER_ASMS_OF_READ_STATES THEN

    (* 2. One step on the right program. *)
    (fun (asl,g) -> Printf.printf "Running right...\n"; ALL_TAC (asl,g)) THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    STASH_ASMS_OF_READ_STATES [new_stname] THEN
    X86_N_STEP_TAC execth' [] new_stname' (Some update_eqs_prog2) None THEN
    (*cleanup assumptions that use old abbrevs*)
    DISCARD_OLDSTATE_AGGRESSIVELY_TAC [new_stname'] true THEN
    (* .. and dead registers. *)
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
         failwith "X86_LOCKSTEP_TAC")
      else if List.length aux_mem_updates_prog1_list <>
              List.length aux_mem_updates_prog2_list
      then
        (Printf.printf "Updated auxiliary memory components mismatch:\n";
         Printf.printf "\tprog1: ";
         List.iter (fun th -> print_qterm (concl th)) aux_mem_updates_prog1_list;
         Printf.printf "\n\tprog2: ";
         List.iter (fun th -> print_qterm (concl th)) aux_mem_updates_prog2_list;
         failwith "X86_LOCKSTEP_TAC")
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
              ABBREV_READS_TAC (eq1,eq2) (forget_expr comp1)
            | _ -> ALL_TAC)
          eqs);;

let EQUIV_INITIATE_TAC input_equiv_states_th =
  ENSURES2_INIT_TAC "s0" "s0'" THEN
  let input_pred = SPEC_ALL
      (SPECL [`s0:x86state`;`s0':x86state`] input_equiv_states_th) in
  UNDISCH_TAC (fst (dest_binary "=" (concl input_pred))) THEN
  GEN_REWRITE_TAC LAND_CONV [input_equiv_states_th] THEN
  REWRITE_TAC [C_ARGUMENTS;SOME_FLAGS;mk_equiv_regs;mk_equiv_regs2;mk_equiv_bool_regs] THEN
  STRIP_TAC;;

let X86_N_STUTTER_LEFT_TAC exec_th (snames:int list): tactic =
  W (fun (asl,w) ->
    (* get the state name of the 'right' program *)
    let t' = fst (dest_comb w) in
    let inner_eventually = snd (dest_abs (snd (dest_comb (t')))) in
    let sname = fst (dest_var (snd (dest_comb inner_eventually))) in
    STASH_ASMS_OF_READ_STATES [sname] THEN
    X86_N_STEPS_TAC exec_th snames "" [] THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    CLARIFY_TAC);;

let X86_N_STUTTER_RIGHT_TAC exec_th (snames:int list) (st_suffix:string)
    : tactic =
  W (fun (asl,w) ->
    (* get the state name of the 'left' program *)
    let sname = fst (dest_var (snd (dest_comb w))) in
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    STASH_ASMS_OF_READ_STATES [sname] THEN
    X86_N_STEPS_TAC exec_th snames st_suffix [] THEN
    RECOVER_ASMS_OF_READ_STATES THEN
    MATCH_MP_TAC EVENTUALLY_N_SWAP THEN
    CLARIFY_TAC);;


(* EQUIV_STEPS_TAC simulates two partially different programs and makes
  abbreviations of the new symbolic expressions after each step.
  Instructions are considered equivalent if they are alpha-equivalent.
  It takes a list of 'action's that describe how the symbolic execution
  engine must be run. Each action is consumed by EQUIV_STEP_TAC and
  a proper tactic is taken.

  Note that this tactic may remove assumptions on abbreviations if they are
  considered unused.

  TODO: implement dead_value_info_left and dead_value_info_right arguments
  as Arm's EQUIV_STEP_TAC and use those.
  TODO2: implement & use SIMPLIFY_MAYCHANGES_TAC as Arm's EQUIV_STEP_TAC does.
*)

let EQUIV_STEP_TAC action execth1 execth2: tactic =
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
        time (X86_LOCKSTEP_TAC execth1 execth2 (il+1) (ir+1) "'")
        THEN (if i mod 20 = 0 then CLEAR_UNUSED_ABBREVS else ALL_TAC)
        THEN CLARIFY_TAC)
  | ("insert",lstart,lend,rstart,rend) ->
    if lstart <> lend then failwith "insert's lstart and lend must be equal"
    else begin
      (if rend - rstart > 50 then
        Printf.printf "Warning: too many instructions: insert %d~%d\n" rstart rend);
      X86_N_STUTTER_RIGHT_TAC execth2 ((rstart+1)--rend) "'"
        ORELSE (PRINT_TAC "insert failed" THEN PRINT_GOAL_TAC THEN NO_TAC)
    end
  | ("delete",lstart,lend,rstart,rend) ->
    if rstart <> rend then failwith "delete's rstart and rend must be equal"
    else begin
      (if lend - lstart > 50 then
        Printf.printf "Warning: too many instructions: delete %d~%d\n" lstart lend);
      X86_N_STUTTER_LEFT_TAC execth1 ((lstart+1)--lend)
        ORELSE (PRINT_TAC "delete failed" THEN PRINT_GOAL_TAC THEN NO_TAC)
    end
  | ("replace",lstart,lend,rstart,rend) ->
    (if lend - lstart > 50 || rend - rstart > 50 then
      Printf.printf "Warning: too many instructions: replace %d~%d %d~%d\n"
          lstart lend rstart rend);
    ((X86_N_STUTTER_LEFT_TAC execth1 ((lstart+1)--lend)
     ORELSE (PRINT_TAC "replace failed: stuttering left" THEN PRINT_GOAL_TAC THEN NO_TAC))
     THEN
     (X86_N_STUTTER_RIGHT_TAC execth2 ((rstart+1)--rend) "'"
      ORELSE (PRINT_TAC "replace failed: stuttering right" THEN PRINT_GOAL_TAC THEN NO_TAC)))
  | (s,_,_,_,_) -> failwith ("Unknown action: " ^ s);;


let EQUIV_STEPS_TAC actions execth1 execth2: tactic =
  MAP_EVERY
    (fun action ->
      EQUIV_STEP_TAC action execth1 execth2)
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


let X86_N_STEP_AND_ABBREV_TAC =
  let update_eqs_prog = ref ([],[]) in
  let inst_term = ref `T` in
  fun execth (new_stname) (store_to:thm list ref)
             (regs_to_avoid_abbrev: term list)->
    (* Stash the right program's state equations first *)
    (fun (asl,g) ->
      let cur_stname' = name_of (rand (snd ((dest_abs o rand o rator) g))) in
      STASH_ASMS_OF_READ_STATES [cur_stname'] (asl,g)) THEN
    (* One step on the left program *)
    X86_N_STEP_TAC execth [] new_stname (Some update_eqs_prog) (Some inst_term) THEN
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
   Unlike X86_N_STEP_AND_ABBREV_TAC, the equations on assigned fresh variables
    (`RHS = assigned_fresh_var`) are added as assumptions. *)
let X86_N_STEPS_AND_ABBREV_TAC execth (snums:int list)
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
      `eventually_n x86 n0 (\s'. eventually_n x86 n1 P s0) s1` in
    let _,assigns,_ = pat g in
    let cur_stname = name_of
      (fst (List.find (fun a,b -> b=`s0:x86state`) assigns)) in
    STASH_ASMS_OF_READ_STATES [cur_stname] (asl,g)) THEN
  MAP_EVERY
    (fun n,regs_to_avoid_abbrev ->
      let stname = "s" ^ (string_of_int n) in
      let store_to_n = ref [] in
      (fun (asl,g) ->
        let _ = Printf.printf "Stepping to state %s..\n%!" stname in
        ALL_TAC (asl,g)) THEN
      X86_N_STEP_AND_ABBREV_TAC execth stname store_to_n regs_to_avoid_abbrev THEN
      (fun (asl,g) ->
        store_to := (map (fun x -> (n,x)) !store_to_n) @ !store_to;
        if !x86_print_log then begin
          Printf.printf "%d new abbreviations (%d in total)\n%!"
            (List.length !store_to_n) (List.length !store_to)
        end;
        ALL_TAC (asl,g)) THEN
      CLARIFY_TAC)
    (zip snums regs_to_avoid_abbrev) THEN
  RECOVER_ASMS_OF_READ_STATES;;

(* For the right program. abbrevs must be generated by X86_N_STEPS_AND_ABBREV_TAC. *)
let X86_N_STEPS_AND_REWRITE_TAC execth (snums:int list) (inst_map: int list)
      (abbrevs: (int * thm) list ref)
      (regs_to_avoid_abbrev: (term list) list option)
      : tactic =
  (* Warning: no nested call of X86_N_STEPS_AND_REWRITE_TAC *)
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
      X86_N_STEP_TAC execth [] stname (Some new_state_eq) (Some inst_term) THEN
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

        (if !x86_print_log then begin
          Printf.printf "X86_N_STEPS_AND_REWRITE_TAC: new_state_eqs:\n";
          List.iter (fun t -> Printf.printf "    `%s`\n" (string_of_term (concl t))) new_state_eqs;
          Printf.printf "X86_N_STEPS_AND_REWRITE_TAC: new_aux_mem_eqs:\n";
          List.iter (fun t -> Printf.printf "    `%s`\n" (string_of_term (concl t))) new_aux_mem_eqs;
        end);

        (* Reading flags may not have 'read flag s = ..' form, but just
            'read flag s' or '~(read flag s)'. They don't need to be rewritten.
           Also, 'read PC' should not be rewritten as well. Collect them
           separately. *)
        let new_state_eqs_norewrite,new_state_eqs =
          List.partition
            (fun th -> not (is_eq (concl th)) || (is_read_pc (lhs (concl th))))
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
                    failwith "X86_N_STEPS_AND_REWRITE_TAC"))
              | None -> begin
                (* This case happens when new_state_eq already has abbreviated RHS *)
                (if !x86_print_log then begin
                  Printf.printf "X86_N_STEPS_AND_REWRITE_TAC: abbrevs_for_st_n does not have matching abbreviation for this: `%s`\n" (string_of_term rhs);
                end);
                None
              end)
            new_state_eqs in
          (if !x86_print_log then begin
            Printf.printf "X86_N_STEPS_AND_REWRITE_TAC: updated new_state_eqs:\n";
            List.iter (fun t -> Printf.printf "    `%s`\n" (string_of_term (concl t))) new_state_eqs;
            Printf.printf "X86_N_STEPS_AND_REWRITE_TAC: new_state_eqs_noabbrev\n";
            List.iter (fun t -> Printf.printf "    `%s`\n" (string_of_term (concl t))) new_state_eqs_noabbrev;
            Printf.printf "X86_N_STEPS_AND_REWRITE_TAC: new_state_eqs_norewrite\n";
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
          failwith "X86_N_STEPS_AND_REWRITE_TAC")) THEN CLARIFY_TAC)
    (zip snums regs_to_avoid_abbrev) THEN
  RECOVER_ASMS_OF_READ_STATES THEN
  CLARIFY_TAC;;


(* ------------------------------------------------------------------------- *)
(* Functions that create statements that are related to program equivalence. *)
(* ------------------------------------------------------------------------- *)

(* mk_equiv_statement creates a term
   `!pc pc2 <other quantifiers>.
      assum ==> ensures2 x86
        (\(s,s2). bytes_loaded s (word pc) mc1 /\
                  read RIP s = word (pc+pc_ofs1) /\
                  bytes_loaded s2 (word pc2) mc2 /\
                  read RIP s2 = word (pc2+pc_ofs2) /\
                  equiv_in (s,s2))
        (\(s,s2). bytes_loaded s (word pc) mc1 /\
                  read RIP s = word (pc+pc_ofs1_to) /\
                  bytes_loaded s2 (word pc2) mc2 /\
                  read RIP s2 = word (pc2+pc_ofs2_to) /\
                  equiv_out (s,s2))
        (\(s,s2) (s',s2'). maychange1 s s' /\ maychange2 s2 s2')
        fnsteps1
        fnsteps2`
  equiv_in and equiv_out's first two universal quantifiers must be x86states.
*)
let mk_equiv_statement (assum:term) (equiv_in:thm) (equiv_out:thm)
    (mc1:thm) (pc_ofs1:int) (pc_ofs1_to:int) (maychange1:term)
    (mc2:thm) (pc_ofs2:int) (pc_ofs2_to:int) (maychange2:term)
    (fnsteps1:term) (fnsteps2:term):term =
  let _ = List.map2 type_check
      [assum;maychange1;maychange2]
      [`:bool`;`:x86state->x86state->bool`;`:x86state->x86state->bool`] in
  let quants_in,equiv_in_body = strip_forall (concl equiv_in) in
  let quants_out,equiv_out_body = strip_forall (concl equiv_out) in
  let _ = if !x86_print_log then
    Printf.printf "quants_in: %s\nquants_out: %s\n%!"
      (String.concat ", " (List.map string_of_term quants_in))
      (String.concat ", " (List.map string_of_term quants_out)) in
  (* equiv_in and equiv_out's first two universal quantifiers must be x86states. *)
  let quants_in_states,quants_in = takedrop 2 quants_in in
  let quants_out_states,quants_out = takedrop 2 quants_out in
  let _ = List.map2 type_check
    (quants_in_states @ quants_out_states)
    [`:x86state`;`:x86state`;`:x86state`;`:x86state`] in
  let quants = union quants_in quants_out in
  let quants = [`pc:num`;`pc2:num`] @ quants in
  (* There might be more free variables in 'assum'. Let's add them too. *)
  let quants = quants @
    (List.filter (fun t -> not (mem t quants)) (frees assum)) in
  let _ = if !x86_print_log then
    Printf.printf "quantifiers: %s\n%!" (String.concat ", "
      (List.map string_of_term quants)) in

  (* Now build 'ensures2' *)
  let mk_bytes_loaded (s:term) (pc_var:term) (mc:term) =
    let _ = List.map2 type_check [s;pc_var;mc] [`:x86state`;`:num`;`:((8)word)list`] in
    let template = `bytes_loaded s (word pc) mc` in
    subst [s,`s:x86state`;mc,`mc:((8)word)list`;pc_var,`pc:num`] template
  in
  let mk_read_pc (s:term) (pc_var:term) (pc_ofs:int):term =
    let _ = List.map2 type_check [s;pc_var] [`:x86state`;`:num`] in
    if pc_ofs = 0 then
      let template = `read RIP s = word pc` in
      subst [s,`s:x86state`;pc_var,`pc:num`] template
    else
      let template = `read RIP s = word (pc+pc_ofs)` in
      subst [s,`s:x86state`;pc_var,`pc:num`;mk_small_numeral(pc_ofs),`pc_ofs:num`]
            template
  in
  let s = `s:x86state` and s2 = `s2:x86state` in
  let pc = `pc:num` and pc2 = `pc2:num` in
  let equiv_in_pred = fst (strip_comb (fst (dest_eq equiv_in_body))) in
  let equiv_out_pred = fst (strip_comb (fst (dest_eq equiv_out_body))) in

  let precond = mk_gabs (`(s:x86state,s2:x86state)`,
    (list_mk_conj [
      mk_bytes_loaded s pc (lhs (concl mc1));
      mk_read_pc s pc pc_ofs1;
      mk_bytes_loaded s2 pc2 (lhs (concl mc2));
      mk_read_pc s2 pc2 pc_ofs2;
      list_mk_comb (equiv_in_pred, (`(s:x86state,s2:x86state)`::quants_in))
    ])) in
  let postcond = mk_gabs (`(s:x86state,s2:x86state)`,
    (list_mk_conj [
      mk_bytes_loaded s pc (lhs (concl mc1));
      mk_read_pc s pc pc_ofs1_to;
      mk_bytes_loaded s2 pc2 (lhs (concl mc2));
      mk_read_pc s2 pc2 pc_ofs2_to;
      list_mk_comb (equiv_out_pred, (`(s:x86state,s2:x86state)`::quants_out))
    ])) in
  let maychange = list_mk_gabs (
    [`(s:x86state,s2:x86state)`;`(s':x86state,s2':x86state)`],
    mk_conj
      (list_mk_comb (maychange1,[`s:x86state`;`s':x86state`]),
       list_mk_comb (maychange2,[`s2:x86state`;`s2':x86state`]))) in

  let _ = List.iter (fun t -> Printf.printf "\t%s\n" (string_of_term t))
    [precond;postcond;maychange;fnsteps1;fnsteps2] in
  let ensures2_pred = list_mk_comb
    (`ensures2:
      (x86state->x86state->bool)->(x86state#x86state->bool)
      ->(x86state#x86state->bool)
      ->(x86state#x86state->x86state#x86state->bool)
      ->(x86state->num)->(x86state->num)->bool`,
     [`x86`;precond;postcond;maychange;fnsteps1;fnsteps2]) in
  let imp = mk_imp (assum,ensures2_pred) in
  list_mk_forall (quants, imp);;

(* Program equivalence between two straight-line programs,
   starting from its begin to end. *)
let mk_equiv_statement_simple (assum:term) (equiv_in:thm) (equiv_out:thm)
    mc1 (exec1:thm * thm option array) (maychange1:term)
    mc2 (exec2:thm * thm option array) (maychange2:term):term =
  let count_num_insts (a:thm option array) =
    let n = ref 0 in
    for i = 0 to Array.length a - 1 do
      if a.(i) <> None then n := 1 + !n
    done;
    !n in
  let mc1_length = Array.length (snd exec1) in
  let mc2_length = Array.length (snd exec2) in
  mk_equiv_statement assum equiv_in equiv_out
    mc1 0 mc1_length maychange1
    mc2 0 mc2_length maychange2
    (mk_abs (`s:x86state`,mk_small_numeral(count_num_insts (snd exec1))))
    (mk_abs (`s:x86state`,mk_small_numeral(count_num_insts (snd exec2))));;
