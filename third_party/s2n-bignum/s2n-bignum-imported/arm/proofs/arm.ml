(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Simplified model of aarch64 (64-bit ARM) semantics.                       *)
(* ========================================================================= *)

let arm_print_log = ref false;;

(* ------------------------------------------------------------------------- *)
(* Stating assumptions about instruction decoding. For ARM we                *)
(* currently go all the way to the semantics in one jump, no asm.            *)
(* ------------------------------------------------------------------------- *)

let arm_decode = new_definition `arm_decode s pc inst <=>
  ?i:int32. aligned_bytes_loaded s pc (bytelist_of_num 4 (val i)) /\
            decode i = SOME inst`;;

let ARM_DECODE_CONS = prove
 (`!s pc l i inst l'. aligned_bytes_loaded s (word pc) l ==>
   read_int32 l = SOME (i, l') ==> decode i = SOME inst ==>
   arm_decode s (word pc) inst /\
   aligned_bytes_loaded s (word (pc + 4)) l'`,
  REWRITE_TAC [read_int32; read_word_eq_some;
    aligned_bytes_loaded_word] THEN
  REPLICATE_TAC 9 STRIP_TAC THEN
  POP_ASSUM_LIST (fun [h1;h2;h3;h4;h5;h6] ->
    let t1,t2 = CONJ_PAIR (REWRITE_RULE
      [GSYM WORD_ADD; h3; bytes_loaded_append; h4] h5) in
    let th1 = MATCH_MP DIVIDES_ADD (CONJ h6 (SPEC `4` DIVIDES_REFL)) in
    REWRITE_TAC [th1; h6; t2; h1; arm_decode; aligned_bytes_loaded_word] THEN
    EXISTS_TAC `i:int32` THEN REWRITE_TAC [h1; h2; VAL_WORD;
      DIMINDEX_32; ARITH_RULE `2 EXP 32 = 256 EXP 4`;
      BYTELIST_OF_NUM_MOD; SYM h3; BYTELIST_OF_NUM_OF_BYTELIST; t1]));;

let arm_decode_unique = prove
 (`!s pc x y. arm_decode s pc x ==> arm_decode s pc y ==> x = y`,
  REWRITE_TAC [arm_decode] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM_LIST (fun [d2;l2; d1;l1] ->
    let t = REWRITE_RULE [LENGTH_BYTELIST_OF_NUM]
      (MATCH_MP (MATCH_MP aligned_bytes_loaded_unique l1) l2) in
    let t2 = REWRITE_RULE [NUM_OF_BYTELIST_OF_NUM; GSYM CONG;
      ARITH_RULE `256 EXP 4 = 2 EXP 32`; SYM DIMINDEX_32;
      GSYM WORD_EQ; WORD_VAL] (AP_TERM `num_of_bytelist` t) in
    ACCEPT_TAC (REWRITE_RULE [REWRITE_RULE [t2] d1; OPTION_INJ] d2)));;

let ARM_DECODES_THM =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + 4 = pc' ==>
     aligned_bytes_loaded s (word pc) l ==>
     read_int32 l = SOME (a, l') ==> decode a = SOME i ==>
     arm_decode s (word pc) i' /\
     aligned_bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC ARM_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + 4 = p ==> (pc + n) + 4 = pc + p`
  and r32,dec,n4 = `read_int32`,`decode`,`4`
  and ei,ei' = `i:armstate->armstate->bool`,`i':armstate->armstate->bool`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and ea,en,ep,epc,epc' = `a:int32`,`n:num`,`p:num`,`pc:num`,`pc':num` in
  (* go returns a list of pairs of arm_decode theorem and its PC offset. *)
  let rec go th: (thm*term) list =
    let pc,l = (rand o rand F_F I) (dest_comb (concl th)) in
    let th1 = READ_WORD_CONV (mk_comb (r32, l)) in
    let a,l' = dest_pair (rand (rhs (concl th1))) in
    let th2 = DECODE_CONV (mk_comb (dec, a)) in
    let i = rand (rhs (concl th2)) in
    let th3 = REWRITE_CONV (invert_condition :: ARM_INSTRUCTION_ALIASES) i in
    let i' = rhs (concl th3) in
    let th4,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n4)) in
      PROVE_HYP th (INST [pc,epc; a,en; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n4)),`0` in
    let pc' = rhs (concl th4) in
    let th' = itlist PROVE_HYP [th3; th4; th; th1; th2]
      (INST [i,ei; i',ei'; pc,epc; pc',epc'; l,el; a,ea; l',el'] pth) in
    match l' with
    | Const("NIL",_) -> [CONJUNCT1 th',pcofs]
    | _ -> let dth,bth = CONJ_PAIR th' in (dth,pcofs)::(go bth) in
  fun th ->
    let decodes:(thm*term) list = (go o
      (fun dth -> EQ_MP dth (ASSUME (lhs (concl dth)))) o
      AP_TERM `aligned_bytes_loaded s (word pc)`) th in
    map (fun th,pcofs -> ((GENL [`s:armstate`; `pc:num`] o DISCH_ALL) th, pcofs))
      decodes;;

let ARM_MK_EXEC_RULE th0: thm * (thm option array) =
  let reloc_op_convert_th = prove(
    `forall (x:num) y.
      CONS (word (x MOD 256):(8)word)
        (CONS (word ((x DIV 256) MOD 256):(8)word)
          (CONS (word ((x DIV 256 DIV 256) MOD 256):(8)word)
            (CONS (word ((x DIV 256 DIV 256 DIV 256) MOD 256):(8)word)
              y)))
      = APPEND (bytelist_of_num 4 x) y`,
    REPEAT GEN_TAC THEN
    CONV_TAC (RAND_CONV (TOP_DEPTH_CONV num_CONV)) THEN
    REWRITE_TAC[bytelist_of_num;APPEND]) in

  let th0 = INST [`pc':num`,`pc:num`] (SPEC_ALL
    (PURE_REWRITE_RULE[reloc_op_convert_th] th0)) in
  let th1 = AP_TERM `LENGTH:byte list->num` th0 in
  let th2 =
    (REWRITE_CONV [LENGTH_BYTELIST_OF_NUM; LENGTH_BYTELIST_OF_INT;
      LENGTH; LENGTH_APPEND] THENC NUM_REDUCE_CONV) (rhs (concl th1)) in
  (* Length *)
  let execth1 = TRANS th1 th2 in
  (* Decode *)
  let execth2_raw:(thm*term) list = ARM_DECODES_THM th0 in
  let (decode_arr:thm option array) = Array.make
    (dest_small_numeral (snd (dest_eq (concl execth1)))) None in
  let _ = List.iter (fun decode_th,pcofs ->
    decode_arr.(dest_small_numeral pcofs) <- Some decode_th)
    execth2_raw in
  (execth1,decode_arr);;


(* Take a slice of a machine code using SUB_LIST.
   Returns a new definition of sliced machine code nmaed new_mc_name,
   its SUB_LIST_CONV-reduced version, and
   its EXEC version created by ARM_MK_EXEC_RULE. *)
let mk_sublist_of_mc (new_mc_name:string) (mc_th:thm)
    (ofs_and_len:term*term) (mc_length_th:thm): thm * thm * (thm * thm option array) =
  let type_check (t:term) (ty:hol_type): unit =
    if type_of t <> ty then
      failwith (Printf.sprintf "`%s` must have type `%s` but has `%s`"
          (string_of_term t) (string_of_type ty)
          (string_of_type (type_of t)))
    else
      () in
  let _ = type_check (fst ofs_and_len) `:num` in
  let _ = type_check (snd ofs_and_len) `:num` in
  let mc = fst (dest_eq (concl mc_th)) in
  let new_mc = mk_var(new_mc_name,`:((8)word)list`) in
  let new_mc_def = define (mk_eq (new_mc,
    list_mk_comb (`SUB_LIST:num#num->((8)word)list->((8)word)list`,
      [mk_pair ofs_and_len;mc]))) in
  let new_mc = CONV_RULE (REWRITE_CONV [mc_length_th] THENC
               ONCE_DEPTH_CONV NUM_SUB_CONV THENC
               REWRITE_CONV [mc_th] THENC
               RAND_CONV SUB_LIST_CONV) new_mc_def in
  new_mc_def,new_mc,(ARM_MK_EXEC_RULE new_mc);;

(* ------------------------------------------------------------------------- *)
(* For ARM this is a trivial function.                                       *)
(* ------------------------------------------------------------------------- *)

let arm_execute = define
 `arm_execute = \i:(armstate->armstate->bool). i`;;

(* ------------------------------------------------------------------------- *)
(* Now the basic fetch-decode-execute cycle.                                 *)
(* ------------------------------------------------------------------------- *)

let arm = define
 `arm s s' <=>
    ?instr. arm_decode s (read PC s) instr /\
            (PC := word_add (read PC s) (word 4) ,,
             arm_execute instr) s s'`;;

(* ------------------------------------------------------------------------- *)
(* Normalize an address in the same style as x86 bsid.                       *)
(* ------------------------------------------------------------------------- *)

let OFFSET_ADDRESS_CLAUSES = prove
 (`offset_address (Register_Offset r) s = word(val(read r s)) /\
   offset_address (Shiftreg_Offset r 1) s = word(2 * val(read r s)) /\
   offset_address (Shiftreg_Offset r 2) s = word(4 * val(read r s)) /\
   offset_address (Shiftreg_Offset r 3) s = word(8 * val(read r s)) /\
   offset_address (Shiftreg_Offset r 4) s = word(16 * val(read r s)) /\
   offset_address (Postreg_Offset r) s = word 0 /\
   offset_address (Immediate_Offset w) s = w /\
   offset_address (Preimmediate_Offset w) s = w /\
   offset_address (Postimmediate_Offset w) s = word 0`,
  REWRITE_TAC[offset_address; word_shl; WORD_VAL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_AC]);;

(* ------------------------------------------------------------------------- *)
(* Basic execution of ARM instruction into sequence of state updates.        *)
(* ------------------------------------------------------------------------- *)

let WREG_EXPAND_CLAUSES = prove
 (`W0 = X0 :> zerotop_32 /\
   W1 = X1 :> zerotop_32 /\
   W2 = X2 :> zerotop_32 /\
   W3 = X3 :> zerotop_32 /\
   W4 = X4 :> zerotop_32 /\
   W5 = X5 :> zerotop_32 /\
   W6 = X6 :> zerotop_32 /\
   W7 = X7 :> zerotop_32 /\
   W8 = X8 :> zerotop_32 /\
   W9 = X9 :> zerotop_32 /\
   W10 = X10 :> zerotop_32 /\
   W11 = X11 :> zerotop_32 /\
   W12 = X12 :> zerotop_32 /\
   W13 = X13 :> zerotop_32 /\
   W14 = X14 :> zerotop_32 /\
   W15 = X15 :> zerotop_32 /\
   W16 = X16 :> zerotop_32 /\
   W17 = X17 :> zerotop_32 /\
   W18 = X18 :> zerotop_32 /\
   W19 = X19 :> zerotop_32 /\
   W20 = X20 :> zerotop_32 /\
   W21 = X21 :> zerotop_32 /\
   W22 = X22 :> zerotop_32 /\
   W23 = X23 :> zerotop_32 /\
   W24 = X24 :> zerotop_32 /\
   W25 = X25 :> zerotop_32 /\
   W26 = X26 :> zerotop_32 /\
   W27 = X27 :> zerotop_32 /\
   W28 = X28 :> zerotop_32 /\
   W29 = X29 :> zerotop_32 /\
   W30 = X30 :> zerotop_32`,
  REWRITE_TAC(!component_alias_thms));;

let DREG_EXPAND_CLAUSES = prove
 (`D0 = Q0 :> zerotop_64 /\
   D1 = Q1 :> zerotop_64 /\
   D2 = Q2 :> zerotop_64 /\
   D3 = Q3 :> zerotop_64 /\
   D4 = Q4 :> zerotop_64 /\
   D5 = Q5 :> zerotop_64 /\
   D6 = Q6 :> zerotop_64 /\
   D7 = Q7 :> zerotop_64 /\
   D8 = Q8 :> zerotop_64 /\
   D9 = Q9 :> zerotop_64 /\
   D10 = Q10 :> zerotop_64 /\
   D11 = Q11 :> zerotop_64 /\
   D12 = Q12 :> zerotop_64 /\
   D13 = Q13 :> zerotop_64 /\
   D14 = Q14 :> zerotop_64 /\
   D15 = Q15 :> zerotop_64 /\
   D16 = Q16 :> zerotop_64 /\
   D17 = Q17 :> zerotop_64 /\
   D18 = Q18 :> zerotop_64 /\
   D19 = Q19 :> zerotop_64 /\
   D20 = Q20 :> zerotop_64 /\
   D21 = Q21 :> zerotop_64 /\
   D22 = Q22 :> zerotop_64 /\
   D23 = Q23 :> zerotop_64 /\
   D24 = Q24 :> zerotop_64 /\
   D25 = Q25 :> zerotop_64 /\
   D26 = Q26 :> zerotop_64 /\
   D27 = Q27 :> zerotop_64 /\
   D28 = Q28 :> zerotop_64 /\
   D29 = Q29 :> zerotop_64 /\
   D30 = Q30 :> zerotop_64 /\
   D31 = Q31 :> zerotop_64`,
  REWRITE_TAC(!component_alias_thms));;

let READ_SHIFTEDREG_CLAUSES = prove
 (`read (Shiftedreg Rn LSL n) s = word_shl (read Rn s) n /\
   read (Shiftedreg Rn LSR n) s = word_ushr (read Rn s) n /\
   read (Shiftedreg Rn ASR n) s = word_ishr (read Rn s) n /\
   read (Shiftedreg Rn ROR n) s = word_ror (read Rn s) n`,
  REWRITE_TAC[Shiftedreg_DEF; read; regshift_operation; ETA_AX]);;

let READ_EXTENDEDREG_CLAUSES = prove
 (`read (Extendedreg Rn UXTB) s = word_zx (word_zx (read Rn s):byte) /\
   read (Extendedreg Rn UXTH) s = word_zx (word_zx (read Rn s):int16) /\
   read (Extendedreg Rn UXTW) s = word_zx (word_zx (read Rn s):int32) /\
   read (Extendedreg Rn UXTX) s = word_zx (word_zx (read Rn s):int64) /\
   read (Extendedreg Rn SXTB) s = word_sx (word_zx (read Rn s):byte) /\
   read (Extendedreg Rn SXTH) s = word_sx (word_zx (read Rn s):int16) /\
   read (Extendedreg Rn SXTW) s = word_sx (word_zx (read Rn s):int32) /\
   read (Extendedreg Rn SXTX) s = word_sx (word_zx (read Rn s):int64)`,
  REWRITE_TAC[Extendedreg_DEF; read; extendreg_operation; ETA_AX]);;

let READ_LANE_CLAUSES = prove
 (`read (Rn :> LANE_B i) (s:armstate) =
   word_duplicate(word_subword (read Rn s:int128) (8*i,8):byte) /\
   read (Rn :> LANE_H i) (s:armstate) =
   word_duplicate(word_subword (read Rn s:int128) (16*i,16):int16) /\
   read (Rn :> LANE_S i) (s:armstate) =
   word_duplicate(word_subword (read Rn s:int128) (32*i,32):int32) /\
   read (Rn :> LANE_D i) (s:armstate) =
   word_duplicate(word_subword (read Rn s:int128) (64*i,64):int64)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; LANE_B; LANE_H; LANE_S; LANE_D;
              through; read]);;

let ARM_EXEC_CONV =
  let qth = prove(`bytes64 (word_add a (word 0)) = bytes64 a /\
                   bytes128 (word_add b (word 0)) = bytes128 b`,
                  REWRITE_TAC[WORD_ADD_0])
  and rth = prove
   (`word_add (x:(N)word) (iword (-- &n)) =
     word_sub x (word n)`, CONV_TAC WORD_RULE) in
  ((GEN_REWRITE_CONV I ARM_LOAD_STORE_CLAUSES THENC
    REWRITE_CONV [offset_writesback; offset_writeback;
                  no_offset; OFFSET_ADDRESS_CLAUSES] THENC
    ONCE_DEPTH_CONV(EQT_INTRO o ORTHOGONAL_COMPONENTS_CONV) THENC
    REWRITE_CONV[] THENC
    ONCE_DEPTH_CONV(LAND_CONV DIMINDEX_CONV THENC NUM_DIV_CONV) THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [GSYM BYTES8_WBYTES; GSYM BYTES16_WBYTES;
      GSYM BYTES32_WBYTES; GSYM BYTES64_WBYTES;
      GSYM BYTES128_WBYTES; GSYM BYTES256_WBYTES] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [qth] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [rth] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [CONJUNCT2 SEQ_ID]) ORELSEC
   (GEN_REWRITE_CONV I ARM_OPERATION_CLAUSES THENC
    REWRITE_CONV [condition_semantics])) THENC
  REWRITE_CONV[WREG_EXPAND_CLAUSES; DREG_EXPAND_CLAUSES] THENC
  REWRITE_CONV[READ_RVALUE; ARM_ZERO_REGISTER;
               ASSIGN_ZEROTOP_32; ASSIGN_ZEROTOP_64;
               READ_ZEROTOP_32; WRITE_ZEROTOP_32;
               READ_ZEROTOP_64; WRITE_ZEROTOP_64;
               READ_SHIFTEDREG_CLAUSES; READ_EXTENDEDREG_CLAUSES;
               READ_LANE_CLAUSES] THENC
  DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_WORD_OPERATION_CONV);;

(* ------------------------------------------------------------------------- *)
(* Additional proof support for SP restriction to "aligned 16".              *)
(* ------------------------------------------------------------------------- *)

let XREG_NE_SP = prove
 (`~(X0 = SP) /\ ~(X1 = SP) /\ ~(X2 = SP) /\ ~(X3 = SP) /\ ~(X4 = SP) /\
   ~(X5 = SP) /\ ~(X6 = SP) /\ ~(X7 = SP) /\ ~(X8 = SP) /\ ~(X9 = SP) /\
   ~(X10 = SP) /\ ~(X11 = SP) /\ ~(X12 = SP) /\ ~(X13 = SP) /\ ~(X14 = SP) /\
   ~(X15 = SP) /\ ~(X16 = SP) /\ ~(X17 = SP) /\ ~(X18 = SP) /\ ~(X19 = SP) /\
   ~(X20 = SP) /\ ~(X21 = SP) /\ ~(X22 = SP) /\ ~(X23 = SP) /\ ~(X24 = SP) /\
   ~(X25 = SP) /\ ~(X26 = SP) /\ ~(X27 = SP) /\ ~(X28 = SP) /\ ~(X29 = SP) /\
   ~(X30 = SP)`,
  REPEAT CONJ_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `c = d
    ==> !y z s. read c (write c y (write d z s)) =
                read c (write d y (write c z s))`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`word 0:int64`; `word 1:int64`]) THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  REWRITE_TAC[WORD_NE_10]);;

(* ------------------------------------------------------------------------- *)
(* Support for the "forward symbolic execution" proof style.                 *)
(* ------------------------------------------------------------------------- *)

let ARM_THM =
  let pth = prove
   (`read PC s = word pc ==> arm_decode s (word pc) instr ==>
     (arm s s' <=> (PC := word (pc + 4) ,, instr) s s')`,
    REPEAT STRIP_TAC THEN REWRITE_TAC [arm] THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD; arm_execute] THEN
    ASM_MESON_TAC[arm_decode_unique]) in
  (* pc_th: `|- ... = word <pc_expr>` *)
  fun (execth2:thm option array) loaded_mc_th pc_th ->
    let th = MATCH_MP pth pc_th in
    let pc_ofs:int =
      let pc_expr = snd (dest_comb (snd (dest_eq (concl pc_th)))) in
      if is_var pc_expr then 0
      else try
        let pc_base,ofs = dest_binary "+" pc_expr in
        dest_small_numeral ofs
      with Failure _ ->
        failwith ("ARM_THM: Cannot decompose PC expression: " ^ (string_of_term (concl pc_th))) in
    MATCH_MP th (MATCH_MP (Option.get execth2.(pc_ofs)) loaded_mc_th);;

let ARM_ENSURES_SUBLEMMA_TAC =
  ENSURES_SUBLEMMA_TAC o MATCH_MP aligned_bytes_loaded_update o CONJUNCT1;;

let ARM_ENSURES_SUBSUBLEMMA_TAC =
  ENSURES_SUBSUBLEMMA_TAC o
  map (MATCH_MP aligned_bytes_loaded_update o CONJUNCT1);;

(* returns true if t is `read PC <state>`. *)
let is_read_pc t =
  match t with
  | Comb (Comb (Const ("read", _), Const ("PC", _)), _) -> true
  | _ -> false;;

(* returns true if t is `read events <state>`. *)
let is_read_events t =
  match t with
  | Comb (Comb (Const ("read", _), Const ("events", _)), _) -> true
  | _ -> false;;

(*** decode_ths is an array from int offset i to
 ***   Some `|- !s pc. aligned_bytes_loaded s pc *_mc
 ***            ==> arm_decode s (word (pc+i)) (..inst..)`
 *** .. if it is a valid byte sequence, or None otherwise.
 ***)

let ARM_CONV (decode_ths:thm option array) (ths:thm list) tm =
  let pc_th = find
    (fun th -> (* do not use term_match because it is slow. *)
      let c = concl th in
      is_eq c && is_read_pc (fst (dest_eq c)))
    ths in
  let eth = try
    tryfind (fun loaded_mc_th ->
      GEN_REWRITE_CONV I [ARM_THM decode_ths loaded_mc_th pc_th] tm) ths
    with Failure s ->
      let pcstr = string_of_term (concl pc_th) in
      failwith ("ARM_CONV: can't find aligned_bytes_loaded (pc: `" ^
          pcstr ^ "`)") in
 (K eth THENC
  ONCE_DEPTH_CONV ARM_EXEC_CONV THENC
  REWRITE_CONV[XREG_NE_SP; SEQ; condition_semantics] THENC
  ALIGNED_16_CONV ths THENC
  REWRITE_CONV[SEQ; condition_semantics] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [assign] THENC
  REWRITE_CONV[] THENC
  TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV [WRITE_RVALUE] THENC
  ONCE_REWRITE_CONV [WORD_SUB_ADD] THENC
  ONCE_DEPTH_CONV
   (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV) THENC
  ONCE_DEPTH_CONV
   (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
    GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
    RAND_CONV NUM_REDUCE_CONV) THENC
  TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
  GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL] THENC
  ONCE_DEPTH_CONV WORD_PC_PLUS_CONV THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV
 ) tm;;

let ARM_BASIC_STEP_TAC =
  let arm_tm = `arm` and arm_ty = `:armstate` in
  fun (decode_ths: thm option array) sname (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,arm_ty) in
    let atm = mk_comb(mk_comb(arm_tm,sv),sv') in
    let eth = ARM_CONV decode_ths (map snd asl) atm in
    (GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth]]) (asl,w);;

let ARM_STEP_TAC (mc_length_th,decode_ths) (subths:thm list) sname =
  (*** This does the basic decoding setup ***)

  ARM_BASIC_STEP_TAC decode_ths sname THEN

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
    STRIP_TAC);;

let ARM_VERBOSE_STEP_TAC (exth1,exth2) sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  ARM_STEP_TAC (exth1,exth2) [] sname g;;

let ARM_VERBOSE_SUBSTEP_TAC (exth1,exth2) subths sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  ARM_STEP_TAC (exth1,exth2) subths sname g;;

(* ------------------------------------------------------------------------- *)
(* Throw away assumptions according to patterns.                             *)
(* ------------------------------------------------------------------------- *)

let DISCARD_FLAGS_TAC =
  DISCARD_MATCHING_ASSUMPTIONS
   [`read CF s = y`; `read ZF s = y`;
    `read NF s = y`; `read VF s = y`];;

let DISCARD_STATE_TAC s =
  DISCARD_ASSUMPTIONS_TAC (vfree_in (mk_var(s,`:armstate`)) o concl);;

let DISCARD_OLDSTATE_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound_svars tm =
    match tm with
      Comb(Comb(Const("read",_),cmp),s) ->
        if mem s bound_svars then [] else [s]
    | Comb(a,b) -> union (unbound_statevars_of_read bound_svars a)
                         (unbound_statevars_of_read bound_svars b)
    | Abs(v,t) -> unbound_statevars_of_read (v::bound_svars) t
    | _ -> [] in
  DISCARD_ASSUMPTIONS_TAC(
    fun thm ->
      let us = unbound_statevars_of_read [] (concl thm) in
      if us = [] || us = [v] then false
      else if not(mem v us) then true
      else
        if !arm_print_log then
          (Printf.printf
            "Info: assumption `%s` is erased, but it might have contained useful information\n"
            (string_of_term (concl thm)); true)
        else true);;

(* ------------------------------------------------------------------------- *)
(* More convenient stepping tactics, optionally with accumulation.           *)
(* ------------------------------------------------------------------------- *)

let ARM_SINGLE_STEP_TAC th s =
  time (ARM_VERBOSE_STEP_TAC th s) THEN
  DISCARD_OLDSTATE_TAC s THEN
  CLARIFY_TAC;;

let ARM_VACCSTEP_TAC th aflag s =
  ARM_VERBOSE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC) else ALL_TAC);;

let ARM_XACCSTEP_TAC th excs aflag s =
  ARM_SINGLE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATEX_ARITH_TAC excs s THEN CLARIFY_TAC)
   else ALL_TAC);;

(* ARM_GEN_ACCSTEP_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC. This is
   useful when the output goal of ARM_SINGLE_STEP_TAC needs additional rewrites
   for accumulator to recognize it. *)
let ARM_GEN_ACCSTEP_TAC acc_preproc th aflag s =
  ARM_SINGLE_STEP_TAC th s THEN
  (if aflag then acc_preproc THEN TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
   else ALL_TAC);;

let ARM_ACCSTEP_TAC th aflag s = ARM_GEN_ACCSTEP_TAC ALL_TAC th aflag s;;

let ARM_VSTEPS_TAC th snums =
  MAP_EVERY (ARM_VERBOSE_STEP_TAC th) (statenames "s" snums);;

let ARM_STEPS_TAC th snums =
  MAP_EVERY (ARM_SINGLE_STEP_TAC th) (statenames "s" snums);;

let ARM_VACCSTEPS_TAC th anums snums =
  MAP_EVERY (fun n -> ARM_VACCSTEP_TAC th (mem n anums) ("s"^string_of_int n))
            snums;;

let ARM_XACCSTEPS_TAC th excs anums snums =
  MAP_EVERY
   (fun n -> ARM_XACCSTEP_TAC th excs (mem n anums) ("s"^string_of_int n))
   snums;;

(* ARM_GEN_ACCSTEPS_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC.
   acc_preproc is a function from string (which is a state name) to tactic. *)
let ARM_GEN_ACCSTEPS_TAC acc_preproc th anums snums =
  MAP_EVERY
    (fun n ->
      let state_name = "s"^string_of_int n in
      ARM_GEN_ACCSTEP_TAC (acc_preproc state_name) th (mem n anums) state_name)
    snums;;

let ARM_ACCSTEPS_TAC th anums snums =
  ARM_XACCSTEPS_TAC th [`SP`] anums snums;;

let ARM_QUICKSTEP_TAC th pats =
  let pats' =
   [`nonoverlapping_modulo a b c`; `aligned_bytes_loaded a b c`;
    `MAYCHANGE a b c`; `(a ,, b) c d`; `read PC s = x`] @ pats in
  fun s -> time (ARM_VERBOSE_STEP_TAC th s) THEN
           DISCARD_NONMATCHING_ASSUMPTIONS pats' THEN
           DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC;;

let ARM_QUICKSTEPS_TAC th pats snums =
  MAP_EVERY (ARM_QUICKSTEP_TAC th pats) (statenames "s" snums);;

let ARM_QUICKSIM_TAC execth pats snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN ARM_QUICKSTEPS_TAC execth pats snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* More convenient wrappings of basic simulation flow.                       *)
(* ------------------------------------------------------------------------- *)

let ARM_SIM_TAC execth snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC execth snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

let ARM_ACCSIM_TAC execth anums snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN ARM_ACCSTEPS_TAC execth anums snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Simulate through a lemma in ?- ensures step P Q C ==> eventually R s      *)
(* ------------------------------------------------------------------------- *)

let (ARM_BIGSTEP_TAC:(thm*thm option array)->string->tactic) =
  let lemma = prove
   (`P s /\ (!s':S. Q s' /\ C s s' ==> eventually step R s')
     ==> ensures step P Q C ==> eventually step R s`,
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ensures] THEN
    DISCH_THEN(MP_TAC o SPEC `s:S`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `(!s:S. eventually step P s ==> eventually step Q s)
      ==> eventually step P s ==> eventually step Q s`) THEN
    GEN_REWRITE_TAC I [EVENTUALLY_IMP_EVENTUALLY] THEN
    ASM_REWRITE_TAC[]) in
  fun (execth1,_) sname (asl,w) ->
    let sv = mk_var(sname,type_of(rand(rand w))) in
    (* do sanity-check and print a warning message if it fails *)
    (if not (is_imp w) ||
      let the_lhs,the_rhs = dest_imp w in
      not (is_comb the_lhs &&
           name_of (fst (strip_comb the_lhs)) = "ensures" &&
           is_comb the_rhs &&
           name_of (fst (strip_comb the_rhs)) = "eventually")
    then
      Printf.printf "ARM_BIGSTEP_TAC: `ensures ... ==> eventually ...` expected, but got `%s`.\n"
        (string_of_term w));
    (GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
      (!simulation_precanon_thms) THEN
     MATCH_MP_TAC lemma THEN CONJ_TAC THENL
      [BETA_TAC THEN ASM_REWRITE_TAC[];
       BETA_TAC THEN X_GEN_TAC sv THEN
       REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
       REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
       NONSELFMODIFYING_STATE_UPDATE_TAC
        (MATCH_MP aligned_bytes_loaded_update execth1) THEN
       ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(K ALL_TAC) THEN DISCARD_OLDSTATE_TAC sname])
    (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Simulate a subroutine, instantiating it from the state.                   *)
(* ------------------------------------------------------------------------- *)

let TWEAK_PC_OFFSET =
  let conv =
   GEN_REWRITE_CONV (RAND_CONV o RAND_CONV) [ARITH_RULE `pc = pc + 0`]
  and tweakneeded tm =
    match tm with
      Comb(Comb(Const("aligned_bytes_loaded",_),Var(_,_)),
           Comb(Const("word",_),Var("pc",_))) -> true
    | _ -> false in
  CONV_RULE(ONCE_DEPTH_CONV(conv o check tweakneeded));;

let ARM_SUBROUTINE_SIM_TAC (machinecode,execth,offset,submachinecode,subth) =
  let subimpth =
    let th = MATCH_MP aligned_bytes_loaded_of_append3
      (TRANS machinecode
         (N_SUBLIST_CONV (SPEC_ALL submachinecode) offset
                         (rhs(concl machinecode)))) in
    let len = rand (lhand (concl th)) in
    let th = REWRITE_RULE [
      (REWRITE_CONV [LENGTH] THENC NUM_REDUCE_CONV) len] th in
    MP th (EQT_ELIM (NUM_DIVIDES_CONV (lhand (concl th)))) in
  (* Replace 'LENGTH .._mc' with its actual constant. This frequently appears
     at nonoverlapping criteria of subth. *)
  let subth =
    if is_const (fst (dest_eq (concl submachinecode))) then
      let auxth = METIS[]
          `(a:(A)list) = b /\ LENGTH b = n ==> LENGTH a = n` in
      let len_submc_th = LENGTH_CONV
        (mk_comb (`LENGTH:((8)word)list->num`,snd (dest_eq (concl submachinecode)))) in
      let main_th = MATCH_MP auxth (CONJ submachinecode len_submc_th) in
      REWRITE_RULE[main_th] subth
    else subth in
  fun ilist0 n ->
    let sname = "s"^string_of_int(n-1)
    and sname' = "s"^string_of_int n in
    let svar = mk_var(sname,`:armstate`)
    and svar0 = mk_var("s",`:armstate`) in
    let ilist = map (vsubst[svar,svar0]) ilist0 in
    let subth_specl =
      try SPECL ilist subth with _ -> begin
        (if (!arm_print_log) then
          (Printf.printf "ilist and subth's forall vars do not match\n";
           Printf.printf "ilist: [%s]\n" (end_itlist
            (fun s s2 -> s ^ "; " ^ s2) (map string_of_term ilist));
           Printf.printf "subth's forall vars: [%s]\n"
              (end_itlist (fun s s2 -> s ^ "; " ^ s2)
                (map string_of_term (fst (strip_forall (concl subth)))))));
        failwith "ARM_SUBROUTINE_SIM_TAC: subth vars don't not match ilist0"
      end in
    MP_TAC(TWEAK_PC_OFFSET subth_specl) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                    MODIFIABLE_UPPER_SIMD_REGS; fst execth] THEN
    REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
    TRY(ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ALIGNED_16_TAC THEN REPEAT CONJ_TAC THEN
      TRY(CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN NO_TAC) THEN
      (NONOVERLAPPING_TAC ORELSE
       DISJ1_TAC THEN NONOVERLAPPING_TAC ORELSE
       DISJ2_TAC THEN NONOVERLAPPING_TAC);
      ALL_TAC]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[] THEN
    ARM_BIGSTEP_TAC execth sname' THENL
     [(* Precondition of subth *)
      (MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC) ORELSE
       (PRINT_GOAL_TAC THEN
        FAIL_TAC "Could not discharge precond (subgoal after ARM_BIGSTEP_TAC)");
      ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV
     (GEN_REWRITE_CONV I [MESON[ADD_ASSOC]
      `read PC s = word((pc + m) + n) <=>
       read PC s = word(pc + m + n)`] THENC
     funpow 3 RAND_CONV NUM_ADD_CONV)));;

let ARM_SUBROUTINE_SIM_ABBREV_TAC tupper ilist0 =
  let tac = ARM_SUBROUTINE_SIM_TAC tupper ilist0 in
  fun comp0 abn n (asl,w) ->
    let svar0 = mk_var("s",`:armstate`)
    and svar0' = mk_var("s'",`:armstate`)
    and svar = mk_var("s"^string_of_int(n-1),`:armstate`)
    and svar' = mk_var("s"^string_of_int n,`:armstate`) in
    let comp1 =
      rand(concl(PURE_ONCE_REWRITE_CONV (map snd asl)
        (vsubst[svar,svar0;svar',svar0'] comp0))) in
    (tac n THEN
     ABBREV_TAC(mk_eq(mk_var(abn,type_of comp1),comp1))) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Simulate a macro, generating subgoal from a template                      *)
(* The state variable of template's postcondition must be 's'.               *)
(* ------------------------------------------------------------------------- *)

let ARM_MACRO_SIM_ABBREV_TAC =
  let dest_pc tm =
    match tm with
      Comb(Const("word",_),Var("pc",_)) -> 0
    | Comb(Const("word",_),Comb(Comb(Const("+",_),Var("pc",_)),n)) ->
          dest_small_numeral n
    | _ -> failwith "dest_pc"
  and mk_pc =
    let pat0 = `word pc:int64`
    and patn = `word(pc + n):int64`
    and pan = `n:num` in
    fun n ->  if n = 0 then pat0
              else vsubst[mk_small_numeral n,pan] patn
  and grab_dest =
    let pat = `read (memory :> bytes(p,8 * n)) s` in
    fun th ->
      let cortm = rand(body(lhand(repeat (snd o dest_imp) (concl th)))) in
      let matched = find_terms (can (term_match [] pat)) cortm in
      (* only consider state variable 's' of the postcondition *)
      let matched = filter (fun t -> rand t = `s:armstate`) matched in
      rator(hd(matched)) in
  let get_statenpc =
    let fils = can (term_match [] `read PC s = word n`) o concl o snd in
    fun asl ->
      let rips = concl(snd(find fils asl)) in
      rand(lhand rips),dest_pc(rand rips) in
  let simprule =
    CONV_RULE (ONCE_DEPTH_CONV NORMALIZE_ADD_SUBTRACT_WORD_CONV) o
    GEN_REWRITE_RULE ONCE_DEPTH_CONV
     [WORD_RULE `word_add z (word 0):int64 = z`] in
  fun mc ->
    let execth = ARM_MK_EXEC_RULE mc in
    fun codelen localvars template core_tac prep ilist ->
      (* Rewrite 'LENGTH ..._mc = ..' *)
      let _,template = dest_eq(concl(REWRITE_CONV[fst execth] template)) in
      let main_tac (asl,w) =
        let svp,pc = get_statenpc asl in
        let gv = genvar(type_of svp) in
        let n = int_of_string(implode(tl(explode(fst(dest_var svp))))) + 1 in
        let svn = mk_var("s"^string_of_int n,`:armstate`) in
        let pc' = pc + 4 * codelen in
        let svs = svp::(mk_pc pc)::(mk_pc pc')::
                  end_itlist (@) (map (C assoc localvars) ilist) in
        let rawsg = simprule(SPECL svs (ASSUME template)) in
        let asimprule = PURE_REWRITE_RULE
         (filter (is_eq o concl) (map snd asl)) in
        let insig = (asimprule o simprule o asimprule) rawsg in
        let subg = mk_forall(gv,vsubst[gv,svp] (concl(simprule insig))) in
        let avoids = itlist (union o thm_frees o snd) asl (frees w) in
        let abv = mk_primed_var avoids (mk_var(hd ilist,`:num`)) in
        (SUBGOAL_THEN subg MP_TAC THENL
         [X_GEN_TAC gv THEN POP_ASSUM_LIST(K ALL_TAC) THEN
          REPEAT(GEN_TAC THEN DISCH_THEN(K ALL_TAC o SYM)) THEN
          core_tac THEN NO_TAC;
          ALL_TAC] THEN
         DISCH_THEN(MP_TAC o SPEC svp) THEN
         GEN_REWRITE_TAC (REPEATC o LAND_CONV) [FORALL_UNWIND_THM1] THEN
         DISCH_THEN(fun subth ->
          let dest = grab_dest subth in
          ARM_SUBROUTINE_SIM_TAC(mc,execth,0,mc,subth) [] n THEN
          let dest_abbrev_eq = mk_eq(abv,mk_comb(dest,svn)) in
          let _ = if !arm_print_log then
            Printf.printf "ARM_MACRO_SIM_ABBREV_TAC: destination buffer is `%s`"
              (string_of_term dest_abbrev_eq)
          in
          ABBREV_TAC (dest_abbrev_eq)))
        (asl,w) in
     fun (asl,w) ->
        let sv,_ = get_statenpc asl in
        let n = int_of_string(implode(tl(explode(fst(dest_var sv))))) in
        (ARM_STEPS_TAC execth ((n+1)--(n+prep)) THEN main_tac) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Refinment of ENSURES_PRESERVED_TAC for special D register handling.       *)
(* ------------------------------------------------------------------------- *)

let ENSURES_PRESERVED_DREG_TAC =
  let pth = prove
   (`read (Q8 :> bottomhalf) s = word_zx(read Q8 s) /\
     read (Q9 :> bottomhalf) s = word_zx (read Q9 s) /\
     read (Q10 :> bottomhalf) s = word_zx (read Q10 s) /\
     read (Q11 :> bottomhalf) s = word_zx (read Q11 s) /\
     read (Q12 :> bottomhalf) s = word_zx (read Q12 s) /\
     read (Q13 :> bottomhalf) s = word_zx (read Q13 s) /\
     read (Q14 :> bottomhalf) s = word_zx (read Q14 s) /\
     read (Q15 :> bottomhalf) s = word_zx (read Q15 s)`,
    CONV_TAC(ONCE_DEPTH_CONV COMPONENT_CANON_CONV) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_ZEROTOP_64;
                bottomhalf; subword; read; FUN_EQ_THM] THEN
    REWRITE_TAC[word_zx; DIV_1; EXP; WORD_MOD_SIZE])
  and sth = prove
   (`valid_component c /\
     R ,, R = R /\
     MAYCHANGE [c :> tophalf] subsumed R /\
     ensures step P Q (R ,, MAYCHANGE [c])
     ==> ensures step P Q (R ,, MAYCHANGE [c :> bottomhalf])`,
    REWRITE_TAC[MAYCHANGE_SING] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN MATCH_MP_TAC SUBSUMED_SEQ THEN
    REWRITE_TAC[SUBSUMED_REFL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP ASSIGNS_TOPHALF_BOTTOMHALF) THEN
    MATCH_MP_TAC SUBSUMED_SEQ THEN ASM_REWRITE_TAC[SUBSUMED_REFL]) in
  let alist = zip [`D8`; `D9`; `D10`; `D11`; `D12`; `D13`; `D14`; `D15`]
                  (map (lhand o lhand o concl) (CONJUNCTS pth)) in
  let dregs = map fst alist in
  fun pname ctm ->
    if not (mem ctm dregs) then ENSURES_PRESERVED_TAC pname ctm else
    let ctm' = assoc ctm alist in
    ENSURES_PRESERVED_TAC pname ctm' THEN REWRITE_TAC[pth] THEN
    TRY(REWRITE_TAC[SEQ_ASSOC] THEN MATCH_MP_TAC sth THEN
        CONJ_TAC THENL [CONV_TAC VALID_COMPONENT_CONV; ALL_TAC] THEN
        CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC THEN NO_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM SEQ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Fix up call/return boilerplate given core correctness.                    *)
(* ------------------------------------------------------------------------- *)

let ARM_ADD_RETURN_NOSTACK_TAC =
  let lemma1 = prove
   (`ensures step P Q R /\
     (!s s'. P s /\ Q s' /\ R s s' ==> Q' s')
     ==> ensures step P (\s. Q s /\ Q' s) R`,
    ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
    REWRITE_TAC[SUBSUMED_REFL] THEN ASM_MESON_TAC[]) in
  let ENSURES_TRANS_SUBSUMED = prove(`!P Q R C C'.
        C ,, C = C /\ C subsumed C' /\
        ensures step P Q C /\ ensures step Q R C
        ==> ensures step P R C'`,
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[ENSURES_TRANS_SIMPLE; ENSURES_FRAME_SUBSUMED]) in
  let lemma2 = prove
   (`C ,, C = C /\ C subsumed C' /\
     (!s s'. program_decodes s /\ pcdata s /\ returndata s /\ P s /\
             Q s' /\ C s s'
             ==> program_decodes s' /\ returndata s') /\
     ensures step (\s. program_decodes s /\ returndata s /\ Q s) R C
     ==> ensures step (\s. program_decodes s /\ pcdata s /\ P s) Q C
          ==> ensures step
               (\s. program_decodes s /\ pcdata s /\ returndata s /\ P s) R C'`,
    ONCE_REWRITE_TAC[TAUT
     `a /\ p /\ subsm /\ q ==> r ==> s <=>
      a ==> p ==> subsm ==> r ==> q ==> s`] THEN
    DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE
     [TAUT `p /\ q /\ r /\ r2 ==> s <=> p /\ q /\ r ==> r2 ==> s`]
     ENSURES_TRANS_SUBSUMED) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
     [TAUT `p /\ q /\ r <=> r /\ p /\ q`] THEN
    MATCH_MP_TAC lemma1 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          ENSURES_PRECONDITION_THM)) THEN
    SIMP_TAC[]) in
  fun execth coreth ->
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                MODIFIABLE_UPPER_SIMD_REGS] THEN
    MP_TAC coreth THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
      MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN ALIGNED_16_TAC THEN
      TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    MATCH_MP_TAC lemma2 THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC;
      SUBSUMED_MAYCHANGE_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      NONSELFMODIFYING_STATE_UPDATE_TAC
       (MATCH_MP aligned_bytes_loaded_update (fst execth)) THEN
      ASSUMPTION_STATE_UPDATE_TAC THEN
      DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check
       (can (term_match [] `read PC s = a \/ Q` o concl)))) THEN
      ARM_STEPS_TAC execth [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Version with register save/restore and stack adjustment.                  *)
(* ------------------------------------------------------------------------- *)

let ARM_ADD_RETURN_STACK_TAC =
  let mono2lemma = MESON[]
   `(!x. (!y. P x y) ==> (!y. Q x y)) ==> (!x y. P x y) ==> (!x y. Q x y)`
  and sp_tm = `SP` and x30_tm = `X30`
  and dqd_thm = WORD_BLAST `(word_zx:int128->int64)(word_zx(x:int64)) = x` in
  fun ?(pre_post_nsteps:(int*int) option) execth coreth reglist stackoff ->
    let regs = dest_list reglist in
    (* The number of steps that ARM_STEPS will take before/after BIGSTEP. *)
    let pre_n,post_n =
      match pre_post_nsteps with
      | Some (a,b) -> a,b
      | None ->
        let n = let n0 = (length regs + 1 (* +1 if len is odd *)) / 2 in
                    if 16 * n0 = stackoff then n0 else n0 + 1 in
        (n,n) in
    MP_TAC coreth THEN
    REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                 MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                 MODIFIABLE_UPPER_SIMD_REGS;
                 fst execth (* Length of mc *)] THEN
    REPEAT(MATCH_MP_TAC mono2lemma THEN GEN_TAC) THEN
    (if vfree_in sp_tm (concl coreth) then
      DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
     else
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(fun th ->
        WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN ALIGNED_16_TAC THEN
      TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
      ((ENSURES_EXISTING_PRESERVED_TAC sp_tm THEN
       (if mem x30_tm regs then ENSURES_EXISTING_PRESERVED_TAC x30_tm
        else ALL_TAC) THEN
       MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC
                             ("init_"^fst(dest_const c)) c)
                 (subtract regs [x30_tm]))
        ORELSE
        FAIL_TAC "callee-save registers are still in MAYCHANGE") THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC execth (1--pre_n) THEN
      MP_TAC th) THEN
    ARM_BIGSTEP_TAC execth ("s"^string_of_int(pre_n+1)) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ARM_STEPS_TAC execth ((pre_n+2)--(pre_n+post_n+2)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[dqd_thm];;

(* ------------------------------------------------------------------------- *)
(* Version with a program defined as SUB_LIST of a bigger program.           *)
(* ------------------------------------------------------------------------- *)

(* Given a goal which is
  `!<vars> pc.
      <assumptions on program_mc, vars and pc>
      ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) program_mc /\
             read PC s = word (pc + begin_ofs) /\ <precondition>(s))
        (\s. read PC s = word (pc + (begin_ofs + n) /\
             <postcondition>(s))
        (<maychange>)`,
  prove it using correct_th which is
    `|- !<vars> pc.
      <assumptions on program_sub_mc, vars and pc>
      ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) program_sub_mc /\
             read PC s = word pc /\ <precondition>(s))
        (\s. read PC s = word (pc + n) /\
             <postcondition>(s))
        (<maychange>)`
  where program_sub_mc is SUB_LIST(begin_ofs,n) program_mc.
  length_ths contains `|- LENGTH program_mc = ...` and that of program_sub_mc. *)
let ARM_SUB_LIST_OF_MC_TAC (correct_th:thm) (program_sub_mc_def:thm)
    (length_ths:thm list): tactic =
  W (fun (asl,g) ->
    let begin_ofs,n =
      let rhs = snd (dest_eq (concl program_sub_mc_def)) in
      dest_pair (rand(rator rhs)) in
    let correct_th_vars =
      let xs = fst (strip_forall g) in
      if List.exists (fun t -> t = `pc:num`) xs
      then
        List.map
          (fun t -> if t = `pc:num` then mk_binary "+" (t,begin_ofs) else t) xs
      else
        let xs,pc = butlast xs, last xs in
        xs @ [mk_binary "+" (pc,begin_ofs)] in
    if !arm_print_log then begin
      Printf.printf "ARM_SUB_LIST_OF_MC_TAC: begin_ofs: %s, n: %s\n"
        (string_of_term begin_ofs) (string_of_term n);
      Printf.printf "\tvars: %s\n"
        (String.concat "," (map string_of_term correct_th_vars))
    end else ();
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL correct_th_vars correct_th) THEN
    (* Prove antedecent of correct_th *)
    ANTS_TAC THENL [
      (REPEAT (POP_ASSUM MP_TAC) THEN
      REWRITE_TAC(length_ths @ [ALL;NONOVERLAPPING_CLAUSES]) THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN NONOVERLAPPING_TAC) ORELSE ALL_TAC;
      (* Leave it to user *)

      MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
      REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ADD_0] THEN
        REWRITE_TAC[program_sub_mc_def;WORD_ADD] THEN
        IMP_REWRITE_TAC(CONJUNCTS ALIGNED_BYTES_LOADED_SUB_LIST) THEN
        CONV_TAC NUM_DIVIDES_CONV;

        SUBSUMED_MAYCHANGE_TAC;

        MESON_TAC[ADD_ASSOC;ADD_0] ORELSE
        FAIL_TAC ("MESON_TAC could not prove the third precondition of " ^
                  "ENSURES_SUBLEMMA_THM " ^
                  "`(!s s'. P s /\ Q' s' /\ R' s s' ==> Q s')`")
      ]
    ]);;

(* ------------------------------------------------------------------------- *)
(* Handling more general branch targets                                      *)
(* ------------------------------------------------------------------------- *)

let BL_TARGET_CONV =
  let pth = prove
   (`pc < 0x8000000 /\ tgt < 0x8000000 /\ 4 divides pc /\ 4 divides tgt ==>
     word_add (word pc) (word_sx (word (val (iword
      ((&tgt - &pc) div &4):26 word) * 4):28 word)):int64 = word tgt`,
    STRIP_TAC THEN SUBGOAL_THEN
    `word (val (iword ((&tgt - &pc) div &4):26 word) * 4) =
      iword (&tgt - &pc):28 word` (fun th ->
      IMP_REWRITE_TAC [
        th; word_sx; IVAL_IWORD; WORD_VAL; WORD_IWORD; IWORD_IVAL;
        GSYM IWORD_INT_ADD; INT_SUB_ADD2] THEN
      CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV THENC
        NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_ARITH_TAC) THEN
    let arith = ARITH_RULE `~(&2 = &0:int) /\ ~(&4 = &0:int)` in
    SUBGOAL_THEN `&tgt - &pc = ((&tgt - &pc) div &4) * &4` (fun th ->
      CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) THENL
     [REPEAT (POP_ASSUM
        (SUBST1_TAC o SYM o REWRITE_RULE [DIVIDES_DIV_MULT])) THEN
      IMP_REWRITE_TAC [GSYM INT_OF_NUM_MUL; GSYM INT_SUB_RDISTRIB;
        INT_DIV_MUL; arith]; ALL_TAC] THEN
    REWRITE_TAC [iword; VAL_WORD] THEN AP_TERM_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    IMP_REWRITE_TAC [GSYM INT_OF_NUM_EQ; INT_OF_NUM_OF_INT;
      GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_POW;
      INT_REM_REM; INT_REM_POS; INT_POW_EQ_0; INT_REM_MUL_REM;
      INT_POW_LE; INT_POS; arith;
      ARITH_RULE `&2:int pow 28 = &4 * &2 pow 26`;
      INT_DIV_MUL; INT_REM_MUL; INT_ADD_RID; INT_MUL_SYM])

  and pth2 = METIS [aligned_bytes_loaded_word]
   `aligned_bytes_loaded s (word pc) v ==> 4 divides pc` in

  fun asl ->
    let rec prover = function
    | Comb(Comb(Const("/\\",_),a),b) -> CONJ (prover a) (prover b)
    | Comb(Comb(Const("num_divides",_),_),
        Comb(Comb(Const("+",_),_),_)) as tm ->
      let th = PART_MATCH rand DIVIDES_ADD tm in
      MP th (prover (lhand (concl th)))
    | Comb(Comb(Const("num_divides",_),_),n) as tm when is_numeral n ->
      EQT_ELIM (NUM_DIVIDES_CONV tm)
    | Comb(Comb(Const("num_divides",_),_),pc) ->
      let pth' = INST [pc,`pc:num`] pth2
      and lconsts = frees pc in
      let tm' = lhand (concl pth') in
      tryfind (fun h ->
        MP (INSTANTIATE (term_match lconsts tm' (concl h)) pth') h) asl
    | Comb(Comb(Const("<",_),pc),_) as tm ->
      let pc = repeat lhand pc in
      tryfind (fun h ->
        match concl h with
        | Comb(Comb(Const("<",_),pc'),_)
        | Comb(Comb(Const("<=",_),pc'),_) when pc' = pc ->
          MP (ARITH_RULE (list_mk_comb (`==>`, [concl h; tm]))) h
        | _ -> fail ()) asl
    | t -> failwith ("BL_TARGET_TAC " ^ string_of_term t) in
    fun tm ->
      let th = PART_MATCH (lhs o rand) pth tm in
      MP th (prover (lhand (concl th)));;

let BL_TARGET_TAC =
  ASSUM_LIST (CONV_TAC o CHANGED_CONV o ONCE_DEPTH_CONV o BL_TARGET_CONV) THEN
  REWRITE_TAC [];;

(* ------------------------------------------------------------------------- *)
(* Handling PC-relative offsets (ADRP + ADD, which is ADRL pseudo-instr)     *)
(* ------------------------------------------------------------------------- *)

let adrp_within_bounds = new_definition (
  `adrp_within_bounds (x:int64) (pc:int64) =
    let xhi = word_subword x (12,54):(54)word in
    let pchi = word_subword pc (12,54):(54)word in
    // -2^20 <= xhi - pchi < 2^20
    (word_uge xhi pchi /\ word_ult (word_sub xhi pchi) (word (2 EXP 20))) \/
    (word_ult xhi pchi /\ word_ule (word_sub pchi xhi) (word (2 EXP 20)))`);;

let ADRP_ADD_FOLD = prove(`forall (pc:int64) (x:int64).
  adrp_within_bounds x pc
  ==>
  word_add
    (word_add
        (word_and pc (word 0xFFFFFFFFFFFFF000))
        (word_sx
            (word_join
                (word_join
                    (word_subword
                        (word_sub
                            (word_and x (word 0xFFFFFFFFFFFFF000))
                            (word_and pc (word 0xFFFFFFFFFFFFF000)):(64)word)
                        (14,19):(19)word)
                    (word_subword
                        (word_sub
                            (word_and x (word 0xFFFFFFFFFFFFF000))
                            (word_and pc (word 0xFFFFFFFFFFFFF000)):(64)word)
                        (12,2):(2)word)
                    :(21)word)
                (word 0:(12)word)
            :(33)word)
        :(64)word)
    )
    (word (val (word_subword x (0,12):(12)word)):(64)word)
    = x`,

  REWRITE_TAC[adrp_within_bounds] THEN
  BITBLAST_TAC);;
