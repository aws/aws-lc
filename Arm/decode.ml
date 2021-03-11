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
(* ARM instruction decoding.                                                 *)
(* ========================================================================= *)

let XREG_SP = new_definition `XREG_SP n = registers :> element n`;;
let WREG_SP = new_definition `WREG_SP n = XREG_SP n :> zerotop_32`;;
let XREG' = new_definition `XREG' (n:5 word) = XREG (val n)`;;
let WREG' = new_definition `WREG' (n:5 word) = WREG (val n)`;;

let arm_bitop = new_definition `arm_bitop (opc:2 word):
    (armstate,N word)component->(armstate,N word)component->
    (armstate,N word)component->armstate->armstate->bool =
  bitmatch opc with
  | [0:2] -> arm_AND
  | [1:2] -> arm_ORR
  | [2:2] -> arm_EOR
  | [3:2] -> arm_ANDS`;;

let arm_adcop = new_definition `arm_adcop op S:
    (armstate,N word)component->(armstate,N word)component->
    (armstate,N word)component->armstate->armstate->bool =
  if op then if S then arm_SBCS else arm_SBC
        else if S then arm_ADCS else arm_ADC`;;

let arm_addop = new_definition `arm_addop op S:
    (armstate,N word)component->(armstate,N word)component->
    (armstate,N word)component->armstate->armstate->bool =
  if op then if S then arm_SUBS else arm_SUB
        else if S then arm_ADDS else arm_ADD`;;

let arm_logop = new_definition `arm_logop (opc:2 word) N
    (Rd:(armstate,N word)component) Rn Rm =
  bitmatch opc with
  | [0:2] -> if N then NONE else SOME (arm_AND Rd Rn Rm)
  | [1:2] -> SOME ((if N then arm_ORN else arm_ORR) Rd Rn Rm)
  | [2:2] -> SOME ((if N then arm_EON else arm_EOR) Rd Rn Rm)
  | [3:2] -> if N then NONE else SOME (arm_ANDS Rd Rn Rm)`;;

let arm_movop = new_definition `arm_movop (opc:2 word)
    (Rd:(armstate,N word)component) imm pos =
  bitmatch opc with
  | [0:2] -> SOME (arm_MOVN Rd imm pos)
  | [2:2] -> SOME (arm_MOVZ Rd imm pos)
  | [3:2] -> SOME (arm_MOVK Rd imm pos)
  | _ -> NONE`;;

let arm_csop = new_definition `arm_csop op o2:
    (armstate,N word)component->(armstate,N word)component->
    (armstate,N word)component->condition->armstate->armstate->bool =
  if op then if o2 then arm_CSNEG else arm_CSINV
        else if o2 then arm_CSINC else arm_CSEL`;;

let arm_lsvop = new_definition `arm_lsvop (op2:2 word)
    (Rd:(armstate,N word)component) Rn Rm =
  bitmatch op2 with
  | [0:2] -> SOME (arm_LSLV Rd Rn Rm)
  | [1:2] -> SOME (arm_LSRV Rd Rn Rm)
  | _ -> NONE`;;

let arm_ldst = new_definition `arm_ldst ld x Rt =
  if x then (if ld then arm_LDR else arm_STR) (XREG' Rt)
       else (if ld then arm_LDR else arm_STR) (WREG' Rt)`;;
let arm_ldstp = new_definition `arm_ldstp ld x Rt Rt2 =
  if x then (if ld then arm_LDP else arm_STP) (XREG' Rt) (XREG' Rt2)
       else (if ld then arm_LDP else arm_STP) (WREG' Rt) (WREG' Rt2)`;;

let decode_bitmask = new_definition `!N immr imms.
  decode_bitmask (N:bool) (immr:6 word) (imms:6 word):(N word)option =
  let len = 6 - word_clz (word_join (word1 N) (word_not imms):7 word) in
  if len >= 1 /\ (N ==> dimindex(:N) = 64) then
    let size = 2 EXP len in
    let S = val imms MOD size in
    if S = 2 EXP len - 1 then NONE else
    SOME (word_of_bits {i | (i + val immr) MOD size <= S})
  else NONE`;;

let arm_ubfmop = new_definition `arm_ubfmop sf Rd Rn N immr imms =
  if sf then
    if N then
      if imms = 63 then
        SOME (arm_LSR (XREG' Rd) (XREG' Rn) (rvalue (word immr)))
      else if imms + 1 = immr then
        SOME (arm_LSL (XREG' Rd) (XREG' Rn) (rvalue (word (63 - imms))))
      else NONE // general UBFM
    else NONE
  else if N \/ immr >= 32 \/ imms >= 32 then NONE else
    if imms = 31 then
      SOME (arm_LSR (WREG' Rd) (WREG' Rn) (rvalue (word immr)))
    else if imms + 1 = immr then
      SOME (arm_LSL (WREG' Rd) (WREG' Rn) (rvalue (word (31 - imms))))
    else NONE // general UBFM`;;

let decode = new_definition `!w:int32. decode w =
  bitmatch w:int32 with
  | [sf; op; S; 0b11010000:8; Rm:5; 0:6; Rn:5; Rd:5] ->
    SOME (if sf then arm_adcop op S (XREG' Rd) (XREG' Rn) (XREG' Rm)
                else arm_adcop op S (WREG' Rd) (WREG' Rn) (WREG' Rm))
  | [sf; op; S; 0b100010:6; sh; imm12:12; Rn:5; Rd:5] ->
    let val = if sh then val imm12 * 2 EXP 12 else val imm12 in
    SOME (if sf
      then arm_addop op S (XREG' Rd) (XREG_SP Rn) (rvalue (word val))
      else arm_addop op S (WREG' Rd) (WREG_SP Rn) (rvalue (word val)))
  | [sf; op; S; 0b01011000:8; Rm:5; 0:6; Rn:5; Rd:5] ->
    SOME (if sf then arm_addop op S (XREG' Rd) (XREG' Rn) (XREG' Rm)
                else arm_addop op S (WREG' Rd) (WREG' Rn) (WREG' Rm))
  | [sf; opc:2; 0b100100:6; N; immr:6; imms:6; Rn:5; Rd:5] ->
    if sf then
      decode_bitmask N immr imms >>= \imm.
      SOME (arm_bitop opc (XREG' Rd) (XREG' Rn) (rvalue imm))
    else if N then NONE else
      decode_bitmask N immr imms >>= \imm.
      SOME (arm_bitop opc (WREG' Rd) (WREG' Rn) (rvalue imm))
  | [op; 0b00101:5; imm26:26] ->
    SOME ((if op then arm_BL else arm_B) (word (val imm26 * 4)))
  | [0b01010100:8; imm19:19; 0:1; cond:4] ->
    SOME (arm_Bcond (Condition cond) (word (val imm19 * 4)))
  | [sf; 0b011010:6; op; imm19:19; Rt:5] ->
    SOME ((if sf then (if op then arm_CBNZ else arm_CBZ) (XREG' Rt)
                 else (if op then arm_CBNZ else arm_CBZ) (WREG' Rt))
      (word (val imm19 * 4)))
  | [sf; op; 0b011010100:9; Rm:5; cond:4; 0:1; o2; Rn:5; Rd:5] ->
    SOME ((if sf
      then arm_csop op o2 (XREG' Rd) (XREG' Rn) (XREG' Rm)
      else arm_csop op o2 (WREG' Rd) (WREG' Rn) (WREG' Rm)) (Condition cond))
  | [sf; opc:2; 0b0101000:7; N; Rm:5; 0:6; Rn:5; Rd:5] ->
    if sf then arm_logop opc N (XREG' Rd) (XREG' Rn) (XREG' Rm)
          else arm_logop opc N (WREG' Rd) (WREG' Rn) (WREG' Rm)
  | [sf; opc:2; 0b100101:6; hw:2; imm16:16; Rd:5] ->
    if sf then arm_movop opc (XREG' Rd) imm16 (val hw * 16)
          else if val hw >= 2 then NONE else
               arm_movop opc (WREG' Rd) imm16 (val hw * 16)
  | [sf; 0b00100111:8; N; 0:1; Rm:5; imms:6; Rn:5; Rd:5] ->
    if sf then
      SOME (arm_EXTR (XREG' Rd) (XREG' Rn) (XREG' Rm) (rvalue (word_zx imms)))
    else if val imms < 32 then
      SOME (arm_EXTR (WREG' Rd) (WREG' Rn) (WREG' Rm) (rvalue (word_zx imms)))
    else NONE
  | [sf; 0b0011010110:10; Rm:5; 0b0010:4; op2:2; Rn:5; Rd:5] ->
    if sf then arm_lsvop op2 (XREG' Rd) (XREG' Rn) (XREG' Rm)
          else arm_lsvop op2 (WREG' Rd) (WREG' Rn) (WREG' Rm)
  | [sf; 0b10100110:8; N; immr:6; imms:6; Rn:5; Rd:5] ->
    arm_ubfmop sf Rd Rn N (val immr) (val imms)
  | [sf; 0b101101011000000000100:21; Rn:5; Rd:5] ->
    SOME (if sf then arm_CLZ (XREG' Rd) (XREG' Rn)
          else arm_CLZ (WREG' Rd) (WREG' Rn))
  | [sf; 0b0011011000:10; Rm:5; o0; Ra:5; Rn:5; Rd:5] ->
    SOME (if sf then (if o0 then arm_MSUB else arm_MADD)
                  (XREG' Rd) (XREG' Rn) (XREG' Rm) (XREG' Ra)
                else (if o0 then arm_MSUB else arm_MADD)
                  (WREG' Rd) (WREG' Rn) (WREG' Rm) (WREG' Ra))
  | [0b1101011001011111000000:22; Rn:5; 0:5] ->
    SOME (arm_RET (XREG' Rn))
  | [0b10011011110:11; Rm:5; 0b011111:6; Rn:5; Rd:5] ->
    SOME (arm_UMULH (XREG' Rd) (XREG' Rn) (XREG' Rm))
  | [1:1; x; 0b1110000:7; ld; 0:1; imm9:9; 0b01:2; Rn:5; Rt:5] ->
    SOME (arm_ldst ld x Rt (XREG_SP Rn) (Postimmediate_Offset (word_sx imm9)))
  | [1:1; x; 0b1110000:7; ld; 0:1; imm9:9; 0b11:2; Rn:5; Rt:5] ->
    SOME (arm_ldst ld x Rt (XREG_SP Rn) (Preimmediate_Offset (word_sx imm9)))
  | [1:1; x; 0b1110010:7; ld; imm12:12; Rn:5; Rt:5] ->
    SOME (arm_ldst ld x Rt (XREG_SP Rn)
      (Immediate_Offset (word (val imm12 * if x then 8 else 4))))
  | [1:1; x; 0b1110000:7; ld; 1:1; Rm:5; 0b011:3; S; 0b10:2; Rn:5; Rt:5] ->
    SOME (arm_ldst ld x Rt (XREG_SP Rn)
      (if S then Shiftreg_Offset (XREG' Rm) (if x then 3 else 2)
            else Register_Offset (XREG' Rm)))
  | [x; 0b010100:6; pre; 0b1:1; ld; imm7:7; Rt2:5; Rn:5; Rt:5] ->
    SOME (arm_ldstp ld x Rt Rt2 (XREG_SP Rn)
      ((if pre then Preimmediate_Offset else Postimmediate_Offset)
        (iword (ival imm7 * &(if x then 8 else 4)))))
  | [x; 0b01010010:8; ld; imm7:7; Rt2:5; Rn:5; Rt:5] ->
    SOME (arm_ldstp ld x Rt Rt2 (XREG_SP Rn)
      (Immediate_Offset (iword (ival imm7 * &(if x then 8 else 4)))))
  | _ -> NONE`;;

(* ------------------------------------------------------------------------- *)
(* Decode tactics.                                                           *)
(* ------------------------------------------------------------------------- *)

let encode_BL = new_definition `encode_BL n =
  0x94000000 + val (iword (n div &4):26 word)`;;

let decode_encode_BL = prove (`decode (word (encode_BL n)) =
  SOME (arm_BL (word (val (iword (n div &4):26 word) * 4)))`,
  MATCH_MP_TAC (
    let th = SPEC `word (encode_BL n):int32` decode in
    let tm = rhs (concl th) in
    let A, tr = bm_build_tree (rhs (concl th)) in
    let a = Array.init 32 (fun i -> Some ((0x94000000 land (1 lsl i)) != 0)) in
    (DISCH_ALL o REWRITE_RULE [] o INST [`T`,`op:bool`] o TRANS th)
      (hd (snd (snd (get_dt a (bm_add_pos tr tm)))))) THEN
  REWRITE_TAC [encode_BL] THEN
  SPEC_TAC (`iword (n div &4):26 word`,`w:26 word`) THEN
  REWRITE_TAC [FORALL_VAL_GEN; VAL_WORD; CONSPAT_pat_set; NILPAT_pat_set;
    word1; bitval] THEN
  CONV_TAC (DEPTH_CONV UNWIND_CONV THENC ONCE_DEPTH_CONV DIMINDEX_CONV THENC
    NUM_REDUCE_CONV) THEN IMP_REWRITE_TAC [MOD_LT] THEN ARITH_TAC);;

let split_32_64 F =
  let a = F `:32` and b = F `:64` in
  fun ty -> match Num.int_of_num (dest_finty ty) with
  | 32 -> a
  | 64 -> b
  | _ -> failwith "split_32_64";;

let REG_CONV =
  let xs = [|X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;X11;X12;X13;X14;X15;
             X16;X17;X18;X19;X20;X21;X22;X23;X24;X25;X26;X27;X28;X29;X30;XZR|]
  and ws = [|W0; W1; W2; W3; W4; W5; W6; W7; W8; W9; W10;W11;W12;W13;W14;W15;
             W16;W17;W18;W19;W20;W21;W22;W23;W24;W25;W26;W27;W28;W29;W30;WZR|] in
  List.iter (fun A -> Array.iteri (fun i th -> A.(i) <- SYM th) A) [xs;ws];
  let _ =
    let th1,th2 = (CONJ_PAIR o prove) (`XREG 31 = XZR /\ WREG 31 = WZR`,
      REWRITE_TAC [ARM_ZERO_REGISTER]) in
    xs.(31) <- th1; ws.(31) <- th2 in
  let xsp,wsp =
    let xth = REWRITE_RULE [GSYM XREG_SP; GE;
        REWRITE_RULE [GSYM NOT_LE] (ASSUME `n < 31`)] (SYM XREG) in
    let wth = REWRITE_RULE [xth; GSYM WREG] (SPEC `word n:5 word` WREG_SP) in
    let sp = REWRITE_RULE [GSYM XREG_SP] SP in
    let wsp = REWRITE_RULE [GSYM WREG_SP; sp] WSP in
    let F spth regth A = Array.mapi (fun i th ->
      if i = 31 then SYM spth else
      let th' = INST [mk_numeral (Int i),`n:num`] regth in
      TRANS (PROVE_HYP (EQT_ELIM (NUM_RED_CONV (hd (hyp th')))) th') th) A in
    F sp xth xs, F wsp wth ws in
  let xs',ws' =
    let F th' A = Array.mapi (fun i ->
      TRANS (CONV_RULE (RAND_CONV (RAND_CONV WORD_RED_CONV))
        (SPEC (mk_comb (`word:num->5 word`, mk_numeral (Int i))) th'))) A in
    F XREG' xs, F WREG' ws in
  function
  | Comb(Const("XREG",_),n) -> xs.(Num.int_of_num (dest_numeral n))
  | Comb(Const("WREG",_),n) -> ws.(Num.int_of_num (dest_numeral n))
  | Comb(Const("XREG'",_),Comb(Const("word",_),n)) ->
    xs'.(Num.int_of_num (dest_numeral n))
  | Comb(Const("WREG'",_),Comb(Const("word",_),n)) ->
    ws'.(Num.int_of_num (dest_numeral n))
  | Comb(Const("XREG_SP",_),Comb(Const("word",_),n)) ->
    xsp.(Num.int_of_num (dest_numeral n))
  | Comb(Const("WREG_SP",_),Comb(Const("word",_),n)) ->
    wsp.(Num.int_of_num (dest_numeral n))
  | _ -> failwith "REG_CONV";;

let CONDITION_CONV =
  let pths =
    let l = map SYM CONDITION_CLAUSES in
    Array.init 16 (fun i -> find ((=) i o
      Num.int_of_num o dest_numeral o rand o rand o lhs o concl) l) in
  function
  | Comb(Const("Condition",_),Comb(Const("word",_),n)) ->
    pths.(Num.int_of_num (dest_numeral n))
  | _ -> failwith "CONDITION_CONV";;

let bool_split pth =
  let pthT = pth `T` and pthF = pth `F` in
  function
  | Const("T",_) -> pthT
  | Const("F",_) -> pthF
  | e -> failwith "bool_split";;

let BINARY_NSUM_CONV =
  let pth0 = prove (`nsum {i | i < 0 /\ p i} f = _0`,
     REWRITE_TAC [LT; EMPTY_GSPEC; NSUM_CLAUSES; NUMERAL])
  and pthS = prove (`SUC a' = a ==>
    nsum {i | i < a /\ p i} (\i. 2 EXP i) =
    (if p 0 then BIT1 else BIT0)
      (nsum {i | i < a' /\ p (SUC i)} (\i. 2 EXP i))`,
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MP_TAC (ISPECL [`SUC`; `\i. 2 EXP i`;
      `{i | i < a' /\ p (SUC i)}`] NSUM_IMAGE) THEN
    ANTS_TAC THENL [METIS_TAC [SUC_INJ]; ALL_TAC] THEN
    REWRITE_TAC [o_DEF; EXP; NSUM_LMUL] THEN
    COND_CASES_TAC THENL (map (fun t ->
      SUBGOAL_THEN t (SUBST1_TAC) THENL [
        REWRITE_TAC [EXTENSION; IN_ELIM_THM; IN_INSERT; IN_IMAGE] THEN
        GEN_TAC THEN DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
          (SPEC `x:num` num_CASES) THEN
        ASM_REWRITE_TAC [CONJUNCT1 LT; LT_0; LT_SUC; SUC_INJ;
          ARITH_RULE `~(0 = SUC n)`] THEN
        CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REFL_TAC;
        DISCH_THEN (fun th ->
          CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [BIT0; BIT1])) THEN
          IMP_REWRITE_TAC [GSYM MULT_2; SYM th; NSUM_CLAUSES; IN_IMAGE;
            ARITH_RULE `~(0 = SUC n)`; ARITH_RULE `2 EXP 0 + x = SUC x`] THEN
          MATCH_MP_TAC FINITE_IMAGE THEN ASSUME_TAC th THEN
          MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < a'}` THEN
          REWRITE_TAC [FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
          METIS_TAC [])])
      [`{i | i < SUC a' /\ p i} =
        0 INSERT IMAGE SUC {i | i < a' /\ p (SUC i)}`;
       `{i | i < SUC a' /\ p i} = IMAGE SUC {i | i < a' /\ p (SUC i)}`]))
  and zero_conv = TRY_CONV (PART_MATCH lhs (REWRITE_RULE [NUMERAL] BIT0_0)) in
  fun conv -> function
  | Comb(Comb(Const("nsum",_),s),f) as t when aconv f `\i. 2 EXP i` ->
    let rec go n =
      if n = 0 then PART_MATCH lhs pth0 else
      PART_MATCH lhs (MATCH_MP pthS
        (NUM_SUC_CONV (mk_comb (`SUC`, mk_numeral (Int (n-1)))))) THENC
      COMB2_CONV
        (RATOR_CONV (LAND_CONV (TRY_CONV BETA_CONV THENC conv)) THENC REWRITE_CONV [])
        (go (n-1)) THENC zero_conv in
    let _,ls,_ = term_match [] `{i:num | i < a /\ p i}` s in
    (go (Num.int_of_num (dest_numeral (vsubst ls `a:num`))) THENC
      PART_MATCH lhs (SYM (SPEC_ALL NUMERAL))) t
  | _ -> failwith "BINARY_NSUM_CONV";;

let DECODE_BITMASK_CONV =
  let pths = split_32_64 (fun ty -> bool_split (fun n ->
    Array.init 64 (fun r -> Array.init 64 (fun s -> lazy (
      let r = mk_comb (`word:num->6 word`, mk_numeral (Int r))
      and s = mk_comb (`word:num->6 word`, mk_numeral (Int s)) in
      CONV_RULE (WORD_REDUCE_CONV THENC
        NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
        NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
        NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
        NUM_REDUCE_CONV THENC REWRITE_CONV [
          WORD_OF_BITS_AS_WORD; IN_ELIM_THM; DIMINDEX_32; DIMINDEX_64] THENC
        TRY_CONV (funpow 3 RAND_CONV (BINARY_NSUM_CONV NUM_REDUCE_CONV)))
      (REWRITE_RULE [word1; bitval]
        (SPECL [n; r; s] (INST_TYPE [ty,`:N`] decode_bitmask)))))))) in
  function
  | Comb(Comb(Comb(Const("decode_bitmask",_),n),
      Comb(Const("word",_),immr)),Comb(Const("word",_),imms)) as t ->
    let nty = dest_word_ty (hd (snd (dest_type (type_of t)))) in
    Lazy.force (pths nty n)
      .(Num.int_of_num (dest_numeral immr))
      .(Num.int_of_num (dest_numeral imms))
  | _ -> failwith "DECODE_BITMASK_CONV";;

let dest_component = function
| Tyapp("component", [A; B]) -> A, B
| _ -> failwith "dest_component";;

let ALIAS_CONV =
  let self = ref NO_CONV in
  let ALIAS_CONV t = !self t in
  let net = basic_net() in
  let specialize th f =
    let g ty xth =
      let th' = INST_TYPE (map (fun ty' -> ty,ty')
        (type_vars_in_term (concl th))) th in
      try f (CONV_RULE (CHANGED_CONV (REWRITE_CONV [SYM xth])) th')
      with _ -> I in
    g `:64` XZR_ZR o g `:32` WZR_ZR o f th in
  let f th =
    if can (find_term
        (fun e -> `invert_condition cc` = e) o lhs) (concl th) then
      let th = REWRITE_RULE [INVERT_CONDITION_TWICE]
        (INST [`invert_condition cc`,`cc:condition`] th) in
      specialize th (fun th ->
        net_of_conv (lhs (concl th)) (REWR_CONV th THENC
          REWRITE_CONV [invert_condition] THENC TRY_CONV ALIAS_CONV))
    else specialize th (fun th ->
      net_of_conv (lhs (concl th)) (REWR_CONV th)) in
  let net = itlist (f o SYM o SPEC_ALL) ARM_INSTRUCTION_ALIASES net in
  let MOVZ_CONV =
    (fun th -> MP th (EQT_ELIM (NUM_LT_CONV (lhand (concl th))))) o
    PART_MATCH (lhs o rand) (GSYM arm_MOVZ_ALT) in
  let net = itlist (uncurry net_of_conv)
    [`arm_MOVZ (Rd:(armstate,N word)component) (word imm) 0`,MOVZ_CONV]
    net in
  self := ONCE_DEPTH_CONV (REWRITES_CONV net);
  ALIAS_CONV;;

let PURE_DECODE_CONV =
  let constructors =
    let constructors_of =
      let rec f = function
      | Const(s,_) -> s
      | Comb(tm,_) -> f tm
      | _ -> failwith "constructors_of" in
      map (f o rand o snd o strip_forall) o
      conjuncts o lhand o snd o dest_forall o concl in
    ["T";"F";",";"NONE";"SOME";"int_of_num"] @
    ["XZR";"WZR";"SP";"WSP";"rvalue";"word";"iword"] @
    constructors_of offset_INDUCT @
    map (fun n -> "X"^string_of_int n) (0--30) @
    map (fun n -> "W"^string_of_int n) (0--30) @
    map (fst o dest_const o fst o strip_comb o lhs o concl)
      (CONDITION_CLAUSES @ ARM_OPERATION_CLAUSES @ ARM_LOAD_STORE_CLAUSES) @
    ["arm_LSL";"arm_LSR"] in

  let genvar =
    let gcounter = ref 0 in
    fun ty ->
      let count = !gcounter in
      (gcounter := count + 1;
      mk_var ("eval%"^(string_of_int count), ty)) in

  let mk_pth th =
    let th = SPEC_ALL th in
    let _,es = strip_comb (lhs (concl th)) in
    C INST th o C zip es in
  let mk_pth_split th =
    split_32_64 (fun ty -> mk_pth (INST_TYPE [ty,`:N`] th)) in

  let pth_obind = (UNDISCH o prove)
   (`f = SOME (a:A) ==> (f >>= g) = g a:B option`,
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [obind])
  and pth_cond_T = (UNDISCH o prove)
   (`p = T ==> (if p then a else b:A) = a`,
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [])
  and pth_cond_F = (UNDISCH o prove)
   (`p = F ==> (if p then a else b:A) = b`,
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [])
  and pth_bitop = mk_pth_split arm_bitop
  and pth_adcop = mk_pth_split arm_adcop
  and pth_addop = mk_pth_split arm_addop
  and pth_logop = mk_pth_split arm_logop
  and pth_movop = mk_pth_split arm_movop
  and pth_csop = mk_pth_split arm_csop
  and pth_lsvop = mk_pth_split arm_lsvop
  and pth_ubfmop = mk_pth arm_ubfmop
  and pth_ldst = mk_pth arm_ldst
  and pth_ldstp = mk_pth arm_ldstp in

  let rec eval_prod = function
  | Tyapp("prod",[A;B]) ->
    let tm1, f1 = eval_prod A in
    let tm2, f2 = eval_prod B in
    mk_pair (tm1, tm2),
    (function
    | Comb(Comb(Const(",",_),t1'),t2'),ls -> f1 (t1', f2 (t2', ls))
    | _ -> failwith "eval_prod")
  | A -> let v = genvar A in v, fun e,ls -> (e,v)::ls in

  let delay_if b t k conv =
    if b then
      let x, f = eval_prod (type_of t) in
      let g = k (ASSUME (mk_eq (t, x))) in
      fun ls ->
        let th' = conv (vsubst ls t) in
        PROVE_HYP th' (g (f (rhs (concl th'), ls)))
    else k (conv t)

  and eval_opt =
    let some = mk_const ("SOME", []) in
    fun tm F conv -> match type_of tm with
    | Tyapp("option",[A]) ->
      let tm', f = eval_prod A in
      let g = F (ASSUME (mk_eq (tm, mk_comb (inst [A,aty] some, tm')))) in
      fun ls ->
        let th = conv (vsubst ls tm) in
        (match rhs (concl th) with
        | Comb(Const("SOME",_),tm1) -> PROVE_HYP th (g (f (tm1, ls)))
        | Const("NONE",_) -> failwith "eval_opt got NONE"
        | _ -> failwith "eval_opt")
    | ty -> failwith ("eval_opt " ^ string_of_type ty) in

  let rec evaluate t (F:thm->(term*term)list->thm) = match t with
  | Comb(Comb(Const(">>=",_),f),g) ->
    evaluate f (fun th ->
      match rhs (concl th) with
      | Comb(Const("SOME",_),a) ->
        let A,B = match type_of g with
        | Tyapp(_,[A;Tyapp(_,[B])]) -> A,B | _ -> fail() in
        let th' = PROVE_HYP th (PINST [A,aty; B,bty]
          [f,`f:A option`; a,`a:A`; g,`g:A->B option`] pth_obind) in
        evaluate (rhs (concl th')) (F o TRANS th')
      | _ -> failwith "evaluate >>= did not get SOME a")
  | Comb(Comb(Comb(Const("COND",_),e),a),b) ->
    evaluate e (fun th ->
      let A = type_of a in
      let inst = PINST [A, aty] [e,`p:bool`; a,`a:A`; b,`b:A`] in
      match rhs (concl th) with
      | Const("T",_) -> evaluate a (F o TRANS (PROVE_HYP th (inst pth_cond_T)))
      | Const("F",_) -> evaluate b (F o TRANS (PROVE_HYP th (inst pth_cond_F)))
      | e' ->
        let gT,gF =
          let gi rhs r pth =
            let th = PROVE_HYP (TRANS th (ASSUME (mk_eq (e',r)))) (inst pth) in
            try evaluate rhs (F o TRANS th)
            with Failure s -> fun _ ->
              failwith (sprintf "failed at %s:\n%s" (string_of_term t) s) in
          gi a `T` pth_cond_T, gi b `F` pth_cond_F in
        fun ls ->
          let th' = TRY_CONV WORD_RED_CONV (vsubst ls e') in
          match rhs (concl th') with
          | Const("T",_) -> PROVE_HYP th' (gT ls)
          | Const("F",_) -> PROVE_HYP th' (gF ls)
          | _ -> failwith "evaluate if..then failed")
  | Comb(Comb(Const("_BITMATCH",_),(Var(_,ty) as e)),cs) ->
    let one_pattern = function
    | Comb(Comb(Const("_SEQPATTERN",_),_),
        Comb(Const("_ELSEPATTERN",_),Const(s,_))) -> mem s ["NONE"; "ARB"]
    | _ -> false in
    if one_pattern cs then
      let th = BM_FIRST_CASE_CONV t in
      let fn = inst_bitpat_numeral (hd (hyp th)) in
      let g = evaluate (rhs (concl th)) (F o TRANS th) in
      fun ls ->
        let ls', th' = fn (dest_numeral (rand (vsubst ls e))) in
        PROVE_HYP th' (g (ls' @ ls))
    else
      let sz = Num.int_of_num (dest_finty (dest_word_ty ty))
      and gs =
        let f th = try
          let fn = inst_bitpat_numeral (hd (hyp th))
          and g = evaluate (rhs (concl th)) (F o TRANS th) in
          fun n ls ->
            let ls', th' = try fn n with Failure _ ->
              failwith (sprintf "match failed: 0x%08x" (Num.int_of_num n)) in
            PROVE_HYP th' (g (ls' @ ls))
        with Failure _ as e -> fun _ _ -> raise e in
        map_dt (f o hd o snd) (snd (bm_build_pos_tree t)) in
      fun ls ->
        let nn = dest_numeral (rand (rev_assoc e ls)) in
        let n = Num.int_of_num nn in
        let A = Array.init sz (fun i -> Some (n land (1 lsl i) != 0)) in
        snd (get_dt A gs) nn ls
  | Comb(Comb((Const("_MATCH",_) as f),e),cs) ->
    if not (is_var e) then
      let th = CHANGED_CONV MATCH_CONV t in
      evaluate (rhs (concl th)) (F o TRANS th) else
    let one_pattern = function
    | Comb(Comb(Const("_SEQPATTERN",_),_),cs) ->
      (match cs with
      | Abs(_,Abs(_,Comb(Const("?",_),Abs(Var("_",_),
          Comb(Comb(Const("_UNGUARDED_PATTERN",_),_),
            Comb(Comb(Const("GEQ",_),Const(s,_)),_)))))) ->
        mem s ["NONE"; "ARB"]
      | _ -> false)
    | _ -> true in
    let ty = type_of e in
    if one_pattern cs then
      match snd (strip_exists (body (body (lhand cs)))) with
      | Comb(Comb(Const("_UNGUARDED_PATTERN",_),
          Comb(Comb(Const("GEQ",_),p),_)),_) ->
        let th = AP_THM (AP_TERM f (ASSUME (mk_eq (e, p)))) cs in
        let th = TRANS th (MATCH_CONV (rhs (concl th))) in
        let g = evaluate (rhs (concl th)) (F o TRANS th) in
        fun ls ->
          let e' = vsubst ls e in
          let _,ls',_ = term_unify (frees p) p e' in
          PROVE_HYP (REFL e') (g (ls' @ ls))
      | _ -> raise (Invalid_argument "unsupported match kind")
    else
      raise (Invalid_argument ("Unknown match type " ^ string_of_type ty))
  | Comb((Const("XREG'",_) as f),a) -> eval_unary f a F REG_CONV
  | Comb((Const("WREG'",_) as f),a) -> eval_unary f a F REG_CONV
  | Comb((Const("XREG_SP",_) as f),a) -> eval_unary f a F REG_CONV
  | Comb((Const("WREG_SP",_) as f),a) -> eval_unary f a F REG_CONV
  | Comb(Const("arm_bitop",_),_) ->
    eval_nary (pth_bitop (dest_word_ty (snd (dest_component
      (fst (dest_fun_ty (type_of t))))))) t F
  | Comb(Comb(Const("arm_adcop",_),_),_) ->
    eval_nary (pth_adcop (dest_word_ty (snd (dest_component
      (fst (dest_fun_ty (type_of t))))))) t F
  | Comb(Comb(Const("arm_addop",_),_),_) ->
    eval_nary (pth_addop (dest_word_ty (snd (dest_component
      (fst (dest_fun_ty (type_of t))))))) t F
  | Comb(Comb(Comb(Comb(Comb(Const("arm_logop",_),_),_),rd),_),_) ->
    let N = dest_word_ty (snd (dest_component (type_of rd))) in
    eval_nary (pth_logop N) t F
  | Comb(Comb(Comb(Comb(Const("arm_movop",_),_),rd),_),_) ->
    let N = dest_word_ty (snd (dest_component (type_of rd))) in
    eval_nary (pth_movop N) t F
  | Comb(Comb(Const("arm_csop",_),_),_) ->
    eval_nary (pth_csop (dest_word_ty (snd (dest_component
      (fst (dest_fun_ty (type_of t))))))) t F
  | Comb(Comb(Comb(Comb(Const("arm_lsvop",_),_),rd),_),_) ->
    let N = dest_word_ty (snd (dest_component (type_of rd))) in
    eval_nary (pth_lsvop N) t F
  | Comb(Comb(Comb(Comb(Comb(Comb(Const("arm_ubfmop",_),_),_),_),_),_),_) ->
    eval_nary pth_ubfmop t F
  | Comb(Comb(Comb(Const("arm_ldst",_),_),_),_) -> eval_nary pth_ldst t F
  | Comb(Comb(Comb(Comb(Const("arm_ldstp",_),_),_),_),_) ->
    eval_nary pth_ldstp t F
  | Comb((Const("Condition",_) as f),a) -> eval_unary f a F CONDITION_CONV
  | Comb(Comb(Comb(Const("decode_bitmask",_),_),_),_) ->
    eval_opt t F DECODE_BITMASK_CONV
  | Comb((Const("word_zx",_) as f),a) -> eval_unary f a F WORD_ZX_CONV
  | Comb((Const("word_sx",_) as f),a) -> eval_unary f a F IWORD_SX_CONV
  | Comb((Const("word_not",_) as f),a) -> eval_unary f a F WORD_RED_CONV
  | Comb(Const("@",_),_) -> raise (Invalid_argument "ARB")
  | Const("ARB",_) -> raise (Invalid_argument "ARB")
  | Comb(Comb((Const("=",_) as f),a),b) -> eval_binary f a b F
    (if type_of a = `:num` then NUM_RED_CONV else
     if can dest_word_ty (type_of a) then WORD_RED_CONV else
     raise (Invalid_argument "unknown = type"))
  | Comb(Comb((Const("/\\",_) as f),a),b) ->
    eval_binary f a b F (REWRITE_CONV [])
  | Comb(Comb((Const("\\/",_) as f),a),b) ->
    eval_binary f a b F (REWRITE_CONV [])
  | Comb(Comb((Const(">=",_) as f),a),b) -> eval_binary f a b F NUM_RED_CONV
  | Comb(Comb((Const("<",_) as f),a),b) -> eval_binary f a b F NUM_RED_CONV
  | Comb(Comb((Const("*",_) as f),a),b) -> eval_binary f a b F NUM_RED_CONV
  | Comb(Comb((Const("+",_) as f),a),b) -> eval_binary f a b F NUM_RED_CONV
  | Comb(Comb((Const("-",_) as f),a),b) -> eval_binary f a b F NUM_RED_CONV
  | Comb(Comb((Const("EXP",_) as f),a),b) -> eval_binary f a b F NUM_RED_CONV
  | Comb(Comb((Const("int_mul",_) as f),a),b) ->
    eval_binary f a b F INT_RED_CONV
  | Comb((Const("val",_) as f),a) -> eval_unary f a F WORD_RED_CONV
  | Comb((Const("ival",_) as f),a) -> eval_unary f a F WORD_RED_CONV
  (* | Comb((Const("iword",_) as f),a) -> eval_unary f a F WORD_RED_CONV *)
  | Comb(f,a) when (match f with
    | Comb(Const("GABS",_),_) -> true
    | Abs(_,_) -> true
    | _ -> false) ->
    evaluate a (fun th ->
      let th1 = AP_TERM f th in
      let th2 = TRANS th1 (GEN_BETA_CONV (rhs (concl th1))) in
      evaluate (rhs (concl th2)) (F o TRANS th2))
  | Comb((Comb(Const("LET",_),_) as f),a) ->
    evaluate a (fun th ->
      let th1 = AP_TERM f th in
      let th2 = TRANS th1 (let_CONV (rhs (concl th1))) in
      evaluate (rhs (concl th2)) (F o TRANS th2))
  | Comb(Const("NUMERAL",_),_) when is_numeral t -> F (REFL t)
  | Comb(f,a) ->
    evaluate f (fun th -> evaluate a (fun th' ->
      if f = rhs (concl th) then F (AP_TERM f th') else
      let th2 = MK_COMB (th, th') in
      evaluate (rhs (concl th2)) (F o TRANS th2)))
  | Const(s,_) -> if mem s constructors then F (REFL t) else
    raise (Invalid_argument ("evaluate: unknown function " ^ s))
  | Var(_,_) -> F (REFL t)
  | Abs(_,_) -> F (REFL t)
  and eval_unary' f a F conv =
    evaluate a (fun th ->
      let th1 = f th in
      let tm = rhs (concl th1) in
      delay_if (is_var (rand tm)) tm (F o TRANS th1) conv)
  and eval_unary f a F conv = eval_unary' (AP_TERM f) a F conv
  and eval_binary f a b F conv =
    evaluate a (fun tha -> evaluate b (fun thb ->
      let th1 = MK_COMB (AP_TERM f tha, thb) in
      let tm = rhs (concl th1) in
      delay_if (is_var (lhand tm) || is_var (rand tm))
        tm (F o TRANS th1) conv))
  and eval_nary pth t F =
    let rec go t F = match t with
    | Comb(f,x) -> go f (fun th ls -> evaluate x (fun th' ->
      F (MK_COMB (th, th')) (rhs (concl th') :: ls)))
    | _ -> F (REFL t) [] in
    go t (fun th ls ->
      let th1 = TRANS th (pth (rev ls)) in
      evaluate (rhs (concl th1)) (F o TRANS th1)) in

  let g =
    let th = SPEC_ALL decode in
    evaluate (rhs (concl th)) (C INST o TRANS th) in
  function
  | Comb(Const("decode",_),w) ->
    (match w with
    | Comb(Const("word",_),Comb(Const("encode_BL",_),n)) ->
      INST [n,`n:int`] decode_encode_BL
    | _ -> g [w,`w:int32`])
  | _ -> failwith "PURE_DECODE_CONV";;
PURE_DECODE_CONV `decode (word 0xa9bf57f4)`;;

let DECODE_CONV tm =
  let th = PURE_DECODE_CONV tm in
  try CONV_RULE (RAND_CONV (RAND_CONV ALIAS_CONV)) th
  with _ -> th;;

(* ------------------------------------------------------------------------- *)
(* Testing and preparation.                                                  *)
(* ------------------------------------------------------------------------- *)

let rec decode_all = function
| Const("NIL",_) -> []
| tm ->
  let th1 = READ_WORD_CONV (mk_comb (`read_int32`, tm)) in
  let a,next = dest_pair (rand (rhs (concl th1))) in
  let th = DECODE_CONV (mk_comb (`decode`, a)) in
  rand (rhs (concl th)) :: decode_all next;;

let dest_cons4 =
  let assert_byte n = function
  | Comb(Const("word",_),a) -> dest_numeral a = Int n
  | _ -> false in
  fun n -> function
  | Comb(Comb(Const("CONS",_),a1), Comb(Comb(Const("CONS",_),a2),
      Comb(Comb(Const("CONS",_),a3), Comb(Comb(Const("CONS",_),a4),tm)))) when
    0 <= n && n <= 0xffffffff &&
    assert_byte (n land 0xff) a1 &&
    assert_byte ((n lsr 8) land 0xff) a2 &&
    assert_byte ((n lsr 16) land 0xff) a3 &&
    assert_byte ((n lsr 24) land 0xff) a4 -> tm
  | _ -> failwith "dest_cons4";;

(* Asserts that the input term is the given list of words, and returns it. *)
let assert_word_list tm ls =
  if type_of tm = `:byte list` then
    let rec go = function
    | [], Const("NIL",_) -> ()
    | n::ls, tm -> go (ls, dest_cons4 n tm)
    | _ -> failwith "assert_word_list" in
    go (ls, tm)
  else failwith "assert_word_list";
  tm;;

let define_word_list name tm =
  try new_definition (mk_eq (mk_var (name, `:byte list`), tm))
  with Failure _ ->
    new_definition (mk_eq (mk_mconst (name, `:byte list`), tm));;

let define_assert_word_list name tm ls =
  define_word_list name (assert_word_list tm ls);;

let define_relocs name (args, tm) =
  let rec mk_tm_comb f A = function
  | [] -> f (name, A)
  | (v::vs) -> mk_comb (mk_tm_comb f (mk_fun_ty (type_of v) A) vs, v) in
  try new_definition (mk_eq (mk_tm_comb mk_var `:byte list` (rev args), tm))
  with Failure _ ->
    new_definition (mk_eq (mk_tm_comb mk_mconst `:byte list` (rev args), tm));;

let assert_relocs =
  let consume_word n (pc,tm) = pc+4, dest_cons4 n tm in
  let ptm = `bytelist_of_num 4 (encode_BL (&v - &(pc + i)))` in
  let rec consume_reloc_BL sym = function
    | pc, Comb(Comb(Const("APPEND",_),v),tm)
      when v = vsubst [mk_var(sym,`:num`),`v:num`;
        mk_numeral (Int pc),`i:num`] ptm -> (pc+4,tm)
    | _ -> failwith "assert_relocs" in
  fun (args,tm) F ->
    if type_of tm = `:byte list` then
      match rev_itlist I (F consume_word consume_reloc_BL) (0,tm) with
      | _,Const("NIL",_) -> ()
      | _ -> failwith "assert_relocs"
    else failwith "assert_relocs";
    (args,tm);;

let define_assert_relocs name tm =
  define_relocs name o assert_relocs tm;;

needs "Common/elf.ml";;

let make_fn_word_list, make_fn_word_list_reloc =
  let go rhs_col =
    let indent = "\n" ^ String.make rhs_col ' ' in
    fun rels start end_ head bs dec ->
      let buf = Buffer.create 1024 in
      Buffer.add_string buf start;
      let rec go i r = function
      | [] -> r ""
      | (inst::l) ->
        let () = r ";" in
        let j = i + 4 in
        go j (fun s ->
          let col = match rels i with
          | None ->
          (bprintf buf "  %s0x%08x%s" head (get_int_le bs i 4) s;
            String.length head + String.length s + 12)
          | Some (Arm_call26,sym,_) ->
          (bprintf buf "  BL \"%s\"%s" sym s;
            String.length sym + String.length s + 7)
          | Some (Arm_condbr19,sym,0) -> failwith "unsupported Arm_condbr19" in
          bprintf buf "%s(* %s *)\n"
            (if col < rhs_col then String.make (rhs_col - col) ' ' else indent)
            (string_of_term inst)) l in
      go 0 (fun _ -> ()) dec;
      bprintf buf end_;
      Buffer.contents buf in
  go 20 (fun _ -> None) "[\n" "];;\n" "",
  let go = go 24 in
  fun (bs, rels) ->
    let r = ref rels in
    let f i = match !r with
    | (ty,(off,sym,add)) :: rels when off = i -> r := rels; Some (ty,sym,add)
    | _ -> None in
    go f "(fun w BL -> [\n" "]);;\n" "w " bs;;
(*
let trim_ret_core dec =
  let m1 = Array.length dec - 1 in
  if m1 < 0 then failwith "trim_ret: empty" else
  let lr,r = dec.(m1) in
  if r <> `RET` then
    failwith "trim_ret: function does not end with RET" else
  let rec go a b i j =
    match if i < j then
      match dec.(i), dec.(j) with
      | (n,Comb(Const("PUSH",_),tm)), (m,Comb(Const("POP",_),tm'))
        when tm = tm' -> Some(a+n,b+m,tm)
      | _ -> None
    else None with
    | Some(a',b',tm) -> let ls,r = go a' b' (i+1) (j-1) in tm::ls, r
    | None -> [], (a, b, Array.sub dec i (j+1-i)) in
  go 0 lr 0 (m1-1);;

let trim_ret ((bs:term array), dec) =
  let ls,(a,b,dec) = trim_ret_core (Array.of_list dec) in
  ls, a, (Array.sub bs a (Array.length bs - b - a), Array.to_list dec);; *)

let rec dest_mc_list = function
| Const("NIL",_) -> []
| Comb(Comb(Const("CONS",_),a),t) -> a :: dest_mc_list t
| Comb(Comb(Const("APPEND",_),a),t) -> a :: dest_mc_list t
| _ -> failwith "dest_mc_list";;

let rec term_of_mc_list =
  let nil = `NIL:byte list`
  and cons = `CONS:byte->byte list->byte list`
  and append = `APPEND:byte list->byte list->byte list` in
  function
  | [] -> nil
  | (Comb(Const("word",_),_) as a) :: ls ->
    mk_comb (mk_comb (cons, a), term_of_mc_list ls)
  | a :: ls -> mk_comb (mk_comb (append, a), term_of_mc_list ls);;
(*
let trim_ret_off tm =
  let _,n,bs = trim_ret (Array.of_list (dest_mc_list tm), decode_all tm) in
  n,term_of_mc_list (Array.to_list (fst bs));;

let trim_ret' = snd o trim_ret_off;; *)

let N_SUBLIST_CONV =
  let pth1,pth2 =
    W f_f_ (PART_MATCH lhs o SPEC_ALL) (CONJ_PAIR (GSYM APPEND))
  and pth3 = PART_MATCH lhs (SPEC_ALL APPEND_ASSOC) in
  fun th ->
    let rec right tm = function
    | Const("NIL",_) -> pth1 tm
    | Comb(Comb(Const("CONS",_),_),l) ->
      let f,tm' = dest_comb tm in
      let th = AP_TERM f (right tm' l) in
      TRANS th (pth2 (rhs (concl th)))
    | Comb(Comb(Const("APPEND",_),_),l) ->
      let f,tm' = dest_comb tm in
      let th = AP_TERM f (right tm' l) in
      TRANS th (pth3 (rhs (concl th)))
    | _ -> failwith "N_SUBLIST_CONV" in
    let rec left n tm = if n = 0 then
      let th = SYM th in
      let th1 = right tm (lhs (concl th)) in
      let th2 = CONV_RULE (RAND_CONV (LAND_CONV (K th))) th1 in
      TRANS th2 (pth1 (rhs (concl th2)))
    else
      let f,tm' = dest_comb tm in
      let th = AP_TERM f (left (n-1) tm') in
      TRANS th (pth2 (rhs (concl th))) in
    left;;
(*
let define_trim_ret_thm name th =
  let th = SPEC_ALL th in
  let df,tm1 = dest_eq (concl th) in
  let n, tm = trim_ret_off tm1 in
  let rec args ls = function
  | Comb(f,v) -> args (v::ls) f
  | _ -> ls in
  let defn = define_relocs name (args [] df, tm) in
  defn, TRANS th (N_SUBLIST_CONV (SPEC_ALL defn) n tm1);; *)

let define_assert_from_elf name file =
  define_assert_word_list name (term_of_bytes (load_elf_contents_arm file));;

let print_literal_from_elf file =
  let bs = load_elf_contents_arm file in
  print_string (make_fn_word_list bs (decode_all (term_of_bytes bs)));;

(* Usage:
Use
  print_literal_from_elf "Arm/bignum_madd.o";;
to print the assembly listing, and copy it into the code below:

let bignum_madd_subroutine =
define_assert_from_elf "bignum_madd_subroutine" "Arm/bignum_madd.o" [
  0x53;                    (* PUSH (% rbx) *)
...
  0xc3                     (* RET *)
];;

let bignum_madd_mc = define_word_list "bignum_madd_mc"
  (trim_ret' (rhs (concl bignum_madd_subroutine)));; *)

let term_of_relocs_arm =
  let reloc_BL = `APPEND (bytelist_of_num 4 (encode_BL (&v - &(pc + i))))` in
  let append_reloc_BL sym add = curry mk_comb (vsubst
      [sym,`v:num`; mk_numeral (Int add),`i:num`] reloc_BL) in
  term_of_relocs (fun bs,ty,off,sym,add -> 4,
    match ty, get_int_le bs off 4, add with
    | Arm_call26, 0x94000000, 0 -> append_reloc_BL sym off
    | _ -> failwith "unsupported relocation kind");;

let assert_relocs_from_elf name file =
  assert_relocs (term_of_relocs_arm (load_elf_arm file));;

let define_assert_relocs_from_elf name file =
  define_assert_relocs name (term_of_relocs_arm (load_elf_arm file));;

let print_literal_relocs_from_elf file =
  let bs = load_elf_arm file in
  print_string (make_fn_word_list_reloc bs
    (decode_all (snd (term_of_relocs_arm bs))));;
