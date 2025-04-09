(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* Additional proof support for SP restriction to "aligned 16".              *)
(* ------------------------------------------------------------------------- *)

let NORMALIZE_ALIGNED_16_CONV =
  let pth = prove
   (`(!n x:int64.
      16 divides n ==> (aligned 16 (word_add x (word n)) <=> aligned 16 x)) /\
     (!n x:int64.
      16 divides n ==> (aligned 16 (word_add (word n) x) <=> aligned 16 x)) /\
     (!n x:int64.
      16 divides n ==> (aligned 16 (word_sub x (word n)) <=> aligned 16 x)) /\
     (!n x:int64.
      16 divides n ==> (aligned 16 (word_sub (word n) x) <=> aligned 16 x))`,
    REPEAT STRIP_TAC THEN FIRST (map MATCH_MP_TAC
     (CONJUNCTS ALIGNED_WORD_ADD_EQ @ CONJUNCTS ALIGNED_WORD_SUB_EQ)) THEN
    ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC DIVIDES_CONV) in
  let funs = map (PART_MATCH (lhs o rand)) (CONJUNCTS pth) in
  let conv tm =
    try let th = tryfind (fun f -> f tm) funs in
        MP th (EQT_ELIM(DIVIDES_CONV(lhand(concl th))))
    with Failure _ -> failwith ""
  and ptm = `aligned 16 :int64->bool` in
  fun tm ->
    if is_comb tm && rator tm = ptm then REPEATC conv tm
    else failwith "NORMALIZE_ALIGNED_16_CONV";;

let SUB_ALIGNED_16_CONV =
  let ptm = `aligned 16 :int64->bool` in
  let rec subconv conv tm =
    match tm with
    | Comb(ptm',_) when ptm' = ptm -> RAND_CONV conv tm
    | Comb(l,r) -> COMB_CONV (subconv conv) tm
    | Abs(x,bod) -> ABS_CONV (subconv conv) tm
    | _ -> REFL tm in
  subconv;;

let (ALIGNED_16_TAC:tactic) =
  let basetac =
    CONV_TAC
     (SUB_ALIGNED_16_CONV(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV)) THEN
    ASM (GEN_REWRITE_TAC
      (LAND_CONV o SUB_ALIGNED_16_CONV o TOP_DEPTH_CONV)) [] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_16_CONV) THEN
    ASSUM_LIST(fun thl ->
      REWRITE_TAC(mapfilter (CONV_RULE NORMALIZE_ALIGNED_16_CONV) thl))
  and trigger = vfree_in `aligned:num->int64->bool` in
  fun (asl,w) -> if trigger w then basetac (asl,w) else ALL_TAC (asl,w);;

let ALIGNED_16_CONV ths =
  let baseconv =
    SUB_ALIGNED_16_CONV(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THENC
    GEN_REWRITE_CONV (SUB_ALIGNED_16_CONV o TOP_DEPTH_CONV) ths THENC
    ONCE_DEPTH_CONV NORMALIZE_ALIGNED_16_CONV THENC
    REWRITE_CONV(mapfilter (CONV_RULE NORMALIZE_ALIGNED_16_CONV) ths)
  and trigger = vfree_in `aligned:num->int64->bool` in
  fun tm -> if trigger tm then baseconv tm else REFL tm;;
