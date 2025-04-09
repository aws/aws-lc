(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*            Common tactics for proving program equivalence.                *)
(*  Assumes that this file will be loaded after necessary assembly semantics *)
(*  is loaded ({arm,x86}/proofs/...), as common/bignum.ml does).             *)
(* ========================================================================= *)

needs "common/relational2.ml";;

let equiv_print_log = ref false;;


(* ------------------------------------------------------------------------- *)
(* Memory read expression rewriter. This is useful when there is no exactly  *)
(* matching `read (memory :> bytesXX ...) = ..` equality in assumptions but  *)
(* can be somehow inferred from it. MK_MEMORY_READ_EQ_BIGDIGIT_CONV examples *)
(* demonstrate a few useful cases.                                           *)
(* ------------------------------------------------------------------------- *)

(* Given t which is `memory :> bytes (..)` or `memory :> bytes64 (..)`,
   return the address, byte size and constructor name ("bytes64", "bytes", ...).
   Note that this relies on the fact that both armstate and x86state structures
   have the memory field. *)
let get_memory_read_info (t:term): (term * term * string) option =
  if not (is_binary ":>" t) then None else
  let l,r = dest_binary ":>" t in
  let lname,_ = dest_const l in
  if lname <> "memory" then None else
  let c,args = strip_comb r in
  match fst (dest_const c) with
  | "bytes64" ->
    (* args is just a location *)
    assert (List.length args = 1);
    Some (List.hd args, `8`, "bytes64")
  | "bytes128" ->
    (* args is just a location *)
    assert (List.length args = 1);
    Some (List.hd args, `16`, "bytes128")
  | "bytes" ->
    (* args is (loc, len). *)
    assert (List.length args = 1);
    let a, sz = dest_pair (List.hd args) in
    Some (a, sz, "bytes")
  | _ -> (* don't know what it is *)
    None;;

let get_base_ptr_and_ofs (t:term): term * term =
  try (* t is "word_add baseptr (word ofs)" *)
    let baseptr,y = dest_binary "word_add" t in
    let wordc, ofs = dest_comb y in
    if name_of wordc <> "word" then failwith "not word" else
    (baseptr, ofs)
  with _ -> (t, mk_small_numeral 0);;

assert (get_base_ptr_and_ofs `x:int64` = (`x:int64`,`0`));;
assert (get_base_ptr_and_ofs `word_add x (word 32):int64` = (`x:int64`,`32`));;
assert (get_base_ptr_and_ofs `word_add x (word (8*4)):int64` = (`x:int64`,`8*4`));;
(* To get (x, 48) from this, WORD_ADD_ASSOC_CONST must be applied first. *)
assert (get_base_ptr_and_ofs `word_add (word_add x (word 16)) (word 32):int64` =
        (`word_add x (word 16):int64`, `32`));;
assert (get_base_ptr_and_ofs `word_add x (word k):int64` = (`x:int64`, `k:num`));;

let get_base_ptr_and_constofs (t:term): term * int =
  let base,ofs = get_base_ptr_and_ofs t in
  if is_numeral ofs then (base,dest_small_numeral ofs)
  else
    try
      let ofs = rhs (concl (NUM_RED_CONV ofs)) in
      (base,dest_small_numeral ofs)
    with _ -> (t,0);;

assert (get_base_ptr_and_constofs `word_add x (word (8*4)):int64` = (`x:int64`,32));;


let WORD_SUB2 = MESON [WORD_SUB]
  `y <= x ==> word_sub (word x) (word y):int64 = word (x - y)`;;

(** See the examples below.
    Input: a term 'read (memory :> ...)' as well as assumptions list.
    Returns: a pair of (the main rewrite rule theorem `t = ...`,
      auxiliary equality rules on memory reads that were needed to derive the
      equality but did not exist in the assumptions. **)
let rec MK_MEMORY_READ_EQ_BIGDIGIT_CONV =
  (* return (pointer, (baseptr and ofs), size, "constructor name", state var) *)
  let get_full_info t =
    match t with
    | Comb (Comb (Const ("read", _), comp), state_var) ->
      begin match get_memory_read_info comp with
      | Some (x,size,constrname) ->
        Some (x,get_base_ptr_and_ofs x,size,constrname,state_var)
      | _ -> None
      end
    | _ -> None in

  let const_num_opt (t:term): int option =
    try if is_numeral t then Some (dest_small_numeral t)
        else Some (dest_small_numeral (rhs (concl (NUM_RED_CONV t))))
    with _ -> None in
  let eight = `8` in
  let rec divide_by_8 t: term option =
    try Some (mk_small_numeral ((Option.get (const_num_opt t)) / 8))
    with _ -> try
      let l,r = dest_binary "*" t in
      if l = eight then Some r else if r = eight then Some l else None
    with _ -> try
      let l,r = dest_binary "+" t in
      match (divide_by_8 l),(divide_by_8 r) with
      | Some l', Some r' -> Some (mk_binary "+" (l',r'))
      | _ -> None
    with _ -> try
      let l,r = dest_binary "-" t in
      match (divide_by_8 l),(divide_by_8 r) with
      | Some l', Some r' -> Some (mk_binary "-" (l',r'))
      | _ -> None
    with _ -> None
    in
  let is_multiple_of_8 t = divide_by_8 t <> None in
  let subtract_num t1 t2: term option =
    if t2 = `0` then Some t1
    else if t1 = t2 then Some `0`
    else
      (* returns: ((sym expr, coeff) list, constant) *)
      let rec decompose_adds t: ((term * int) list) * int =
        try ([], dest_small_numeral t) with _ ->
        try let l,r = dest_binary "+" t in
          let lsyms,lconst = decompose_adds l in
          let rsyms,rconst = decompose_adds r in
          let syms = itlist (fun (lsym,lcoeff) rsyms ->
            if not (exists (fun (rsym,_) -> rsym=lsym) rsyms)
            then rsyms @ [lsym,lcoeff]
            else map (fun (rsym,rcoeff) ->
              if rsym = lsym then (lsym,lcoeff + rcoeff) else (rsym,rcoeff))
              rsyms) lsyms rsyms in
          (syms,lconst+rconst) with _ ->
        try (* note that num's subtraction is a bit complicated because
               num cannot be negative. However, there is a chance
               that even if the intermediate constants are negative the
               final subtracted result is non-negative. Let's hope a good
               luck and anticipate that SIMPLE_ARITH_TAC will solve it
               in the end. *)
          let l,r = dest_binary "-" t in
          let lsyms,lconst = decompose_adds l in
          let rsyms,rconst = decompose_adds r in
          let syms = itlist (fun (lsym,lcoeff) rsyms ->
            if not (exists (fun (rsym,_) -> rsym=lsym) rsyms)
            then rsyms @ [lsym,lcoeff]
            else map (fun (rsym,rcoeff) ->
              if rsym = lsym then (lsym,lcoeff - rcoeff) else (rsym,-rcoeff))
              rsyms) lsyms rsyms in
          (syms,lconst-rconst) with _ ->
        try let l,r = dest_binary "*" t in
          let lconst = dest_small_numeral l in
          let rsyms,rconst = decompose_adds r in
          (map (fun (sym,coeff) -> (sym,coeff * lconst)) rsyms,
           rconst * lconst)
        with _ -> ([t,1],0)
      in
      let syms1,const1 = decompose_adds t1 in
      let syms2,const2 = decompose_adds t2 in
      if syms1 = syms2 && const1 >= const2
      then Some (mk_small_numeral (const1 - const2))
      else None in

  let rec mk_word_add =
    let rec num_add expr (imm:int) =
      if is_numeral expr then
        mk_small_numeral(imm + dest_small_numeral expr)
      else if is_binary "+" expr then
        let l,r = dest_binary "+" expr in
        mk_binary "+" (l,num_add r imm)
      else mk_binary "+" (expr,mk_small_numeral imm) in
    let template = `word_add ptr (word ofs):int64` in
    (fun ptrofs imm ->
      if is_binary "word_add" ptrofs then
        let ptr,ofs = dest_binary "word_add" ptrofs in
        let ofs = mk_word_add ofs imm in
        mk_binop `word_add:int64->int64->int64` ptr ofs
      else if is_comb ptrofs && is_const (fst (dest_comb ptrofs)) &&
              name_of (fst (dest_comb ptrofs)) = "word" then
        let expr = snd (dest_comb ptrofs) in
        mk_comb(`word:num->int64`,num_add expr imm)
      else vsubst [ptrofs,`ptr:int64`;(mk_small_numeral imm),`ofs:num`] template) in
  let mk_read_mem_bytes64 =
    let template = ref None in
    (fun ptrofs state_var ->
      let temp = match !template with
        | None -> let t = `read (memory :> bytes64 ptrofs)` in
          (* The 'memory' constant must be parsable at this point. It is either armstate
              or x86state. *)
          (template := Some t; t)
        | Some t -> t in
      mk_comb(vsubst [ptrofs,`ptrofs:int64`] temp, state_var)) in
  let mk_word_join_128 =
    let wj = `word_join:int64->int64->int128` in
    (fun high low -> (mk_comb ((mk_comb (wj,high)),low))) in

  (* if ptrofs is word_add p (word_sub (word x) (word y)),
      return 'word_add p (word (x - y))' *)
  let canonicalize_word_add_sub ptrofs =
    if not (is_binary "word_add" ptrofs) then None else
    let w,the_rhs = dest_comb ptrofs in
    let the_wordadd,base = dest_comb w in
    if not (is_binary "word_sub" the_rhs) then None else
    let x,y = dest_binary "word_sub" the_rhs in
    if name_of (fst (dest_comb x)) <> "word" ||
       name_of (fst (dest_comb y)) <> "word" then None else
    let (the_word,x),y = dest_comb x,snd (dest_comb y) in
    Some (mk_binop the_wordadd base (mk_comb(the_word,mk_binary "-" (x,y)))) in

  fun (t:term) (assumptions:(string * thm) list): (thm * (thm list)) ->
    match get_full_info t with
    | Some (ptrofs,(ptr, ofs),size,constr_name,state_var) ->
      (* if ptrofs is word_add p (word_sub (word x) (word y)), try to make it
        'word_add p (word (x - y))' *)
      let canon_wordsub_rule = ref None in
      let ptr,ofs = match canonicalize_word_add_sub ptrofs with
      | None -> ptr,ofs
      | Some ptrofs' ->
        try
          let _ = canon_wordsub_rule := Some
            (TAC_PROOF((assumptions,mk_eq(ptrofs,ptrofs')),
              IMP_REWRITE_TAC[WORD_SUB2] THEN SIMPLE_ARITH_TAC)) in
          get_base_ptr_and_ofs ptrofs'
        with _ -> (ptr,ofs)
      in

      if not (is_multiple_of_8 ofs) then
        failwith ("offset is not divisible by 8: `" ^ (string_of_term ofs) ^ "`") else
      (if !equiv_print_log then
        Printf.printf "digitizing read %s: (`%s`,`%s`), sz=`%s`\n"
          constr_name (string_of_term ptr) (string_of_term ofs)
          (string_of_term size));
      let ofs_opt = const_num_opt ofs in

      if constr_name = "bytes64" then
        let _ = assert (size = eight) in
        let larger_reads = List.filter_map (fun (_,ath) ->
          try
            let c = concl ath in
            if not (is_eq c) then None else
            let c = lhs c in
            let c_access_info = get_full_info c in
            begin match c_access_info with
            | Some (ptrofs2,(ptr2,ofs2),size2,"bytes",state_var2) ->
              begin
              (if !equiv_print_log then
                Printf.printf "read bytes assum: (`%s`,`%s`), sz=`%s`\n"
                  (string_of_term ptr2) (string_of_term ofs2) (string_of_term size2));
              if (ptr = ptr2 && state_var = state_var2 &&

              begin match ofs_opt,(const_num_opt size2),(const_num_opt ofs2) with
              | Some ofs,Some size2,Some ofs2 ->
                (* everything is constant; easy to determine *)
                (* size must be `8` here *)
                ofs2 <= ofs && ofs + 8 <= ofs2 + size2
              | Some ofs,None,Some ofs2 ->
                (* offsets are constant! *)
                (* size must be `8` here *)
                not (ofs + 8 <= ofs2)
              | _ -> true
              end) then
                Some (ath,Option.get c_access_info)
              else None
              end
            | _ -> None
            end
          with _ ->
            let _ = Printf.printf "Warning: MK_MEMORY_READ_EQ_BIGDIGIT_CONV: unexpected failure: `%s`\n" (string_of_term (concl ath))in
            None) assumptions in
        if larger_reads = []
        then failwith ("No memory read assumption that encompasses `" ^ (string_of_term t) ^ "`") else
        (if !equiv_print_log then (
          Printf.printf "MK_MEMORY_READ_EQ_BIGDIGIT_CONV: found:\n";
          List.iter (fun th,_ -> Printf.printf "  `%s`\n" (string_of_term (concl th))) larger_reads));

        let extracted_reads = List.filter_map
          (fun larger_read_th,(ptrofs2,(ptr2,ofs2),size2,_,_) ->
          try
            let larger_read = lhs (concl larger_read_th) in
            if not (is_multiple_of_8 ofs2) then
              let _ = if !equiv_print_log then
                Printf.printf "not multiple of 8: `%s`\n"
                  (string_of_term ofs2) in None else

            let ofsdiff = subtract_num ofs ofs2 in
            let reldigitofs = Option.bind ofsdiff divide_by_8 in
            let nwords = divide_by_8 size2 in

            begin match reldigitofs, nwords with
            | Some reldigitofs, Some nwords ->

              (* t = bigdigit t' ofs *)
              let the_goal = mk_eq(t,mk_comb
                (`word:num->int64`,list_mk_comb (`bigdigit`,[larger_read;reldigitofs]))) in
              begin try

                let eq_th = TAC_PROOF((assumptions,the_goal),
                  (* If t was 'word_add ptr (word_sub ...)', convert it into
                    'word_add (word (.. - ..))'. *)
                  (match !canon_wordsub_rule with | None -> ALL_TAC
                    | Some th -> REWRITE_TAC[th]) THEN
                  SUBGOAL_THEN (subst [size2,`size2:num`;nwords,`nwords:num`] `8 * nwords = size2`) MP_TAC
                  THENL [ ARITH_TAC; DISCH_THEN (LABEL_TAC "H_NWORDS") ] THEN
                  USE_THEN "H_NWORDS" (fun hth -> REWRITE_TAC[REWRITE_RULE[hth]
                    (SPECL [nwords;ptrofs2] (GSYM BIGNUM_FROM_MEMORY_BYTES))]) THEN
                  REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
                  COND_CASES_TAC THENL [ALL_TAC; SIMPLE_ARITH_TAC (* index must be within bounds *) ] THEN
                  (* read (memory :> bytes64 (expr1)) s =
                     read (memory :> bytes64 (expr2)) s *)
                  REWRITE_TAC[WORD_VAL; WORD_ADD_ASSOC_CONSTS; WORD_ADD_0;
                      MULT_0; LEFT_SUB_DISTRIB; LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
                  (* get the 'expr1 = expr2' *)
                  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC
                  THEN
                  (SIMPLE_ARITH_TAC ORELSE
                    (* strip word_add *)
                    (AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC))) in
                Some (REWRITE_RULE[larger_read_th] eq_th,[])
              with _ ->
                (if !equiv_print_log then
                  Printf.printf "Could not prove `%s`\n" (string_of_term the_goal)); None
              end
            | _, _ -> begin
              (if !equiv_print_log then
              Printf.printf "cannot simplify offset difference or nwords; (`%s`-`%s`)/8, `%s`/8\n"
                (string_of_term ofs) (string_of_term ofs2) (string_of_term size2));
              None
            end
            end
          with _ -> begin
            Printf.printf "Warning: MK_MEMORY_READ_EQ_BIGDIGIT_CONV: failed while processing `%s`\n" (string_of_term (concl larger_read_th)); None
          end) larger_reads in

        let _ = if length extracted_reads > 1 then
          Printf.printf "Warning: There are more than one memory read assumption that encompasses `%s`\n"
              (string_of_term t) in
        (if !equiv_print_log then begin
          Printf.printf "MK_MEMORY_READ_EQ_BIGDIGIT_CONV: extracted:\n";
          List.iter (fun th,_ ->
            Printf.printf "  `%s`\n" (string_of_term (concl th))) extracted_reads
        end);
        List.hd extracted_reads

      else if constr_name = "bytes128" then
        (* bytes128 to word_join of two bytes64 reads *)
        let readl = mk_read_mem_bytes64 ptrofs state_var in
        let readh = mk_read_mem_bytes64 (mk_word_add ptrofs 8) state_var in
        let construct_bigdigit_rule t =
          match List.find_opt (fun _,asm -> let c = concl asm in is_eq c && lhs c = t) assumptions with
          | None -> MK_MEMORY_READ_EQ_BIGDIGIT_CONV t assumptions
          | Some (_,ath) -> (ath,[]) in
        let readl_th,extra_ths1 = construct_bigdigit_rule readl in
        let readh_th,extra_ths2 = construct_bigdigit_rule readh in
        (* word_join readh_th readl_th *)
        let the_goal =
          let readl = rhs (concl readl_th) and readh = rhs (concl readh_th) in
          mk_eq (t,mk_word_join_128 readh readl) in
        let result =
          let new_assums = readl_th::readh_th::(extra_ths1 @ extra_ths2) in
          TAC_PROOF((map (fun th -> ("",th)) new_assums,the_goal),
            REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
            REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
            REWRITE_TAC[GSYM ADD_ASSOC] THEN
            RULE_ASSUM_TAC (REWRITE_RULE[GSYM ADD_ASSOC]) THEN
            RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV NUM_ADD_CONV)) THEN
            CONV_TAC (DEPTH_CONV NUM_ADD_CONV) THEN
            ASM_REWRITE_TAC[] THEN
            (if !equiv_print_log then
              (PRINT_TAC "could not synthesize bytes128 from join(bytes64,bytes64)" THEN
               PRINT_GOAL_TAC) else ALL_TAC)
            THEN
            FAIL_TAC "could not synthesize bytes128 from join(bytes64,bytes64)") in
        (* Eliminate the assumptions that are readl_th and readh_th, and put assumptions
           that readl_th and readh_th were relying on. *)
        let result = PROVE_HYP readh_th (PROVE_HYP readl_th result) in
        (result, readl_th::readh_th::(extra_ths1 @ extra_ths2))

      else failwith ("cannot deal with size `" ^ (string_of_term size) ^ "`")
    | None -> failwith "not memory read";;

(*** examples ***)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 x) s`
    ["",mk_fthm([], `read (memory :> bytes (x:int64,32)) s = k`)];;
(* (_FALSITY_ |- read (memory :> bytes64 x) s = word (bigdigit k 0), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word 16))) s`
    ["",mk_fthm([], `read (memory :> bytes (word_add x (word 8):int64,32)) s = k`)];;
(* (_FALSITY_ |- read (memory :> bytes64 (word_add x (word 16))) s = word (bigdigit k 1), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word 16))) s`
    ["",mk_fthm([], `read (memory :> bytes (word_add x (word 8):int64,8 * 4)) s = k`)];;
(* (_FALSITY_ |- read (memory :> bytes64 (word_add x (word 16))) s = word (bigdigit k 1), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word 16))) s`
    ["",mk_fthm([], `read (memory :> bytes (word_add x (word 8):int64,8 * n)) s = k`);
     "",mk_fthm([], `n > 3`)];;
(* (_FALSITY_ |- read (memory :> bytes64 (word_add x (word 16))) s = word (bigdigit k 1), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word (8 * 2)))) s`
    ["",mk_fthm([], `read (memory :> bytes (word_add x (word (8 * 1)):int64,8 * n)) s = k`);
     "",mk_fthm([], `n > 3`)];;
(* (_FALSITY_ |- read (memory :> bytes64 (word_add x (word (8 * 2)))) s = word (bigdigit k 1), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word (8 * 2)))) s`
    ["",mk_fthm([], `read (memory :> bytes (x:int64,8 * 2)) s = k`);
     "",mk_fthm([], `read (memory :> bytes (word_add x (word (8 * 2)):int64,8 * n)) s = k2`);
     "",mk_fthm([], `read (memory :> bytes (word_add x (word (8 * 4)):int64,8 * n)) s = k2`);
     "",mk_fthm([], `n > 3`)];;
(* (_FALSITY_ |- read (memory :> bytes64 (word_add x (word (8 * 2)))) s = word (bigdigit k2 0), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word (8 * i)))) s`
    ["",mk_fthm ([],`read (memory :> bytes (x:int64,8 * n)) s = k`);
     "",mk_fthm ([],`i < n`)];;
(* (_FALSITY_ |- read (memory :> bytes64 (word_add x (word (8 * i)))) s =
    word (bigdigit k i),
 []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV
    `read (memory :> bytes64 (word_add z (word (8 * (4 * k4 - 4) + 24)))) s`
    ["",mk_fthm([], `read (memory :> bytes (word_add z (word (8 * (4 * k4 - 4))),8 * 4)) s = a`);
     "",mk_fthm([], `read (memory :> bytes (z,8 * (4 * k4 - 4))) s = b`)];;
(* (_FALSITY_ |- read (memory :> bytes64 (word_add z (word (8 * (4 * k4 - 4) + 24)))) s =
    word (bigdigit a 3),
 []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV
    `read (memory :> bytes64
      (word_add m_precalc (word_sub (word (8 * 12 * (k4 - 1))) (word 8))))
     s`
    ["",mk_fthm([],`read (memory :> bytes (m_precalc,8 * 12 * (k4 - 1))) s = k`);
     "",mk_fthm([],`1 < k4`)];;
(* (_FALSITY_
 |- read
    (memory :>
     bytes64
     (word_add m_precalc (word_sub (word (8 * 12 * (k4 - 1))) (word 8))))
    s =
    word (bigdigit k (12 * (k4 - 1) - 1)),
 [])
*)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV
  `read (memory :> bytes64 (word_add z (word (8 * 4 * (i' + 1) + 24)))) s`
  ["", mk_fthm([],`read (memory :> bytes (word_add z (word (8 * 4 * (i' + 1))),32)) s =
     a`)];;
(* (_FALSITY_
 |- read (memory :> bytes64 (word_add z (word (8 * 4 * (i' + 1) + 24)))) s =
    word (bigdigit a 3),
 [])
*)

(** bytes128 **)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes128 (word_add x (word (8 * 2)))) s`
    ["",mk_fthm ([],`read (memory :> bytes (x:int64,8 * 2)) s = k`);
     "",mk_fthm ([],`read (memory :> bytes (word_add x (word (8 * 2)):int64,8 * n)) s = k2`);
     "",mk_fthm ([],`read (memory :> bytes (word_add x (word (8 * 4)):int64,8 * n)) s = k2`);
     "",mk_fthm ([],`n > 3`)];;
(* (_FALSITY_
 |- read (memory :> bytes128 (word_add x (word (8 * 2)))) s =
    word_join (word (bigdigit k2 1)) (word (bigdigit k2 0)),
 [_FALSITY_
  |- read (memory :> bytes64 (word_add x (word (8 * 2)))) s =
     word (bigdigit k2 0);
  _FALSITY_
  |- read (memory :> bytes64 (word_add x (word (8 * 2 + 8)))) s =
     word (bigdigit k2 1)])
*)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes128 (word_add m (word ((8 * 4 * i + 32) + 16)))) s`
    ["",mk_fthm ([],`read (memory :> bytes64 (word_add m (word ((8 * 4 * i + 32) + 24))))
      s =
      k1`);
     "",mk_fthm ([],`read (memory :> bytes64 (word_add m (word ((8 * 4 * i + 32) + 16))))
      s =
      k2`)];;
(* (_FALSITY_
 |- read (memory :> bytes128 (word_add m (word ((8 * 4 * i + 32) + 16)))) s =
    word_join k1 k2,
 [_FALSITY_
  |- read (memory :> bytes64 (word_add m (word ((8 * 4 * i + 32) + 16)))) s =
     k2;
  _FALSITY_
  |- read (memory :> bytes64 (word_add m (word ((8 * 4 * i + 32) + 24)))) s =
     k1]) *)

(** DIGITIZE_MEMORY_READS will return (thm * (thm option)) where
    1. the first thm is the simplified read statements using bigdigit and
       conjoined with /\
    2. newly constructed equalities between memory reads and bigdigits, returned
       as the second component of MK_MEMORY_READ_EQ_BIGDIGIT_CONV, and conjoined
       with /\. **)
let DIGITIZE_MEMORY_READS th state_update_th =
  fun (asl,w):(thm * (thm option)) ->
    let new_memory_reads: thm list ref = ref [] in
    let ths = map (fun th2 ->
      try
        (* rhs is the memory read to digitize *)
        let the_rhs = rhs (concl th2) in
        let th2',smaller_read_ths = MK_MEMORY_READ_EQ_BIGDIGIT_CONV the_rhs asl in
        let _ = new_memory_reads := th2'::(smaller_read_ths @ !new_memory_reads) in
        GEN_REWRITE_RULE RAND_CONV [th2'] th2
      with _ -> th2) (CONJUNCTS th) in

    (* new_memory_reads will still use the 'previous' state. update it. *)
    new_memory_reads := map
      (fun th -> try STATE_UPDATE_RULE state_update_th th with _ -> th)
      !new_memory_reads;

    let res_th = end_itlist CONJ ths in
    let newmems_th = if !new_memory_reads = [] then None
      else Some (end_itlist CONJ !new_memory_reads) in
    let _ = if !equiv_print_log then
       (Printf.printf "original th: %s\n" (string_of_term (concl th));
        Printf.printf "rewritten th: %s\n" (string_of_term (concl res_th));
        Printf.printf "new_memory_reads th: %s\n"
          (if newmems_th = None then "None" else
            ("Some " ^ (string_of_term (concl (Option.get newmems_th)))))) in
    res_th,newmems_th;;


(* ------------------------------------------------------------------------- *)
(* Manipulates assumptions.                                                  *)
(* ------------------------------------------------------------------------- *)

(* A variant of DISCARD_OLDSTATE_TAC which receives a list of state names
   to preserve, 'ss'.
   If clean_old_abbrevs is true, transitively remove assumptions that
   were using the removed variables (rhs of the removed assumptions) *)
let DISCARD_OLDSTATE_AGGRESSIVELY_TAC ss (clean_old_abbrevs:bool) =
  let rec unbound_statevars_of_read bound_svars tm =
    match tm with
      Comb(Comb(Const("read",_),cmp),s) ->
      let sname = name_of s in
      if mem sname bound_svars then [] else [sname]
    | Comb(a,b) -> union (unbound_statevars_of_read bound_svars a)
                         (unbound_statevars_of_read bound_svars b)
    | Abs(v,t) ->
      let vname = name_of v in
      unbound_statevars_of_read (vname::bound_svars) t
    | _ -> [] in
  let is_read (tm:term): bool =
    match tm with
    Comb(Comb(Const("read",_),_),_) -> true
    | _ -> false in
  let old_abbrevs: term list ref = ref [] in
  (* Erase all 'read c s' equations from assumptions whose s does not
     belong to ss. *)
  DISCARD_ASSUMPTIONS_TAC(
    fun thm ->
      let us = unbound_statevars_of_read [] (concl thm) in
      if us = [] || subset us ss then false
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

(* Assumption stash/recovery tactic. *)
let stashed_asms: (string * thm) list list ref = ref [];;

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
  | Comb (Comb (Comb
    (Const ("bytes_loaded",_), Var (stname, _)),_),_) ->
    store_state_name := stname; true
  | _ ->
    maychange_term c &&
      (let s' = snd (dest_comb c) in is_var s' &&
        (store_state_name := name_of s'; true));;

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

(* Given readth,readth2 = (`|- read c s = e1`, `|- read c' s' = e2`),
   prove e1 = e2 using WORD_RULE, abbreviate e1 and e2 as a
   fresh variable, and assume the abbreviated readth and readth2 as well as
   `e1 = freshvar` (if forget_expr is false).
   If forget_expr is set, do not add 'e1 = abbrev_var' as an assumption.
   Note that forget_expr is rarely false; it is false in special cases
   like when `c` is the SP register.
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
      let _,rhs2 = dest_eq eq2 in
      (* If lhs is PC update, don't abbrevate it. Or, if rhs is already a
        variable, don't abbreviate it again. Don't try to prove the rhs of
        eq2. *)
      if is_read_pc lhs || is_read_events lhs || is_var rhs
      then MAP_EVERY STRIP_ASSUME_TAC [readth;readth2]
      else
        let vname = mk_fresh_temp_name() in
        let _ = if !equiv_print_log then
          Printf.printf "Abbreviating `%s` (which is `%s`) as \"%s\".. (forget_expr: %b)\n"
            (string_of_term rhs) (string_of_term lhs) vname forget_expr
          in

        let readth2 =
          (if rhs2 = rhs then readth2 else
          try
            let r = WORD_RULE (mk_eq(rhs2,rhs)) in
            let _ = if !equiv_print_log then
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

let get_read_component (targ:term): term option =
  let targ = if is_eq targ then lhand targ else targ in
  match targ with
  | Comb(Comb(Const("read",_),comp),_) -> Some comp
  | _ -> None;;

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
    if is_read_pc lhs || is_read_events lhs then ASSUME_TAC eqth
    else
      if get_read_component lhs = None then failwith "LHS is not read ..?" else
      let vname = mk_fresh_temp_name() in
      if !equiv_print_log then begin
        Printf.printf "Abbreviating `%s` (which is `%s`) as \"%s\"..\n"
            (string_of_term rhs) (string_of_term lhs) vname
      end;

      let fresh_var = mk_var (vname,type_of rhs) in
      let abbrev_th = prove(mk_exists(fresh_var,mk_eq(rhs,fresh_var)),
        EXISTS_TAC rhs THEN REFL_TAC) in
      CHOOSE_THEN (fun abbrev_th ->
        ASSUME_TAC (REWRITE_RULE[abbrev_th] eqth) THEN
        (fun (asl,g) ->
          append_to := abbrev_th::!append_to;
          ALL_TAC(asl,g))) abbrev_th);;


(* Clear unused abbreviations in assumptions.
   Do not clear it if its name ends with "DO_NOT_CLEAR". *)
let CLEAR_UNUSED_ABBREVS =
  fun (asl,w) ->
    (* asl_with_flags: (keep it?, (abbrev var, asm name, th)) array *)
    let asl_with_flags = ref (Array.of_list (map
      (fun (asmname,th) -> true, (None, asmname, th)) asl)) in

    (* From assumptions, find those that abbreviates to the_var *)
    let find_indices (the_var:term): int list =
      let res = ref [] in
      for i = 0 to Array.length !asl_with_flags - 1 do
        let _,(abbrev_var,_,_) = !asl_with_flags.(i) in
        if abbrev_var = Some the_var then
          res := i::!res
      done;
      !res in

    (* do BFS to mark assumptions that must not be cleared *)
    let alive_queue = ref [] in
    for i = 0 to Array.length !asl_with_flags - 1 do
      let _,(_,asmname,th) = !asl_with_flags.(i) in
      let dummy_ref = ref "" in
      if reads_state (concl th) dummy_ref then
        (* assumptions that read states should not be removed *)
        alive_queue := i::!alive_queue
      else if is_eq (concl th) && is_var (rand (concl th)) &&
              not (String.ends_with ~suffix:"DO_NOT_CLEAR" asmname) then
        (* if th is 'e = var', mark it as initially dead & extract rhs var *)
        !asl_with_flags.(i) <- (false, (Some (rand (concl th)), asmname, th))
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


(* ------------------------------------------------------------------------- *)
(* Tactics that do not perform symbolic execution but are necessary to       *)
(* initiate/finalize program equivalence proofs.                             *)
(* ------------------------------------------------------------------------- *)

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

let READ_OVER_WRITE_MEMORY_BYTELIST =
  prove(`!s (loc:int64) (l:((8)word)list).
      LENGTH l < 2 EXP 64
      ==> read (memory :> bytelist (loc,LENGTH l))
        (write (memory :> bytelist (loc,LENGTH l)) l s) = l`,
  let read_write_mem_th =
    ISPECL [`memory`] READ_WRITE_VALID_COMPONENT in
  REWRITE_TAC[component_compose] THEN
  REWRITE_TAC[read;write;o_THM] THEN
  IMP_REWRITE_TAC([read_write_mem_th] @ (!valid_component_thms)) THEN
  REWRITE_TAC[READ_OVER_WRITE_BYTELIST]);;

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

let READ_OVER_WRITE_MEMORY_APPEND_BYTELIST =
  prove(`!s (loc:int64) (l:((8)word)list) (l':((8)word)list).
      LENGTH (APPEND l l') < 2 EXP 64
      ==> read (memory :> bytelist (loc,LENGTH l))
        (write (memory :> bytelist (loc,LENGTH (APPEND l l'))) (APPEND l l') s) = l`,
  let read_write_mem_th =
    ISPECL [`memory`] READ_WRITE_VALID_COMPONENT in
  REWRITE_TAC[component_compose] THEN
  REWRITE_TAC[read;write;o_THM] THEN
  IMP_REWRITE_TAC([read_write_mem_th] @ (!valid_component_thms)) THEN
  REWRITE_TAC[READ_OVER_WRITE_APPEND_BYTELIST]);;


let prove_conj_of_eq_reads_unfold_rules = ref [bytes_loaded];;

(* An ad-hoc tactic for proving a goal
    `read c1 s = .. /\ read c2 s = .. /\ ...`. This also accepts
   a clause which is a predicate 'aligned_bytes_loaded'.
   Clauses which cannot not be proven with this tactic will remain as a goal. *)
let PROVE_CONJ_OF_EQ_READS_TAC execth =
  (* Given a goal `read c (updated state) = e`, EXPAND_RHS_TAC tries to find assumption
     `e' = e`. If there are multiple such assumptions. find
     `read c' s' = e` such that the 'root' state of updated state is s', and
     and expands e as follows: `read c (updated state) = read c' s'`.
     If e is a variable and there is `e' = e`, just use this regardless of s'. *)
  let EXPAND_RHS_TAC: tactic =
    (* t must be always `read ...` or a state variable *)
    let rec get_root_state t =
      if is_comb t then get_root_state (snd (dest_comb t))
      else if is_var t then t
      else failwith ("get_root_state: unknown form: " ^ (string_of_term t)) in
    fun (asl,w) ->
      let rhs_expr = rhs w in
      let eqths = filter (fun _,th -> let c = concl th in
        is_eq c && rhs c = rhs_expr) asl in
      match eqths with
      | [] -> failwith "PROVE_CONJ_OF_EQ_READS_TAC"
      | (_,eqth)::[] ->       GEN_REWRITE_TAC RAND_CONV [GSYM eqth] (asl,w)
      | eqths ->
        let state = get_root_state (lhs w) in
        let _,eqth = find (fun _,th -> let c = concl th in
          let the_lhs = lhs c in snd (dest_comb the_lhs) = state) eqths in
        GEN_REWRITE_TAC RAND_CONV [GSYM eqth] (asl,w) in

  REPEAT CONJ_TAC THEN
  let main_tac =
    (* for register updates *)
    (REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN
      (REFL_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC))) ORELSE
    (* for register updates, with rhses abbreviated *)
    (EXPAND_RHS_TAC THEN REPEAT COMPONENT_READ_OVER_WRITE_LHS_TAC THEN REFL_TAC)
    ORELSE
    (* for memory updates *)
    (ASM_REWRITE_TAC(!prove_conj_of_eq_reads_unfold_rules) THEN
      (EXPAND_RHS_TAC THEN
       ((REWRITE_TAC([LENGTH_APPEND;fst execth;
                     PAIR_EQ;BIGNUM_FROM_MEMORY_BYTES] @
                     !prove_conj_of_eq_reads_unfold_rules) THEN
         REPEAT CONJ_TAC THEN READ_OVER_WRITE_ORTHOGONAL_TAC) ORELSE
        (* sometimes the rewrites are not necessary.. *)
        READ_OVER_WRITE_ORTHOGONAL_TAC))
      (* sometimes EXPAND_RHS_TAC is not necessary.. *)
      ORELSE
        (REWRITE_TAC([LENGTH_APPEND;fst execth;
                     PAIR_EQ;BIGNUM_FROM_MEMORY_BYTES] @
                     !prove_conj_of_eq_reads_unfold_rules) THEN
        REPEAT CONJ_TAC THEN READ_OVER_WRITE_ORTHOGONAL_TAC)) ORELSE
    (* for aligned_bytes_loaded *)
    (ASM_REWRITE_TAC(!prove_conj_of_eq_reads_unfold_rules) THEN
      (MATCH_MP_TAC READ_OVER_WRITE_MEMORY_APPEND_BYTELIST ORELSE
      MATCH_MP_TAC READ_OVER_WRITE_MEMORY_BYTELIST) THEN
      REWRITE_TAC([LENGTH_APPEND;fst execth] @ !prove_conj_of_eq_reads_unfold_rules) THEN
      ARITH_TAC) in
  TRY (main_tac ORELSE (MATCH_MP_TAC EQ_SYM THEN main_tac));;
