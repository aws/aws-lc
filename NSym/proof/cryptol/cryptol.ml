(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: Apache-2.0 *)

(* Interface library for Cryptol *)
(* This is a shallow embedding of a subset of Cryptol in Ocaml+Air *)

module A = Air
module C = Specs.Common
type airExp = A.airExp

let undefined = fun () -> failwith "undefined"
let raise err = failwith ("Error: " ^ err)

(** {0. Type Symbols} *)
type cryType = 
  | Integer | Bit | Seq of string * cryType
  | Array of cryType * cryType | Inf;;

let seq (s : string) (k : cryType) = Seq(s,k)
let array (k : cryType) (v : cryType) = Array(k, v)

(** {1. Types} *)
type cryBool = bool

type cryExp = 
| CrySeq of (cryExp list)
| CryMem of airExp
| CryInt of airExp
| CryBV of airExp
| CryBool of airExp

(** {2. Numbers} *)

(** Assumption: v chould be represented in 32 bits. *)
let number (v : string) (t : cryType) : cryExp =
  match t with
  | Integer -> CryInt(A.ci (int_of_string v))
  | Seq(n, Bit) -> CryBV(A.z_cb (int_of_string n) (Z.of_string v))
  | _ -> raise ("Invalid Cryptol number " ^ v)

(** {3. Sequence Primitives} *)

let mkZero1Dim (k : cryType) (len : int) : cryExp = 
  match k with
  | Bit -> CryBV(A.cb len 0)
  | _ -> raise "Could not make one dimentional zero"

let mkZero2Dim (k : cryType) (row : int) (col : int) : cryExp = 
  match k with
  | Bit -> CrySeq(List.init row (fun _ -> (mkZero1Dim k col)))
  | _ -> raise "Could not make two dimentional zero"

let zero (k : cryType) : cryExp =
  match k with
  | Seq(w, Bit) -> mkZero1Dim Bit (int_of_string w)
  | Seq(row, Seq(col, Bit)) -> mkZero2Dim Bit (int_of_string row) (int_of_string col)
  | _ -> raise "Could not make zero"

let bvnot (k : cryType) (x : cryExp) : cryExp =
  match (k, x) with
  | (Seq(w, Bit), CryBV xb) ->
    CryBV(A.bvnot (int_of_string w) xb)
  | _ -> raise "Currently only bvnot of bit-vectors are supported"

let bvxor (k : cryType) (x : cryExp) (y: cryExp) : cryExp =
  match (k, x, y) with
  | (Seq(w, Bit), CryBV xb, CryBV yb) ->
     CryBV(A.bvxor (int_of_string w) xb yb)
  | _ -> raise "Currently only bvxor of bit-vectors are supported"

let bvand (k : cryType) (x : cryExp) (y : cryExp) : cryExp =
  match (k, x, y) with
  | (Seq(w, Bit), CryBV xb, CryBV yb) ->
    CryBV(A.bvand (int_of_string w) xb yb)
  | _ -> raise "Currently only bvand of bit-vectors are supported"

let bvror (_ : string) (t1 : cryType) (t2 : cryType) (x : cryExp) (i : cryExp)
      : cryExp =
  match (t1, t2, x, i) with
  | (Integer, Bit, CryBV xb, CryInt ii) when (A.is_ci ii) ->
    let j = (Z.to_int (A.get_ci_val ii)) in CryBV(A.bvror j xb)
  | _ -> raise "Currently only bvror of bit-vectors are supported"

let bvrsh (w : string) (t1 : cryType) (t2 : cryType) (x : cryExp) (i : cryExp)
       : cryExp =
  match (t1, t2, x, i) with
  | (Integer, Bit, CryBV xb, CryInt ii) when (A.is_ci ii) ->
    CryBV(A.bvrsh (int_of_string w) xb (A.int_to_bv 32 ii))
  | _ -> raise "Currently only bvrsh of bit-vectors are supported"

let add (k : cryType) (x : cryExp) (y : cryExp) : cryExp =
  match (k, x, y) with
  | (Seq(_, Seq(w, Bit)), CrySeq(xl), CrySeq(yl)) ->
    let tup = List.combine xl yl in
    let fn = fun (x, y) -> 
      match (x, y) with 
      | (CryBV xb, CryBV yb) -> CryBV(A.bvadd (int_of_string w) xb yb)
      | _ -> raise "Malformed two-dimentional sequence" in
    let res = List.map fn tup in 
    CrySeq(res)
  | (Seq(w, Bit), CryBV xb, CryBV yb) ->
    CryBV(A.bvadd (int_of_string w) xb yb)
  | (Integer, CryInt(xi), CryInt(yi)) ->
    CryInt(A.z_ci(Z.add (A.get_ci_val xi) (A.get_ci_val yi)))
  | _ -> raise "Currently only add of two-dimentional sequences, bit-vectors and integers are supported"

let sub (k : cryType) (x : cryExp) (y : cryExp) : cryExp = 
  match (k, x, y) with
  | (Seq(w, Bit), CryBV xb, CryBV yb) ->
    CryBV(A.bvsub (int_of_string w) xb yb)
  | (Integer, CryInt(xi), CryInt(yi)) ->
    CryInt(A.z_ci(Z.sub (A.get_ci_val xi) (A.get_ci_val yi)))
  | _ -> raise "Currently only sub of bit-vectors and integers are supported"

let mul (k : cryType) (x : cryExp) (y : cryExp) : cryExp = 
  match (k, x, y) with
  | (Seq(w, Bit), CryBV xb, CryBV yb) ->
    CryBV(A.bvmul (int_of_string w) xb yb)
  | (Integer, CryInt(xi), CryInt(yi)) ->
    CryInt(A.z_ci(Z.mul (A.get_ci_val xi) (A.get_ci_val yi)))
  | _ -> raise "Currently only mul of bit-vectors and integers are supported"

let div (k : cryType) (x : cryExp) (y : cryExp) : cryExp = 
  match (k, x, y) with
  | (Integer, CryInt(xi), CryInt(yi)) ->
    CryInt(A.z_ci(Z.div (A.get_ci_val xi) (A.get_ci_val yi)))
  | _ -> raise "Currently only div of integers are supported"

let inc (w : string) (e : cryExp) : cryExp = 
  add (seq w Bit) e (CryBV(A.s_cb (int_of_string w) "0x1"))

let dec (w : string) (e : cryExp) : cryExp = 
  sub (seq w Bit) e (CryBV(A.s_cb (int_of_string w) "0x1"))

let update (_w : string) (ek : cryType) (ik : cryType) (l : cryExp) (i : cryExp) (v : cryExp) 
  : cryExp =
  match (ek, ik, l, i) with
  | (Seq(_, Bit), Integer, CrySeq(lb), CryInt ii) -> 
    let id = Z.to_int (A.get_ci_val ii) in
    CrySeq(List.mapi (fun i x -> if i == id then v else x) lb)
  | _ -> raise "Currently only update of sequence of bit-vectors are supported"

let at (_w : string) (ek : cryType) (ik : cryType) (l : cryExp) (i : cryExp) : cryExp =
  match (ek, ik, l, i) with
  | (Seq(_, Bit), Integer, CrySeq(lb), CryInt ii) -> 
    List.nth lb (Z.to_int (A.get_ci_val ii))
  | _ -> raise "Currently only at of sequence of bit-vectors are supported"

(* The following definition respects Cryptol sematics. *)
let join (_parts : string) (_each : string) (k : cryType) (v : cryExp) : cryExp = 
  let rec joinHelper (_parts : string) (_each : string) (lb : cryExp list) : airExp = 
    match lb with
    | [] -> raise "Could not join an empty list of cryExps"
    | x :: [] -> (match x with
               | CryBV(bv) -> bv
               | _ -> raise "Element to join must be a bit-vector")
    | x :: xs -> match x with
              | CryBV(bv) -> A.bvapp bv (joinHelper _parts _each xs)
              | _ -> raise "Elements to join must be a bit-vector"
  in
  match (k, v) with
  | (Bit, CrySeq(lb)) -> CryBV(joinHelper _parts _each (List.rev lb))
  | _ -> raise "Currently only join of sequence of bit-vectors are supported"  

(* The following definition respects Cryptol sematics. *)
let split (parts : string) (each : string) (k : cryType) (v : cryExp) : cryExp = 
  let rec splitHelper (parts : int) (each : int) (v : airExp) (ind : int) (acc : cryExp list)
    : cryExp list = 
    if ind < parts * each - 1
    then (splitHelper parts each v (ind + each) (CryBV(A.bv_partsel v ind each) :: acc))
    else acc
  in
  match (k, v) with
  | (Bit, CryBV(bv)) -> CrySeq(splitHelper (int_of_string parts) (int_of_string each) bv 0 [])
  | _ -> raise "Currently only split of bit-vectors are supported"

(* The following definition respects Cryptol sematics. *)
let take (front : string) (back : string) (_elt : cryType) (s : cryExp) : cryExp = 
  let rec take_aux (n : int) (s : cryExp list) (acc : cryExp list) : cryExp list = 
    if n = 0
    then acc 
    else (match s with 
          | hd::tl -> take_aux (n-1) tl (hd::acc)
          | _ -> raise "Taking elements from empty sequence") in
  match s with
  | CrySeq(sl) -> CrySeq(List.rev (take_aux (int_of_string front) sl []))
  | CryBV(bv) -> CryBV(A.bv_partsel bv (int_of_string back) (int_of_string front))
  | _ -> raise "Taking elements from a non sequence nor bit-vector"

let fromTo (start : string) (finish : string) (elt : cryType) : cryExp = 
  let rec fromToHelper (start : cryExp) (finish : cryExp) (elt : cryType) (acc : cryExp) 
    : cryExp = 
    match (elt, acc) with
    | (Seq(w, Bit), CrySeq(s)) -> 
      (if start = finish
       then (CrySeq(finish :: s))
       else fromToHelper start (dec w finish) elt (CrySeq(finish :: s)))
    | _ -> raise "Malformed fromTo" in
  (if (int_of_string start) <= (int_of_string finish)
   then fromToHelper (number start elt) (number finish elt) elt (CrySeq([]))
   else raise "`start` of fromTo needs to be smaller than or equal to `finish`")

let seqSel (bv : cryExp) (i : int) : cryExp = 
  match bv with
  | CrySeq(lb) -> List.nth lb i
  | _ -> raise "Input to seqSel must be a sequence"

(** {4. Comparison Primitives } *)
(* Note: Nsym specification now uses two kinds of if statement.
   `Air.ite` only handles return types of `airExp`. For higher-dimentional bit-vectors,
   for example, `airExp list`, we will need to use Ocaml `if` instead of `Air.ite`. 
   The Ocaml function `if` and `Air.ite` requires different input type for the condition.
   To solve this problem, we define two sets of comparison functions with different type
   signatures. They should be used in Ocaml `if` and `Air.ite` respectively. *)

let lt (k : cryType) (x : cryExp) (y : cryExp) : cryBool = 
  match (k, x, y) with
  | (Integer, CryInt(xi), CryInt(yi)) -> 
    Z.lt (A.get_ci_val xi) (A.get_ci_val yi)
  | (Seq(w, Bit), CryBV(xb), CryBV(yb)) ->
    let res = (A.bvlt (int_of_string w) xb yb) in
    (assert (A.is_ct res); A.get_ct_val res)
  | _ -> raise "Currently only lt of integers and bit-vectors are supported"

let leq (k : cryType) (x : cryExp) (y : cryExp) : cryBool = 
  match (k, x, y) with
  | (Integer, CryInt(xi), CryInt(yi)) -> 
    Z.leq (A.get_ci_val xi) (A.get_ci_val yi)
  | (Seq(w, Bit), CryBV(xb), CryBV(yb)) ->
    let res = (A.bvle (int_of_string w) xb yb) in
    (assert (A.is_ct res); A.get_ct_val res)
  | _ -> raise "Currently only leq of integers and bit-vectors are supported"  

let geq (k : cryType) (x : cryExp) (y : cryExp) : cryBool = 
  match (k, x, y) with
  | (Integer, CryInt(xi), CryInt(yi)) -> 
    Z.geq (A.get_ci_val xi) (A.get_ci_val yi)
  | (Seq(w, Bit), CryBV(xb), CryBV(yb)) ->
    let res = (A.bvge (int_of_string w) xb yb) in
    (assert (A.is_ct res); A.get_ct_val  res)
  | _ -> raise "Currently only geq of integers and bit-vectors are supported"

let gt (k : cryType) (x : cryExp) (y : cryExp) : cryBool = 
  match (k, x, y) with
  | (Integer, CryInt(xi), CryInt(yi)) -> 
    Z.gt (A.get_ci_val xi) (A.get_ci_val yi)
  | (Seq(w, Bit), CryBV(xb), CryBV(yb)) ->
    let res = (A.bvgt (int_of_string w) xb yb) in
    (assert (A.is_ct res); A.get_ct_val res)
  | _ -> raise "Currently only gt of integers and bit-vectors are supported"

let eqAir (k : cryType) (x : cryExp) (y : cryExp) : cryExp = 
  match (k, x, y) with
  | (Integer, CryInt(xi), CryInt(yi)) -> 
    CryBool(A.int_equal xi yi)
  | (Seq(w, Bit), CryBV(xb), CryBV(yb)) ->
    let res = A.bveq (int_of_string w) xb yb in
    CryBool(res)
  | _ -> raise "Currently only eq of integers and bit-vectors are supported"

let eq (k : cryType) (x : cryExp) (y : cryExp) : bool = 
  match (k, x, y) with
  | (Integer, CryInt(xi), CryInt(yi)) -> 
    Z.equal (A.get_ci_val xi) (A.get_ci_val yi)
  | (Seq(w, Bit), CryBV(xb), CryBV(yb)) ->
    let res = (A.bveq (int_of_string w) xb yb) in
    (assert (A.is_ct res); A.get_ct_val res)
  | _ -> raise "Currently only eq of integers and bit-vectors are supported"

(** {5. Array Primitives } *)
(* module CryArray = Map.Make(struct type t = cryExp let compare = compare end)
type 'a cryArray = 'a CryArray.t *)

let read_mem (dw : int) (i : airExp) (mem: airExp) : airExp = 
  match dw with
  | 64 -> C.bv_revbytes64 (A.air_read_mem i mem)
  | 8 -> A.air_read_mem i mem
  | _ -> raise "Currently only array of 64-bit words or byte-arrays are supported"

(* Note: currently only Word(64)Array access are implemented *)
let arrayLookup (keyk : cryType) (valk : cryType) (ar : cryExp) (ind: cryExp)
  : cryExp =
  match (keyk, valk, ar, ind) with
  | (Seq(kw, Bit), Seq(vw, Bit), CryMem(mem), CryBV(i)) ->
    let kw = int_of_string kw in
    let vw = int_of_string vw in
    let offset = int_of_float (Float.log2 (float_of_int (vw/8))) in
    let pos = A.bvlsh kw i (A.cb 32 offset) in
    (* Air smem is little-endian, therefore we reverse the bytes after read from mem. *)
    CryBV(read_mem vw pos mem)
  | _ -> raise "arrayLookup input type error"

(* Note: the input inc represents how many bytes to add onto the ind.
   We do this instead of incrementing ind to take advantage of concrete evaluation
   and to avoid stack overflow. *)
let rec arrayRangeLookupHelper (keyk : cryType) (valk : cryType) (n : int) (inc : int)
  (ar : cryExp) (ind : cryExp) (acc : cryExp list) : cryExp list =
  match keyk with
  | Seq(w, Bit) ->
    (if (n <= 0)
    then acc
    else (let newind = add (seq w Bit) ind (CryBV(A.int_to_bv (int_of_string w) (A.ci inc))) in
          let res = (arrayLookup keyk valk ar newind) in
          (arrayRangeLookupHelper keyk valk (n-1) (inc+1) ar ind (res::acc))))
  | _ -> raise "arrayRangeLookupHelper input type error"

let arrayRangeLookup (keyk : cryType) (valk : cryType) (len : string) (ar : cryExp)
  (ind : cryExp) : cryExp = 
  match keyk with
  | Seq(_, Bit) ->
    let n = (int_of_string len) in
    CrySeq(List.rev (arrayRangeLookupHelper keyk valk n 0 ar ind []))
  | _ -> raise "arrayRangeLookup: key type error"

let write_mem (dw : int) (i : airExp) (e : airExp) (mem: airExp) : airExp = 
  match dw with
  | 64 -> A.air_write_mem i (C.bv_revbytes64 e) mem
  | 8 -> A.air_write_mem i e mem
  | _ -> raise "Currently only array of 64-bit words or byte-arrays are supported"

let rec array_from_seq_helper (aw : string) (dw : string) (ind : cryExp) (lst : cryExp list) 
  (mem : airExp) : cryExp = 
  match (lst, ind) with
  | ([], _) -> CryMem(mem)
  | ((CryBV(hd)) :: tl, CryBV(i)) -> 
    let awi = int_of_string aw in
    let dwi = int_of_string dw in
    let newind = CryBV(A.bvadd awi i (A.cb awi (dwi/8))) in
    (* Air smem is little-endian, we reverse the bytes when storing into memory. *)
    let newacc = write_mem dwi i hd mem in
    array_from_seq_helper aw dw newind tl newacc
  | _ -> raise "Input to array_from_seq_helper must be a list of bit-vectors"

let array_from_seq (aw : string) (dw : string) (e : cryExp) (mem: cryExp): cryExp =
  match (e, mem) with 
  | (CrySeq(lst), CryMem(m)) -> 
    array_from_seq_helper aw dw (CryBV(A.s_cb (int_of_string aw) "0x0")) lst m
  | _ -> raise "Input to array_from_seq must be a CrySeq"

let symbolic_malloc (name : string) (aw : int) (dw : int) : cryExp = 
  CryMem(A.smem name aw dw)

(** 7. CryExp vs AirExp *)
let toAir (e : cryExp) : airExp =
  match e with
  | CryBV(b) -> b
  | CryInt(i) -> i
  | CryMem(m) -> m
  | _ -> raise "Input to toAir must be CryBV, CryInt or CryMem"

let toAir2Dim (e : cryExp) : airExp list =
  match e with
  | CrySeq(lst) -> 
    List.map toAir lst
  | _ -> raise "Input to toAir2Dim must be a CrySeq"

let toCryMem (e : airExp) : cryExp = CryMem(e)

let toCry1Dim (e : airExp) : cryExp = CryBV(e)

let toCry2Dim (lst : airExp list) : cryExp = 
  CrySeq(List.map (fun x -> toCry1Dim x) lst)

(** {9. control } *)
(* ite is only used on recursive definitions *)
(* cond, then and else clauses must be airExp wrapped as cryExp, so they must be 1Dim *)
let airIte (c : cryExp) (t : cryExp) (e : cryExp) : cryExp = 
  match c with
  | CryBool(c) -> toCry1Dim (A.ite c (toAir t) (toAir e))
  | _ -> raise "Condition to airIte should be a CryBool"

(** {10. Others} *)
let defun = Air.defun
let defun_rec = Air.defun_rec
let apply = Air.apply
let apply_rec = Air.apply_rec
let sb name w = Air.sb w name
let smem = Air.smem

let rev_digest_blocks (digest : cryExp) : airExp =
  let s = split "0x8" "0x40" Bit digest in
  match s with
  | CrySeq(l) ->
    let flat_digest = join "0x40" "0x8" Bit (CrySeq(List.rev l)) in 
    (match flat_digest with
     | CryBV(l) -> l
     | _ -> raise "Malformed flat_digest")
  | _ -> raise "Malformed digest"

(* Pretty Printers *)

let pp (e : cryExp) =
  match e with
  | CryBV(x) -> A.print_airexp x
  | CryMem(x) -> A.print_airexp x
  |_ -> undefined ()
