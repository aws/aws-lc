(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* Generalized low-level specification for NIST prime curve arithmetic. These functions
are equivalent to the functions extracted from Cryptol, and the following changes are made:
* Operations using Cryptol sequences are replaced with equivalent operations on vectors. 
* Vectors are replaced with lists in situations where a list is more natural (e.g. folding 
  over a list).
* Definitions are abstracted over window size, number of windows, word size, number of bits 
    used to represent the field, etc. 
*)

Set Implicit Arguments.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import Vectors.VectorSpec.
From Coq Require Import Lia.
From Coq Require Import ZArith.BinInt.
From Coq Require Import BinNat.
From Coq Require Import BinPos.
From Coq Require Import Pnat.
From Coq Require Import Nat.
From Coq Require Import Arith.
From Coq Require Import Utils.

From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
Import ListNotations.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePreludeExtra.

From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import Everything.

From Crypto Require Import Algebra.Hierarchy.
From Crypto Require Import Algebra.Field.
From Crypto Require Import Algebra.Nsatz.
From Crypto Require Import Curves.Weierstrass.Jacobian.
From Crypto Require Import Curves.Weierstrass.Affine.
From Crypto Require Import Curves.Weierstrass.AffineProofs.

From EC Require Import Util.
From EC Require Import Curve.
From EC Require Import WindowedMulMachine.
From EC Require Import CryptolToCoq_equiv.
From EC Require Import GroupMulWNAF.

Local Arguments cons [_] h [_] t.
Local Arguments append [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments bvOr [n] _ _.
Local Arguments bvAnd [n] _ _.
Local Arguments reverse [n] [a]%type_scope {Inh_a} _.
Local Arguments bvSub [n] _ _.
Local Arguments SAWCorePrelude.map [a]%type_scope {Inh_a} [b]%type_scope f%function_scope _ _.

From Coq Require Import List.

Global Instance list_inhabited : forall (A : Type), Inhabited (list A).
  intros.
  econstructor.
  apply List.nil.

Defined.

Definition mul_scalar_rwnaf_odd_loop_body_abstract (wsize : nat)(s : bitvector 384) :=
(drop Bool 368 16
   (bvSub
      (bvURem 384 s
         (bvMul 384 (bvNat 384 2)
            (shiftL 384 bool false (bvNat 384 1) wsize)))
      (shiftL 384 bool false (bvNat 384 1) wsize)),
shiftR 384 bool false
  (bvSub s
     (bvSub
        (bvURem 384 s
           (bvMul 384 (bvNat 384 2)
              (shiftL 384 bool false (bvNat 384 1) wsize)))
        (shiftL 384 bool false (bvNat 384 1) wsize))) wsize).


(* The abstract form of the double-and-add loop.
The function uses scanl to build a list of intermediate results and uses
hd to get the last result from the head of the list. The form of hd used
requires a default value that is returned when the list is empty (but the 
proof will show that the list is never empty). To produce this default value,
we use the Inhabited typeclass instances that proves that certain types are
inhabited, and the inhabitant function that produces a value from an inhabited 
type.
*)
Definition mul_scalar_rwnaf_odd_abstract wsize numWindows s :=
  List.map (fun x : bitvector 16 * bitvector 384 => fst x)
  (scanl
     (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
      mul_scalar_rwnaf_odd_loop_body_abstract wsize (snd __p2)) (toN_int numWindows)
     (mul_scalar_rwnaf_odd_loop_body_abstract wsize s)) ++
[drop Bool 368%nat 16%nat
   (snd
      (hd (inhabitant (Inhabited_prod (bitvector 16) (bitvector 384)))
         (rev
            (scanl
               (fun (__p2 : bitvector 16 * bitvector 384) (_ : Integer) =>
                mul_scalar_rwnaf_odd_loop_body_abstract wsize (snd __p2)) 
               (toN_int numWindows) (mul_scalar_rwnaf_odd_loop_body_abstract wsize s)))))].


Local Open Scope Z_scope.

Require Import Coq.ZArith.Zdigits.

Definition mul_scalar_rwnaf_abstract wsize nw s := 
  mul_scalar_rwnaf_odd_abstract wsize nw
    (bvOr s (intToBv 384%nat 1)).


Require Import Coq.Logic.EqdepFacts.

Section EC_P384_Abstract.

  Definition F := Vec 6 (Vec 64 Bool).
  Definition Feq := (@eq F).
  Definition Fzero : F := (replicate 6 _ (replicate 64 _ false)).

  Instance Feq_dec : DecidableRel Feq.

    unfold Decidable.
    intros.
    apply Vector_eq_dec.
    intros.
    apply Vector_eq_dec.
    intros.
    decide equality.
  Defined.

  Context `{curve : Curve  F Feq Fzero}.
  Definition Fsquare x := Fmul x x.

  Definition Fsquare_n n x :=
    (List.fold_left (fun x y => Fsquare x) (forNats n) x).

  Definition felem_inv_sqr_abstract x :=
    let x2 := Fmul (Fsquare x) x in
    let x3 := Fmul (Fsquare x2) x in
    let x6 := Fmul (Fsquare_n 3 x3) x3 in
    let x12 := Fmul (Fsquare_n 6 x6) x6 in
    let x15 := Fmul (Fsquare_n 3 x12) x3 in
    let x30 := Fmul (Fsquare_n 15 x15) x15 in
    let x60 := Fmul (Fsquare_n 30 x30) x30 in
    let x120 := Fmul (Fsquare_n 60 x60) x60 in
    let ret_0 := Fmul (Fsquare_n 120 x120) x120 in
    let ret_1 := Fmul (Fsquare_n 15 ret_0) x15 in
    let ret_2 := Fmul (Fsquare_n 31 ret_1) x30 in
    let ret_3 := Fmul (Fsquare (Fsquare ret_2)) x2 in
    let ret_4 := Fmul (Fsquare_n 94 ret_3) x30 in
    Fsquare (Fsquare ret_4).

  Variable F_cmovznz : (bitvector 64) -> F -> F -> F.

  Definition point := Vec 3 F.
  Variable select_point_loop_body : (bitvector 64) -> point -> (bitvector 64) -> point -> point.
  Variable point_add : bool -> point -> point -> point.
  Variable point_double : point -> point.
  Variable sign_extend_16_64 : (bitvector 16) -> (bitvector 64).

  Variable conditional_subtract_if_even :  point -> (bitvector 384) -> point -> point.

  Definition point_id_to_limb_abstract (id : Vector.t bool 16) : Vector.t bool 64 := 
    Vector.append (vecRepeat false 48) id.

  Definition select_point_abstract x t :=
    fold_left
    (fun acc p =>
     select_point_loop_body x acc (fst p) (snd p))
    (combine (toN_excl_bv 64%nat (length t)) t) (of_list [Fzero; Fzero; Fzero]).

  Definition point_opp_abstract (p : point) : point :=
    Vector.cons (Vector.nth_order p zero_lt_three) 
      (Vector.cons (Fopp (Vector.nth_order p one_lt_three)  ) 
        (Vector.cons (Vector.nth_order p two_lt_three)   (Vector.nil F))).

  Definition pre_comp_table_abstract pred_tsize p :=
    scanl
  (fun
     (z : CryptolPrimitivesForSAWCore.seq 3%nat
            (CryptolPrimitivesForSAWCore.seq 6%nat
               (CryptolPrimitivesForSAWCore.seq 64%nat Bool))) 
     (_ : Integer) =>
   point_add false
     (point_double p) z)
  (map (BinIntDef.Z.add (BinIntDef.Z.of_nat 1)) (toN_int pred_tsize)) p .

  Definition conditional_point_opp_abstract (t : bitvector 64) (p : point): point :=
    Vector.cons (Vector.nth_order p zero_lt_three)  (Vector.cons (F_cmovznz t (Vector.nth_order p one_lt_three)  (Fopp (Vector.nth_order p one_lt_three) )) (Vector.cons (Vector.nth_order p two_lt_three)  (Vector.nil _))).

  Definition double_add_body_abstract pred_wsize t p id :=
    point_add false
  (fold_left
     (fun
        (x : CryptolPrimitivesForSAWCore.seq 3%nat
               (CryptolPrimitivesForSAWCore.seq 6%nat
                  (CryptolPrimitivesForSAWCore.seq 64%nat Bool)))
        (_ : Integer) =>
      point_double x)
     (toN_int pred_wsize) p)
  (conditional_point_opp_abstract
     (point_id_to_limb_abstract
        (shiftR 16 bool false id 15))
     (select_point_abstract
        (sign_extend_16_64
           (bvSShr 15%nat
              (bvAdd 16
                  (shiftR 16 bool false id 15)


                 (bvXor 16%nat id
                      (bvSShr 15%nat id 15)
)) 1%nat)) t)).


  Definition point_mul_abstract wsize nw pred_tsize p s : point := 
    conditional_subtract_if_even 
  (fold_left
     (double_add_body_abstract (Nat.pred wsize) (pre_comp_table_abstract pred_tsize p))
     (skipn 1 (rev (mul_scalar_rwnaf_abstract wsize nw s)))
     (select_point_abstract
        (sign_extend_16_64
           (bvSShr 15
              (nth (S (S nw)) (mul_scalar_rwnaf_abstract wsize nw s)
                 (bvNat 16%nat 0%nat))
              1%nat) )
        (pre_comp_table_abstract pred_tsize p))) s
  (nth 0 (pre_comp_table_abstract pred_tsize p)
     (inhabitant (ecNumber 0%nat Integer PLiteralInteger))).


  Section PointMulBase.


    Variable base_precomp_table : list (list affine_point).

    Import VectorNotations. 

    Variable select_point_affine_loop_body : (bitvector 64) -> affine_point -> (bitvector 64) -> affine_point -> affine_point.

    Definition select_point_affine_abstract x t :=
      fold_left
      (fun acc p =>
       select_point_affine_loop_body x acc (fst p) (snd p))
      (combine (toN_excl_bv 64%nat (length t)) t) (of_list [Fzero; Fzero]).

    Definition add_base_abstract one pred_wsize (rnaf : list (Vector.t bool 16))(p : point)(j : nat) : point :=
      let window  := nth j rnaf (vecRepeat false 16) in
      let selected   := select_point_affine_abstract (sign_extend_16_64 (bvSShr _ (bvAdd _ (shiftR _ _ false window 15) (bvXor _ window (bvSShr _ window 15%nat))) 1%nat)) (nth (Nat.div j pred_wsize) base_precomp_table nil) in
      let x_coord   :=nth_order  selected zero_lt_two in
      let y_coord   :=nth_order  selected one_lt_two in
      point_add true p [x_coord; F_cmovznz (point_id_to_limb_abstract (bvShr _ window 15)) y_coord (Fopp y_coord); one].

    Import VectorNotations. 
    
    Definition b8_114 := CryptolPrimitivesForSAWCore.ecNumber 114%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_110 := CryptolPrimitivesForSAWCore.ecNumber 110%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_104 := CryptolPrimitivesForSAWCore.ecNumber 104%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_101 := CryptolPrimitivesForSAWCore.ecNumber 101%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_99 := CryptolPrimitivesForSAWCore.ecNumber 99%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_98 := CryptolPrimitivesForSAWCore.ecNumber 98%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_97 := CryptolPrimitivesForSAWCore.ecNumber 97%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b8_32 := CryptolPrimitivesForSAWCore.ecNumber 32%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 8%nat).
    Definition b64_4 := CryptolPrimitivesForSAWCore.ecNumber 4%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 64%nat).
    Definition b64_3 := CryptolPrimitivesForSAWCore.ecNumber 3%nat _ (CryptolPrimitivesForSAWCore.PLiteralSeqBool 64%nat).

    Definition double_add_base_abstract one (wsize : nat) (nw : nat) rnaf
      (p : point) 
      (i : nat) 
        : point :=
    let doubled   := if (eq_nat_dec i (Nat.pred (Nat.pred wsize)))  then p else fold_left (fun x _ => point_double x) (forNats wsize) p  in
      fold_left (add_base_abstract one (Nat.pred wsize) rnaf) (List.rev (lsMultiples nw (Nat.pred wsize) i)) doubled.

    Definition conditional_subtract_if_even_mixed_abstract p1 n p2 :=
      if (even (bvToNat 384 n)) then (point_add true p1 (point_opp_abstract p2)) else p1.

    Definition affine_g := (nth 0 (nth 0 base_precomp_table nil) (inhabitant affine_point)).
    Definition affine_default := affine_g.
    Definition g one := Vector.append (nth 0 (nth 0 base_precomp_table nil) affine_default) [one].

    Definition point_mul_base_abstract one (wsize nw : nat)  s :=
      conditional_subtract_if_even_mixed_abstract 
      (fold_left
         (double_add_base_abstract one wsize nw (mul_scalar_rwnaf_abstract wsize (Nat.pred (Nat.pred (Nat.pred nw))) s))
          (forNats (Nat.pred wsize))
          (replicate 3 (Vec 6 (bitvector 64)) (replicate 6 (bitvector 64) (intToBv 64 0)))
      ) s (g one).

  End PointMulBase.

  Variable F_nz : F -> bitvector 64.
  Definition F_ne x y := F_nz (Fsub x y).

  (* Base point table validation function. *)
  Definition jacobian_affine_eq_abstract (jp : point) (ap : affine_point) := 
    (if bvEq 64 (F_nz (nth_order jp two_lt_three)) (intToBv 64 0)
     then 0%bool
     else
      if
       negb
         (bvEq 64
            (F_ne (Fmul (nth_order ap zero_lt_two) (Fsquare (nth_order jp two_lt_three))) (nth_order jp zero_lt_three))
            (intToBv 64 0))
      then 0%bool
      else
       if
        negb
          (bvEq 64
             (F_ne
                (Fmul (nth_order ap one_lt_two) (Fmul (Fsquare (nth_order jp two_lt_three)) (nth_order jp two_lt_three)))
                (nth_order jp one_lt_three)) (intToBv 64 0))
       then 0%bool
       else 1%bool).

  Definition validate_base_row_body_abstract g x y := 
    (point_add 0 (fst x) g, (snd x && jacobian_affine_eq_abstract (fst x) y)%bool).

  Definition validate_base_row_abstract (wsize : nat)(p : point)(r : list affine_point) : bool := 
    snd
    (fold_left (validate_base_row_body_abstract (point_double p))
     (map (fun i : Z => nth (Z.to_nat i) r (inhabitant affine_point)) (map (Z.add 1) (toN_int (Nat.pred (Nat.pred (Nat.pow 2 (Nat.pred wsize)))))))
     (point_add false p (point_double p),
     jacobian_affine_eq_abstract p (nth 0 r (inhabitant affine_point)))).

  
  Definition point_double_base_abstract (p : point)(n : nat) : point := 
    fold_left (fun x _ => point_double x) (toN_bv 64 (Nat.pred n)) p.
  Definition point_double_base_tsize_abstract (tsize : nat)(p : point) : point := point_double_base_abstract p tsize.
  
  Definition validate_base_table_body_abstract (wsize : nat)(st : point * bool)(r : list affine_point) : (point * bool) := 
    (point_double_base_tsize_abstract (wsize * (Nat.pred wsize)) (fst st), (snd st && validate_base_row_abstract wsize (fst st) r)%bool).

  Definition affineToJac (a : affine_point) : Vec 3 F :=
    (Vector.append a (Vector.cons Fone (@Vector.nil F))).

  Definition validate_base_table_abstract wsize (t : list (list affine_point)) : bool := 
    snd
      (fold_left (validate_base_table_body_abstract wsize) t
         (affineToJac (nth 0%nat (nth 0%nat t (inhabitant (list affine_point))) (inhabitant affine_point)), 1%bool)).

  Theorem fold_left_map : forall (A B C : Type)(f1 : A -> B)(f2 : C -> B -> C) ls y,
    fold_left f2 (map f1 ls) y = fold_left (fun x y => f2 x (f1 y)) ls y.

    Local Transparent map fold_left.
    induction ls; intros; simpl in *.
    reflexivity.
    eapply IHls.

  Qed.

  Theorem affineToJac_cons_eq : forall z,
      affineToJac z =
      Vector.cons (nth_order z zero_lt_two)
        (Vector.cons (nth_order z one_lt_two)
           (Vector.cons Fone (@Vector.nil F))).

    intros.
    unfold affineToJac. 
    destruct (Vec_S_cons _ _ z). destruct H.
    destruct (Vec_S_cons _ _ x0). destruct H0.
    subst.
    rewrite (Vec_0_nil _ x2).
    reflexivity.
  Qed.

  Theorem affineToJac_cons_eq_gen : forall z1 z2,   
    z1 = z2 -> 
    affineToJac z1 =
    Vector.cons (nth_order z2 zero_lt_two)
      (Vector.cons (nth_order z2 one_lt_two)
         (Vector.cons Fone (@Vector.nil F))).

    intros.
    subst.
    apply affineToJac_cons_eq.
  Qed.


End EC_P384_Abstract.

