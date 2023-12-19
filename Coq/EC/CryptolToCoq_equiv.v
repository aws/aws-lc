(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
SPDX-License-Identifier: Apache-2.0 *)

(* This file contains theory and tactics for proving equivalence between definitions extracted from Cryptol and 
simpler hand-written definitions. *)

(* Cryptol sequences are extracted to Coq vectors, and it is difficult to write well-typed expressions in which these vectors are reversed. 
To avoid this problem, we develop alternative definitions using lists and prove them equivalent to the definitions using vectors. *)

Set Implicit Arguments.

From Coq Require Import Lists.List.
From Coq Require Import String.
From Coq Require Import Vectors.Vector.
From Coq Require Import Vectors.VectorSpec.
From Coq Require Import Lia.


From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
Import ListNotations.

From CryptolToCoq Require Import CryptolPrimitivesForSAWCore.
Import CryptolPrimitivesForSAWCore.
From CryptolToCoq Require Import CryptolPrimitivesForSAWCoreExtra.
From CryptolToCoq Require Import SAWCorePrelude.
Import SAWCorePrelude.
From CryptolToCoq Require Import SAWCorePrelude_proofs.
From CryptolToCoq Require Import CoqVectorsExtra.
From CryptolToCoq Require Import SAWCorePreludeExtra.
From CryptolToCoq Require Import SAWCoreScaffolding.


From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import Everything.

From Bits Require Import operations.
From Bits Require Import operations.properties.
From Bits Require Import spec.properties.


Ltac ecSimpl_one :=
  match goal with
    | [ |- context[ecNumber (TCNum ?a) ?t (PLiteralSeqBool (TCNum ?s))]] =>
        replace (ecNumber (TCNum a) t (PLiteralSeqBool (TCNum s))) with (bvNat s a); [idtac | reflexivity] 
    | [ |- context[ecNumber (TCNum ?a) ?t PLiteralInteger]] =>
        replace (ecNumber (TCNum a) t PLiteralInteger) with (Z.of_nat a); [idtac | reflexivity] 
    | [|- context[ecCat ?s1 ?s2 ?t ?a ?b]] =>
        replace (ecCat s1 s2 t a b) with (append a b); [idtac | reflexivity]
    | [|- context[map ?s ?t1 ?t2 ?f ?ls]] =>
        replace (map s t1 t2 f ls) with (SAWCorePrelude.map f _ ls); [idtac | reflexivity]
    | [ |- context[ecPlus Integer ?r (Z.of_nat ?a) (Z.of_nat ?b)]] =>
        replace (ecPlus Integer r (Z.of_nat a) (Z.of_nat b)) with (ecNumber (a + b) Integer PLiteralInteger); [idtac | reflexivity]
    | [ |- context[ecMinus ?t (PRingSeqBool ?s) ?a ?b]] => 
        replace (ecMinus t (PRingSeqBool s) a b) with (bvSub a b); [idtac | reflexivity]
    | [ |- context[ecPlus ?t (PRingSeqBool ?s) ?a ?b]] => 
        replace (ecPlus t (PRingSeqBool s) a b) with (bvAdd a b); [idtac | reflexivity]
    | [ |- context[ecAnd ?t (PLogicSeqBool ?s) ?a ?b]] => 
        replace (ecAnd t (PLogicSeqBool s) a b) with (bvAnd a b); [idtac | reflexivity]
    | [ |- context[ecMul ?t (PRingSeqBool ?s) ?a ?b]] => 
        replace (ecMul t (PRingSeqBool s) a b) with (bvMul _ a b); [idtac | reflexivity]
    | [ |- context[ecMod ?t (PIntegralSeqBool ?s) ?a ?b]] => 
        replace (ecMod t (PIntegralSeqBool s) a b) with (bvURem _ a b); [idtac | reflexivity]
    | [ |- context[ecDrop (TCNum ?s1) (TCNum ?s2) ?t ?a]] => 
        replace (ecDrop (TCNum s1) (TCNum s2) t a) with (drop _ s1 s2 a); [idtac | reflexivity]
    | [ |- context[ecShiftL ?s ?t Bool ?r PZeroBit ?a (Z.of_nat ?b)]] => 
        replace (ecShiftL s t Bool r PZeroBit a (Z.of_nat b)) with (shiftL _ _ false a b); [idtac | reflexivity]
    | [ |- context[ecShiftR ?s1 ?t Bool ?r PZeroBit ?a (bvNat ?s2 ?b)]] => 
        replace (ecShiftR s1 t Bool r PZeroBit a (bvNat s2 b)) with (shiftR _ _ false a b); [idtac | reflexivity]
    | [ |- context[ecShiftR ?s ?t Bool ?r PZeroBit ?a (Z.of_nat ?b)]] => 
        replace (ecShiftR s t Bool r PZeroBit a (Z.of_nat b)) with (shiftR _ _ false a b); [idtac | reflexivity]
  end.

Ltac removeCoerce :=
  match goal with
  | [ |- context[coerce ?t1 ?t2 ?p ?a]] => 
    replace (coerce t1 t2 p a) with a; [idtac | reflexivity]
  end.


Theorem vec_0_eq : forall (A : Type)(v1 v2 : Vector.t A 0%nat),
  v1 = v2.

  intros.
  specialize (Vec_0_nil _ v1); intros.
  specialize (Vec_0_nil _ v2); intros.
  subst.
  reflexivity.

Qed.


Theorem eq_if_to_list_eq : forall (A : Type) n (v1 v2 : Vector.t A n),
  to_list v1 = to_list v2 ->
  v1 = v2.

  induction n; intros; simpl in *.
  eapply vec_0_eq.
  destruct (Vec_S_cons _  _ v1). destruct H0. subst.
  destruct (Vec_S_cons _ _ v2). destruct H0. subst.
  repeat rewrite to_list_cons in H.
  inversion H; clear H; subst.
  f_equal.
  eapply IHn.
  eauto.

Qed.

Fixpoint toN_excl_int n :=
  match n with 
  | 0 => List.nil
  | S n' => (toN_excl_int n') ++ (Z.of_nat n') :: List.nil
  end.

Definition toN_int n :=
  (toN_excl_int n) ++ ((Z.of_nat n) :: List.nil).


Fixpoint toN_excl_bv s n :=
  match n with 
  | 0 => List.nil
  | S n' => (toN_excl_bv s n') ++ (bvNat s n') :: List.nil
  end.

Definition toN_bv s n :=
  (toN_excl_bv s n) ++ ((bvNat s n) :: List.nil).


Fixpoint fromN_excl_bv (s n1 count : nat) : list (Vec s bool) :=
  match count with
  | 0%nat => List.nil
  | S count' => (bvNat s n1) :: (fromN_excl_bv s (S n1) count') 
  end.

Definition fromToN_bv (s n1 n2 : nat) : list (Vec s bool) :=
  (bvNat s n1) :: (fromN_excl_bv s (S n1) (n2 - n1)).

Theorem fromN_excl_bv_rev : forall s n2 n1,
  (n2 > 0)%nat ->
  fromN_excl_bv s n1 n2 = fromN_excl_bv s n1 (pred n2) ++ [bvNat s ((pred n2) + n1)%nat].

  induction n2; intros; simpl in *.
  lia.
  destruct (Peano_dec.eq_nat_dec n2 0%nat).
  subst.
  reflexivity.
  rewrite IHn2; try lia.
  destruct n2. lia.
  simpl.
  f_equal.
  f_equal.
  rewrite PeanoNat.Nat.add_comm.
  simpl.
  rewrite PeanoNat.Nat.add_comm.
  reflexivity.

Qed.

Theorem toN_bv_fromToN_bv_eq : forall s n2,
  toN_bv s n2 = 
  fromToN_bv s 0%nat n2.

  intros.
  unfold toN_bv, fromToN_bv.
  rewrite PeanoNat.Nat.sub_0_r.
  generalize n2 as n.
  induction n; intros; simpl in *.
  reflexivity.
  rewrite IHn.
  rewrite <- app_comm_cons.
  f_equal.
  specialize (@fromN_excl_bv_rev s (S n) 1); intros.
  simpl in *.
  rewrite H.
  f_equal.
  rewrite Znat.Zpos_P_of_succ_nat.
  rewrite <- BinInt.Z.add_1_r.
  rewrite Znat.Nat2Z.inj_add.
  reflexivity.
  lia.

Qed.

Theorem fromN_excl_bv_eq_gen : forall s n1 n2,
  fromN_excl_bv s n2 n1 = to_list (gen n1 _ (fun x => bvNat s (x + n2))).

  induction n1; intros; simpl in *.
  reflexivity.
  rewrite IHn1.
  rewrite to_list_cons.
  f_equal.
  f_equal.
  apply gen_domain_eq.
  intros.
  f_equal.
  rewrite PeanoNat.Nat.add_comm.
  simpl.
  rewrite PeanoNat.Nat.add_comm.
  reflexivity.
Qed.

Theorem ecFromTo_0_n_bv_equiv : forall (s : nat) n,
  to_list (ecFromTo 0 (TCNum n) (CryptolPrimitivesForSAWCore.seq (TCNum s) Bool)
           (PLiteralSeqBool (TCNum s))) = 
  (toN_bv s n).

  intros.
  unfold ecFromTo.
  rewrite toN_bv_fromToN_bv_eq.
  simpl.
  rewrite to_list_cons.
  unfold fromToN_bv.
  f_equal.
  rewrite PeanoNat.Nat.sub_0_r.
  rewrite fromN_excl_bv_eq_gen.
  f_equal.
  apply gen_domain_eq.
  intros.
  unfold bvNat.
  f_equal.
  rewrite PeanoNat.Nat.add_comm.
  simpl.
  rewrite addNat_add.
  rewrite PeanoNat.Nat.add_comm.
  reflexivity.

Qed.


Theorem map_cons : forall A B n (v : Vec n A) (f : A -> B) a,
  map _ _ f _ (VectorDef.cons _ a _ v) = Vector.cons _ (f a) _ (map _ _ f _ v).

  intros.
  reflexivity.

Qed.

Theorem toList_map_equiv : forall A (inh : Inhabited A) B n (v : Vec n A) (f : A -> B),
  to_list (SAWCorePrelude.map _ _ f _ v) = List.map f (to_list v).

  induction v; intros.
  reflexivity.

  rewrite to_list_cons.
  simpl.
  match goal with
  | [|- to_list (map ?A ?B ?f (S ?n) (VectorDef.cons ?A ?h ?n ?v)) = _] =>
    assert ((map A B f (S n) (VectorDef.cons A h n v)) = (Vector.cons _ (f h) _ (map _ _ f _ v)))
  end.
  reflexivity.
  rewrite H.
  rewrite to_list_cons.
  f_equal.
  eauto.

Qed.



Fixpoint scanl (A B : Type)(f : A -> B -> A)(ls : list B)(a : A) :=
  match ls with 
  | List.nil => a :: List.nil 
  | b :: ls' => a :: scanl f ls' (f a b)
  end.

Theorem toList_scanl_equiv : forall (A B : Type)(f : A -> B -> A) n (v : Vec n B)(a : A),
  to_list (ecScanl (TCNum n) A B f a v) = scanl f (to_list v) a.

  induction v; intros.
  simpl. reflexivity.

  simpl.
  rewrite to_list_cons.
  f_equal.
  eapply IHv.

Qed.


Fixpoint scanl_fix (A C : Type)(f : A -> A)(f1 f2 : A -> C) n a := 
  match n with
  | 0 => List.nil
  | 1 => (f1 a) :: (f2 a) :: List.nil
  | S n' => (f1 a) :: (scanl_fix f f1 f2 n' (f a))
  end.

Theorem hd_app_eq : forall (A : Type)(defA: A)(ls1 ls2 : list A),
  List.length ls1 <> O ->
  List.hd defA (ls1 ++ ls2) = List.hd defA ls1.

  intros.
  destruct ls1; simpl in *.
  intuition.
  trivial.
Qed.

Theorem scanl_length : forall (A B : Type)(ls : list A)(f : B -> A -> B)(b : B),
  Datatypes.length (scanl f ls b) <> O.

  intros.
  destruct ls; simpl; intuition.

Qed.


Theorem scanl_fix_equiv : forall (A B C: Type) (defA : A) (f : A -> A) (ls : list B) (n : nat) (f1 f2 : A -> C) a,
  List.length ls = n ->  
  (List.map f1 (scanl (fun x y => f x) ls a)) ++ (f2 (List.hd defA (List.rev (scanl (fun x y => f x) ls a))))::List.nil = 
  scanl_fix f f1 f2 (S n) a.

  induction ls; destruct n; intros; simpl in *.
  reflexivity.
  discriminate.
  discriminate.
  
  f_equal.

  rewrite hd_app_eq.
  eapply IHls.
  lia.

  rewrite rev_length.
  eapply scanl_length.
Qed.

Require Import ZArith.BinInt.

Require Import BinNat.
Require Import BinPos.
Require Import Pnat.
Require Import Nat.
Require Import List.
Require Import Arith.
Local Open Scope Z_scope.
Require Import Coq.ZArith.Zdigits.


Theorem ecCat_equiv : forall s1 s2 t (inh : Inhabited t)(a : Vec s1 t) (b : Vec s2 t),
  (ecCat (TCNum s1) (TCNum s2) t a b) = (SAWCorePrelude.append _ _ _ a b).

  intros.
  reflexivity.
Qed.


Theorem sawAt_nth_equiv : forall (A : Type)(inh : Inhabited A)(n1 : nat)(ls : Vec n1 A)(n2 : nat),
   (n2 < n1)%nat ->
   (sawAt _ _ ls n2) = (nth n2 (to_list ls) (inhabitant inh)).

  induction ls; intros; simpl in *.
  lia.

  destruct n2; simpl in *.
  trivial.

  unfold sawAt in *. simpl.
  rewrite IHls.
  reflexivity.
  lia.
Qed.

Fixpoint gen_ls (n : nat)(A : Type)(f : nat -> A) : list A :=
  match n with
  | O => nil
  | S p => cons (f 0%nat) (gen_ls p (fun i => f (S i)))
  end.

Theorem to_list_gen_sawAt_eq : forall (A : Type)(inh : Inhabited A) n n' (ls : Vec n' A)(f : nat-> nat),
  (forall i, i < n -> f i < n')%nat -> 
  to_list (gen n _ (fun i => sawAt n' _ ls (f i) )) = gen_ls n (fun i => nth (f i) (to_list ls) inhabitant). 

  induction n; intros; simpl in *.
  reflexivity.

  rewrite to_list_cons.
  rewrite (@IHn _ ls (fun x => (f (S x)))).
  f_equal.
  apply sawAt_nth_equiv.
  eapply H.
  lia.
  intros.
  eapply H.
  lia.

Qed.

Theorem gen_ls_ext : forall (A : Type) n (f1 f2 : nat -> A),
  (forall i, (i < n)%nat -> f1 i = f2 i) ->
  gen_ls n f1 = gen_ls n f2.

  induction n; intros; simpl in *.
  trivial.

  f_equal.
  eapply H.
  lia.
  eapply IHn.
  intros.
  eapply H.
  lia.

Qed.


Theorem gen_ls_reverse_equiv : forall (A : Type)(inh : Inhabited A) n (ls : list A) , 
  length ls = n ->
  gen_ls n (fun i : nat => nth ((n - 1) - i)%nat ls inhabitant) = rev ls.

  induction n; intuition; simpl in *.
  destruct ls; simpl in *; trivial; try discriminate.

  destruct ls using rev_ind.
  simpl in *. discriminate.
  rewrite app_length in H.
  assert (n = Datatypes.length ls).
  simpl in *. lia.
  subst.
  rewrite rev_app_distr.
  simpl.
  f_equal.
  rewrite app_nth2.
  simpl in *.
  repeat rewrite Nat.sub_0_r.
  rewrite minus_diag. trivial.
  lia.

  specialize (IHn ls).
  rewrite <- IHn; trivial.
  eapply gen_ls_ext.
  intros.
  repeat rewrite Nat.sub_0_r.
  replace (Datatypes.length ls - 1 - i)%nat with (Datatypes.length ls - (S i))%nat.
  rewrite app_nth1.
  trivial.
  lia.
  lia.
 
Qed.

Theorem gen_ls_reverse_subNat_equiv : forall (A : Type)(inh : Inhabited A) n (ls : list A) , 
  length ls = n ->
  gen_ls n (fun i : nat => nth (subNat (subNat n 1%nat) i) ls inhabitant) = rev ls.

  intros.
  erewrite gen_ls_ext.
  apply gen_ls_reverse_equiv; eauto.
  intros.  
  repeat rewrite subNat_sub.
  reflexivity.
Qed.


Theorem toList_reverse_equiv : forall (A : Type)(inh : Inhabited A) n (ls : Vec n A),
  to_list (SAWCorePrelude.reverse _ _ ls) = rev (to_list ls).

  intros.
  unfold reverse.
  rewrite to_list_gen_sawAt_eq.
  apply gen_ls_reverse_subNat_equiv.
  apply length_to_list.
  intros.
  repeat rewrite subNat_sub.
  lia.

Qed.

Theorem nth_0_hd_equiv : forall (A : Type)(defA : A)(ls : list A),
  nth 0 ls defA = hd defA ls.

  destruct ls; trivial.

Qed.

Theorem scanl_ext : forall (A B : Type)(f1 f2 : A -> B -> A) ls a,
    (forall a b, f1 a b = f2 a b) ->
    (scanl f1 ls a) = (scanl f2 ls a).

  induction ls; intuition idtac; simpl in *.
  f_equal.
  rewrite H.
  eapply IHls.
  eauto.

Qed.

(* zip is in the generated code. It is reproduced here to allow us to reason about it without importing
generated code. *)

Definition zip (n : CryptolPrimitivesForSAWCore.Num) (a : Type) {Inh_a : SAWCoreScaffolding.Inhabited a} (b : Type) {Inh_b : SAWCoreScaffolding.Inhabited b} (xs : CryptolPrimitivesForSAWCore.seq n a) (ys : CryptolPrimitivesForSAWCore.seq n b)  :=
  let var__0   := prod a b in
  CryptolPrimitivesForSAWCore.seqMap var__0 var__0 n (SAWCorePrelude.uncurry a b var__0 (fun (x : a) (y : b) => pair x y)) (CryptolPrimitivesForSAWCore.seqZipSame a b n xs ys).

Theorem zip_cons_equiv : forall A B (inha : Inhabited A)(inhb : Inhabited B) n (lsa: Vec n A) (lsb: Vec n B) h h0,
  (@zip (TCNum (S n)) A inha B inhb (VectorDef.cons A h n lsa)
     (VectorDef.cons B h0 n lsb)) = VectorDef.cons _ (h, h0) _ (@zip (TCNum n) A inha B inhb lsa lsb).

  intros.
  reflexivity.

Qed.

Theorem toList_zip_equiv : forall (A B : Type)(inha : Inhabited A)(inhb: Inhabited B) n (lsa: Vec n A) (lsb : Vec n B),
  to_list (zip (TCNum n) lsa lsb) = List.combine (to_list lsa) (to_list lsb).

  induction lsa; intros.
  rewrite (@Vec_0_nil _ lsb0).
  simpl.
  reflexivity.
  destruct (Vec_S_cons _ _  lsb0).
  destruct H. subst.
  rewrite zip_cons_equiv.
  repeat rewrite to_list_cons.
  rewrite IHlsa.
  reflexivity. 
Qed.


Theorem fold_left_ext : forall (A B : Type)(f1 f2 : A -> B -> A) ls a,
    (forall a b, f1 a b = f2 a b) ->
    fold_left f1 ls a = fold_left f2 ls a.

  induction ls; intuition idtac; simpl in *.
  rewrite H.
  apply IHls.
  intuition idtac.  
Qed.

Theorem drop_cons_eq : forall (A : Type)(inh : Inhabited A) n1 n2 ls a,
  drop A (S n1) n2 (Vector.cons _ a _ ls) = drop A n1 n2 ls.

  intros.
  reflexivity.

Qed.

Theorem toList_drop_equiv : forall A (inh : Inhabited A) n1 n2 ls,
  to_list (drop A n1 n2 ls) = skipn n1 (to_list ls).

  induction n1; intros; simpl in *.
  unfold drop.
  erewrite gen_domain_eq.
  rewrite gen_sawAt.
  reflexivity.
  intros.
  simpl.
  reflexivity.

  destruct (Vec_S_cons _ _ ls). destruct H.
  subst.
  rewrite drop_cons_eq.
  rewrite IHn1.
  rewrite to_list_cons.
  reflexivity.

Qed.

Theorem nth_order_S_cons : forall (A : Type) a n (v : Vec n A) n' (pf : (S n' < S n)%nat)(pf' : (n' < n)%nat),
  nth_order (Vector.cons _ a _ v) pf = nth_order v pf'.

  intros.
  unfold nth_order.
  simpl.
  eapply Vector.eq_nth_iff; trivial.
  apply Fin.of_nat_ext.
Qed.

Theorem ssr_addn_even : forall n1 n2,
  even n1 = true ->
  even n2 = true ->
  even (ssrnat.addn n1 n2) = true.

  intros.
  rewrite <- ssrnat.plusE.
  rewrite Nat.even_add_even; trivial.
  apply Nat.even_spec; trivial.

Qed.


Theorem ssr_double_even : forall n,
  even (ssrnat.double n) = true.

  induction n; intros; simpl in *; trivial.

Qed.

Theorem nth_order_0_cons : forall (A : Type) a n (v : Vec n A) (pf : (0 < S n)%nat),
  nth_order (Vector.cons _ a _ v) pf = a.

  intros.
  reflexivity.
Qed.

Theorem lsb_0_even_h : forall n (v : Vec n _) acc (pf : (pred n < n)%nat),
  nth_order v pf = false -> 
  even (Vector.fold_left bvToNatFolder acc v)  = true.

  induction n; intros; simpl in *.
  lia.

  unfold bvToNat in *.
  destruct (Vec_S_cons _ _ v).
  destruct H0.
  subst.
  simpl.
  destruct n.
  rewrite nth_order_0_cons in H.
  subst.
  rewrite (@Vec_0_nil _ x0).
  simpl.
  unfold bvToNatFolder.
  simpl.
  (* double anything is even, 0 is even, even plus even is even*)
  apply ssr_addn_even.
  reflexivity.
  apply ssr_double_even.

  assert (n < S n)%nat by lia.
  rewrite (@nth_order_S_cons _ _ _ _ _ _ H0) in H.
  eapply IHn.
  eauto.

Qed.

Theorem lsb_0_even : forall n (v : Vec n _) (pf : (pred n < n)%nat),
  nth_order v pf = false -> 
  even (bvToNat _ v) = true.

  intros. 
  eapply lsb_0_even_h; eauto.

Qed.

Theorem lsb_1_not_even_h : forall n (v : Vec n _) acc (pf : (pred n < n)%nat),
  nth_order v pf = true -> 
  even (Vector.fold_left bvToNatFolder acc v)  = false.

  induction n; intros; simpl in *.
  lia.

  unfold bvToNat in *.
  destruct (Vec_S_cons _ _ v).
  destruct H0.
  subst.
  simpl.
  destruct n.
  rewrite nth_order_0_cons in H.
  subst.
  rewrite (@Vec_0_nil _ x0).
  simpl.
  case_eq (ssrnat.double acc); intros; trivial.
  rewrite <- Nat.negb_odd.
  rewrite <- Nat.even_succ.
  rewrite <- H.
  rewrite ssr_double_even.
  reflexivity.

  assert (n < S n)%nat by lia.
  rewrite (@nth_order_S_cons _ _ _ _ _ _ H0) in H.
  eapply IHn.
  eauto.

Qed.

Theorem lsb_1_not_even : forall n (v : Vec n _) (pf : (pred n < n)%nat),
  nth_order v pf = true -> 
  even (bvToNat _ v) = false.

  intros. 
  eapply lsb_1_not_even_h; eauto.

Qed.


Theorem append_nil_eq : forall (A : Type)(inh : Inhabited A) n (v : Vec n A),
  SAWCorePrelude.append _ _ _ (@Vector.nil A) v = v.

  intros.
  unfold SAWCorePrelude.append.
  simpl.
  apply gen_sawAt.

Qed.

Theorem bvZipWith_cons : forall f n2 a b (v2a v2b : Vec n2 _),
  bvZipWith f _ (Vector.cons _ a _ v2a) (Vector.cons _ b _ v2b) = 
  Vector.cons _ (f a b) _ (bvZipWith f _ v2a v2b).

  intros.
  reflexivity.

Qed.

Local Arguments Vector.cons [_] h [_] t.
Local Arguments append [m] [n] [a]%type_scope {Inh_a} x y.
Local Arguments bvOr [n] _ _.
Local Arguments bvAnd [n] _ _.
Local Arguments reverse [n] [a]%type_scope {Inh_a} _.
Local Arguments bvSub [n] _ _.
Local Arguments SAWCorePrelude.map [a]%type_scope {Inh_a} [b]%type_scope f%function_scope _ _.


Theorem bvZipWith_append : forall f n1 n2 (v1a v1b : Vec n1 _) (v2a v2b : Vec n2 _),
  bvZipWith f _ (append v1a v2a) (append v1b v2b) = 
  append (bvZipWith f _ v1a v1b) (bvZipWith f _ v2a v2b).

  induction n1; intros; simpl in *.
  rewrite (@Vec_0_nil _ v1a).
  rewrite (@Vec_0_nil _ v1b).
  repeat rewrite append_nil_eq.
  reflexivity.

  destruct (Vec_S_cons _ _ v1a).
  destruct H.
  destruct (Vec_S_cons _ _ v1b).
  destruct H0.
  subst.
  repeat rewrite SAWCorePrelude_proofs.append_cons.
  unfold Succ.
  repeat rewrite bvZipWith_cons.
  rewrite IHn1.
  rewrite SAWCorePrelude_proofs.append_cons.
  reflexivity.
Qed.


Theorem bvZipWith_append' : forall f n1 n2 (v1a v1b : Vec n1 _) (v2a v2b : Vec n2 _),
  bvZipWith f _ (Vector.append v1a v2a) (Vector.append v1b v2b) = 
  Vector.append (bvZipWith f _ v1a v1b) (bvZipWith f _ v2a v2b).

  induction n1; intros; simpl in *.
  rewrite (@Vec_0_nil _ v1a).
  rewrite (@Vec_0_nil _ v1b).
  reflexivity.

  destruct (Vec_S_cons _ _ v1a).
  destruct H.
  destruct (Vec_S_cons _ _ v1b).
  destruct H0.
  subst.
  simpl.
  repeat rewrite bvZipWith_cons.
  rewrite IHn1.
  reflexivity.

Qed.

Theorem ecEq_bv_true : forall n v,  
  ecEq (bitvector n) (PEqWord n) v v = true.

  intros.
  apply bvEq_refl.

Qed.

Theorem ecEq_bv_false : forall n v1 v2,
  v1 <> v2 ->
  ecEq (bitvector n) (PEqWord n) v1 v2 = false.

  intros.
  unfold ecEq.
  simpl.
  case_eq (bvEq n v1 v2); intros; trivial.
  apply bvEq_eq in H0.
  intuition.
Qed.


Theorem scanl_gen_equiv : forall A n f1 f2 z1 x,
  (SAWCoreVectorsAsCoqVectors.scanl Integer A n
         (fun (z : A) (_ : Integer) =>
          z1 z) x
         (gen n Integer f1))
  = 
  (SAWCoreVectorsAsCoqVectors.scanl Integer A n
         (fun (z : A) (_ : Integer) =>
          z1 z) x
         (gen n Integer f2)).

  induction n; intuition; simpl in *.
  f_equal.
  apply IHn.
Qed.

Fixpoint bv64Nats_h (n : nat) v :=
  match n with
  | 0%nat => List.nil
  | S n' => (intToBv 64%nat (Z.of_nat v)) :: (bv64Nats_h n' (S v))
  end.

Definition bv64Nats n := bv64Nats_h n 0.


Fixpoint nats_h n v :=
  match n with
  | 0%nat => List.nil
  | S n' => v :: (nats_h n' (S v))
  end.

Definition nats n := nats_h n 0.

Theorem toN_int_excl_length : forall n, 
  List.length (toN_excl_int n) = n.

  induction n; intuition idtac; simpl in *.

  rewrite app_length.
  rewrite IHn.
  simpl.
  lia.

Qed.

Theorem toN_int_length : forall n, 
  List.length (toN_int n) = (S n).

  intros.
  unfold toN_int.
  rewrite app_length.
  rewrite toN_int_excl_length.
  simpl.
  lia.

Qed.

Theorem shiftL1_shiftL : forall (A : Type) n (b : A) v n1,
  (shiftL1 n _ b (shiftL n _ b v n1)) = shiftL n _ b v (S n1).

  induction n1; intros; simpl in *.
  reflexivity.
  reflexivity.

Qed.

Theorem shiftL_shiftL1 : forall (A : Type) n (b : A) v n1,
  (shiftL n _ b (shiftL1 n _ b v) n1) = shiftL n _ b v (S n1).

  induction n1; intros; simpl in *.
  reflexivity.
  rewrite IHn1.
  reflexivity.

Qed.

Theorem shiftL_shiftL : forall (A : Type) n (b : A) v n1 n2,
  (shiftL n _ b (shiftL n _ b v n1) n2) = shiftL n _ b v (n1 + n2).

  induction n1; intros; simpl in *; trivial.
  rewrite shiftL_shiftL1.
  rewrite IHn1.
  rewrite shiftL1_shiftL.
  f_equal.
  lia.

Qed.


Theorem forall2_symm : forall (A B : Type)(P : B -> A -> Prop) lsa lsb,
  List.Forall2 (fun a b => P b a) lsa lsb ->
  List.Forall2 P lsb lsa.

  induction 1; intros;
  econstructor; eauto.

Qed.

Theorem forall2_trans : forall ( A B C : Type)(R1 : A -> B -> Prop)(R2 : B -> C -> Prop)(R3 : A -> C -> Prop)
  lsa lsb lsc,
  List.Forall2 R1 lsa lsb ->
  (forall a b c, R1 a b -> R2 b c -> R3 a c) ->
  List.Forall2 R2 lsb lsc ->
  List.Forall2 R3 lsa lsc.

  induction lsa; intuition; simpl in *.
  inversion H; subst.
  inversion H1; subst.
  econstructor.

  inversion H; subst.
  inversion H1; subst.
  econstructor.
  eauto.
  eapply IHlsa; eauto.

Qed.

Theorem forall2_eq : forall (A : Type)(ls1 ls2 : list A),
  ls1 = ls2 ->
  List.Forall2 eq ls1 ls2.

  induction ls1; intros; simpl in *; subst.
  econstructor.

  econstructor; trivial.
  eauto.

Qed.

Theorem forall2_map_eq : forall (A B : Type)(f : B -> A) lsa lsb,
  List.Forall2 (fun a b => a = f b) lsa lsb ->
  lsa = List.map f lsb.

  induction 1; intros; simpl in *; trivial.
  congruence.

Qed.


Theorem fold_left_unroll_one : forall (A B : Type) def (f : A -> B -> A) (ls : list B) a,
  (List.length ls > 0)%nat ->
  List.fold_left f ls a = List.fold_left f (List.tl ls) (f a (List.hd def ls)).

  destruct ls; intros; simpl in *.
  lia.
  reflexivity.

Qed.

Theorem fold_left_R : forall (A1 A2 B1 B2 : Type)(RA : A1 -> A2 -> Prop)(RB : B1 -> B2 -> Prop)(f1 : A1 -> B1 -> A1)(f2: A2 -> B2 -> A2) ls1 ls2 a1 a2,
  RA a1 a2 ->
  List.Forall2 RB ls1 ls2 ->
  (forall a1 a2 b1 b2, RA a1 a2 -> RB b1 b2 -> In b1 ls1 -> In b2 ls2 -> RA (f1 a1 b1) (f2 a2 b2)) ->
  RA (List.fold_left f1 ls1 a1) (List.fold_left f2 ls2 a2).

  induction ls1; destruct ls2; intros; simpl in *; trivial.
  inversion H0.
  inversion H0.
  inversion H0; subst; clear H0.
  eapply IHls1.
  eapply H1; eauto.
  trivial.
  eauto.

Qed.

Theorem hd_rev_eq_last : forall (A : Type)(ls : list A)(def : A),
  List.hd def (List.rev ls) = List.last ls def.

  induction ls using rev_ind; intros; simpl in *; trivial.
  rewrite rev_unit.
  simpl.
  rewrite last_last.
  reflexivity.
Qed.

Theorem fold_left_scanl_app_equiv : forall (A B : Type) (f : A -> B -> A) ls def a1 a2,
  a2 <> List.nil ->
  List.fold_left
(fun (x : list A) (y : B) =>
 x ++ [f (List.last x def) y]) ls 
(List.cons a1 a2) =
  a1 :: (List.fold_left (fun (x : list A) (y : B) =>
 x ++ [f (List.last x def) y]) ls 
a2 ).

  induction ls; intros; simpl in *; trivial.
  rewrite (@IHls _ a1).
  destruct a2.
  intuition idtac.
  reflexivity.
  f_equal.
  intuition idtac.
  apply app_eq_nil in H0.
  intuition idtac.

Qed.

Theorem fold_left_scanl_equiv : forall (A B : Type) def (f : A -> B -> A) ls a,
  List.fold_left (fun x y => x ++ (f (List.last x def) y)::List.nil) ls [a] = 
  CryptolToCoq_equiv.scanl f ls a.

  induction ls; intros; simpl in *; trivial.
  rewrite <- IHls.
  rewrite fold_left_scanl_app_equiv.
  reflexivity.
  congruence.
Qed.

Theorem Forall2_scanl : forall (A1 A2 B1 B2 : Type)(PA : A1 -> A2 -> Prop)(PB : B1 -> B2 -> Prop)
  (f1 : A1 -> B1 -> A1)(f2 : A2 -> B2 -> A2) ls1 ls2 a1 a2,
  List.Forall2 PB ls1 ls2 ->
  (forall a1 a2 b1 b2, PA a1 a2 -> PB b1 b2 -> PA (f1 a1 b1) (f2 a2 b2)) ->
  PA a1 a2 ->
  List.Forall2 PA (scanl f1 ls1 a1) (scanl f2 ls2 a2).

  induction ls1; destruct ls2; simpl in *; intros.
  econstructor; eauto.
  inversion H.
  inversion H.
  inversion H; clear H; subst.
  econstructor; eauto.

Qed.

Theorem Forall2_I : forall (A B : Type)(ls1 : list A)(ls2 : list B),
  List.length ls1 = List.length ls2 ->
  List.Forall2 (fun a b => True) ls1 ls2.

  induction ls1; destruct ls2; intros; simpl in *; try lia.
  econstructor.
  econstructor; eauto; econstructor.

Qed.

Theorem Forall2_nth_lt : forall (A B : Type)(P : A -> B -> Prop) lsa lsb,
  List.Forall2 P lsa lsb ->
  forall n defA defB,
  (n < List.length lsa)%nat ->
  P (List.nth n lsa defA) (List.nth n lsb defB).

  induction 1; intros; simpl in *.
  destruct n; try lia.
  destruct n; trivial.
  eapply IHForall2; trivial; lia.

Qed.

Theorem skipn_1_eq_tl : forall (A : Type)(ls : list A),
  skipn 1 ls = List.tl ls.

  intros.
  destruct ls; trivial.

Qed.

Theorem Forall2_tl : forall (A B : Type)(P : A -> B -> Prop) ls1 ls2,
  List.Forall2 P ls1 ls2 ->
  List.Forall2 P (List.tl ls1) (List.tl ls2).

  intros.
  inversion H; clear H; subst;
  simpl.
  econstructor.
  trivial.

Qed.

Theorem Forall2_rev : forall (A B : Type)(P : A -> B -> Prop) ls1 ls2,
  List.Forall2 P ls1 ls2 ->
  List.Forall2 P (List.rev ls1) (List.rev ls2).

  induction 1; intros; simpl in *.
  econstructor.
  eapply Forall2_app.
  eauto.
  econstructor.
  trivial.  
  econstructor.

Qed.


Theorem bvXor_cons : forall n x y u v,
  bvXor (S n) (Vector.cons u x) (Vector.cons v y) = 
  Vector.cons (xor u v) (bvXor _ x y).

  intros.
  reflexivity.

Qed.


Theorem replicate_S_cons : forall (A : Type) n (a : A),
  replicate (S n) _ a = Vector.cons a (replicate n _ a).

  intros.
  reflexivity.

Qed.


Theorem addb_same_l : forall n (x y1 y2 : spec.BITS n),
  y1 = y2 ->
  addB x y1 = addB x y2.

  intros. subst. trivial.
Qed.

Theorem zipWith_cons : forall (A B C: Type)(inha : Inhabited A)(inhb : Inhabited B) f n (v1 : Vec n A)(v2 : Vec n B) a b,
  zipWith A B C f _ (Vector.cons a v1) (Vector.cons b v2) = Vector.cons (f a b) (zipWith A B C f _ v1 v2).

  intros.
  reflexivity.

Qed.


Theorem zipWith_comm : forall (A B : Type)(inha : Inhabited A) (f : A -> A -> B) n (v1 v2 : Vec n A),
  (forall a1 a2, f a1 a2 = f a2 a1) ->
  zipWith A A B f n v1 v2 = zipWith A A B f n v2 v1.

  induction n; intros; simpl in *.
  apply vec_0_eq.

  destruct (Vec_S_cons _ _  v1).
  destruct H0.
  destruct (Vec_S_cons _ _ v2).
  destruct H1.  
  subst.
  repeat rewrite zipWith_cons.
  f_equal; eauto.

Qed.

Theorem bits_cons_decomp : forall (n : nat) (v : spec.BITS (S n)), 
  exists (b : bool) (v' : spec.BITS n), v = spec.consB b v'.

  intros.
  exists (tuple.thead v).
  exists (tuple.behead_tuple v).
  unfold spec.consB.
  apply tuple.tuple_eta.

Qed.


Definition bitsToBv_ls (ls : list bool) := rev ls.

Definition bitsToBv_ls_0 size := 
tuple_foldl_dep bool (fun n : Nat => list bool) size
  (fun (n : Nat) ls (b : bool) => b::ls) (@nil bool).

Theorem tuple_S_ex : forall (A : Type) n (t : tuple.tuple_of (S n) A),
  exists a (t' : tuple.tuple_of n A),
  t = tuple.cons_tuple a t'.

  intros.
  exists (tuple.thead t).
  exists (tuple.behead_tuple t).
  apply tuple.tuple_eta.

Qed.

Theorem tuple_head_cons : forall (A: Type) n x (x0 : tuple.tuple_of n A),
  (tuple.thead (tuple.cons_tuple x x0)) = x.

  intros.
  apply tuple.theadCons.

Qed.

Theorem tuple_behead_cons : forall (A: Type) n x (x0 : tuple.tuple_of n A),
  (tuple.behead_tuple (tuple.cons_tuple x x0)) = x0.

  intros.
  apply tuple.beheadCons.

Qed.

Theorem tuple_tval_cons : forall (A: Type) n x (x0 : tuple.tuple_of n A),
  (tuple.tval (tuple.cons_tuple x x0)) = x :: (tuple.tval x0).

  intros.
  reflexivity.

Qed.

Theorem tuple_foldl_dep_conv_const_equiv : forall (A : Type) n (v : tuple.tuple_of n A)
  (B1 : nat -> Type)(B2 : Type)
  (conv : forall n, B1 n -> B2) b1
  (f1 : forall (n : nat), B1 n -> A -> B1 (S n))(f2 : B2 -> A -> B2),
  (forall n b a, conv _ (f1 n b a) = f2 (conv _ b) a) ->
  conv _ (tuple_foldl_dep A B1 n f1 b1 v) = tuple_foldl_dep A (fun _ => B2) n (fun _ => f2) (conv _ b1) v.

  induction n; intros; simpl in *; trivial.
  destruct (tuple_S_ex v).
  destruct H0.
  subst.
  
  specialize (IHn x0).
  specialize (IHn (fun n => B1 (S n)) B2).
  specialize (IHn (fun n => conv (S n))).
  specialize (IHn (f1 _ b1 x)).
  
  specialize (IHn (fun n0 : nat => f1 (S n0)) f2).
  simpl in *.
  unfold Nat in *.
  rewrite tuple_head_cons.
  rewrite tuple_behead_cons.
  rewrite IHn.
  rewrite H.
  reflexivity.

  intros.
  eapply H.

Qed.

Theorem tuple_fold_dep_ls_equiv : forall (A : Type) n (v : tuple.tuple_of n A)
  (B : Type)(f : B -> A -> B) b,
  tuple_foldl_dep A (fun _ => B) n (fun _ => f) b v = fold_left f (tuple.tval v) b.

  induction n; intros.
  simpl in *.
  destruct v.
  destruct tval; simpl in *; trivial.
  inversion i.

  destruct (tuple_S_ex v).
  destruct H.
  subst.
  simpl.
  rewrite tuple_behead_cons.
  rewrite tuple_head_cons.
  rewrite IHn.
  reflexivity.

Qed.

Theorem bitsToBv_ls_0_eq : forall n (bs : spec.BITS n),
  bitsToBv_ls_0 bs = to_list (bitsToBv bs).

  intros.
  symmetry.
  unfold bitsToBv_ls_0, bitsToBv.
  specialize (tuple_foldl_dep_conv_const_equiv bs (Vector.t bool) (@to_list bool)); intros.
  simpl in *.
  erewrite H.
  replace (to_list (Vector.nil Bool)) with (@nil bool).
  reflexivity.
  reflexivity.
  intros. simpl.
  rewrite to_list_cons.
  reflexivity.

Qed.

Theorem bitsToBv_ls_eq : forall n (bs : spec.BITS n),
  bitsToBv_ls (tuple.tval bs) = to_list (bitsToBv bs).

  intros.
  rewrite <- bitsToBv_ls_0_eq.

  unfold bitsToBv_ls_0, bitsToBv_ls.
  rewrite tuple_fold_dep_ls_equiv.
  generalize (tuple.tval bs) as ls.
  induction ls using rev_ind; intros; simpl in *; trivial.
  rewrite rev_app_distr.
  simpl.
  rewrite IHls.
  rewrite fold_left_app.
  simpl.
  reflexivity.

Qed.


Fixpoint zipWith_ls (A B C : Type)(f : A -> B -> C)(lsa : list A)(lsb : list B) :=
  match lsa with 
    | nil => nil
    | a :: lsa' =>
      match lsb with
      | nil => nil
      | b :: lsb' =>
      (f a b) :: (zipWith_ls f lsa' lsb')
      end
    end.

Definition bvAnd_ls :=
  zipWith_ls and.

Theorem zipWith_nil : forall (A B C : Type)(inha : Inhabited A)(inhb : Inhabited B) (f : A -> B -> C),
  zipWith _ _ _ f _ (@Vector.nil A) (Vector.nil B) = (@Vector.nil C).

  intros.
  reflexivity.

Qed.

Theorem zipWith_ls_eq : forall (A B C : Type)(inha : Inhabited A)(inhb : Inhabited B) n (lsa : Vec n A)(lsb : Vec n B)(f : A -> B -> C),
  to_list (zipWith _ _ _ f _ lsa lsb) =zipWith_ls f (to_list lsa) (to_list lsb).

  induction lsa; intros.
  simpl in *.
  specialize (Vec_0_nil _ lsb0); intros.
  subst.
  rewrite zipWith_nil.
  trivial.

  destruct (Vec_S_cons _ _ lsb0).
  destruct H.
  subst.
 repeat  rewrite to_list_cons.
  simpl.
  rewrite zipWith_cons.
  rewrite to_list_cons.
  f_equal.
  eauto.

Qed.


Theorem tuple_map_eq : forall (A B : Type) (f : A -> B) n (t : tuple.tuple_of n A),
  tuple.tval (tuple.map_tuple f t) = map f (tuple.tval t).

  induction n; intros; simpl in *.
  destruct t.
  destruct tval.
  simpl.
  reflexivity.
  inversion i.

  destruct (tuple_S_ex t).
  destruct H.
  subst.
  simpl.
  f_equal.
Qed.



Theorem tuple_zip_eq : forall (A B : Type) n (t1 : tuple.tuple_of n A)(t2 : tuple.tuple_of n B),
  tuple.tval (tuple.zip_tuple t1 t2) = combine (tuple.tval t1) (tuple.tval t2).

  induction n; intros; simpl in *.
  destruct t1.
  destruct t2.
  destruct tval.
  destruct tval0.
  simpl.
  reflexivity.
  inversion i0.
  inversion i.

  destruct (tuple_S_ex t1).
  destruct H.
  destruct (tuple_S_ex t2).
  destruct H0.
  subst.
  simpl.
  f_equal.
  eapply IHn.

Qed.

Theorem zipWith_ls_eq_map : forall (A B C : Type)(f : A -> B -> C) ls1 ls2,
  (length ls1 = length ls2) ->
  zipWith_ls f ls1 ls2 = map (fun p => f (fst p) (snd p)) (combine ls1 ls2).

  induction ls1; intros; simpl in *; trivial.
  destruct ls2; simpl in *; try lia.
  f_equal.
  eapply IHls1.
  lia.

Qed.

Theorem combine_app_eq : forall (A B : Type)(lsa1 lsa2 : list A)(lsb1 lsb2 : list B),
  length lsa1 = length lsb1 ->
  combine (lsa1 ++ lsa2)  (lsb1 ++ lsb2) = (combine lsa1 lsb1) ++ (combine lsa2 lsb2).

  induction lsa1; destruct lsb1; intros; simpl in *; trivial; try lia.
  f_equal.
  eapply IHlsa1.
  lia.

Qed.

Theorem combine_rev_eq : forall (A B : Type)(ls1 : list A)(ls2 : list B),
  length ls1 = length ls2 ->
  rev (combine ls1 ls2) = combine (rev ls1) (rev ls2).

  induction ls1; destruct ls2; intros; simpl in *; trivial; try lia.
  rewrite IHls1.
  rewrite combine_app_eq.
  reflexivity.
  repeat rewrite rev_length.
  lia.
  lia.

Qed.

Theorem seq_size_eq_length : forall (A : Type)(ls : list A),
  seq.size ls = List.length ls.

  induction ls; intros; simpl in *; trivial.

Qed.

Theorem tuple_tval_length : forall (A : Type) n  (t : tuple.tuple_of n A),
  length (tuple.tval t) = n.

  intros.
  destruct t.
  unfold is_true in *.  
  simpl.
  
  rewrite eqtype.eqE in i.
  simpl in *.
  specialize (@ssrnat.eqnP (seq.size tval) n); intros.
  inversion H.
  rewrite seq_size_eq_length in H1.
  trivial.
  congruence.

Qed.

Theorem toList_append_equiv : forall A (inh : Inhabited A) n m (v1 : Vec n A)(v2 : Vec m A),
  to_list (SAWCorePrelude.append v1 v2) = 
  List.app (to_list v1) (to_list v2).

  induction n; intros; simpl in *.
  
  rewrite (Vec_0_nil _ v1).
  simpl.
  rewrite append_nil_eq.
  reflexivity.

  destruct (Vec_S_cons _ _ v1). destruct H. subst.
  rewrite append_cons.
  repeat rewrite to_list_cons.
  rewrite IHn.
  simpl.
  reflexivity.

Qed.

Theorem shiftout_cons : forall (A : Type)(a : A) n (v : Vec (S n) A),
  shiftout (Vector.cons a v) = Vector.cons a (shiftout v).

  intros.
  reflexivity.

Qed.

Theorem shiftR1_false_0 : forall n1, 
    (shiftR1 n1 bool false (replicate n1 bool false)) = (replicate n1 bool false).

  induction n1; intros; simpl in *.
  apply vec_0_eq.

  repeat rewrite replicate_S_cons.
  unfold shiftR1.
  rewrite shiftout_cons.
  f_equal.
  eapply IHn1.

Qed.

Theorem shiftR_false_0 : forall n2 n1, 
    (shiftR n1 bool false (replicate n1 bool false) n2) = (replicate n1 bool false).

  induction n2; intros; simpl in *; trivial.
  rewrite IHn2.
  eapply shiftR1_false_0.

Qed.

Theorem replicate_repeat_eq : forall n (A  : Type)(v : A),
  repeat v n = to_list (replicate n A v).

  induction n; intros; simpl in *.
  rewrite (Vec_0_nil _ (replicate 0%nat A v)).
  reflexivity.
  rewrite replicate_S_cons.
  rewrite to_list_cons.
  f_equal.
  eauto.

Qed.

Definition shiftout_ls (A : Type)(ls : list A):=
  (firstn (pred (length ls)) ls).

Definition shiftR1_ls (A : Type)(a : A)(ls : list A) :=
  shiftout_ls (cons a ls).

Theorem shiftR1_ls_equiv : forall (A : Type) n  (v : Vector.t A n) a,
  to_list (shiftR1 n A a v) = shiftR1_ls a (to_list v).

  induction v; intros; simpl in *.
  reflexivity.

  unfold shiftR1 in *.
  rewrite shiftout_cons.
  rewrite to_list_cons.
  rewrite IHv.
  reflexivity.

Qed.

Definition shiftR_ls (A : Type) (x : A) (v :list A) (i : nat) := 
  ssrnat.iter i (shiftR1_ls x) v.

Theorem shiftR_ls_equiv : forall (A : Type) n2  n (v : Vector.t A n) a,
  to_list (shiftR n A a v n2) = shiftR_ls a (to_list v) n2.

  induction n2; intros; simpl in *; trivial.

  rewrite shiftR1_ls_equiv.
  rewrite IHn2.
  reflexivity.

Qed.

Theorem shiftR1_ls_length : forall (A: Type) a (ls : list A),
  length (shiftR1_ls a ls) = length ls.

  intros.
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  rewrite firstn_length.
  simpl.
  lia.

Qed.

Theorem shiftR_ls_length : forall (A: Type) a n (ls : list A),
  length (shiftR_ls a ls n) = length ls.

  induction n; intros; simpl in *; trivial.
  rewrite shiftR1_ls_length.
  eapply IHn.

Qed.

Theorem firstn_app_1 : forall (A : Type)(ls1 ls2 : list A) n,
  (n <= length ls1)%nat -> 
  firstn n (ls1 ++ ls2) = firstn n ls1.

  induction ls1; intros; destruct n; simpl in *; trivial.
  lia.
  f_equal.
  eapply IHls1.
  lia.

Qed.

Theorem shiftR1_ls_firstn : forall (A : Type) n (ls : list A) a,
  (n <= length ls)%nat ->
  firstn n (shiftR1_ls a ls) = shiftR1_ls a (firstn n ls).

  intros. 
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  rewrite firstn_length.
  rewrite Nat.min_l; trivial.
  rewrite firstn_firstn.
  rewrite Nat.min_l; trivial.
  destruct n.
  simpl in *; trivial.
  repeat rewrite firstn_cons.
  f_equal.
  rewrite firstn_firstn.
  rewrite Nat.min_l; trivial; lia.

Qed.


Theorem shiftR_ls_firstn : forall (A : Type) n2 n (ls : list A) a,
  (n <= length ls)%nat ->
  firstn n (shiftR_ls a ls n2) = shiftR_ls a (firstn n ls) n2.

  induction n2; intros; simpl in *; trivial.
  rewrite shiftR1_ls_firstn.
  rewrite IHn2.
  reflexivity.
  trivial.
  rewrite shiftR_ls_length.
  trivial.

Qed.


Theorem shiftR_ls_eq_repeat : forall (A : Type) n (ls : list A) a,
  (n <= length ls)%nat -> 
  shiftR_ls a ls n = (repeat a n) ++ (firstn (length ls - n)%nat ls).

  induction n; intros; simpl in *.
  rewrite Nat.sub_0_r.
  rewrite firstn_all. reflexivity.
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  rewrite shiftR_ls_length.

  destruct ls using rev_ind.
  simpl in *. lia.
  rewrite app_length.
  simpl.
  rewrite plus_comm.
  simpl.
  f_equal.
  rewrite firstn_app_1; try lia.
  rewrite <- IHn.
  rewrite shiftR_ls_firstn.
  rewrite firstn_app_1; try lia.
  rewrite firstn_all.
  reflexivity.
  rewrite app_length.
  lia.
  rewrite app_length in H.
  simpl in *. lia.
Qed.

Definition joinlsb_ls(pair : (list bool) * bool) := (snd pair) :: (fst pair).

Theorem foldl_dep_conv_const_equiv : forall (A : Type) n (v : Vec n A)
  (B1 : nat -> Type)(B2 : Type)
  (conv : forall n, B1 n -> B2) b1
  (f1 : forall (n : nat), B1 n -> A -> B1 (S n))(f2 : B2 -> A -> B2),
  (forall n b a, conv _ (f1 n b a) = f2 (conv _ b) a) ->
  conv _ (foldl_dep A B1 n f1 b1 v) = foldl_dep A (fun _ => B2) n (fun _ => f2) (conv _ b1) v.

  induction v; intros; simpl in *.
  trivial.
  specialize (IHv (fun n => B1 (S n)) B2).
  specialize (IHv (fun n => conv (S n))).
  specialize (IHv (f1 _ b1 h)).
  
  specialize (IHv (fun n0 : nat => f1 (S n0)) f2).
  simpl in *.
  unfold Nat in *.
  rewrite IHv.
  rewrite H.
  reflexivity.

  intros.
  eapply H.

Qed.

Theorem fold_dep_ls_equiv : forall (A : Type) n (v : Vec n A)
  (B : Type)(f : B -> A -> B) b,
  foldl_dep A (fun _ => B) n (fun _ => f) b v = fold_left f (to_list v) b.

  induction v; intros.
  simpl in *.
  trivial.
  rewrite to_list_cons.
  simpl.
  rewrite IHv.
  reflexivity.

Qed.


Definition bvToBITS_ls_0 n (bs : Vec n bool) :=
  fold_left (fun (bs : list bool) (b : bool) => b ::bs)(to_list  bs) nil.


Theorem bvToBITS_ls_0_equiv : forall n (bs : Vec n bool),
  tuple.tval (bvToBITS bs) = bvToBITS_ls_0 bs.

  intros.
  unfold bvToBITS, bvToBITS_ls_0.
  rewrite <- fold_dep_ls_equiv.
  specialize (foldl_dep_conv_const_equiv bs spec.BITS (fun n b => tuple.tval b)); intros.
  simpl in *.
  eapply H.
  intros.
  simpl.
  reflexivity.
Qed.

Definition bvToBITS_ls n (bs : Vec n bool) := rev (to_list bs).

Theorem bvToBITS_ls_0_equiv' : forall n (bs : Vec n bool),
  bvToBITS_ls_0 bs = bvToBITS_ls bs.

  intros. 
  unfold bvToBITS_ls_0, bvToBITS_ls.
  generalize (to_list bs) as ls.
  induction ls using rev_ind; intros; simpl in *.
  reflexivity.

  rewrite rev_app_distr.
  rewrite fold_left_app.
  simpl.
  f_equal.
  eauto.

Qed.

Theorem bvToBITS_ls_equiv : forall n (bs : Vec n bool),
  tuple.tval (bvToBITS bs) = bvToBITS_ls bs.

  intros.
  rewrite bvToBITS_ls_0_equiv.
  rewrite bvToBITS_ls_0_equiv'.
  reflexivity.
Qed.

Definition splitmsb_ls(ls : list bool):=
  match (seq.rev ls) with
  | nil => (false, nil)
  | b :: ls' => (b, seq.rev ls')
  end.

Definition toPosZ_ls bs :=
  seq.foldr (fun (b : bool) (z : Z) => if b then Z.succ (Z.double z) else Z.double z) 0 bs.

Definition toNegZ_ls bs :=
  seq.foldr (fun (b : bool) (z : Z) => if b then Z.double z else Z.succ (Z.double z)) 0 bs.

Definition toZ_ls bs :=
  let (b, bs') := splitmsb_ls bs in if b then - Z.succ (toNegZ_ls bs') else toPosZ_ls bs'.


Definition sbvToInt_ls n (v : Vec n bool) :=
  (match n as n0 return (bitvector n0 -> Z) with
    | 0%nat => fun _ : bitvector 0 => 0
    | S n0 => fun b0 : bitvector (S n0) => toZ_ls (bvToBITS_ls b0)
  end) v.

Theorem splitmsb_ls_eq : forall n (b : spec.BITS (S n)),
  splitmsb_ls (tuple.tval b)  = 
    let p :=
      (spec.splitmsb b) in (fst p, (tuple.tval (snd p))).

  intros.
  remember (spec.splitmsb b) as z.
  destruct z.
  symmetry in Heqz.
  apply splitmsb_rev in Heqz.
  simpl.
  unfold splitmsb_ls.
  rewrite Heqz.
  rewrite seq.revK.
  reflexivity.
Qed.

Theorem toZ_ls_eq : forall n (b : spec.BITS (S n)),
  toZ_ls (tuple.tval b) = spec.toZ b.

  intros.
  unfold toZ_ls, spec.toZ.
  rewrite splitmsb_ls_eq.
  remember (spec.splitmsb b) as z.
  destruct z.
  simpl.
  destruct b0.
  reflexivity.
  reflexivity.

Qed.

Theorem sbvToInt_ls_equiv : forall n (v : Vec n bool),
  sbvToInt_ls v = sbvToInt n v.

  intros.
  destruct n; simpl in *; trivial.
  rewrite <- toZ_ls_eq.
  rewrite bvToBITS_ls_equiv.
  reflexivity.

Qed.

Theorem seq_rev_eq : forall (A : Type)(ls : list A),
  seq.rev ls = rev ls.

  induction ls; intros; simpl in *; trivial.
  rewrite <- IHls.
  rewrite seq.rev_cons.
  rewrite <- seq.cats1.
  reflexivity.

Qed.

Theorem toNegZ_ls_nonneg : forall ls,
  0 <= toNegZ_ls ls.

  induction ls; intros; simpl in *.
  lia.
  destruct a; simpl in *; lia.

Qed.

Theorem nonneg_sign_bit_clear :  forall n v h,
  0 <= sbvToInt (S n) (VectorDef.cons h v) ->
  h = false.

  intros. 
  rewrite <- sbvToInt_ls_equiv in *.
  simpl in *.
  unfold bvToBITS_ls in *.
  rewrite to_list_cons in H.
  simpl in *.
  
  unfold toZ_ls in *.
  unfold splitmsb_ls in *.
  rewrite seq_rev_eq in *.
  rewrite rev_app_distr in H.
  rewrite rev_involutive in *.
  simpl in *.
  destruct h; simpl in *; trivial.
  match goal with 
  | [H: 0 <= - Z.succ (toNegZ_ls ?a) |- _] =>
    remember a as z
  end.
  specialize (toNegZ_ls_nonneg z); intros.
  lia.
Qed.


Theorem shiftR_all_nonneg : forall n1 v,
  n1 <> O ->
  (0 <= sbvToInt _ v)%Z ->
  (shiftR n1 bool false v (pred n1)) = replicate n1 bool false.

  intros.
  apply eq_if_to_list_eq.
  rewrite <- replicate_repeat_eq.
  rewrite shiftR_ls_equiv.
  rewrite shiftR_ls_eq_repeat.
  match goal with 
  | [|- context[ (?a - ?b)%nat]] =>
  replace (a - b)%nat with 1%nat
  end.
  destruct v; simpl; trivial.
  erewrite (nonneg_sign_bit_clear _ h); eauto.
  replace [false] with (repeat false 1%nat); trivial.
  rewrite <- repeat_app.
  rewrite plus_comm.
  trivial.
  rewrite length_to_list.
  lia.
  rewrite length_to_list.
  lia.

Qed.

Definition zero_ls n := repeat false n.


Fixpoint fromPosZ_ls n z :=
  match n with
    | 0%nat => nil
    | S n0 => joinlsb_ls (fromPosZ_ls n0 (Z.div2 z), negb (Z.even z))
  end.

Fixpoint fromNegZ_ls n z :=
  match n with
    | 0%nat => nil
    | S n0 => joinlsb_ls (fromNegZ_ls n0 (Z.div2 z), Z.even z)
  end.

Definition fromZ_ls n z :=
  match z with
     | 0 => zero_ls n
     | Z.pos _ => fromPosZ_ls n z
     | Z.neg _ => fromNegZ_ls n (Z.pred (- z))
   end.

Definition intToBv_ls n z:=
  bitsToBv_ls (fromZ_ls n z).

Theorem tuple_nseq_ls_eq : forall n (A : Type) (a: A), 
  repeat a n = tuple.tval (tuple.nseq_tuple n a).

  induction n; intros; simpl in *; trivial.

  f_equal; eauto.

Qed.

Theorem zero_ls_eq : forall n,
  zero_ls n = tuple.tval (spec.zero n).

  intros.
  eapply tuple_nseq_ls_eq.
Qed.

Theorem fromPosZ_ls_eq : forall n z,
  fromPosZ_ls n z = tuple.tval (@spec.fromPosZ n z).

  induction n; intros; simpl in *; trivial.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  eauto.

Qed.

Theorem fromNegZ_ls_eq : forall n z,
  fromNegZ_ls n z = tuple.tval (@spec.fromNegZ n z).

  induction n; intros; simpl in *; trivial.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  eauto.

Qed.

Theorem fromZ_ls_eq : forall n z,
  fromZ_ls n z = tuple.tval (@spec.fromZ n z).

  intros.
  unfold fromZ_ls, spec.fromZ.
  destruct z.
  apply zero_ls_eq.
  apply fromPosZ_ls_eq.
  apply fromNegZ_ls_eq.

Qed.

Theorem intToBv_ls_eq : forall n z,
  intToBv_ls n z = to_list (intToBv n z).

  intros.
  unfold intToBv, intToBv_ls.
  rewrite <- bitsToBv_ls_eq.
  f_equal.
  apply fromZ_ls_eq.

Qed.

Theorem fromPosZ_ls_0_eq : forall n,
  fromPosZ_ls n 0 = repeat 0%bool n.

  induction n; intros; simpl in *; trivial.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  eauto.

Qed.

Theorem fromZ_ls_1_eq :  forall n,
  fromZ_ls (S n) 1 = true :: repeat false n.

  intros.
  unfold fromZ_ls.
  simpl.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  apply fromPosZ_ls_0_eq.

Qed.

Theorem repeat_S_rev : forall (A : Type) n (a : A),
  repeat a (S n) = (repeat a n) ++ [a].

  induction n; intros; simpl in *; trivial.
  f_equal.
  eauto.

Qed.

Theorem rev_repeat_id : forall (A : Type) n (a : A),
  rev (repeat a n) = repeat a n.

  induction n; intros; simpl in *; trivial.
  rewrite IHn.
  destruct n.
  simpl in *; trivial.
  rewrite repeat_S_rev at 2.
  simpl.
  reflexivity.

Qed.

Theorem intToBv_1_to_list_eq : forall n, 
  to_list (intToBv (S n) 1) = repeat 0%bool n ++ [true].

  intros.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls.
  unfold bitsToBv_ls.
  rewrite fromZ_ls_1_eq.
  simpl.
  rewrite rev_repeat_id.
  reflexivity.

Qed.

Theorem intToBv_0_eq_replicate : forall n,
    intToBv n 0 = replicate n bool false.

  intros.
  apply eq_if_to_list_eq.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls.
  simpl.
  unfold bitsToBv_ls, zero_ls.
  rewrite rev_repeat_id.
  rewrite replicate_repeat_eq.
  reflexivity.

Qed.


Definition shiftin_ls(A : Type) a (ls : list A) :=
  ls ++ [a].

Definition shiftL1_ls (A : Type) (a : A) (ls : list A) :=
  tl (shiftin_ls a ls).

Definition shiftL_ls (A : Type) (x : A) (v : list A) (i : nat) := ssrnat.iter i (shiftL1_ls x) v.

Theorem shiftin_ls_eq : forall n (A : Type) a (ls : Vec n A),
  to_list (shiftin a ls) = shiftin_ls a (to_list ls).

  intros.
  induction ls; intros; simpl in *.
  rewrite to_list_cons.
  reflexivity.

  rewrite to_list_cons.
  rewrite IHls.
  unfold shiftin_ls.
  rewrite to_list_cons.
  rewrite app_comm_cons.
  reflexivity.

Qed.

Theorem shiftL1_ls_eq : forall n (A : Type) a (ls : Vec n A),
  to_list (shiftL1 n A a ls) = shiftL1_ls a (to_list ls).

  intros.
  unfold shiftL1, shiftL1_ls.
  rewrite to_list_tl.
  f_equal.
  apply shiftin_ls_eq.
  
Qed.


Theorem shiftL_to_list_eq : forall n n1 (A : Type)(a : A)(ls : Vec n A),
  to_list (shiftL n A a ls n1) = shiftL_ls a (to_list ls) n1.

  induction n1; intros; simpl in *; trivial.
  rewrite shiftL1_ls_eq.
  f_equal.
  eapply IHn1.

Qed.

Theorem shiftR1_ls_comm: forall (A : Type) (a : A) ls n1,
  shiftR1_ls a (shiftR_ls a ls n1) = shiftR_ls a (shiftR1_ls a ls) n1.

  induction n1; intros; simpl in *; trivial.
  rewrite IHn1.
  reflexivity.

Qed.

Theorem shiftR1_app_repeat_eq : forall n1 (A : Type)(a b : A) ls,
  (n1 > 0)%nat ->
  shiftR1_ls a (ls ++ repeat b n1) = (a :: ls ++ repeat b (pred n1)).

  intros.
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  rewrite app_length. 

  destruct n1.
  simpl in *; lia.

  rewrite repeat_S_rev at 2.
  simpl.
  rewrite plus_comm.
  simpl.
  f_equal.
  rewrite plus_comm.
  rewrite app_assoc.
  rewrite firstn_app_1.
  rewrite <- app_length.
  apply firstn_all.
  rewrite app_length.
  lia.

Qed.

Theorem shiftout_ls_app_rev : forall (A : Type)(ls : list A) a,
  shiftout_ls (ls ++ [a]) = ls.

  intros.
  unfold shiftout_ls.
  rewrite app_length.
  rewrite plus_comm.
  simpl.
  rewrite firstn_app_1.
  apply firstn_all.
  lia.

Qed.

Theorem splitmsb_ls_app_eq : forall ls a,
  splitmsb_ls (ls ++ [a])  = (a, ls).

  intros.
  unfold splitmsb_ls.
  rewrite seq_rev_eq.
  rewrite rev_app_distr.
  simpl.
  rewrite seq_rev_eq.
  rewrite rev_involutive.
  reflexivity.

Qed.

Theorem toPosZ_app_0_eq : forall ls,
  toPosZ_ls (ls ++ [0%bool]) = toPosZ_ls ls.

  induction ls; intros; simpl in *; trivial.
  destruct a.
  rewrite IHls.
  reflexivity.
  rewrite IHls.
  reflexivity.

Qed.

Theorem toPosZ_app_repeat_0_eq : forall n ls,
  toPosZ_ls (ls ++ (repeat false n)) = toPosZ_ls ls.

  induction n; intros; simpl in *.
  rewrite app_nil_r.
  reflexivity.
  replace (ls ++ 0%bool :: repeat 0%bool n)  with ((ls ++ [false]) ++ repeat 0%bool n).
  rewrite IHn.
  apply toPosZ_app_0_eq.
  rewrite <-  app_assoc.
  reflexivity.

Qed.


Theorem toPosZ_cons_0_eq : forall ls,
  toPosZ_ls (0%bool :: ls) = Z.double (toPosZ_ls ls).

  reflexivity.
Qed.

Theorem toZ_ls_shiftR1_ls_eq : forall ls,
  (length ls > 1)%nat ->
  last ls false = false ->
  last (removelast ls) false = false ->
  toZ_ls (shiftR1_ls false ls) = Z.shiftl (toZ_ls ls ) 1.

  destruct ls using rev_ind; intros; simpl in *.
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  reflexivity.

  rewrite last_last in H0.
  subst.

  unfold shiftR1_ls.
  rewrite (app_comm_cons).
  rewrite shiftout_ls_app_rev.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  
  destruct ls using rev_ind.
  simpl in *.
  lia.

  rewrite app_comm_cons.
  rewrite splitmsb_ls_app_eq.
  rewrite removelast_last in H1.
  rewrite last_last in H1.
  subst.
  rewrite toPosZ_app_0_eq.
  rewrite toPosZ_cons_0_eq.
  remember (toPosZ_ls ls) as z.

  destruct z;
  lia.

Qed.

Theorem last_app_2 : forall (A : Type)(ls1 ls2 : list A) a,
  (length ls2 > 0)%nat ->
  last (ls1 ++ ls2) a = last ls2 a.


  intros.
  destruct ls2 using rev_ind.
  simpl in *.
  lia.

  rewrite app_assoc.
  rewrite last_last.
  rewrite last_last.
  reflexivity.

Qed.

Theorem last_repeat_eq : forall n (A : Type) (a : A),
  last (repeat a n) a = a.

  induction n; intros; simpl in *.
  trivial.
  rewrite IHn.
  destruct (repeat a n); trivial.

Qed.


Theorem removelast_repeat_eq : forall (A : Type)(a : A) n,
  (n > 0)%nat ->
  removelast (repeat a n) = repeat a (pred n).

  intros.
  destruct n.
  lia.
  rewrite repeat_S_rev.
  rewrite removelast_last.
  reflexivity.

Qed.

Theorem removelast_length : forall (A : Type)(ls : list A),
  ls <> nil ->
  List.length (removelast ls) = pred (List.length ls).

  induction ls using rev_ind; intros.
  intuition idtac.
  rewrite removelast_last.
  rewrite app_length.
  rewrite plus_comm.
  simpl.
  reflexivity.

Qed.

Theorem toZ_ls_shiftR_ls_eq : forall n n1 ls,
  (n < n1)%nat ->
  toZ_ls (shiftR_ls false (ls ++ repeat false n1) n) = Z.shiftl (toZ_ls (ls ++ repeat false n1) ) (Z.of_nat n).

  induction n; intros.
  simpl in *; trivial.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_l.

  simpl.
  rewrite shiftR1_ls_comm.
  rewrite shiftR1_app_repeat_eq.
  rewrite app_comm_cons.
  rewrite IHn; try lia.

  rewrite <- (Z.shiftl_shiftl _ 1 (Z.of_nat n)).
  f_equal.
  rewrite <- app_comm_cons.
  rewrite <- shiftR1_app_repeat_eq; try lia.
  rewrite toZ_ls_shiftR1_ls_eq.
  reflexivity.

  rewrite app_length.
  rewrite repeat_length.
  lia.
  rewrite last_app_2.
  apply last_repeat_eq.
  rewrite repeat_length.
  lia.
  rewrite removelast_app.
  rewrite last_app_2.
  rewrite removelast_repeat_eq; try lia.
  rewrite last_repeat_eq.
  trivial.
  rewrite removelast_length.
  rewrite repeat_length.
  lia.
  intuition idtac.
  apply length_zero_iff_nil in H0.
  rewrite repeat_length in *.
  lia.
  intuition idtac.
  apply length_zero_iff_nil in H0.
  rewrite repeat_length in *.
  lia.
  lia.
  lia.

Qed.

Theorem shiftL1_ls_shiftL_ls_comm : forall (A : Type) n (a : A) ls,
  shiftL1_ls a (shiftL_ls a ls n) = shiftL_ls a (shiftL1_ls a ls) n.

  induction n; intros; simpl in *; trivial.
  rewrite IHn.
  reflexivity.

Qed.

Theorem shiftL1_ls_repeat_eq : forall n1 (A : Type)(a : A) b,
  (n1 > 0)%nat ->
  (shiftL1_ls a (repeat a n1 ++ b)) = (repeat a (pred n1) ++ b ++ [a]).

  intros.
  unfold shiftL1_ls.
  unfold shiftin_ls.
  destruct n1; simpl in *; try lia.
  rewrite app_assoc.
  reflexivity.

Qed.


Theorem rev_shiftL_ls_eq_h : forall (A : Type) n n1 (a : A) b,
  (n < n1)%nat ->
  rev (shiftL_ls a (repeat a n1 ++ b ) n) = shiftR_ls a ((rev b)++ (repeat a n1))  n.

  induction n;
  intros;
  simpl in *.
  rewrite rev_app_distr.
  rewrite rev_repeat_id.
  reflexivity.

  rewrite shiftL1_ls_shiftL_ls_comm.
  rewrite shiftL1_ls_repeat_eq.
  rewrite IHn.
  rewrite shiftR1_ls_comm.
  rewrite shiftR1_app_repeat_eq.
  rewrite rev_app_distr.
  simpl.
  reflexivity.
  lia.
  lia.
  lia.

Qed.


Theorem rev_shiftL_ls_eq : forall (A : Type) n1 n (a b : A),
  (n < n1)%nat ->
  rev (shiftL_ls a (repeat a n1 ++ [b] ) n) = shiftR_ls a (b:: (repeat a n1))  n.

  intros.
  apply rev_shiftL_ls_eq_h.
  trivial.

Qed.

Theorem sbvToInt_shiftL_1_equiv : forall n s,
  (n > 0)%nat ->
  (s < pred n)%nat ->
  sbvToInt n (shiftL _ _ false (intToBv _ 1) s) = 
  Z.shiftl 1 (Z.of_nat s).

  intros.
  rewrite <- sbvToInt_ls_equiv.
  unfold sbvToInt_ls.
  destruct n.
  lia.
  unfold bvToBITS_ls.
  rewrite shiftL_to_list_eq.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls, bitsToBv_ls.
  simpl in *.
  rewrite fromPosZ_ls_0_eq.
  rewrite rev_repeat_id.
  rewrite rev_shiftL_ls_eq.
  replace (1%bool :: repeat 0%bool n) with ([true] ++ (repeat false n)).
  rewrite toZ_ls_shiftR_ls_eq.
  unfold toZ_ls.
  destruct n.
  lia.
  rewrite repeat_S_rev.
  rewrite app_assoc.
  rewrite splitmsb_ls_app_eq.
  
  rewrite toPosZ_app_repeat_0_eq.
  simpl.
  reflexivity.
  lia.
  simpl.
  reflexivity.
  lia.

Qed.

Theorem toPosZ_ls_repeat_0 : forall n,
  toPosZ_ls (repeat 0%bool n) = 0.

  induction n; intros; simpl in *; trivial.
  rewrite IHn.
  lia.

Qed.

Theorem sbvToInt_replicate_0 : forall n,
  sbvToInt _ (replicate n bool false) = 0.

  intros.
  rewrite <- sbvToInt_ls_equiv.
  unfold sbvToInt_ls.
  destruct n; simpl; trivial.
  unfold bvToBITS_ls.
  rewrite <- replicate_repeat_eq.
  rewrite rev_repeat_id.
  rewrite repeat_S_rev.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  apply toPosZ_ls_repeat_0.
  
Qed.

Theorem nth_to_list_eq : forall (A : Type) n (f : Fin.t n) (v : Vec n A) a,
  Vector.nth v f = nth (proj1_sig (Fin.to_nat f) ) (to_list v) a.

  induction f; intros; simpl in *; subst.
  destruct (Vec_S_cons _ _ v).
  destruct H. 
  subst.
  rewrite to_list_cons.
  simpl.
  reflexivity.

  remember (Fin.to_nat f ) as z.  
  destruct z.
  simpl.
  
  destruct (Vec_S_cons _ _ v).
  destruct H. 
  subst.
  rewrite to_list_cons.
  simpl in *.
  eapply IHf.

Qed.

Theorem nth_to_list_eq_gen : forall (A : Type) n (f : Fin.t n) (v : Vec n A) a n',
  n' = (proj1_sig (Fin.to_nat f) ) ->
  Vector.nth v f = nth n' (to_list v) a.

  intros.
  subst.
  apply nth_to_list_eq. 

Qed.


Theorem nth_order_to_list_eq : forall (A : Type) (a : A) n (v : Vec n A) n' (pf : (n' < n)%nat),
  nth_order v pf = nth n' (to_list v) a.

  intros.
  unfold nth_order.
  eapply nth_to_list_eq_gen.
  rewrite Fin.to_nat_of_nat.
  reflexivity.

Qed.

Theorem toPosZ_ls_nonneg : forall ls,
  0 <= toPosZ_ls ls.

  induction ls; intros; simpl in *; try lia.
  destruct a; lia.

Qed.

Theorem toPosZ_ls_In_true_nz : forall ls,
  In true ls ->
  toPosZ_ls ls <> 0%Z.

  induction ls; intros; simpl in *.
  intuition idtac.
  destruct H.
  subst.
  specialize (toPosZ_ls_nonneg ls); intros.
  lia.
  destruct a.
  specialize (toPosZ_ls_nonneg ls); intros.
  lia.
  intuition idtac.
  lia.
Qed.

Theorem toZ_ls_In_true_nz : forall ls,
  In true ls ->
  toZ_ls ls <> 0%Z.

  intros.
  destruct ls using rev_ind; intros; simpl in *.
  intuition idtac.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  apply in_app_or in H.

  destruct x.
  specialize (toNegZ_ls_nonneg ls); intros.
  lia.

  destruct H.
  eapply toPosZ_ls_In_true_nz; eauto.

  simpl in *.
  intuition idtac.
  discriminate.

Qed.

Theorem sbvToInt_nz_nth : forall n (v : Vec n _) n' (nlt : (n' < n)%nat),
  nth_order v nlt = true ->
  sbvToInt _ v <> 0%Z.

  intros.
  rewrite <- sbvToInt_ls_equiv.
  unfold sbvToInt_ls.
  destruct n.
  lia.
  
  unfold bvToBITS_ls.
  rewrite (@nth_order_to_list_eq _ false) in H.
  assert (In true (to_list v)).
  rewrite <- H.
  apply nth_In.
  rewrite length_to_list.
  trivial.
  apply toZ_ls_In_true_nz.
  apply (@in_rev _ (to_list v)).
  trivial.

Qed.

Theorem sbvToInt_neg_sign_bit_set : forall n  b2 (ltpf : (0 < n)%nat),
    (sbvToInt n b2 < 0)%Z ->
    nth_order b2 ltpf = true.

  intros.
  rewrite <- sbvToInt_ls_equiv in *.
  unfold sbvToInt_ls in *.
  destruct n.
  lia.
  unfold bvToBITS_ls in *.
  destruct (Vec_S_cons _ _ b2).
  destruct H0.
  subst.
  rewrite to_list_cons in *.
  unfold toZ_ls in *.
  simpl in *.
  rewrite splitmsb_ls_app_eq in *.
  destruct x.
  reflexivity.
  match goal with
  | [H : toPosZ_ls ?a < 0 |- _ ] =>
    specialize (toPosZ_ls_nonneg a); intros
  end.
  lia.

Qed.

Theorem toZ_ls_repeat_0: forall n : nat, 
  toZ_ls (repeat 0%bool n) = 0.

  intros.
  unfold toZ_ls.
  destruct n.
  simpl.
  reflexivity.

  rewrite repeat_S_rev.
  rewrite splitmsb_ls_app_eq.
  apply toPosZ_ls_repeat_0.

Qed.

Theorem Z_mod_div_eq : forall x y z,
  z > 0 ->
  y > 0 ->
  y mod z = 0 ->
  Z.div (Z.modulo x y) z = Z.modulo (Z.div x z) (Z.div y z).

  intros.
  assert (exists y', y = y'*z).
  exists (y / z).
  rewrite (@Zdiv.Z_div_exact_full_2 y z); trivial; try lia.
  rewrite Z.mul_comm.
  rewrite Z.div_mul.
  reflexivity.
  lia.
  destruct H2.
  subst.

  destruct (Z.eq_decidable x0 0).
  subst.
  repeat rewrite Z.mul_0_l.
  repeat rewrite Z.div_0_l.
  repeat rewrite Zdiv.Zmod_0_r.
  reflexivity.
  lia.

  rewrite Zdiv.Z_div_mult; try lia.
  rewrite Z.mul_comm.
  rewrite Z.rem_mul_r.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_plus.
  rewrite Zdiv.Zmod_div.
  lia.
  lia.
  lia.
  lia.
Qed.


Theorem fromPosZ_ls_app : forall n1 n2 z, 
 
  fromPosZ_ls (n1 + n2) z = (fromPosZ_ls n1 (Z.modulo z (Z.pow 2 (Z.of_nat n1)))) ++ (fromPosZ_ls n2 (Z.div z (Z.pow 2 (Z.of_nat n1)))). 

  induction n1; intros.
  simpl in *.
  rewrite Z.div_1_r.
  reflexivity.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  simpl in *.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  f_equal.
  repeat rewrite Zdiv.Zeven_mod.
  f_equal.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  rewrite Z.rem_mul_r.
  rewrite <- Zdiv.Zplus_mod_idemp_r.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_mod_mult.
  rewrite Z.add_0_r.  
  rewrite Z.pow_1_r.
  rewrite Z.mod_mod.
  reflexivity.
  lia.
  lia.
  apply Z.pow_pos_nonneg; lia.
  lia.
  lia.

  rewrite IHn1.
  repeat rewrite Z.div2_div.
  f_equal.
  f_equal.
  replace (2 ^ (Z.of_nat n1 + 1)) with ((2 ^ (Z.of_nat n1))*2).
  rewrite Z_mod_div_eq; try lia.
  rewrite Zdiv.Z_div_mult.
  reflexivity.
  lia.
  apply Zdiv.Z_mod_mult.
  rewrite Z.pow_add_r.
  reflexivity.
  lia.
  lia.

  f_equal.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.mul_comm.
  rewrite Zdiv.Zdiv_Zdiv; try lia.
  reflexivity.

Qed.

Theorem fromPosZ_ls_rev : forall n z, 
  (n > 0)%nat ->
  fromPosZ_ls n z = (fromPosZ_ls (pred n) (Z.modulo z (Z.pow 2 (Z.of_nat (pred n))))) ++ [negb (Z.even (Z.div z (Z.pow 2 (Z.of_nat (pred n)))))]. 

  intros.
  destruct n.
  lia.

  replace (S n) with (n + 1)%nat; try lia.
  rewrite fromPosZ_ls_app.
  rewrite plus_comm.
  simpl.
  reflexivity.

Qed.

Theorem toPosZ_ls_fromPosZ_ls_eq : forall n z,
  0 <= z < 2^(Z.of_nat n) ->
  toPosZ_ls (fromPosZ_ls n z) = z.

  induction n; intros.
  simpl in *.
  lia.

  rewrite Znat.Nat2Z.inj_succ in *.
  rewrite <- Z.add_1_r in *.
  simpl in *.
  case_eq (Z.even z); intros; simpl in *.
  assert (exists z', z = 2 * z').
  exists (Z.div2 z).
  rewrite Zeven.Zdiv2_odd_eqn at 1.
  rewrite <- Z.negb_even.
  rewrite H0.
  simpl.
  rewrite Z.add_0_r.
  reflexivity.
  destruct H1. subst.
  rewrite Z.div2_div.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_mult; try lia.
  rewrite Z.double_spec.
  rewrite IHn.
  lia.
  intuition idtac.
  lia.
  rewrite Z.pow_add_r in H2.
  rewrite Z.mul_comm in H2.
  rewrite Z.pow_1_r in H2.
  eapply Zorder.Zmult_lt_reg_r; eauto.
  lia.
  lia.
  lia.

  assert (exists z', z = 1 + z' *2 ).
  exists (Z.div2 z).
  rewrite Zeven.Zdiv2_odd_eqn at 1.
  rewrite <- Z.negb_even.
  rewrite H0.
  unfold negb.
  lia.

  destruct H1. subst.
  rewrite <- Z.add_1_l.
  f_equal.
  rewrite Z.div2_div.
  rewrite Zdiv.Z_div_plus.
  simpl.
  rewrite IHn.
  rewrite Z.double_spec.
  lia.
  intuition idtac.
  lia.
  rewrite Z.pow_add_r in H2.
  rewrite Z.mul_comm in H2.
  rewrite Z.pow_1_r in H2.
  lia.
  lia.
  lia.
  lia.
Qed.

Theorem fromNegZ_ls_app : forall n1 n2 z, 
 
  fromNegZ_ls (n1 + n2) z = (fromNegZ_ls n1 (Z.modulo z (Z.pow 2 (Z.of_nat n1)))) ++ (fromNegZ_ls n2 (Z.div z (Z.pow 2 (Z.of_nat n1)))). 

  induction n1; intros.
  simpl in *.
  rewrite Z.div_1_r.
  reflexivity.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  simpl in *.
  unfold joinlsb_ls.
  simpl.
  f_equal.
  repeat rewrite Zdiv.Zeven_mod.
  f_equal.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  rewrite Z.rem_mul_r.
  rewrite <- Zdiv.Zplus_mod_idemp_r.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_mod_mult.
  rewrite Z.add_0_r.  
  rewrite Z.pow_1_r.
  rewrite Z.mod_mod.
  reflexivity.
  lia.
  lia.
  apply Z.pow_pos_nonneg; lia.
  lia.
  lia.

  rewrite IHn1.
  repeat rewrite Z.div2_div.
  f_equal.
  f_equal.
  replace (2 ^ (Z.of_nat n1 + 1)) with ((2 ^ (Z.of_nat n1))*2).
  rewrite Z_mod_div_eq; try lia.
  rewrite Zdiv.Z_div_mult.
  reflexivity.
  lia.
  apply Zdiv.Z_mod_mult.
  rewrite Z.pow_add_r.
  reflexivity.
  lia.
  lia.

  f_equal.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.mul_comm.
  rewrite Zdiv.Zdiv_Zdiv; try lia.
  reflexivity.

Qed.


Theorem fromNegZ_ls_rev : forall n z, 
  (n > 0)%nat ->
  fromNegZ_ls n z = (fromNegZ_ls (pred n) (Z.modulo z (Z.pow 2 (Z.of_nat (pred n))))) ++ [(Z.even (Z.div z (Z.pow 2 (Z.of_nat (pred n)))))]. 

  intros.
  destruct n.
  lia.

  replace (S n) with (n + 1)%nat; try lia.
  rewrite fromNegZ_ls_app.
  rewrite plus_comm.
  simpl.
  unfold joinlsb_ls. simpl.
  reflexivity.

Qed.

Theorem toNegZ_ls_fromNegZ_ls_eq : forall n z,
  0 <= z < 2^(Z.of_nat n) ->
  toNegZ_ls (fromNegZ_ls n z) = z.

  induction n; intros.
  simpl in *.
  lia.

  rewrite Znat.Nat2Z.inj_succ in *.
  rewrite <- Z.add_1_r in *.
  simpl in *.
  case_eq (Z.even z); intros; simpl in *.
  assert (exists z', z = 2 * z').
  exists (Z.div2 z).
  rewrite Zeven.Zdiv2_odd_eqn at 1.
  rewrite <- Z.negb_even.
  rewrite H0.
  simpl.
  rewrite Z.add_0_r.
  reflexivity.
  destruct H1. subst.
  rewrite Z.div2_div.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_mult; try lia.
  rewrite Z.double_spec.
  rewrite IHn.
  lia.
  intuition idtac.
  lia.
  rewrite Z.pow_add_r in H2.
  rewrite Z.mul_comm in H2.
  rewrite Z.pow_1_r in H2.
  eapply Zorder.Zmult_lt_reg_r; eauto.
  lia.
  lia.
  lia.

  assert (exists z', z = 1 + z' *2 ).
  exists (Z.div2 z).
  rewrite Zeven.Zdiv2_odd_eqn at 1.
  rewrite <- Z.negb_even.
  rewrite H0.
  unfold negb.
  lia.

  destruct H1. subst.
  rewrite <- Z.add_1_l.
  f_equal.
  rewrite Z.div2_div.
  rewrite Zdiv.Z_div_plus.
  simpl.
  rewrite IHn.
  rewrite Z.double_spec.
  lia.
  intuition idtac.
  lia.
  rewrite Z.pow_add_r in H2.
  rewrite Z.mul_comm in H2.
  rewrite Z.pow_1_r in H2.
  lia.
  lia.
  lia.
  lia.
Qed.


Theorem sbvToInt_intToBv_id : forall n v,
  (n > 0)%nat ->
  (-Z.pow 2 (Z.of_nat (pred n)) <= v < Z.pow 2 (Z.of_nat (pred n)))%Z ->
  sbvToInt n (intToBv n v) = v.

  intros.
  rewrite <- sbvToInt_ls_equiv .
  unfold sbvToInt_ls .
  destruct n.
  lia.

  unfold bvToBITS_ls.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls, bitsToBv_ls.
  rewrite rev_involutive.
  simpl in *.
  unfold fromZ_ls.
  destruct v.
  unfold zero_ls.
  apply toZ_ls_repeat_0.

  rewrite fromPosZ_ls_rev.
  simpl.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  case_eq (Z.even (Z.pos p / 2^Z.of_nat n)); intros;
  simpl.
  rewrite Zdiv.Zmod_small.
  apply toPosZ_ls_fromPosZ_ls_eq; intuition idtac; lia.
  lia.
  rewrite Z.div_small in H1.
  simpl in *.
  discriminate.
  lia.
  lia.

  rewrite Pos2Z.opp_neg.
  rewrite fromNegZ_ls_rev.
  unfold pred.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  case_eq (Z.even (Z.pred (Z.pos p) / 2^Z.of_nat n)); intros.
  rewrite toNegZ_ls_fromNegZ_ls_eq.
  rewrite Zdiv.Zmod_small.
  lia.
  lia.
  apply Z.mod_bound_pos.
  lia.
  apply Z.pow_pos_nonneg; lia.
  rewrite Z.div_small in H1.
  simpl in *.
  discriminate.
  lia.
  lia.
Qed.

Theorem toPosZ_ls_upper_bound : forall ls,
  toPosZ_ls ls < 2^(Z.of_nat (List.length ls)).

  induction ls; intros.
  simpl in *.
  lia.
  
  replace (Datatypes.length (a :: ls)) with (S (Datatypes.length ls)).
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  simpl.
  destruct a.
  rewrite Z.double_spec.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  lia.
  lia.
  lia.

  rewrite Z.double_spec.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  lia.
  lia.
  lia.

  reflexivity.
Qed.

Theorem toNegZ_ls_upper_bound : forall ls,
  toNegZ_ls ls < 2^(Z.of_nat (List.length ls)).

  induction ls; intros.
  simpl in *.
  lia.
  
  replace (Datatypes.length (a :: ls)) with (S (Datatypes.length ls)).
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  simpl.
  destruct a.
  rewrite Z.double_spec.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  lia.
  lia.
  lia.

  rewrite Z.double_spec.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  lia.
  lia.
  lia.

  reflexivity.
Qed.

Theorem fromPosZ_ls_toPosZ_ls_eq : forall ls,
  fromPosZ_ls (length ls) (toPosZ_ls ls) = ls.

  induction ls; intros; simpl in *; trivial.
  unfold joinlsb_ls. simpl.
  f_equal.
  destruct a.
  rewrite Z.double_spec.
  rewrite <- Z.add_1_l.
  rewrite Z.even_add_mul_2.
  trivial.

  rewrite Z.double_spec.
  specialize (@Z.even_add_mul_2 0 ( toPosZ_ls ls)); intros.
  rewrite Z.add_0_l in H.
  rewrite H.
  trivial.

  destruct a.
  rewrite <- Z.add_1_l.
  rewrite Z.double_spec.
  rewrite Z.div2_div.
  rewrite Z.mul_comm.
  rewrite Z.div_add.
  simpl.
  trivial.
  lia.

  rewrite Z.double_spec.
  rewrite Z.div2_div.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_mult.
  eauto.
  lia.

Qed.

Theorem fromPosZ_ls_toPosZ_ls_eq_gen : forall ls n,
  n = length ls ->
  fromPosZ_ls n (toPosZ_ls ls) = ls.

  intros.
  subst.
  apply fromPosZ_ls_toPosZ_ls_eq.

Qed.

Theorem fromNegZ_ls_toNegZ_ls_eq : forall ls,
  fromNegZ_ls (length ls) (toNegZ_ls ls) = ls.

  induction ls; intros; simpl in *; trivial.
  unfold joinlsb_ls. simpl.
  f_equal.
  destruct a.
  rewrite Z.double_spec.
  specialize (@Z.even_add_mul_2 0 ( toNegZ_ls ls)); intros.
  rewrite Z.add_0_l in H.
  trivial.

  rewrite <- Z.add_1_l.
  rewrite Z.double_spec.
  rewrite Z.even_add_mul_2.
  trivial.

  destruct a.
  rewrite Z.double_spec.
  rewrite Z.div2_div.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_mult.
  eauto.
  lia.

  rewrite Z.double_spec.
  rewrite Z.div2_div.
  rewrite <- Z.add_1_l.
  rewrite Z.mul_comm.
  rewrite Z.div_add.
  simpl.
  eauto.
  lia.

Qed.

Theorem fromNegZ_ls_toNegZ_ls_eq_gen : forall ls n,
  n = length ls ->
  fromNegZ_ls n (toNegZ_ls ls) = ls.

  intros.
  subst.
  apply fromNegZ_ls_toNegZ_ls_eq.

Qed.

Theorem toPosZ_ls_0_impl : forall ls,
  toPosZ_ls ls = 0 ->
  ls = repeat false (List.length ls).

  induction ls; intros; simpl in *; trivial.
  destruct a.
  rewrite Z.double_spec in H.
  rewrite <- Z.add_1_l in H.
  lia.
  f_equal.
  eapply IHls.
  rewrite Z.double_spec in H.
  lia.
Qed.


Theorem sbvToInt_bvToInt_id : forall n x,
  (n > 0)%nat -> 
  intToBv n (sbvToInt n x) = x.

  intros.
  apply eq_if_to_list_eq.
  rewrite <- sbvToInt_ls_equiv .
  rewrite <- intToBv_ls_eq.
  unfold sbvToInt_ls .
  destruct n.
  lia.

  unfold intToBv_ls, bitsToBv_ls.
  unfold bvToBITS_ls.
  destruct (Vec_S_cons _ _ x).
  destruct H0.
  subst.
  rewrite to_list_cons.
  simpl.
  unfold toZ_ls.
  rewrite splitmsb_ls_app_eq.
  destruct x0.
  unfold fromZ_ls.
  match goal with
  | [|- context[match ?a with | 0 => _ | Z.pos _ => _ | Z.neg _ => _ end]] =>
    remember a as z
  end.
  destruct z.
  match goal with
  | [H: 0 = Z.opp (Z.succ (toNegZ_ls ?a)) |- _] =>
    specialize (toNegZ_ls_nonneg a); intros
  end.
  lia.
  match goal with
  | [H: _ = Z.opp (Z.succ (toNegZ_ls ?a)) |- _] =>
    specialize (toNegZ_ls_nonneg a); intros
  end.
  lia.
  rewrite Heqz.
  rewrite Z.opp_involutive.
  rewrite Z.pred_succ.
  replace (S n) with (n + 1)%nat.
  rewrite fromNegZ_ls_app.
  simpl.
  unfold joinlsb_ls.
  simpl.
  rewrite rev_app_distr.
  simpl.
  f_equal.
  rewrite Z.div_small.
  reflexivity.
  intuition idtac.
  apply toNegZ_ls_nonneg.
  eapply Z.lt_le_trans.
  apply toNegZ_ls_upper_bound.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  rewrite Z.mod_small.
  rewrite fromNegZ_ls_toNegZ_ls_eq_gen.
  apply rev_involutive.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  intuition idtac.
  apply toNegZ_ls_nonneg.
  eapply Z.lt_le_trans.
  apply toNegZ_ls_upper_bound.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  lia.

  (* toPosZ case*)
  unfold fromZ_ls.
  
  match goal with
  | [|- context[match ?a with | 0 => _ | Z.pos _ => _ | Z.neg _ => _ end]] =>
    remember a as z
  end.
  destruct z.
  unfold zero_ls.
   symmetry in Heqz.
  apply toPosZ_ls_0_impl in Heqz.
  rewrite rev_length in *.
  rewrite length_to_list in *.
  rewrite repeat_S_rev.
  rewrite rev_app_distr.
  simpl.
  f_equal.
  rewrite <- Heqz.
  rewrite rev_involutive.
  reflexivity.

  rewrite Heqz.
  replace (S n) with (n + 1)%nat.
  rewrite fromPosZ_ls_app.
  simpl.
  unfold joinlsb_ls.
  simpl.
  rewrite rev_app_distr.
  simpl.
  f_equal.
  rewrite Z.div_small.
  reflexivity.
  intuition idtac.
  apply toPosZ_ls_nonneg.
  eapply Z.lt_le_trans.
  apply toPosZ_ls_upper_bound.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  rewrite Z.mod_small.
  rewrite fromPosZ_ls_toPosZ_ls_eq_gen.
  apply rev_involutive.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  intuition idtac.
  apply toPosZ_ls_nonneg.
  eapply Z.lt_le_trans.
  apply toPosZ_ls_upper_bound.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  lia.

   match goal with
  | [H: _ = (toPosZ_ls ?a)|- _] =>
    specialize (toPosZ_ls_nonneg a); intros
  end.  
  lia.
Qed.

Theorem sbvToInt_ls_to_list_eq : forall n (v : Vec n bool),
  sbvToInt_ls v = toZ_ls (bvToBITS_ls v).

  intros.
  unfold sbvToInt_ls.
  destruct v; simpl in *.
  unfold bvToBITS_ls.
  simpl.
  reflexivity.

  unfold bvToBITS_ls.
  rewrite to_list_cons.
  reflexivity.

Qed.

Definition bvToInt_ls n (b : Vec n bool) :=
  toPosZ_ls (bvToBITS_ls b).

Theorem toPosZ_ls_eq : forall n (b : spec.BITS n),
  toPosZ_ls (tuple.tval b) = spec.toPosZ b.

  intros.
  reflexivity.
Qed.

Theorem bvToInt_ls_equiv: forall [n : nat] (v : Vec n bool), 
  bvToInt_ls v = bvToInt n v.

  intros.
  unfold bvToInt, bvToInt_ls.
  rewrite <- bvToBITS_ls_equiv.
  apply toPosZ_ls_eq.

Qed.

Theorem toPosZ_small_impl_skipn_0 : forall ls n,
  (n <= List.length ls)%nat ->
  toPosZ_ls ls < 2 ^ Z.of_nat n ->
  skipn n ls = repeat false (List.length ls - n).

  induction ls; intros.
  simpl in *.
  apply skipn_nil.

  destruct n. 
  simpl in *.
  destruct a.
  specialize (toPosZ_ls_nonneg ls); intros.
  lia.
  f_equal.
  apply toPosZ_ls_0_impl.
  specialize (toPosZ_ls_nonneg ls); intros.
  lia.

  rewrite Znat.Nat2Z.inj_succ in *.
  repeat rewrite <- Z.add_1_r in *.
  simpl in *.
  apply IHls.
  lia.

  rewrite Z.pow_add_r in *.
  destruct a.
  lia.
  lia.
  lia.
  lia.

Qed.

Theorem toNegZ_ls_0_impl
     : forall ls : list bool, toNegZ_ls ls = 0 -> ls = repeat 1%bool (Datatypes.length ls).

  induction ls; intros; simpl in *.
  trivial.
  destruct a.
  f_equal.
  eapply IHls.
  lia.
  lia.

Qed.

Theorem toNegZ_small_impl_skipn_0 : forall ls n,
  (n <= List.length ls)%nat ->
  toNegZ_ls ls < 2 ^ Z.of_nat n ->
  skipn n ls = repeat true (List.length ls - n).

  induction ls; intros.
  simpl in *.
  apply skipn_nil.

  destruct n. 
  simpl in *.
  destruct a.
  f_equal.
  apply toNegZ_ls_0_impl.
  specialize (toNegZ_ls_nonneg ls); intros.
  lia.

  specialize (toNegZ_ls_nonneg ls); intros.
  lia.
  
  rewrite Znat.Nat2Z.inj_succ in *.
  rewrite <- Z.add_1_r in *.
  simpl in *.
  rewrite Z.pow_add_r in *.
  specialize (toNegZ_ls_nonneg ls); intros. 
  eapply IHls.
  destruct a.
  lia.
  lia.

  destruct a.
  lia.
  lia.
  lia.
  lia.

Qed.

Theorem firstn_repeat_eq : forall (A: Type)(a : A) n1 n2,
  firstn n1 (repeat a n2) = repeat a (min n1 n2).

  induction n1; destruct n2; intros; simpl in *; trivial.
  rewrite IHn1.
  reflexivity.

Qed.

Theorem toNegZ_app_1_eq : forall ls,
  toNegZ_ls (ls ++ [1%bool]) = toNegZ_ls ls.

  induction ls; intros; simpl in *; trivial.
  destruct a.
  rewrite IHls.
  reflexivity.
  rewrite IHls.
  reflexivity.

Qed.

Theorem toNegZ_app_repeat_0_eq : forall n ls,
  toNegZ_ls (ls ++ (repeat true n)) = toNegZ_ls ls.

  induction n; intros; simpl in *.
  rewrite app_nil_r.
  reflexivity.
  replace (ls ++ 1%bool :: repeat 1%bool n)  with ((ls ++ [true]) ++ repeat 1%bool n).
  rewrite IHn.
  apply toNegZ_app_1_eq.
  rewrite <-  app_assoc.
  reflexivity.

Qed.

Theorem sbvToInt_drop_equiv_h : forall n2 ls,
  (0 < n2 <= length ls)%nat ->
  -2^Z.of_nat (pred n2) <= toZ_ls (rev ls) < 2 ^ Z.of_nat (pred n2) ->
  toZ_ls (rev (skipn ( List.length ls - n2) ls)) = toZ_ls (rev ls).

  intros.
  rewrite <- firstn_rev.
  destruct ls.
  simpl in *.
  rewrite firstn_nil.
  reflexivity.

  simpl in *.
  unfold toZ_ls in H0.
  rewrite splitmsb_ls_app_eq in *.
  destruct b.

  (* negative case *)
   specialize (toNegZ_ls_nonneg (rev ls)); intros.
  assert ((toNegZ_ls (rev ls)) < 2 ^ Z.of_nat (pred n2)).
  lia.
  apply toNegZ_small_impl_skipn_0 in H2.
  rewrite firstn_app.

  assert (n2 - Datatypes.length (rev ls) = 0 \/ n2 - Datatypes.length (rev ls) = 1)%nat.
  repeat rewrite rev_length in *.
  lia.
  destruct H3.
  rewrite H3.
  simpl.
  rewrite app_nil_r.
  rewrite <- (firstn_skipn (pred n2) (rev ls)) at 1.
  rewrite H2.
  rewrite firstn_app.
  rewrite firstn_firstn.
  rewrite min_r.
  rewrite firstn_length.
  rewrite min_l.
  replace (n2 - pred n2)%nat with 1%nat; try lia.
  rewrite firstn_repeat_eq.
  rewrite min_l; try lia.
  simpl.
  unfold toZ_ls.
  repeat rewrite splitmsb_ls_app_eq.
  rewrite <- (firstn_skipn (pred n2) (rev ls)) at 2.

  rewrite H2.
  rewrite toNegZ_app_repeat_0_eq.
  reflexivity.
  repeat rewrite rev_length in *.
  lia.
  lia.

  rewrite H3.
  simpl.
  unfold toZ_ls.
  repeat rewrite splitmsb_ls_app_eq.
  rewrite <- (firstn_skipn (pred n2) (rev ls)).
  rewrite H2.
  rewrite firstn_app.
  rewrite firstn_firstn.
  rewrite min_r; try lia.
  rewrite firstn_length.
  rewrite min_l; try lia.
  replace (n2 - pred n2)%nat with 1%nat; try lia.
  rewrite firstn_repeat_eq.
  rewrite min_r.
  reflexivity.
  lia.
  repeat rewrite rev_length in *.
  lia. 

  (* positive case *)

  specialize (toPosZ_ls_nonneg (rev ls)); intros.
  assert (toPosZ_ls (rev ls) < 2 ^ Z.of_nat (pred n2)).
  lia.
  apply toPosZ_small_impl_skipn_0 in H2.
  rewrite firstn_app.

  assert (n2 - Datatypes.length (rev ls) = 0 \/ n2 - Datatypes.length (rev ls) = 1)%nat.
  repeat rewrite rev_length in *.
  lia.
  destruct H3.
  rewrite H3.
  simpl.
  rewrite app_nil_r.
  rewrite <- (firstn_skipn (pred n2) (rev ls)) at 1.
  rewrite H2.
  rewrite firstn_app.
  rewrite firstn_firstn.
  rewrite min_r.
  rewrite firstn_length.
  rewrite min_l.
  replace (n2 - pred n2)%nat with 1%nat; try lia.
  rewrite firstn_repeat_eq.
  rewrite min_l; try lia.
  simpl.
  unfold toZ_ls.
  repeat rewrite splitmsb_ls_app_eq.
  rewrite <- (firstn_skipn (pred n2) (rev ls)) at 2.

  rewrite H2.
  rewrite toPosZ_app_repeat_0_eq.
  reflexivity.
  repeat rewrite rev_length in *.
  lia.
  lia.

  rewrite H3.
  simpl.
  unfold toZ_ls.
  repeat rewrite splitmsb_ls_app_eq.
  rewrite <- (firstn_skipn (pred n2) (rev ls)).
  rewrite H2.
  rewrite firstn_app.
  rewrite firstn_firstn.
  rewrite min_r; try lia.
  rewrite firstn_length.
  rewrite min_l; try lia.
  replace (n2 - pred n2)%nat with 1%nat; try lia.
  rewrite firstn_repeat_eq.
  rewrite min_r.
  reflexivity.
  lia.
  repeat rewrite rev_length in *.
  lia.  

Qed.


Theorem sbvToInt_drop_equiv_h_gen : forall n1 n2 ls,
  n1 = ( List.length ls - n2)%nat ->
  (0 < n2 <= length ls)%nat ->
  -2^Z.of_nat (pred n2) <= toZ_ls (rev ls) < 2 ^ Z.of_nat (pred n2) ->
  toZ_ls (rev (skipn n1 ls)) = toZ_ls (rev ls).

  intros.  
  subst.
  apply sbvToInt_drop_equiv_h; eauto.

Qed.

Theorem sbvToInt_drop_equiv : forall n1 n2 x,
  (n2 > 0)%nat -> 
  (-Z.pow 2 (Z.of_nat (pred n2)) <=  (sbvToInt _ x) < Z.pow 2 (Z.of_nat (pred n2)))%Z ->
  sbvToInt _ (drop _ n1 n2 x) = sbvToInt _ x.

  intros.
  repeat rewrite <- sbvToInt_ls_equiv in *.
  repeat rewrite sbvToInt_ls_to_list_eq in *.
  unfold bvToBITS_ls in *.
  rewrite toList_drop_equiv.

  eapply sbvToInt_drop_equiv_h_gen.
  rewrite length_to_list.
  rewrite addNat_add.
  symmetry.
  apply Nat.add_sub.
  rewrite length_to_list.
  rewrite addNat_add.
  lia.
  trivial.
Qed.

Theorem rev_repeat_eq_impl : forall (A : Type)(a : A) ls n,
  rev ls = repeat a n ->
  ls = repeat a n.

  induction ls using rev_ind; destruct n; intros; simpl in *; trivial.
  rewrite rev_app_distr in *.
  simpl in *.
  discriminate.

  rewrite rev_app_distr in *.
  simpl in *.
  rewrite repeat_cons.
  inversion H; clear H; subst.
  f_equal.
  rewrite H2.
  eapply IHls.
  trivial.

Qed.

Theorem sbvToInt_0_replicate: forall n b2,
    sbvToInt n b2 = 0%Z ->
    b2 = replicate _ _ false.

  intros.
  rewrite <- sbvToInt_ls_equiv in *.
  apply eq_if_to_list_eq.
  unfold sbvToInt_ls in *.
  rewrite <- replicate_repeat_eq.
  destruct n.
  rewrite (Vec_0_nil _ b2).
  reflexivity.

  destruct (Vec_S_cons _ _ b2).
  destruct H0.
  subst.
  rewrite to_list_cons.
  unfold bvToBITS_ls in *.
  rewrite to_list_cons in *.
  simpl in *.
  unfold toZ_ls in *.
  rewrite splitmsb_ls_app_eq in *.
  destruct x.
  match goal with 
  | [H : (- Z.succ (toNegZ_ls ?a) = 0) |- _] =>
    specialize (toNegZ_ls_nonneg a); intros
  end.
  lia.
  f_equal.
  eapply rev_repeat_eq_impl.
  apply toPosZ_ls_0_impl in H.
  rewrite rev_length in *.
  rewrite length_to_list in *.
  trivial.
Qed.


Theorem sawAt_nth_order_equiv : forall (A : Type)(inh : Inhabited A)(n1 n2 : nat)(v : Vec n1 A)(ltpf : (n2 < n1)%nat),
  @sawAt n1 A inh v n2 = nth_order v ltpf.

  intros.
  rewrite sawAt_nth_equiv.
  symmetry.
  apply nth_order_to_list_eq.
  lia.

Qed.

Theorem sawAt_3_equiv : forall A (inh : Inhabited A) (v : Vector.t A 3),
  Vector.cons (sawAt 3%nat A v 0%nat)
    (Vector.cons (sawAt 3%nat A v 1%nat)
      (Vector.cons (sawAt 3%nat A v 2%nat) (Vector.nil A)))
  = v.

  intros.
  destruct (Vec_S_cons _ _ v). destruct H. subst.
  destruct (Vec_S_cons _ _ x0). destruct H. subst.
  destruct (Vec_S_cons _ _ x2). destruct H. subst.
  repeat rewrite sawAt_nth_equiv; try lia.
  repeat rewrite to_list_cons.
  simpl.
  specialize (Vec_0_nil _ x3); intros; subst.
  reflexivity.

Qed.

Theorem rep_false_eq_int_bv : forall n : Nat, 
  replicate n bool 0%bool = intToBv n 0.

  intros.
  rewrite intToBv_0_eq_replicate.
  reflexivity.
Qed.

Theorem neg_sign_bit_set : forall (n : nat) (v : VectorDef.t Bool n) (h : Bool), 
  (sbvToInt (S n) (VectorDef.cons h v) < 0)%Z -> 
  h = 1%bool.

  intros.
  assert (0 < S n)%nat.
  lia.
  apply (sbvToInt_neg_sign_bit_set _ H0) in H.
  rewrite nth_order_hd in H.
  simpl in *.
  trivial.
Qed.

Theorem shiftR_all_neg : forall n1 v,
  n1 <> O ->
  (sbvToInt _ v < 0)%Z ->
  (shiftR n1 bool false v (pred n1)) = intToBv _ 1.

  intros.
  apply eq_if_to_list_eq.
  rewrite shiftR_ls_equiv.
  destruct v; simpl; trivial.
  rewrite intToBv_1_to_list_eq.  
  rewrite shiftR_ls_eq_repeat.
  match goal with 
  | [|- context[ (?a - ?b)%nat]] =>
  replace (a - b)%nat with 1%nat
  end.
 
  erewrite (neg_sign_bit_set _ h); eauto.
  rewrite length_to_list.
  lia.
  rewrite length_to_list.
  lia.

Qed.

Theorem nth_shiftR1_S : forall (A : Type) (ls : list A) n a,
  (n < pred (length ls))%nat ->
  nth (S n) (shiftR1_ls a ls) a = nth n ls a.

  intros.
  unfold shiftR1_ls.
  unfold shiftout_ls.
  simpl.
  destruct ls using rev_ind; simpl in *.
  lia.
  rewrite app_length. simpl.
  rewrite plus_comm.
  simpl.
  rewrite firstn_app.
  rewrite firstn_all.
  rewrite minus_diag.
  simpl.
  rewrite app_nil_r.
  symmetry.
  apply app_nth1.
  rewrite app_length in *. simpl in *.
  lia.
Qed.

Theorem nth_shiftR_ls_all_eq : forall (A : Type) n (ls : list A) a,
  (n <  (Datatypes.length ls))%nat ->
  nth n (shiftR_ls a ls n) a = nth 0%nat ls a.

  induction n; intros; simpl in *; trivial.
  
  rewrite nth_shiftR1_S.
  apply IHn.
  simpl in *.
  lia.

  rewrite shiftR_ls_length.
  simpl in *.
  lia.

Qed.

Theorem nth_order_shiftR_all_eq
  : forall (A : Type) (n2 len : nat) (v : Vec len A) (nlt : (n2 < len)%nat) (zlt : (0 < len)%nat) (a : A), 
  nth_order (shiftR len A a v n2) nlt = nth_order v zlt.

  intros.
  repeat rewrite (nth_order_to_list_eq a).
  rewrite shiftR_ls_equiv.
  rewrite nth_shiftR_ls_all_eq; trivial.
  rewrite length_to_list.
  trivial.

Qed.

Theorem nth_skipn_eq : forall (A : Type)(a : A)  n1 n2 ls,
  nth n2 (skipn n1 ls) a = nth (n1 + n2)%nat ls a.

  induction n1; intros; simpl in *; trivial.
  destruct ls; simpl in *.
  destruct n2; trivial.

  apply IHn1.

Qed.

Theorem nth_order_drop_eq
  : forall (A : Type) (inh : Inhabited A) (n1 n2 : Nat) (v : Vec (addNat n1 n2) A) (n' : Nat) (lt1 : (addNat n1 n' < addNat n1 n2)%nat) (lt2 : (n' < n2)%nat),
    nth_order (drop A n1 n2 v) lt2 = nth_order v lt1.

  intros.
  repeat rewrite (nth_order_to_list_eq (inhabitant inh)).
  rewrite toList_drop_equiv.
  generalize (to_list v); intros.
  rewrite addNat_add.
  apply nth_skipn_eq.

Qed.


Theorem nth_zipWith_ls : forall (A B C : Type)(f : A -> B -> C) lsa lsb0 n a b c,
  (n < length lsa)%nat ->
  (n < length lsb0)%nat ->
  nth n (zipWith_ls f lsa lsb0) c = f (nth n lsa a) (nth n lsb0 b).

  induction lsa; destruct lsb0; intros; simpl in *; destruct n; try lia; trivial.

  eapply IHlsa; lia.

Qed.

Theorem nth_repeat_eq : forall (A : Type)(a : A) n n',
  nth n' (repeat a n) a = a.

  induction n; destruct n'; intros; simpl in *; trivial.

Qed.

Theorem nth_intToBv_1_false : forall n' n,
  (n' < (pred n))%nat ->
  (nth n' (intToBv_ls n 1) false = false).

  intros.
  unfold intToBv_ls.
  destruct n.
  simpl in *.
  destruct n'; trivial.
  rewrite fromZ_ls_1_eq.
  unfold bitsToBv_ls.
  simpl in *.
  rewrite app_nth1.
  rewrite rev_repeat_id.
  apply nth_repeat_eq.
  rewrite rev_length.
  rewrite repeat_length.
  trivial.

Qed.

Theorem fromPosZ_ls_length : forall n x,
  List.length (fromPosZ_ls n x) = n.

  induction n; intros; simpl in *; trivial.
  rewrite IHn.
  trivial.

Qed.

Theorem fromNegZ_ls_length : forall n x,
  List.length (fromNegZ_ls n x) = n.

  induction n; intros; simpl in *; trivial.
  rewrite IHn.
  trivial.
Qed.


Theorem fromZ_ls_length : forall n x,
  List.length (fromZ_ls n x) = n.

  intros.
  unfold fromZ_ls.
  destruct x.
  unfold zero_ls.
  apply repeat_length.
  apply fromPosZ_ls_length.
  apply fromNegZ_ls_length.
  

Qed.

Theorem intToBv_ls_length : forall n x,
  List.length (intToBv_ls n x) = n.

  intros.
  unfold intToBv_ls.
  unfold bitsToBv_ls.
  rewrite rev_length.
  apply fromZ_ls_length.

Qed.

Theorem nth_order_bvAnd_l_eq : forall (n : nat) (v : bitvector n) (n' : nat) (plt : (n' < n)%nat), 
  (n' < Nat.pred n)%nat -> 
  nth_order (bvAnd v (intToBv n 1)) plt = 0%bool.

  intros.
  repeat rewrite (nth_order_to_list_eq false).
  unfold bvAnd, bvZipWith.
  rewrite zipWith_ls_eq.
  rewrite <- intToBv_ls_eq.
  rewrite (nth_zipWith_ls _ _ _ false false).
  rewrite nth_intToBv_1_false.
  apply and_False2.
  lia.  
  rewrite length_to_list.
  lia.
  rewrite intToBv_ls_length.
  lia.

Qed.

Theorem nth_intToBv_1_true : forall n,
  (nth (pred n) (intToBv_ls n 1) true = true).

  intros.
  unfold intToBv_ls.
  destruct n.
  simpl in *.
  trivial.

  rewrite fromZ_ls_1_eq.
  unfold bitsToBv_ls.
  simpl in *.
  rewrite app_nth2.
  rewrite rev_length.
  rewrite repeat_length.
  rewrite minus_diag.
  simpl.
  reflexivity.

  rewrite rev_length.
  rewrite repeat_length.
  lia.

Qed.

Theorem nth_order_bvAnd_eq : forall (n : nat) (v : bitvector n) (plt : (Nat.pred n < n)%nat), 
  nth_order (bvAnd v (intToBv n 1)) plt = nth_order v plt.

  intros.
  repeat rewrite (nth_order_to_list_eq false).
  unfold bvAnd, bvZipWith.
  rewrite zipWith_ls_eq.
  rewrite <- intToBv_ls_eq.
  rewrite (nth_zipWith_ls _ _ _ true true).
  rewrite nth_intToBv_1_true.
  rewrite and_True2.
  apply nth_indep.
  rewrite length_to_list.
  lia.
  rewrite length_to_list.
  lia.
  rewrite intToBv_ls_length.
  trivial.

Qed.

Theorem nth_order_append_l_eq
  : forall (A : Type) (inh : Inhabited A) (n1 : nat) (v1 : Vec n1 A) (n2 : nat) (v2 : Vec n2 A) (n' : nat) (nlt2 : (n' < addNat n2 n1)%nat) (nlt1 : (n' < n2)%nat),
    nth_order (append v2 v1) nlt2 = nth_order v2 nlt1.

  intros.
  repeat rewrite (nth_order_to_list_eq (inhabitant inh)).
  rewrite toList_append_equiv.
  rewrite app_nth1.
  reflexivity.
  rewrite length_to_list.
  lia.

Qed.

Theorem nth_order_append_eq
  : forall (A : Type) (inh : Inhabited A) (n1 : nat) (v1 : Vec n1 A) (n2 : nat) (v2 : Vec n2 A) (n' : Nat) (nlt2 : (addNat n' n2 < addNat n2 n1)%nat)
      (nlt1 : (n' < n1)%nat), nth_order (append  v2 v1) nlt2 = nth_order v1 nlt1.

  intros.
  repeat rewrite (nth_order_to_list_eq (inhabitant inh)).
  rewrite toList_append_equiv.
  rewrite app_nth2.
  repeat rewrite length_to_list.
  f_equal.
  rewrite addNat_add.
  lia.
  rewrite length_to_list.
  repeat rewrite addNat_add in *.
  lia.

Qed.

Theorem nth_intToBv_0_false : forall n' n,
  (nth n' (intToBv_ls n 0) false = false).

  intros.
  unfold intToBv_ls.
  unfold fromZ_ls.
  unfold bitsToBv_ls, zero_ls.
  rewrite rev_repeat_id.
  apply nth_repeat_eq.
Qed.


Theorem nth_order_0 : forall (n1 n2 : nat) (nlt : (n2 < n1)%nat), 
  nth_order (intToBv n1 0) nlt = 0%bool.

  intros.
  repeat rewrite (nth_order_to_list_eq false).
  rewrite <- intToBv_ls_eq.
  apply nth_intToBv_0_false.

Qed.

Theorem fromZ_ls_0_eq: forall n : nat, fromZ_ls n 0 =repeat 0%bool n.

  intros.
  unfold fromZ_ls.
  reflexivity.

Qed.


Theorem intToBv_0_S : forall n : nat, 
  intToBv (S n) 0 =Vector.cons false (intToBv n 0).

  intros.
  apply eq_if_to_list_eq.
  rewrite to_list_cons.
  repeat rewrite <- intToBv_ls_eq.
  unfold intToBv_ls.
  rewrite fromZ_ls_0_eq.
  unfold bitsToBv_ls.
  rewrite repeat_S_rev.
  rewrite rev_app_distr.
  simpl.
  reflexivity.
  
Qed.

Theorem eq_impl_to_list_eq : forall (A : Type) n (v1 v2 : Vec n A),
  v1 = v2 ->
  to_list v1 = to_list v2.

  intros.
  subst.
  trivial.

Qed.

Theorem eq_if_rev_eq : forall ( A : Type)(ls1 ls2 : list A),
  rev ls1 = rev ls2 ->
  ls1 = ls2 .

  induction ls1 using rev_ind; intros; simpl in *; trivial.
  destruct ls2 using rev_ind; simpl in *; trivial.
  rewrite rev_app_distr in *; simpl in *; discriminate.
  
  destruct ls2 using rev_ind; simpl in *.
  rewrite rev_app_distr in *; simpl in *; discriminate.
  repeat rewrite rev_app_distr in *; simpl in *.
  inversion H; clear H; subst.
  erewrite IHls1; eauto.

Qed.

Theorem even_exists_factor : forall z,
  Z.even z = true ->
  exists z', z = z'*2.
  
  intros.
  exists (z/2).
  rewrite (@Zdiv.Z_div_mod_eq z 2) at 1.
  rewrite Zdiv.Zeven_mod in H.
  apply Zbool.Zeq_bool_eq in H.
  rewrite H.
  lia.
  lia.
Qed.

Theorem odd_exists_factor : forall z,
  Z.odd z = true ->
  exists z', z = 1 + z'*2.

  intros.
  exists (z/2).
  rewrite (@Zdiv.Z_div_mod_eq z 2) at 1.
  rewrite Zeven.Zodd_even_bool in *.
  rewrite Zdiv.Zeven_mod in H.
  apply Bool.negb_true_iff in H.
  apply Zbool.Zeq_bool_neq in H.
  replace (z mod 2) with 1.
  lia.
  assert (0 <= z mod 2 < 2).
  apply (Z.mod_pos_bound); lia.
  lia.
  lia.

Qed.

Theorem fromPosZ_ls_0_impl : forall n z,
  fromPosZ_ls n z = repeat false n -> z mod (2^ (Z.of_nat n))= 0.

  induction n; intros.
  simpl in *; trivial.
  specialize (Z.mod_pos_bound z 1); intros.
  lia.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  unfold joinlsb_ls in *.
  simpl in *.
  inversion H; clear H; subst.
  rewrite Z.pow_add_r.
  assert (exists z', z = z' * 2).
  apply even_exists_factor.
  destruct (Z.even z); simpl in *; trivial. discriminate. 
  destruct H.
  subst.
  rewrite Zdiv.Zmult_mod_distr_r.
  rewrite IHn.
  lia.
  rewrite Z.div2_div in *.
  rewrite Zdiv.Z_div_mult in *; try lia.
  rewrite H2.
  rewrite Z.mul_comm.
  specialize (@Z.even_add_mul_2 0 x); intros.
  rewrite Z.add_0_l in *.
  rewrite H.
  simpl.
  reflexivity.
  lia.
  lia.

Qed. 

Theorem fromPosZ_eq_impl : forall n z1 z2,
  fromPosZ_ls n z1 = fromPosZ_ls n z2 ->
  z1 mod (2 ^(Z.of_nat n)) = z2 mod (2^ (Z.of_nat n)).

  induction n; intros.
  simpl in *.
  specialize (Z.mod_pos_bound z1 1); intros.
  specialize (Z.mod_pos_bound z2 1); intros.
  lia.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  simpl in *.
  unfold joinlsb_ls in *.
  simpl in *.
  inversion H; clear H; subst.
  repeat rewrite Z.pow_add_r.
  case_eq (Z.even z1); intros.
  rewrite H in H1.
  simpl in *.
  
  case_eq (Z.even z2); intros.
  destruct (even_exists_factor z1); trivial; subst.
  destruct (even_exists_factor z2); trivial; subst.

  repeat rewrite Zdiv.Zmult_mod_distr_r.
  f_equal.
  apply IHn.
  rewrite Z.div2_div in *.
  rewrite Zdiv.Z_div_mult in *; try lia.
  rewrite H2.
  rewrite Z.div2_div.
  rewrite Zdiv.Z_div_mult.
  reflexivity.
  lia.

  rewrite H0 in H1. simpl in *. discriminate. 

  rewrite H in H1.
  case_eq (Z.even z2); intros.
  rewrite H0 in H1.
  simpl in *. discriminate.

  assert (exists z1', z1 = 1 + z1'*2).
  apply odd_exists_factor.
  rewrite Zeven.Zodd_even_bool.
  rewrite H.
  trivial.
  destruct H3.
  subst.
  assert (exists z2', z2 = 1 + z2'*2).
  apply odd_exists_factor.
  rewrite Zeven.Zodd_even_bool.
  rewrite H0.
  trivial.
  destruct H3.
  subst.
  
  repeat rewrite Z.pow_1_r.
  rewrite (@Z.mul_comm (2^Z.of_nat n)).
  rewrite Z.rem_mul_r; try lia.
  rewrite Zdiv.Z_mod_plus; try lia.
  rewrite Z.mod_small; try lia.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_plus; try lia.
  rewrite Z.div_small; try lia.
  rewrite Z.add_0_l.
  symmetry.
  rewrite Z.rem_mul_r; try lia.
  rewrite Zdiv.Z_mod_plus; try lia.
  rewrite Z.mod_small; try lia.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_plus; try lia.
  rewrite Z.div_small; try lia.
  rewrite Z.add_0_l.
  symmetry.
  f_equal; try lia.
  f_equal; try lia.
  eapply IHn.
  repeat rewrite Z.div2_div in *.
  rewrite Zdiv.Z_div_plus in *.
  rewrite Z.div_small in *; try lia.
  rewrite Z.add_0_l in *.
  rewrite H2.
  rewrite Zdiv.Z_div_plus.
  rewrite Z.div_small; try lia.
  rewrite Z.add_0_l.
  reflexivity.
  lia.  
  lia.

  lia.
  lia.

Qed.

Theorem intToBv_eq_pos : forall (n : nat) (x y : Z), 
  (0 <= x < 2 ^ BinInt.Z.of_nat n)%Z -> 
  (0 <= y < 2 ^ BinInt.Z.of_nat n)%Z ->
   intToBv n x = intToBv n y -> 
    x = y.

  intros.
  apply eq_impl_to_list_eq in H1.
  repeat rewrite <- intToBv_ls_eq in *.
  unfold intToBv_ls in *.
  unfold bitsToBv_ls in *.
  apply eq_if_rev_eq in H1.
  unfold fromZ_ls in *.
  destruct x; destruct y; trivial; try lia.
  symmetry in H1.
  apply fromPosZ_ls_0_impl in H1.
  rewrite Z.mod_small in H1.
  lia.
  lia.

  apply fromPosZ_ls_0_impl in H1.
  rewrite Z.mod_small in H1.
  lia.
  lia.
  rewrite <- (@Z.mod_small _  (2 ^ Z.of_nat n)).
  symmetry.
  rewrite <- (@Z.mod_small _  (2 ^ Z.of_nat n)).
  symmetry.
  apply fromPosZ_eq_impl.
  trivial.
  lia.
  lia.

Qed.

Theorem zipWith_ls_0_if : forall x y n,
  length x = length y ->
  zipWith_ls or x y = repeat false n ->
  x = (repeat false n) /\ y = repeat false n.

  induction x; destruct y; destruct n; intros; simpl in *; trivial; try lia; try discriminate.
  intuition idtac; trivial.
  inversion H0; clear H0; subst.
  rewrite H2 in H3.
  assert (List.length x = List.length y ) by lia.
  specialize (IHx y n).
  intuition idtac;
  subst; f_equal; eauto; destruct a; destruct b; simpl in *; trivial; discriminate.

Qed.
  

Theorem ecOr_0_if
  : forall (n : nat) (x y : bitvector n),
    ecOr (bitvector n) (PLogicWord n) x y = replicate n bool 0%bool -> x = replicate n bool 0%bool /\ y = replicate n bool 0%bool.

  intros.
  unfold ecOr in *.
  simpl in *.
  unfold bvOr, bvZipWith in *.
  apply eq_impl_to_list_eq in H.
  rewrite <- replicate_repeat_eq in *.
  rewrite zipWith_ls_eq in *.
  apply zipWith_ls_0_if in H.
  intuition idtac.
  apply eq_if_to_list_eq.
  rewrite <- replicate_repeat_eq.
  trivial.
  apply eq_if_to_list_eq.
  rewrite <- replicate_repeat_eq.
  trivial.

  repeat rewrite length_to_list.
  reflexivity.

Qed.

Theorem fold_or_impl_0 : forall (n1 n2 : nat) x y,
  ecFoldl n1 (CryptolPrimitivesForSAWCore.seq n2 Bool) (CryptolPrimitivesForSAWCore.seq n2 Bool) (ecOr (CryptolPrimitivesForSAWCore.seq n2 Bool) (PLogicSeqBool n2))
     y x = intToBv n2 0 ->
  (x = (replicate n1 _ (replicate n2 _ false)) /\ y = (replicate n2 _ false)).

  induction n1; intros; simpl in *.
  unfold replicate. simpl in *.
  generalize H.
  eapply (case0 (fun x => foldl (bitvector n2) (bitvector n2) 0%nat (ecOr (bitvector n2) (PLogicWord n2)) y x = intToBv n2 0 ->
x = @Vector.nil (Vec n2 bool) /\ y = gen n2 bool (fun _ : Nat => false))); eauto; intuition.
  simpl in *; subst.
  rewrite <- rep_false_eq_int_bv.
  trivial.

  unfold replicate in *. simpl.
  generalize H.
  eapply (caseS' x); intuition;
  simpl in *;
  edestruct IHn1; eauto;
  subst.
  f_equal.
  edestruct ecOr_0_if; eauto.
  edestruct ecOr_0_if; eauto.

Qed.


Theorem sawAt_zero_eq
     : forall (T : Type) (size : nat) (h : T) (t : Vector.t T size), sawAt (S size) T (Vector.cons h t) 0%nat = h.

  intros.
  specialize (sawAt_zero _ size h t); intros.
  simpl in *.
  trivial.

Qed.

Theorem vecEq_correct : forall (A : Type)(inh : Inhabited A) f n (v1 v2 : Vec n A),
  (forall a1 a2, f a1 a2 = true -> a1 = a2) ->
   vecEq n A f v1 v2 = true ->
  v1 = v2.

  induction v1; intros; simpl in *.
  specialize (Vec_0_nil _ v2); intros.
  subst.
  reflexivity.

  destruct (Vec_S_cons _ _ v2). destruct H1. subst.
  unfold vecEq in *.
  simpl in *.
  replace (sawAt (S n) A (VectorDef.cons h v1) 0%nat) with h in *.
  replace (sawAt (S n) A (Vector.cons x x0) 0%nat) with x in *.
  apply and_bool_eq_true in H0.
  intuition idtac.
  f_equal.
  apply H.
  trivial.
  apply IHv1.
  trivial.
  apply H2.
  symmetry.
  eapply sawAt_zero_eq.
  symmetry.
  eapply sawAt_zero_eq.
  Unshelve.
  apply n.
  trivial.
  apply n.
  trivial.

Qed.


Theorem ecNotEq_vec_bv_true
  : forall (n1 n2 : nat) (v1 v2 : Vec n1 (bitvector n2)), v1 <> v2 -> ecNotEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v1 v2 = 1%bool.


  intros.
  unfold ecNotEq, ecEq in *;
  intros; simpl in *.
  unfold not.
  apply Bool.eq_true_not_negb.
  intuition idtac.
  apply H.
  eapply vecEq_correct.
  intros.
  apply bvEq_eq.
  eauto.
  trivial.

Qed.

Theorem vecEq_refl : forall (A : Type)(inh : Inhabited A) f n (v1 : Vec n A),
  (forall a1, f a1 a1 = true) ->
   vecEq n A f v1 v1 = true.

  induction v1; intros; simpl in *.
  unfold vecEq in *.
  simpl in *.
  reflexivity.

  unfold vecEq in *.
  simpl in *.
  replace (sawAt (S n) A (VectorDef.cons h v1) 0%nat) with h.
  rewrite H.
  simpl.
  apply IHv1.
  trivial.
  symmetry.
  eapply sawAt_zero_eq.
  Unshelve.
  apply n.
  trivial.
Qed.

Theorem ecNotEq_vec_bv_false : forall (n1 n2 : nat) (v : Vec n1 (bitvector n2)), ecNotEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v v = 0%bool.

  intros.
  unfold ecNotEq, ecEq in *.
  simpl in *.
  unfold not.
  apply Bool.negb_false_iff.
  
  intuition idtac.
  apply vecEq_refl.
  apply bvEq_refl.

Qed.


Theorem gen_ls_eq:
  forall [A : Type] [n: nat] (f : nat -> A),
  to_list (gen n A f) =
  gen_ls n f.

  induction n; intros; simpl in *.
  reflexivity.

  rewrite to_list_cons.
  f_equal.
  eapply IHn.

Qed.

Theorem gen_ls_rev : forall (A : Type) n (f : nat -> A),
  (n > 0)%nat ->
  gen_ls n f = gen_ls (pred n) f ++ [f (pred n)].

  induction n; intros; simpl in *.
  lia.
  destruct n.
  simpl.
  reflexivity.
  rewrite IHn.
  simpl.
  reflexivity.
  lia.

Qed.

Theorem ecFromTo_m_n_equiv_h : forall n m : nat,
  gen_ls n (fun n0 : nat => Z.of_nat (n0 + m)) =
  map (Z.add (Z.of_nat m)) (toN_excl_int n).

  induction n;
  intros. simpl in *. trivial.
  
  rewrite gen_ls_rev.
  simpl.
  rewrite IHn.
  rewrite map_app.
  simpl.
  f_equal.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.add_comm.
  reflexivity.
  lia.

Qed.

Theorem ecFromTo_m_n_equiv : forall m n : Nat, 
  to_list (ecFromTo m n Integer PLiteralInteger) = List.map (Z.add (Z.of_nat m)) (toN_int (n - m)).

  intros.
  unfold ecFromTo.
  simpl.
  rewrite to_list_cons.
  rewrite gen_ls_eq.
  rewrite subNat_sub.
  rewrite (@gen_ls_ext _ _ _ (fun n => Z.of_nat (n + m)%nat + 1)).
  unfold toN_int.
  rewrite map_app.
  simpl.
  rewrite <- ecFromTo_m_n_equiv_h.
    
  destruct (eq_nat_dec (n-m)%nat O).
  rewrite e.
  simpl.
  rewrite Z.add_0_r.
  reflexivity.
  rewrite gen_ls_rev.
  remember (n - m)%nat as z.
  destruct z.
  lia.
  simpl.
  f_equal.
  f_equal.
  eapply gen_ls_ext.
  intros.
  lia.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Znat.Zpos_P_of_succ_nat.
  rewrite <- Z.add_1_r.
  rewrite (Z.add_comm (Z.of_nat z)).
  rewrite Z.add_assoc.
  reflexivity.
  lia.
  intros.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Znat.Zpos_P_of_succ_nat.
  rewrite <- Z.add_1_r.
  rewrite addNat_add.
   rewrite Znat.Nat2Z.inj_add.
  reflexivity.
Qed.

Theorem ecFromTo_0_n_equiv : forall n : Nat, to_list (ecFromTo 0%nat n Integer PLiteralInteger) = toN_int n.

  intros.
  specialize (ecFromTo_m_n_equiv 0%nat); intros.
  rewrite H.
  rewrite Nat.sub_0_r.
  rewrite (map_ext _ (fun x => x)).
  apply map_id.
  intros.
  apply Z.add_0_l.
Qed.  

Theorem ecFromTo_0_n_bv_excl_equiv : forall (s : nat) (n : Nat), to_list (ecFromTo 0%nat n (CryptolPrimitivesForSAWCore.seq s Bool) (PLiteralSeqBool s)) = toN_excl_bv s (S n).

  intros.
  rewrite ecFromTo_0_n_bv_equiv.
  unfold toN_bv.
  simpl.
  reflexivity.


Qed.

Theorem foldl_ls_eq : forall (A B : Type) f n ls a,
  foldl B A n f a ls = fold_left f (to_list ls) a.

  induction ls; intros; simpl in *.
  trivial.
  rewrite IHls.
  reflexivity.

Qed.


Theorem ecFoldl_foldl_equiv
  : forall (A B : Type) (inhB : Inhabited B) (f : A -> B -> A) (n : Nat) (ls : CryptolPrimitivesForSAWCore.seq n B) (a : A), ecFoldl n A B f a ls = List.fold_left f (to_list ls) a.

  intros.
  unfold ecFoldl.
  simpl.
  apply foldl_ls_eq.

Qed.

Theorem ecEq_vec_bv_true : forall (n1 n2 : nat) (v : Vec n1 (bitvector n2)), ecEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v v = 1%bool.
  intros.
  unfold ecEq.
  simpl.
  apply vecEq_refl.
  apply bvEq_refl.

Qed.

Theorem ecEq_vec_bv_false
  : forall (n1 n2 : nat) (v1 v2 : Vec n1 (bitvector n2)), v1 <> v2 -> ecEq (Vec n1 (bitvector n2)) (PEqVec n1 (bitvector n2) (PEqWord n2)) v1 v2 = 0%bool.

  intros.
  unfold ecEq.
  simpl.
  case_eq (vecEq n1 (bitvector n2) (bvEq n2) v1 v2); intros; trivial.
  exfalso.
  apply H.
  eapply vecEq_correct; eauto.
  intros.
  apply bvEq_eq.
  eauto.

Qed.

Definition toNat_ls bs := 
  seq.foldr (fun (b : bool) (n : nat) => if b then (S (2 * n)%nat) else (2*n)%nat) 0%nat bs.

Definition bvToNat_ls n (v : Vec n bool) :=
  toNat_ls (bvToBITS_ls v).

Definition bvToNat_ls_0 n (v : Vec n bool) :=
  seq.foldl bvToNatFolder 0%nat (to_list v).

Theorem foldr_eq : forall [T R : Type] (f : T -> R-> R) (z : R) (s : list T), seq.foldr f z s = fold_right f z s .
  intros.
  reflexivity.

Qed.


Theorem foldl_eq : forall [T R : Type] (f : R -> T-> R) (s : list T) z, seq.foldl f z s = fold_left f s z .
 
  induction s; intros; simpl in *; trivial.
 
Qed.

Theorem Vector_fold_left_eq : forall [T R : Type] (f : R -> T-> R) n (v : Vec n T) z, 
  Vector.fold_left f z v = foldl _ _ n f z v.

  induction v; intros; simpl in *; trivial.

Qed.

Theorem bvToNat_ls_0_eq : forall n (v : Vec n bool),
  bvToNat n v = bvToNat_ls_0 v.

  intros.
  unfold bvToNat, bvToNat_ls_0.
  rewrite Vector_fold_left_eq.
  rewrite foldl_eq.
  apply foldl_ls_eq.

Qed.


Theorem foldr_rev:
  forall [T R : Type] (f : T -> R-> R) (s : list T) z, seq.foldr f z (rev s) = seq.foldl (fun (x : R) (z0 : T) => f z0 x) z s.

  induction s; intros; simpl in *; trivial.
  simpl in *. 
  rewrite foldr_eq.
  rewrite fold_right_app.
  rewrite <- foldr_eq.
  rewrite IHs.
  reflexivity.

Qed.

Theorem bvToNat_ls_eq : forall n (v : Vec n bool),
  bvToNat n v = bvToNat_ls v.

  intros.
  rewrite bvToNat_ls_0_eq.
  unfold bvToNat_ls, bvToNat_ls_0.
  unfold bvToBITS_ls, toNat_ls.
  rewrite foldr_rev.
  repeat rewrite foldl_eq.
  apply fold_left_ext.
  intros.
  
  unfold bvToNatFolder.
  rewrite <- ssrnat.addnn.
  repeat rewrite <- ssrnat.plusE.
  simpl.
  destruct b; simpl in *.
  lia.
  lia.
Qed.

Theorem toNat_ls_of_nat_eq : forall ls, 
  Z.of_nat (toNat_ls ls) = toPosZ_ls ls.

  induction ls; intros; simpl in *; trivial.
  rewrite <- IHls.
  destruct a.
  lia.
  lia.

Qed.

Theorem bvToNat_toZ_equiv : forall (n : Nat) (x : bitvector n), BinInt.Z.of_nat (bvToNat n x) = bvToInt n x.

  intros.
  rewrite <- bvToInt_ls_equiv.
  rewrite bvToNat_ls_eq.
  unfold bvToNat_ls, bvToInt_ls.
  apply toNat_ls_of_nat_eq.

Qed.

Theorem toNat_ls_lt_word : forall (ls : list bool), (BinInt.Z.of_nat (toNat_ls ls) < 2 ^ BinInt.Z.of_nat (length ls))%Z.

  induction ls; intros.
  simpl in *; try lia.
  
  simpl toNat_ls.
  simpl List.length.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  destruct a.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  rewrite plus_0_r.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.pow_add_r.
  lia.
  lia.
  lia.

  rewrite plus_0_r.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.pow_add_r.
  lia.
  lia.
  lia.

Qed.


Theorem bvToNat_lt_word : forall (n : Nat) (x : bitvector n), (BinInt.Z.of_nat (bvToNat n x) < 2 ^ BinInt.Z.of_nat n)%Z.

  intros.
  rewrite bvToNat_ls_eq.
  eapply Z.lt_le_trans.
  apply toNat_ls_lt_word.
  eapply Z.pow_le_mono.
  lia.
  unfold bvToBITS_ls.
  rewrite rev_length.
  rewrite length_to_list.
  lia.

Qed.

Theorem toNat_ls_0_tl_eq : forall x,
  toNat_ls (x ++ [0%bool]) = toNat_ls x.

  induction x; intros; simpl in *; trivial.
  destruct a.
  rewrite IHx.
  lia.
  rewrite IHx.
  lia.

Qed.

Theorem toNat_ls_toPosZ_ls_eq : forall x,
  toNat_ls x = Z.to_nat (toPosZ_ls x).

  induction x; intros; simpl in *; trivial.
  destruct a.
  rewrite IHx.
  rewrite Z.double_spec.
  rewrite <- Z.add_1_r.
  rewrite Znat.Z2Nat.inj_add.
  rewrite Znat.Z2Nat.inj_mul.
  lia.
  lia.
  apply toPosZ_ls_nonneg.
  specialize (toPosZ_ls_nonneg x); intros.
  lia.
  lia.

  rewrite IHx.
  rewrite Z.double_spec.
  rewrite Znat.Z2Nat.inj_mul.
  lia.
  lia.
  apply toPosZ_ls_nonneg.
Qed.

Theorem toNat_ls_toZ_ls_eq : forall x,
  0 <= toZ_ls x ->
  toNat_ls x = Z.to_nat (toZ_ls x).

  intros.
  destruct x using rev_ind.
  reflexivity.
  clear IHx.
  unfold toZ_ls in *.
  rewrite splitmsb_ls_app_eq in *.
  destruct x.
  specialize (toNegZ_ls_nonneg x0); intros.
  lia.
  rewrite toNat_ls_0_tl_eq.
  apply toNat_ls_toPosZ_ls_eq.

Qed.

Theorem bvToNat_Z_to_nat_equiv : forall (n : Nat) (x : bitvector n) (z : Z), (0 <= z)%Z -> sbvToInt n x = z -> bvToNat n x = BinInt.Z.to_nat z.

  intros.
  subst.
  rewrite bvToNat_ls_eq.
  rewrite <- sbvToInt_ls_equiv in *.
  unfold bvToNat_ls, sbvToInt_ls.
  destruct n.
  specialize (Vec_0_nil _ x); intros; subst.
  reflexivity.

  unfold bvToBITS_ls.
  apply toNat_ls_toZ_ls_eq.
  eauto.

Qed.

Theorem shiftR1_ls_rev_eq : forall (A : Type)(ls : list A) (a : A),
  rev (shiftR1_ls a ls)  = shiftL1_ls a (rev ls).

  intros.
  unfold shiftR1_ls, shiftL1_ls, shiftout_ls, shiftin_ls.
  simpl.
  specialize (@skipn_rev A 1%nat (a::ls)); intros.
  rewrite skipn_1_eq_tl in *.
  simpl in *.
  rewrite  H.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.

Theorem shiftR_ls_rev_eq : forall (A : Type)(ls : list A) n (a : A),
  rev (shiftR_ls a ls n)  = shiftL_ls a (rev ls) n.

  induction n; intros; simpl in *; trivial.
  rewrite shiftR1_ls_rev_eq.
  f_equal.
  eauto.

Qed.

Theorem shiftL1_ls_rev_eq : forall (A : Type)(ls : list A) (a : A),
  rev (shiftL1_ls a ls)  = shiftR1_ls a (rev ls).

  intros.
  unfold shiftR1_ls, shiftL1_ls, shiftout_ls, shiftin_ls.
  simpl.
  specialize (@skipn_rev A 1%nat (a::rev ls)); intros.
  rewrite skipn_1_eq_tl in *.
  simpl in *.
  rewrite Nat.sub_0_r in *.
  rewrite rev_involutive in *.
  rewrite H. 
  rewrite rev_involutive.
  reflexivity.
Qed.

Theorem shiftL_ls_rev_eq : forall (A : Type)(ls : list A) n (a : A),
  rev (shiftL_ls a ls n)  = shiftR_ls a (rev ls) n.

  induction n; intros; simpl in *; trivial.
  rewrite shiftL1_ls_rev_eq.
  f_equal.
  eauto.

Qed.

Theorem toPosZ_ls_shiftL1_ls_eq: forall ls,
  toPosZ_ls (shiftL1_ls 0%bool ls) = (toPosZ_ls ls) / 2.

  intros.
  unfold shiftL1_ls.
  unfold shiftin_ls.
  destruct ls; simpl.
  reflexivity.

  rewrite toPosZ_app_0_eq.
  rewrite Z.double_spec.
  rewrite <- Z.add_1_l.
  destruct b.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_plus; try lia.
  rewrite Z.div_small; lia.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_mult; lia.

Qed.

Theorem toPosZ_ls_shiftL_ls_eq : forall n ls,
  toPosZ_ls (shiftL_ls 0%bool ls n) = (toPosZ_ls ls) / (2 ^ (Z.of_nat n)).

  induction n; intros.
  simpl in *.
  rewrite Z.div_1_r.
  reflexivity.
  simpl shiftL_ls.
  rewrite toPosZ_ls_shiftL1_ls_eq.
  rewrite IHn.
  rewrite Zdiv.Zdiv_Zdiv; try lia.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.pow_1_r.
  reflexivity.

Qed.

Theorem bvToInt_shiftR_lt
  : forall (n : Nat) (v : bitvector n) (s : nat) (b : Z), 
  0 <= b ->
  (bvToInt n v < 2 ^ (BinInt.Z.of_nat s + b))%Z -> (bvToInt n (shiftR n bool 0%bool v s) < 2 ^ b)%Z.

  intros.
  rewrite <-  bvToInt_ls_equiv in *.
  unfold bvToInt_ls in *.
  unfold bvToBITS_ls in *.
  rewrite shiftR_ls_equiv.
  rewrite shiftR_ls_rev_eq.
  rewrite toPosZ_ls_shiftL_ls_eq.
  rewrite  Z.pow_add_r in *; try lia.
  apply Zdiv.Zdiv_lt_upper_bound.
  apply Z.pow_pos_nonneg; lia.
  lia.

Qed.

Theorem bvToInt_shiftR_equiv : forall (n s : nat) (x : Vector.t bool n), (s >= 0)%nat -> bvToInt n (shiftR n bool 0%bool x s) = BinInt.Z.shiftr (bvToInt n x) (BinInt.Z.of_nat s).

  intros.
  repeat rewrite <- bvToInt_ls_equiv.
  unfold bvToInt_ls.
  unfold bvToBITS_ls.
  rewrite shiftR_ls_equiv.
  rewrite shiftR_ls_rev_eq.
  rewrite toPosZ_ls_shiftL_ls_eq.
  rewrite Z.shiftr_div_pow2.
  reflexivity.
  lia.

Qed.

Theorem toPosZ_ls_app : forall x1 x2,
  toPosZ_ls (x1 ++ x2) = (toPosZ_ls x1) + (toPosZ_ls x2)*2^(Z.of_nat (length x1)).

  induction x1; intros.
  simpl in *.
  rewrite Z.mul_1_r.
  reflexivity.
  simpl List.length.
  rewrite <- Nat.add_1_r.
  simpl.
  destruct a.
  rewrite IHx1.
  repeat rewrite <- Z.add_1_l.
  repeat rewrite Z.double_spec.
  rewrite Z.mul_add_distr_l.
  rewrite Z.add_assoc.
  f_equal.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.pow_add_r; try lia.

  rewrite IHx1.
  rewrite Z.double_spec.
  rewrite Z.mul_add_distr_l.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.pow_add_r; try lia.

Qed.

Theorem toPosZ_ls_shiftR1_ls_eq: forall ls,
  toPosZ_ls (shiftR1_ls 0%bool ls) = ((toPosZ_ls ls) * 2) mod (2 ^ (Z.of_nat (length ls))).

  intros.
  unfold shiftR1_ls.
  unfold shiftout_ls.
  simpl.
  destruct ls using rev_ind.
  simpl.
  reflexivity.
  clear IHls.
  rewrite app_length.
  rewrite plus_comm.
  simpl List.length.
  rewrite plus_comm at 2.
  simpl.
  rewrite firstn_app_1; try lia.
  rewrite firstn_all.
  rewrite toPosZ_ls_app.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.mul_add_distr_r.
  rewrite Z.pow_1_r.
  rewrite <- Z.mul_assoc.
  rewrite Zdiv.Z_mod_plus_full.
  rewrite Z.mod_small.
  rewrite Z.double_spec.
  lia.
  specialize (toPosZ_ls_nonneg ls); intros.
  specialize (toPosZ_ls_upper_bound ls); intros.
  lia.

Qed.

Theorem toPosZ_ls_shiftR_ls_eq : forall n ls,
  toPosZ_ls (shiftR_ls 0%bool ls n) = (toPosZ_ls ls) * (2 ^ (Z.of_nat n)) mod (2 ^ (Z.of_nat (length ls))).

  induction n; intros.
  simpl in *.
  rewrite Z.mul_1_r.
  rewrite Z.mod_small.
  reflexivity.
  specialize (toPosZ_ls_nonneg ls); intros.
  specialize (toPosZ_ls_upper_bound ls); intros.
  lia.

  simpl shiftR_ls.
  rewrite toPosZ_ls_shiftR1_ls_eq.
  rewrite IHn.
  rewrite shiftR_ls_length.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.pow_1_r.
  rewrite Zdiv.Zmult_mod_idemp_l.
  rewrite Z.mul_assoc.
  reflexivity.

Qed.

Theorem bvToInt_shiftL_1_equiv : forall n s : nat, (s < n)%nat -> bvToInt n (shiftL n bool 0%bool (intToBv n 1) s) = BinInt.Z.shiftl 1 (BinInt.Z.of_nat s).

  intros.
  repeat rewrite <- bvToInt_ls_equiv.
  unfold bvToInt_ls.
  unfold bvToBITS_ls.
  rewrite shiftL_to_list_eq.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls, bitsToBv_ls.
  rewrite shiftL_ls_rev_eq.
  rewrite rev_involutive.
  rewrite toPosZ_ls_shiftR_ls_eq.
  rewrite fromZ_ls_length.
  unfold fromZ_ls.
  rewrite toPosZ_ls_fromPosZ_ls_eq.
  rewrite Z.mul_1_l.
  rewrite Z.mod_small.
  rewrite Z.shiftl_1_l.
  reflexivity.
  intuition idtac.
  eapply Z.pow_nonneg.
  lia.
  eapply Z.pow_lt_mono_r; lia.
  intuition idtac; try lia.
  eapply (Z.le_lt_trans _ (2^(Z.of_nat 0%nat))).
  reflexivity.
  eapply Z.pow_lt_mono_r; lia.

Qed.

Theorem toPosZ_ls_toZ_ls_equiv : forall ls,
  toPosZ_ls ls < 2^(Z.of_nat (pred (length ls))) ->
  toZ_ls ls = toPosZ_ls ls.

  intros.
  unfold toZ_ls.
  destruct ls using rev_ind.
  simpl.
  trivial.
  clear IHls.
  rewrite splitmsb_ls_app_eq.
  rewrite toPosZ_ls_app in *.
  rewrite app_length in *.
  simpl in *.
  rewrite plus_comm in H.
  simpl in *.
  destruct x.
  specialize (toPosZ_ls_nonneg ls); intros.
  lia.
  lia.

Qed.

Theorem bvToInt_sbvToInt_equiv : forall (n : nat) (v : bitvector n), (n > 0)%nat -> (bvToInt n v < 2 ^ BinInt.Z.of_nat (Nat.pred n))%Z -> sbvToInt n v = bvToInt n v.

  intros.
  rewrite <- sbvToInt_ls_equiv.
  repeat rewrite <- bvToInt_ls_equiv in *.
  unfold sbvToInt_ls, bvToInt_ls in *.
  destruct n.
  lia.
  simpl in *.
  eapply toPosZ_ls_toZ_ls_equiv.
  unfold bvToBITS_ls.
  rewrite rev_length.
  rewrite length_to_list.
  simpl.
  eauto.

Qed.

Theorem bvToInt_nonneg : forall (n : Nat) (v : bitvector n), (0 <= bvToInt n v)%Z.

  intros.
  rewrite <- bvToInt_ls_equiv.
  unfold bvToInt_ls.
  apply toPosZ_ls_nonneg.

Qed.

Theorem bvToInt_intToBv_id : forall (n : Nat) (v : Z),
  0 <= v < 2 ^ (Z.of_nat n)->
   bvToInt n (intToBv n v) = v.

  intros.
  rewrite <- bvToInt_ls_equiv.
  unfold bvToInt_ls.
  unfold bvToBITS_ls.
  rewrite <- intToBv_ls_eq.
  unfold intToBv_ls, bitsToBv_ls.
  rewrite rev_involutive.
  unfold fromZ_ls.
  destruct v.
  apply toPosZ_ls_repeat_0.
  apply toPosZ_ls_fromPosZ_ls_eq.
  trivial.
  lia.

Qed.


Theorem bvToInt_bound : forall (n : Nat) (v : bitvector n), (0 <= bvToInt n v < 2 ^ BinInt.Z.of_nat n)%Z.

  intros.
  rewrite <- bvToInt_ls_equiv.
  unfold bvToInt_ls.
  intuition idtac.
  eapply toPosZ_ls_nonneg.
  unfold bvToBITS_ls.
  eapply Z.lt_le_trans.
  eapply toPosZ_ls_upper_bound.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  
Qed.

Theorem tuple_tval_eq : forall (A : Type) n (t1 t2 : tuple.tuple_of n A),
  t1 = t2 ->
  tuple.tval t1 = tuple.tval t2.

  intros.
  destruct t1. destruct t2.
  inversion H.
  simpl in *.
  trivial.

Qed.

Definition sshiftL_ls (A : Type) (a : A)(v : list A) (i : nat) :=
  ssrnat.iter i (shiftL1_ls (last v a)) v.

Theorem joinmsb_ls_eq : forall n (v : spec.BITS n) b,
  tuple.tval (spec.joinmsb (b,v)) = (tuple.tval v) ++ [b].

  induction n; intros; simpl in *.
  destruct v.
  destruct tval.
  trivial.
  inversion i.
  destruct (tuple_S_ex v).
  destruct H.
  subst.
  simpl.
  rewrite tuple_head_cons.
  f_equal.
  rewrite tuple_behead_cons.
  rewrite IHn.
  reflexivity.

Qed.

Theorem app_tl_eq : forall (A : Type)(ls1 ls2 : list A),
  (length ls1 > 0)%nat ->
  tl (ls1 ++ ls2) = (tl ls1) ++ ls2.

  destruct ls1; intros; simpl in *; trivial; lia.

Qed.

Theorem droplsb_ls_eq : forall n (b : spec.BITS (S n)),
  tuple.tval (spec.droplsb b) = tl (tuple.tval b).

  intros. 
  unfold spec.droplsb.
  unfold spec.splitlsb.
  simpl.
  destruct (tuple_S_ex b).
  destruct H.
  subst.
  simpl.
  reflexivity.

Qed. 

Theorem last_ov_eq : forall (A : Type)(ls : list A) a1 a2,
  (length ls > 0)%nat ->
  last ls a1 = last ls a2.

  induction ls; intros; simpl in *; try lia.
  destruct ls; trivial.
  eapply IHls.
  simpl.
  lia.

Qed.

Theorem seq_last_eq : forall (A : Type)(ls : list A) a,
  seq.last a ls = last ls a.

  induction ls; intros; simpl in *; trivial.
  rewrite IHls.
  destruct ls; trivial.
  apply last_ov_eq.
  simpl. lia.

Qed.

Theorem sarB_shiftL1_ls_eq : forall n (v : spec.BITS (S n)),
  tuple.tval (sarB v) = shiftL1_ls (last (tuple.tval v) false) (tuple.tval v).

  intros.
  unfold sarB, shiftL1_ls, shiftin_ls.
  rewrite joinmsb_ls_eq.
  rewrite app_tl_eq.
  rewrite droplsb_ls_eq.
  f_equal.
  unfold spec.msb.
  rewrite seq_last_eq.
  reflexivity.
  rewrite tuple_tval_length.
  lia.

Qed.

Theorem shiftL1_ls_last_same : forall (A : Type) (ls : list A)  a,
  last (shiftL1_ls (last ls a) ls) a = last ls a.

  intros.
  unfold shiftL1_ls.
  unfold shiftin_ls.
  destruct ls.
  simpl. trivial.
  rewrite app_tl_eq.
  rewrite last_last.
  reflexivity.
  simpl. lia.

Qed.

Theorem shiftL1_ls_last_same_gen : forall (A : Type) (ls : list A)  a b,
  (last ls a) = b ->
  last (shiftL1_ls b ls) a = b.

  intros. subst.
  apply shiftL1_ls_last_same.
Qed.

Theorem sshiftL_ls_last_same : forall (A : Type) i (ls : list A) a,
  last (sshiftL_ls a ls i) a = last ls a.

  induction i; intros; simpl in *; trivial.
  eapply shiftL1_ls_last_same_gen.
  eapply IHi.

Qed.

Theorem sshiftL_ls_eq : forall i n (v : spec.BITS (S n)),
  (tuple.tval (ssrnat.iter i sarB v)) = sshiftL_ls false (tuple.tval v) i.

  induction i; intros; simpl in *; trivial.
  rewrite sarB_shiftL1_ls_eq.
  rewrite IHi.
  f_equal.
  rewrite sshiftL_ls_last_same.
  reflexivity.

Qed.

Local Transparent bvSShr.

Theorem bvSShr_all_nonneg : forall (n1 : nat) (v : bitvector (S n1)), (0 <= sbvToInt (S n1) v)%Z -> bvSShr n1 v n1 = replicate (S n1) bool 0%bool.

  intros.
  unfold bvSShr.
  apply eq_if_to_list_eq.
  rewrite <- bitsToBv_ls_eq.
  rewrite <- replicate_repeat_eq.
  rewrite sshiftL_ls_eq.
  unfold sshiftL_ls.
  rewrite <- sbvToInt_ls_equiv in *.
  rewrite bvToBITS_ls_equiv.
  unfold sbvToInt_ls in *.
  unfold bvToBITS_ls, bitsToBv_ls in *.
  destruct (Vec_S_cons _ _ v).
  destruct H0.
  subst.
  rewrite to_list_cons in *.
  simpl in *.
  unfold toZ_ls in *.
  rewrite splitmsb_ls_app_eq in *.
  destruct x.
  match goal with
  | [H : 0 <= - Z.succ (toNegZ_ls ?a) |- _] =>
    specialize (toNegZ_ls_nonneg a); intros
  end.
  lia.

  rewrite last_last.
  specialize (shiftL_ls_rev_eq); intros.
  unfold shiftL_ls  in *.
  rewrite H0.
  rewrite rev_app_distr.
  rewrite rev_involutive.
  simpl.
  rewrite shiftR_ls_eq_repeat.
  rewrite repeat_cons.
  f_equal.
  simpl List.length.
  rewrite length_to_list.
  replace (S n1 - n1)%nat with 1%nat.
  simpl.
  reflexivity.
  lia.
  simpl.
  rewrite length_to_list.
  lia.

Qed.

Theorem bvSShr_all_neg : forall (n1 : nat) (v : bitvector (S n1)), (sbvToInt (S n1) v < 0)%Z -> bvSShr n1 v n1 = replicate (S n1) bool 1%bool.

  intros.
  unfold bvSShr.
  apply eq_if_to_list_eq.
  rewrite <- bitsToBv_ls_eq.
  rewrite <- replicate_repeat_eq.
  rewrite sshiftL_ls_eq.
  unfold sshiftL_ls.
  rewrite <- sbvToInt_ls_equiv in *.
  rewrite bvToBITS_ls_equiv.
  unfold sbvToInt_ls in *.
  unfold bvToBITS_ls, bitsToBv_ls in *.
  destruct (Vec_S_cons _ _ v).
  destruct H0.
  subst.
  rewrite to_list_cons in *.
  simpl in *.
  unfold toZ_ls in *.
  rewrite splitmsb_ls_app_eq in *.
  destruct x.

  rewrite last_last.
  specialize (shiftL_ls_rev_eq); intros.
  unfold shiftL_ls  in *.
  rewrite H0.
  rewrite rev_app_distr.
  rewrite rev_involutive.
  simpl.
  rewrite shiftR_ls_eq_repeat.
  rewrite repeat_cons.
  f_equal.
  simpl List.length.
  rewrite length_to_list.
  replace (S n1 - n1)%nat with 1%nat.
  simpl.
  reflexivity.
  lia.
  simpl.
  rewrite length_to_list.
  lia.

  match goal with
  | [H : toPosZ_ls ?a < 0 |- _] =>
    specialize (toPosZ_ls_nonneg a); intros
  end.
  lia.

Qed.

Theorem tl_length : forall (A : Type)(ls : list A),
  (0 < length ls)%nat ->
  length (tl ls) = pred (length ls).

  intros.
  destruct ls; simpl in *; trivial; lia.

Qed.

Theorem shiftL1_ls_length : forall (A : Type) ls,
  length (shiftL1_ls A ls) = length ls.

  intros.
  unfold shiftL1_ls, shiftin_ls.
  rewrite tl_length;
  rewrite app_length;
  simpl.
  lia.
  lia.

Qed.

Theorem shiftL1_ls_Z_shiftr_equiv : forall ls,
  toZ_ls (shiftL1_ls (last ls 0%bool) ls) = (Z.shiftr (toZ_ls ls) 1).

  intros. 
  unfold shiftL1_ls, shiftin_ls.
  destruct ls using rev_ind.
  simpl.
  reflexivity.
  clear IHls.
  rewrite last_last.
  rewrite app_tl_eq.
  unfold toZ_ls.
  repeat rewrite splitmsb_ls_app_eq.
  destruct x.
  
  destruct ls; simpl.
  rewrite <- Z.div2_spec.
  rewrite Z.div2_div.
  rewrite <- Pos2Z.opp_pos.
  rewrite Z.div_opp_l_nz; try lia.
  rewrite Z.div_small; try lia.
  rewrite Z.mod_small; lia.

  rewrite toNegZ_app_1_eq.
  rewrite <- Z.div2_spec.
  rewrite Z.div2_div.
  destruct b.
  rewrite Z.double_spec.
  repeat rewrite <- Z.add_1_l.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_nz_opp_full.
  rewrite Zdiv.Z_div_plus; try lia.
  rewrite Z.div_small; try lia.
  lia.
  rewrite Zdiv.Z_mod_plus; try lia.
  rewrite Z.mod_small; lia.

  rewrite Z.double_spec.
  repeat rewrite <- Z.add_1_l.
  rewrite Zdiv.Z_div_zero_opp_full.
  rewrite Z.mul_comm.
  rewrite Z.add_assoc.
  rewrite Zdiv.Z_div_plus_full; try lia.
  reflexivity.
  rewrite Z.add_assoc.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_mod_plus_full.
  reflexivity.  

  destruct ls; simpl.
  reflexivity.
  rewrite toPosZ_app_0_eq.
  repeat rewrite Z.double_spec.
  rewrite <- Z.add_1_l.
  rewrite <- Z.div2_spec.
  rewrite Z.div2_div.
  rewrite Z.mul_comm.
  destruct b.
  rewrite Zdiv.Z_div_plus; try lia.
  rewrite Z.div_small;lia.
  rewrite Zdiv.Z_div_mult.
  reflexivity.
  lia.

  rewrite app_length; simpl; lia.

Qed.

Theorem sshiftL_Z_shiftr_equiv : forall y1 ls, 
  toZ_ls (sshiftL_ls 0%bool ls  y1) = Z.shiftr (toZ_ls ls) (Z.of_nat y1).

  induction y1; intros.
  simpl in *.
  rewrite Z.shiftr_0_r.
  reflexivity.

  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_r.
  rewrite <- Z.shiftr_shiftr.
  simpl.
  erewrite <- sshiftL_ls_last_same.
  rewrite shiftL1_ls_Z_shiftr_equiv.
  rewrite IHy1.
  reflexivity.
  lia.

Qed.

Theorem bvSShr_Z_shiftr_equiv
  : forall (n : nat) (x1 : bitvector (S n)) (x2 : Z) (y1 : nat) (y2 : Z),
    BinInt.Z.of_nat y1 = y2 -> sbvToInt (S n) x1 = x2 -> sbvToInt (S n) (bvSShr n x1 y1) = BinInt.Z.shiftr x2 y2.

  intros.
  subst.
  repeat rewrite <- sbvToInt_ls_equiv.
  unfold sbvToInt_ls.
  unfold bvToBITS_ls.
  unfold bvSShr.
  rewrite <- bitsToBv_ls_eq.
  unfold bitsToBv_ls.
  rewrite rev_involutive.
  rewrite sshiftL_ls_eq.
  rewrite sshiftL_Z_shiftr_equiv.
  rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  reflexivity.
Qed.

Theorem zipWith_ls_app : forall (A B C : Type)(f : A -> B -> C) lsa1 lsa2 lsb1 lsb2,
  length lsa1 = length lsb1 ->
  zipWith_ls f (lsa1 ++ lsa2) (lsb1 ++ lsb2) = (zipWith_ls f lsa1 lsb1) ++ (zipWith_ls f lsa2 lsb2).

  induction lsa1; destruct lsb1; intros; simpl in *; trivial; try discriminate.
  f_equal.
  eapply IHlsa1.
  lia.

Qed.

Theorem rev_zipWith_ls_eq : forall (A B C : Type)(f : A -> B -> C) ls1 ls2,
  (length ls1 = length ls2) ->
  rev (zipWith_ls f ls1 ls2) = zipWith_ls f (rev ls1) (rev ls2).

  induction ls1; destruct ls2; intros; simpl in *; trivial.
  discriminate.
  rewrite IHls1.
  rewrite zipWith_ls_app.
  reflexivity.
  repeat rewrite rev_length.
  lia.
  lia.

Qed.

Theorem bvOr_toPosZ_ls_equiv : forall ls1 ls2,
  length ls1 = length ls2 ->
  toPosZ_ls (zipWith_ls or ls1 ls2) = Z.lor (toPosZ_ls ls1) (toPosZ_ls ls2).

  induction ls1; destruct ls2; intros; simpl in *; trivial; try discriminate.
  rewrite IHls1; try lia.
  remember (toPosZ_ls ls1) as x.
  remember (toPosZ_ls ls2) as y.
  specialize (toPosZ_ls_nonneg ls1); intros.
  specialize (toPosZ_ls_nonneg ls2); intros.

  destruct a.
  rewrite Bool.orb_true_l.
  destruct b;
  destruct x; destruct y; simpl; trivial; try lia.

  rewrite Bool.orb_false_l.
  destruct b;
  destruct x; destruct y; simpl; trivial; try lia.

Qed.

Theorem bvOr_bvToInt_equiv : forall (n : Nat) (x y : bitvector n), bvToInt n (bvOr x y) = BinInt.Z.lor (bvToInt n x) (bvToInt n y).

  intros.
  repeat rewrite <- bvToInt_ls_equiv.
  unfold bvToInt_ls, bvToBITS_ls.
  
  unfold bvOr, bvZipWith.
  rewrite zipWith_ls_eq.
  rewrite rev_zipWith_ls_eq.
  rewrite bvOr_toPosZ_ls_equiv.
  reflexivity.
  repeat rewrite rev_length.
  repeat rewrite length_to_list.
  trivial.
  repeat rewrite length_to_list.
  trivial.

Qed.

Theorem bvEq_nth_order : forall (n : nat) (v1 v2 : bitvector n), bvEq n v1 v2 = 1%bool -> forall (n' : nat) (pf : (n' < n)%nat), nth_order v1 pf = nth_order v2 pf.

  induction v1; intros; simpl in *.
  lia.

  destruct (Vec_S_cons _ _ v2).
  destruct H0.
  subst.
  unfold bvEq, vecEq in *.
  simpl in *.
  apply and_bool_eq_true in H.
  intuition idtac.
  destruct n'.
  repeat rewrite (@sawAt_nth_order_equiv _ _  _ _ _ pf) in H0.
  repeat rewrite nth_order_0_cons in *.
  apply boolEq_eq; auto.

  assert (n' < n)%nat by lia.
  repeat rewrite (@nth_order_S_cons _ _ _ _ _ _ H).
  eapply IHv1.
  eapply H1.

Qed.

Theorem bvEq_false_ne : forall (n : nat) (v1 v2 : bitvector n), 
  bvEq n v1 v2 = 0%bool -> exists (n' : nat) (nlt : (n' < n)%nat), nth_order v1 nlt <> nth_order v2 nlt.

  induction v1; intros; simpl in *.
  unfold bvEq, vecEq in *; simpl in *.
  discriminate.

  destruct (Vec_S_cons _ _ v2).
  destruct H0.
  subst.
  unfold bvEq, vecEq in *.
  simpl in *.
  apply and_bool_eq_false in H.
  intuition idtac.
  assert (0< S n)%nat by lia.
  exists 0%nat.
  exists H.
  
  repeat rewrite (@sawAt_nth_order_equiv _ _  _ _ _ H) in H0.
  repeat rewrite nth_order_0_cons in *.
  intuition idtac.
  subst.
  rewrite boolEq_refl in *.
  discriminate.
  destruct (IHv1 x0).
  apply H0.
  destruct H.
  exists (S x1).
  
  assert (S x1 < S n)%nat by lia.
  exists H1.
  repeat rewrite (@nth_order_S_cons _ _ _ _ _ _ x2).
  trivial.
Qed.

Theorem sbvToInt_bvURem_equiv : forall n v1 v2,
  (n > 0)%nat ->
  (0 < bvToInt _ v2)%Z ->
  (bvToInt _ v2 <= Z.pow 2 (Z.of_nat (pred n)))%Z ->
  sbvToInt n (bvURem _ v1 v2) = Z.modulo (bvToInt _ v1) (bvToInt _ v2).

  intros.
  Local Transparent bvURem.
  unfold bvURem.
  destruct n. lia.
  rewrite bvToInt_sbvToInt_equiv.
  apply bvToInt_intToBv_id.
  intuition idtac.
  apply Z.mod_pos_bound.
  lia.
  eapply Z.lt_le_trans.
  apply Z.mod_pos_bound.
  lia.
  rewrite H1.
  eapply Z.pow_le_mono.
  lia.
  lia.
  lia.
  
  rewrite bvToInt_intToBv_id.
  eapply Z.lt_le_trans.
  eapply Z.mod_pos_bound.
  trivial.
  trivial.
  intuition idtac.
  apply Z.mod_pos_bound.
  lia.
  eapply Z.lt_le_trans.
  apply Z.mod_pos_bound.
  lia.
  rewrite H1.
  eapply Z.pow_le_mono.

  lia.
  lia.
Qed.

Fixpoint adcBmain_ls (carry : bool) ls1 ls2 := 
  match ls1 with
  | nil => carry::nil
  | b1 :: ls1' =>
    match ls2 with
    | nil => nil
    | b2 :: ls2' =>
      let (carry', b) := fullAdder carry b1 b2 in (b :: (adcBmain_ls carry' ls1'  ls2'))
    end
  end.

Definition adcB_ls (carry : bool) (p1 p2 : list bool) :=
   splitmsb_ls (adcBmain_ls carry p1 p2).

Theorem addcBmain_ls_eq : forall n c b1 b2,
  tuple.tval (@adcBmain n c b1 b2) = adcBmain_ls c (tuple.tval b1) (tuple.tval b2).

  induction n; intros; simpl in *.
  destruct b1. destruct b2.
  destruct tval.
  simpl.
  reflexivity.
  inversion i.
  
  destruct (tuple_S_ex b1). destruct H.
  subst.
  destruct (tuple_S_ex b2). destruct H.
  subst.

  repeat rewrite tuple_head_cons.
  repeat rewrite tuple_tval_cons. simpl.
  destruct (fullAdder c x x1).
  simpl.
  f_equal.
  repeat rewrite tuple_behead_cons.
  eauto.

Qed.

Theorem adcB_ls_eq : forall n c b1 b2,
  let (c', b') := (@adcB n c b1 b2)  in
  (c', tuple.tval b') = adcB_ls c (tuple.tval b1) (tuple.tval b2).

  intros.
  Local Transparent adcB.
  unfold adcB, adcB_ls.
  rewrite <- addcBmain_ls_eq.
  rewrite splitmsb_ls_eq.
  destruct (spec.splitmsb (adcBmain (n:=n) c b1 b2) ).
  simpl.
  reflexivity.

Qed.

Definition addB_ls b1 b2 := snd (adcB_ls false b1 b2).

Theorem addB_ls_eq : forall n (b1 b2 : spec.BITS n),
  tuple.tval (addB b1 b2) = addB_ls (tuple.tval b1) (tuple.tval b2).

  intros.
  unfold addB_ls.
  specialize (@adcB_ls_eq n false b1 b2); intros.
  remember (adcB 0 b1 b2) as z. destruct z.
  simpl.
  rewrite <- H.
  reflexivity.

Qed.

Theorem intToBv_1_to_list_eq_pred : forall n,
  (n > 0)%nat ->
  to_list (intToBv n 1) = repeat 0%bool (pred n) ++ [1%bool].

  intros.
  destruct n. lia.
  apply intToBv_1_to_list_eq.
Qed.

Theorem adcB_ls_carry_in_eq : forall ls1 ls2,
  adcB_ls true (false :: ls1) ls2 = adcB_ls false (true :: ls1) ls2.

  intros.
  reflexivity.
Qed.

Theorem map_xor_1_eq_negb : 
  forall ls n,
  (n = length ls) ->
  map (fun p : Bool * Bool => xor (fst p) (snd p)) (combine ls (@repeat bool true n)) = map negb ls.

  induction ls; intros; simpl in *; subst; trivial.
  simpl.
  f_equal.
  eapply IHls; trivial.

Qed.

Theorem splitmsb_ls_cons_eq : forall a ls,
  (length ls > 0)%nat ->
  splitmsb_ls (a :: ls) = (fst (splitmsb_ls ls), (a :: (snd (splitmsb_ls ls)))).

  intros.
  destruct ls using rev_ind.
  simpl in *. lia.
  rewrite app_comm_cons.
  repeat rewrite splitmsb_ls_app_eq.
  simpl.
  reflexivity.
  
Qed.

Theorem adcBmain_not_empty : forall lsa1 lsb1 c,
  (length lsa1  = length lsb1) ->
  adcBmain_ls c lsa1 lsb1 = [] ->
  False.

  destruct lsa1; intros; simpl in *.
  discriminate.
  destruct lsb1; simpl in *.
  lia.
  remember (fullAdder c b b0) as z.
  destruct z.
  discriminate.

Qed.

Theorem adcBmain_ls_app : forall lsa1 lsa2 lsb1 lsb2 c,
  length lsa1 = length lsb1 ->
  adcBmain_ls c (lsa1 ++ lsa2) (lsb1 ++ lsb2) = 
  let (c', ls') := splitmsb_ls (adcBmain_ls c lsa1 lsb1) in
  ls' ++ (adcBmain_ls c' lsa2 lsb2).

  induction lsa1; destruct lsb1; intros; simpl in *; trivial.
  discriminate.
  discriminate.

  remember (fullAdder c a b) as z.
  destruct z.
  rewrite IHlsa1; trivial.

  remember (adcBmain_ls b0 lsa1 lsb1) as z.
  destruct z using rev_ind.
  symmetry in Heqz0.
  apply adcBmain_not_empty in Heqz0.
  intuition idtac.
  lia.

  clear IHz.
  rewrite splitmsb_ls_cons_eq.
  rewrite splitmsb_ls_app_eq.
  simpl.
  reflexivity.
  rewrite app_length; simpl; lia.
  lia.
Qed.

Theorem toPosZ_ls_neg_eq_toNegZ_ls : forall ls,
  toPosZ_ls (map negb ls) = toNegZ_ls ls.

  induction ls; intros; simpl in *; trivial.
  destruct a; simpl in *.
  rewrite IHls.
  reflexivity.
  rewrite IHls.
  reflexivity.

Qed.


Theorem toNegZ_ls_neg_eq_toPosZ_ls : forall ls,
  toNegZ_ls (map negb ls) = toPosZ_ls ls.

  induction ls; intros; simpl in *; trivial.
  destruct a; simpl in *.
  rewrite IHls.
  reflexivity.
  rewrite IHls.
  reflexivity.

Qed.


Theorem adcBmain_ls_zero_eq : forall ls,
  (adcBmain_ls 0 (repeat 0%bool (Datatypes.length ls)) ls) = (ls ++ [false]).

  induction ls; intros; simpl in *; trivial.
  destruct a.
  f_equal.
  eauto.
  f_equal.
  eauto.
Qed.

Theorem adcBmain_ls_zero_eq_gen : forall ls n,
  n = (Datatypes.length ls) ->
  (adcBmain_ls 0 (repeat 0%bool n) ls) = (ls ++ [false]).

  intros. subst.
  apply adcBmain_ls_zero_eq.
Qed.

Theorem adcBmain_length_nz : forall c a b,
  length a = length b ->
  (0 < List.length (adcBmain_ls c a b))%nat.

  intros.
  remember (adcBmain_ls c a b) as z.
  destruct z.
  symmetry in Heqz.
  apply adcBmain_not_empty in Heqz.
  intuition idtac.
  trivial.
  simpl.
  lia.
Qed.

Theorem snd_splitmsb_ls_length : forall ls,
  (length ls > 0)%nat ->
  length (snd (splitmsb_ls ls)) = pred (length ls).

  intros.
  destruct ls using rev_ind.
  simpl in *. lia.
  rewrite splitmsb_ls_app_eq.
  simpl.  
  rewrite app_length.
  rewrite plus_comm.
  simpl.
  reflexivity.
Qed.

Theorem adcBmain_ls_length : forall ls1 ls2 a,
  length ls1 = length ls2 ->
  length (adcBmain_ls a ls1 ls2) = (S (length ls1)).

  induction ls1; destruct ls2; intros; simpl in *; trivial.
  discriminate.
  destruct (fullAdder a0 a b).
  simpl.
  f_equal.
  apply IHls1.
  lia.

Qed.


Theorem toNegZ_ls_toPosZ_ls_twos_complement_equiv : forall ls l,
  length ls = length l ->
  (0%bool, l) = splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls)) ->
  Z.succ (toNegZ_ls l) = toPosZ_ls ls.

  induction ls; intros; simpl in *.
  unfold splitmsb_ls in *. simpl in *.
  inversion H0.

  destruct l; simpl in *.
  discriminate.
  destruct a; simpl in *.
  rewrite splitmsb_ls_cons_eq in *.
  inversion H0; clear H0; subst.
  f_equal.
  f_equal.
  rewrite adcBmain_ls_zero_eq_gen.
  rewrite splitmsb_ls_app_eq.
  simpl.
  apply toNegZ_ls_neg_eq_toPosZ_ls.
  rewrite map_length.
  reflexivity.
  remember ((adcBmain_ls 0 (repeat 0%bool (Datatypes.length ls)) (map negb ls))) as z.
  destruct z.
  symmetry in Heqz.
  apply adcBmain_not_empty in Heqz.
  intuition idtac.  
  rewrite map_length.
  rewrite repeat_length.
  reflexivity.
  simpl.
  lia.

  destruct b.
  rewrite splitmsb_ls_cons_eq in H0.
  inversion H0.
  apply adcBmain_length_nz.
  rewrite repeat_length.
  rewrite map_length.
  reflexivity.

  rewrite splitmsb_ls_cons_eq in *.
  inversion H0; clear H0; subst.
  rewrite <- (IHls (snd (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls))))).
  lia.

  rewrite snd_splitmsb_ls_length.
  rewrite adcBmain_ls_length.
  simpl.
  rewrite repeat_length.
  reflexivity.
  rewrite repeat_length.
  rewrite map_length.
  reflexivity.
  apply adcBmain_length_nz.
  rewrite repeat_length.
  rewrite map_length.
  reflexivity.
  remember ((splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls))))  as z.
  destruct z; simpl in *; subst.
  reflexivity.
  apply adcBmain_length_nz.
  rewrite repeat_length.
  rewrite map_length.
  reflexivity.

Qed.

Theorem toPosZ_ls_toNegZ_ls_twos_complement_equiv : forall ls l,
  length ls = length l ->
  (0%bool, l) = splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls)) ->
  toPosZ_ls l = Z.succ (toNegZ_ls ls).

  induction ls; intros; simpl in *.
  unfold splitmsb_ls in *. simpl in *.
  inversion H0.

  destruct l; simpl in *.
  discriminate.
  destruct a; simpl in *.
  rewrite splitmsb_ls_cons_eq in *.
  inversion H0; clear H0; subst.
  f_equal.
  f_equal.
  rewrite adcBmain_ls_zero_eq_gen.
  rewrite splitmsb_ls_app_eq.
  simpl.
  apply toPosZ_ls_neg_eq_toNegZ_ls.
  rewrite map_length.
  reflexivity.
  remember ((adcBmain_ls 0 (repeat 0%bool (Datatypes.length ls)) (map negb ls))) as z.
  destruct z.
  symmetry in Heqz.
  apply adcBmain_not_empty in Heqz.
  intuition idtac.  
  rewrite map_length.
  rewrite repeat_length.
  reflexivity.
  simpl.
  lia.

  destruct b.
  rewrite splitmsb_ls_cons_eq in H0.
  inversion H0.
  apply adcBmain_length_nz.
  rewrite repeat_length.
  rewrite map_length.
  reflexivity.

  rewrite splitmsb_ls_cons_eq in *.
  inversion H0; clear H0; subst.
  rewrite IHls.
  lia.

  rewrite snd_splitmsb_ls_length.
  rewrite adcBmain_ls_length.
  simpl.
  rewrite repeat_length.
  reflexivity.
  rewrite repeat_length.
  rewrite map_length.
  reflexivity.
  apply adcBmain_length_nz.
  rewrite repeat_length.
  rewrite map_length.
  reflexivity.
  remember ((splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls))))  as z.
  destruct z; simpl in *; subst.
  reflexivity.
  apply adcBmain_length_nz.
  rewrite repeat_length.
  rewrite map_length.
  reflexivity.

Qed.

Theorem twos_complement_carry_out_0 : forall ls l,
  (1%bool, l) = splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls)) ->
  toPosZ_ls ls = 0%Z /\ toPosZ_ls l = 0%Z.

  induction ls; intros; simpl in *; trivial.
  split.
  trivial.
  unfold splitmsb_ls in *. simpl in *.
  inversion H; clear H; subst.
  reflexivity.
  destruct a.
  simpl in *.
  rewrite splitmsb_ls_cons_eq in *.
  inversion H; clear H; subst.
  rewrite adcBmain_ls_zero_eq_gen in H1.
  rewrite splitmsb_ls_app_eq in *.
  simpl in *.
  discriminate.
  rewrite map_length.
  reflexivity.
  apply adcBmain_length_nz.
  rewrite map_length.
  apply repeat_length.
  
  simpl in *.
  rewrite splitmsb_ls_cons_eq in *.
  inversion H; clear H; subst.
  simpl.
  assert (toPosZ_ls ls = 0 /\ toPosZ_ls (snd (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls)))) = 0).
  apply IHls.

  destruct (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls))).
  simpl in *. subst.
  reflexivity.
  intuition idtac.
  rewrite H0.
  lia.
  rewrite H2.
  lia.
  apply adcBmain_length_nz.
  rewrite map_length.
  apply repeat_length.

Qed.

Theorem twos_complement_carry_out_0_neg: forall ls l,
  (1%bool, l) = splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls)) ->
  Z.succ (toNegZ_ls ls) = 2^(Z.of_nat (length ls)).

  induction ls; intros; simpl in *; trivial.
  destruct a; simpl in *.
  inversion H; clear H; subst.
  rewrite splitmsb_ls_cons_eq in *.
  inversion H1; clear H1; subst.
  rewrite adcBmain_ls_zero_eq_gen in H0.
  rewrite splitmsb_ls_app_eq in *.
  simpl in *.
  discriminate.
  rewrite map_length.
  reflexivity.  
  apply adcBmain_length_nz.
  rewrite map_length.
  apply repeat_length.
  replace (Z.succ (Z.succ (Z.double (toNegZ_ls ls)))) with (Z.double (Z.succ (toNegZ_ls ls))).
  rewrite splitmsb_ls_cons_eq in H.
  inversion H; clear H; subst.
  rewrite (IHls (snd (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls))))).
  replace (Z.pow_pos 2 (Pos.of_succ_nat (Datatypes.length ls))) with (2^ (1 + (Z.of_nat (length ls)))).
  rewrite Z.pow_add_r; try lia.
 
  rewrite Z.add_1_l.
  rewrite <- Znat.Nat2Z.inj_succ.
  simpl.
  reflexivity.
  destruct (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls))); simpl in *; subst.
  reflexivity.
  apply adcBmain_length_nz.
  rewrite map_length.
  apply repeat_length.
  lia.
Qed.


Theorem toZ_ls_twos_complement_equiv : forall ls n,
  (0 < n)%nat ->
  n = length ls ->
  - (2 ^ (Z.of_nat (pred n))) < toZ_ls ls ->
  toZ_ls (snd (adcB_ls 1 (repeat 0%bool n) (map negb ls))) = - toZ_ls ls.

  intros.
  unfold toZ_ls in *.
  remember (snd (adcB_ls 1 (repeat 0%bool n) (map negb ls))) as z.
  destruct z using rev_ind; simpl in *; try lia;
  destruct ls using rev_ind; simpl in *; trivial; try lia.
  unfold adcB_ls in *.
  assert (length (snd (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool n) (map negb (ls ++ [x]))))) > 0)%nat.
  rewrite snd_splitmsb_ls_length.
  rewrite adcBmain_ls_length.
  simpl.
  rewrite repeat_length.
  lia.  
  rewrite map_length.
  rewrite repeat_length.
  trivial.
  rewrite adcBmain_ls_length.
  lia.
  rewrite map_length.
  rewrite repeat_length.
  trivial.
  rewrite <- Heqz in H2.
  simpl in *.
  lia.
  
  clear IHz.
  clear IHls.
  repeat rewrite splitmsb_ls_app_eq in *.
  rewrite map_app in *.
  simpl in *.
  
  unfold adcB_ls in *.
  rewrite app_length in *.
  rewrite plus_comm in H0.
  simpl in *.
  subst.
  rewrite repeat_S_rev in Heqz.
  rewrite adcBmain_ls_app in Heqz.
  remember (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls))) as z'.
  destruct z'.
  simpl in *.
  remember ( fullAdder b 0 (negb x0) ) as z'.
  destruct z'.
  replace (l ++ [b1; b0]) with ((l ++ [b1]) ++ [b0]) in *.
  rewrite splitmsb_ls_app_eq in *.
  simpl in *.
  apply app_inj_tail in Heqz.
  intuition idtac.
  subst.
  
  destruct x0.
  simpl in *.
  (* ls represents a negative number *)
  destruct b1.
  (* two's complement is also negative. This only happens when the value is `2^n, so this is a contradiction *)
  destruct b; simpl in *.
  exfalso.
  apply twos_complement_carry_out_0_neg in Heqz'.
  rewrite Heqz' in H1.
  lia.

  inversion Heqz'0.
  
  (* twos complement is non-negative *)
  rewrite Z.opp_involutive.
  destruct b; simpl in *;
  inversion Heqz'0; subst.
  simpl in *.
  unfold adcB_ls in *.
  apply toPosZ_ls_toNegZ_ls_twos_complement_equiv; eauto.
  replace l with (snd (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls)))).
  rewrite snd_splitmsb_ls_length.
  rewrite adcBmain_ls_length.
  simpl.
  rewrite repeat_length.
  reflexivity.
  rewrite map_length.
  apply repeat_length.
  apply adcBmain_length_nz.
  rewrite map_length.
  apply repeat_length.
  destruct (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls))).
  inversion Heqz'; subst.
  reflexivity.
  
  (* ls represents a non-negative number *)
  destruct b1.
  assert (Z.succ (toNegZ_ls l) = toPosZ_ls ls).
  destruct b; simpl in *;
  inversion Heqz'0.
  subst.
  apply toNegZ_ls_toPosZ_ls_twos_complement_equiv; eauto.
  replace l with (snd (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls)))).
  rewrite snd_splitmsb_ls_length.
  rewrite adcBmain_ls_length.
  simpl.
  rewrite repeat_length.
  reflexivity.
  rewrite map_length.
  apply repeat_length.
  apply adcBmain_length_nz.
  rewrite map_length.
  apply repeat_length.
  destruct (splitmsb_ls (adcBmain_ls 1 (repeat 0%bool (Datatypes.length ls)) (map negb ls))).
  inversion Heqz'; subst.
  reflexivity.
  lia.

  (* ls is representation of 0 *)
  destruct b; simpl in *.
  inversion Heqz'0; subst.
  apply twos_complement_carry_out_0 in Heqz'.
  intuition idtac.
  rewrite H0.
  rewrite H2.
  reflexivity.

  inversion Heqz'0.
  
  rewrite <- app_assoc.
  simpl.
  reflexivity.

  rewrite map_length.
  apply repeat_length.

Qed.


Theorem sbvToInt_bvNeg_equiv : forall n v,
  - (2 ^ (Z.of_nat (pred n))) < (sbvToInt _ v) ->
  sbvToInt n (bvNeg _ v) = Z.opp (sbvToInt _ v).

  intros.
  unfold bvNeg.
  Local Transparent bvSub  sbbB.
  unfold bvSub, sbbB.
  simpl.
  repeat rewrite <- sbvToInt_ls_equiv.
  unfold sbvToInt_ls.
  destruct n; trivial.
  unfold bvToBITS_ls.
  rewrite <- bitsToBv_ls_eq.
  unfold bitsToBv_ls.
  rewrite rev_involutive.
  rewrite intToBv_0_eq_replicate.
  specialize (@adcB_ls_eq _ true (bvToBITS (replicate (S n) bool 0%bool)) (invB (bvToBITS v))); intros.
  remember (adcB 1 (bvToBITS (replicate (S n) bool 0%bool)) (invB (bvToBITS v))) as z.
  destruct z.
  simpl.
  assert (tuple.tval b0 = snd (adcB_ls 1 (tuple.tval (bvToBITS (replicate (S n) bool 0%bool))) (tuple.tval (invB (bvToBITS v))))).
  destruct (adcB_ls 1 (tuple.tval (bvToBITS (replicate (S n) bool 0%bool))) (tuple.tval (invB (bvToBITS v)))); simpl; congruence.
  rewrite H1.
  rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  rewrite <- replicate_repeat_eq.
  rewrite rev_repeat_id.
  simpl.
  rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  rewrite <-  (@toZ_ls_twos_complement_equiv _ (S n)).
  simpl.
  reflexivity.
  lia.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.  
  rewrite <-sbvToInt_ls_equiv in *.
  eauto.

Qed.

Local Transparent bvAdd.

Ltac listify_1 :=
  try match goal with
  | [|- _ = _ ] => apply eq_if_to_list_eq
  end; 
  try rewrite rev_involutive;
  try rewrite <- intToBv_ls_eq in *;
  try rewrite <- bitsToBv_ls_eq in *;
  try rewrite addB_ls_eq in *;
  try rewrite bvToBITS_ls_equiv in *;
  unfold bvToBITS_ls, intToBv_ls, bitsToBv_ls in *.

Ltac listify := repeat listify_1.

Theorem fullAdder_comm : forall c a b,
  fullAdder c a b = fullAdder c b a.

  intros.
  destruct c; destruct b; destruct a; simpl in *; reflexivity.

Qed.

Theorem adcBmain_ls_comm: forall b1 b2 c, 
  length b1 = length b2 ->
  (adcBmain_ls c b1 b2) = (adcBmain_ls c b2 b1).

  induction b1; destruct b2; intros; simpl in *; try lia.
  reflexivity.
  rewrite fullAdder_comm.
  destruct (fullAdder c b a).
  f_equal.
  apply IHb1.
  lia.

Qed.

Theorem addB_ls_comm : forall b1 b2,
  length b1 = length b2 ->
  addB_ls b1 b2 = addB_ls b2 b1.

  intros.
  unfold addB_ls, adcB_ls.
  rewrite adcBmain_ls_comm.
  reflexivity.
  trivial.
Qed.

Theorem fromPosZ_mod_eq : forall n z,
  fromPosZ_ls n z = fromPosZ_ls n (Z.modulo z (2^Z.of_nat n)).

  induction n; intros.
  simpl in *. trivial.
  replace (S n ) with (n + 1)%nat.
  rewrite fromPosZ_ls_app.
  rewrite IHn.
  rewrite Zdiv.Zmod_mod.
  rewrite fromPosZ_ls_app.
  f_equal.
  f_equal.
  rewrite <- Znumtheory.Zmod_div_mod.
  reflexivity.
  apply Z.pow_pos_nonneg; lia.
  apply Z.pow_pos_nonneg; lia.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.pow_add_r.
  apply Z.divide_factor_l.
  lia.
  lia.

  simpl.
  f_equal.
  f_equal.
  f_equal.
  repeat rewrite Zdiv.Zeven_mod.
  f_equal.
  rewrite Z_mod_div_eq.
  replace ((2 ^ Z.of_nat (n + 1) / 2 ^ Z.of_nat n)) with 2.
  rewrite Zdiv.Zmod_mod.
  reflexivity.
  rewrite <- Z.pow_sub_r.
  replace (Z.of_nat (n + 1) - Z.of_nat n) with 1.
  lia.
  lia.
  lia.
  lia.
  apply Z.lt_gt.
  apply Z.pow_pos_nonneg; lia.
  apply Z.lt_gt.
  apply Z.pow_pos_nonneg; lia.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  rewrite Z.mod_mul.
  trivial.
  assert (0 < 2^ (Z.of_nat n)).
  apply Z.pow_pos_nonneg; lia.
  lia.
  lia.
  lia.
  lia.
Qed.

Theorem fromPosZ_ls_app' : forall n1 n2 z, 
 
  fromPosZ_ls (n1 + n2) z = (fromPosZ_ls n1 z) ++ (fromPosZ_ls n2 (Z.div z (Z.pow 2 (Z.of_nat n1)))). 

  intros.
  rewrite fromPosZ_ls_app.
  rewrite <- fromPosZ_mod_eq.
  reflexivity.

Qed.

Theorem fromNegZ_mod_eq : forall n z,
  fromNegZ_ls n z = fromNegZ_ls n (Z.modulo z (2^Z.of_nat n)).

  induction n; intros.
  simpl in *. trivial.
  replace (S n ) with (n + 1)%nat.
  rewrite fromNegZ_ls_app.
  rewrite IHn.
  rewrite Zdiv.Zmod_mod.
  rewrite fromNegZ_ls_app.
  f_equal.
  f_equal.
  rewrite <- Znumtheory.Zmod_div_mod.
  reflexivity.
  apply Z.pow_pos_nonneg; lia.
  apply Z.pow_pos_nonneg; lia.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.pow_add_r.
  apply Z.divide_factor_l.
  lia.
  lia.

  simpl.
  f_equal.
  f_equal.
  repeat rewrite Zdiv.Zeven_mod.
  f_equal.
  rewrite Z_mod_div_eq.
  replace ((2 ^ Z.of_nat (n + 1) / 2 ^ Z.of_nat n)) with 2.
  rewrite Zdiv.Zmod_mod.
  reflexivity.
  rewrite <- Z.pow_sub_r.
  replace (Z.of_nat (n + 1) - Z.of_nat n) with 1.
  lia.
  lia.
  lia.
  lia.
  apply Z.lt_gt.
  apply Z.pow_pos_nonneg; lia.
  apply Z.lt_gt.
  apply Z.pow_pos_nonneg; lia.
  rewrite Znat.Nat2Z.inj_add.
  rewrite Z.pow_add_r.
  rewrite Z.mul_comm.
  rewrite Z.mod_mul.
  trivial.
  assert (0 < 2^ (Z.of_nat n)).
  apply Z.pow_pos_nonneg; lia.
  lia.
  lia.
  lia.
  lia.
Qed.

Theorem fromNegZ_ls_app' : forall n1 n2 z, 
 
  fromNegZ_ls (n1 + n2) z = (fromNegZ_ls n1 z) ++ (fromNegZ_ls n2 (Z.div z (Z.pow 2 (Z.of_nat n1)))). 

  intros.
  rewrite fromNegZ_ls_app.
  rewrite <- fromNegZ_mod_eq.
  reflexivity.

Qed.

Ltac pairInv :=
  match goal with
  | [H: (_, _) = (_, _) |- _] => inversion H; clear H; subst
  end.

Theorem not_even_impl_odd : forall z,
  Z.even z = 0%bool ->
  Z.odd z = 1%bool.

  intros.
  rewrite Zeven.Zeven_odd_bool in H.
  destruct (Z.odd z); simpl in *; trivial; discriminate.

Qed.

Ltac evenOddCases_1 :=
  try match goal with
  | [H: Z.even _ = true |- _ ]=>
    apply even_exists_factor in H; destruct H; subst
  | [H: Z.even _ = false |- _ ]=>
    apply not_even_impl_odd in H; apply odd_exists_factor in H; destruct H; subst
  end;
  try rewrite Zdiv.Z_div_plus; try lia;
  try rewrite splitmsb_ls_cons_eq.

Ltac evenOddCases := repeat evenOddCases.

Theorem fromPosZ_add_eq : forall n a b (c : bool),
  0 <= a ->
  0 <= b ->
   fromPosZ_ls n ((if c then 1 else 0) + a + b) = snd (splitmsb_ls (adcBmain_ls c (fromPosZ_ls n a) (fromPosZ_ls n b))).

  induction n; intros.
  simpl in *.
  reflexivity.

  repeat rewrite (fromPosZ_ls_app' 1%nat n).
  rewrite Z.pow_1_r.
  simpl.

  rewrite Z.even_add.
  rewrite Z.even_add.
  destruct c;
  case_eq (Z.even a);
  case_eq (Z.even b); intros;
  
   try evenOddCases_1;
  try evenOddCases_1;
  try evenOddCases_1;
  try evenOddCases_1;
  try evenOddCases_1.
  simpl.
   try evenOddCases_1; simpl.
  f_equal.
  rewrite <- IHn.
  f_equal.
  repeat rewrite Zdiv.Z_div_mult; lia.
  apply Zdiv.Z_div_pos; try lia.
  apply Zdiv.Z_div_pos; try lia.
  apply adcBmain_length_nz. 
  repeat rewrite fromPosZ_ls_length.
  trivial.

  rewrite Z.add_assoc.
  replace (1 + x * 2 + 1 + x0 * 2) with (2 + x * 2 + x0 * 2) .
  try evenOddCases_1.
  try evenOddCases_1.
  rewrite (IHn _ _ true).
  simpl.
  evenOddCases_1.
  simpl.
  f_equal.
  rewrite Zdiv.Z_div_mult; try  lia.
  reflexivity.
  apply adcBmain_length_nz. 
  repeat rewrite fromPosZ_ls_length.
  trivial.
  lia.
  lia.
  lia.
  
  remember (((1 + (1 + x0 * 2)) / 2 + x)) as z.
  simpl.
  rewrite splitmsb_ls_cons_eq.
  simpl.
  f_equal.
  rewrite <- IHn.
  f_equal.
  subst.
  rewrite Z.add_assoc.
  rewrite Zdiv.Z_div_plus.
  rewrite Zdiv.Z_div_mult.
  rewrite Z.div_same.
  lia.
  lia.
  lia.
  lia.
  lia.
  rewrite Zdiv.Z_div_mult.
  lia.
  lia.
  apply adcBmain_length_nz.
  repeat rewrite fromPosZ_ls_length.
  reflexivity.

  remember ((1 + (1 + x * 2) + (1 + x0 * 2)) / 2)  as z.
  simpl.
  rewrite splitmsb_ls_cons_eq.
  simpl.
  f_equal.
  rewrite <- IHn.
  f_equal.
  subst.
  replace (1 + (1 + x * 2) + (1 + x0 * 2)) with (1 +  ( 1 + x + x0) * 2).
  rewrite Zdiv.Z_div_plus.
  rewrite Z.div_small.
  lia.
  lia.
  lia.
  lia.
  lia.
  lia.
  apply adcBmain_length_nz.
  repeat rewrite fromPosZ_ls_length.
  reflexivity.

  remember (0 / 2 + x + x0)  as z.
  simpl.
  rewrite splitmsb_ls_cons_eq.
  simpl.
  f_equal.
  rewrite <- IHn.
  f_equal.
  subst.
  repeat rewrite Z.div_mul; try lia.
  rewrite Z.div_small; try lia.
  rewrite Z.div_mul; lia.
  rewrite Z.div_mul; lia.
  apply adcBmain_length_nz.
  repeat rewrite fromPosZ_ls_length.
  reflexivity.

  remember ((0 + x * 2 + (1 + x0 * 2)) / 2) as z.
  simpl.
  rewrite splitmsb_ls_cons_eq.
  simpl.
  f_equal.
  rewrite <- IHn.
  f_equal.
  subst.
  repeat rewrite Z.div_mul; try lia.
  rewrite Z.add_0_l.
  replace (x * 2 + (1 + x0 * 2)) with (1 + (x + x0)*2).
  rewrite Zdiv.Z_div_plus; try lia.
  rewrite Z.div_small; try lia.
  lia.
  rewrite Z.div_mul; lia.
  lia.
  apply adcBmain_length_nz.
  repeat rewrite fromPosZ_ls_length.
  reflexivity.

  remember ((0 + (1 + x0 * 2)) / 2 + x)  as z.
  simpl.
  rewrite splitmsb_ls_cons_eq.
  simpl.
  f_equal.
  rewrite <- IHn.
  f_equal.
  subst.
  repeat rewrite Z.div_mul; try lia.
  rewrite Z.add_0_l.
  rewrite Zdiv.Z_div_plus; try lia.
  rewrite Z.div_small; try lia.
  lia.
  rewrite Z.div_mul; lia.
  apply adcBmain_length_nz.
  repeat rewrite fromPosZ_ls_length.
  reflexivity.

  remember  ((0 + (1 + x * 2) + (1 + x0 * 2)) / 2)  as z.
  simpl.
  rewrite splitmsb_ls_cons_eq.
  simpl.
  f_equal.
  rewrite <- IHn.
  f_equal.
  subst.
  rewrite Z.add_0_l.
  replace (1 + x * 2 + (1 + x0 * 2))  with ((1 + x + x0)*2) .
  rewrite Z.div_mul; lia.
  lia.
  lia.
  lia.
  apply adcBmain_length_nz.
  repeat rewrite fromPosZ_ls_length.
  reflexivity.
Qed.


Theorem fromNegZ_ls_pos_opp: forall n z,
  fromNegZ_ls n z = fromPosZ_ls n (Z.pred (Z.opp z)).

  induction n; intros.
  reflexivity.
  
  simpl.
  f_equal.
  f_equal.
  rewrite IHn.
  f_equal.

  repeat rewrite Z.div2_div.
  case_eq (Z.even z); intros.
  apply even_exists_factor in H.
  destruct H.
  subst.
  rewrite Zdiv.Z_div_mult; try lia.
  repeat rewrite <- Z.sub_1_r.
  symmetry.
  rewrite <- Z.add_opp_l.
  rewrite Zopp_mult_distr_l.
  rewrite Zdiv.Z_div_plus; try lia.
  rewrite <- Z.add_opp_l.
  reflexivity.

  apply not_even_impl_odd in H.
  apply odd_exists_factor in H.
  destruct H.
  subst.
  repeat rewrite <- Z.sub_1_r.
  rewrite <- Zdiv.Z_div_nz_opp_full; try lia.
  rewrite Z.opp_add_distr.
  rewrite Zopp_mult_distr_l.
  rewrite Zdiv.Z_div_plus; try lia.
  rewrite <- Z.add_opp_l.
  rewrite Z.add_assoc.
  replace (- (1) + - (1)) with (-1 * 2); try lia.
  rewrite Zdiv.Z_div_plus; try lia.
  reflexivity.
  rewrite <- Zdiv.Zplus_mod_idemp_r.
  rewrite Zdiv.Z_mod_mult.
  simpl.
  rewrite Z.mod_1_l; try lia.

  rewrite <- Z.opp_succ.
  rewrite Z.even_opp.
  rewrite Z.even_succ.
  rewrite Z.negb_odd.
  trivial.

Qed.


Theorem fromZ_ls_mod_eq : forall n x,
  fromZ_ls n x = fromZ_ls n (Z.modulo x (Z.pow 2 (Z.of_nat n))).

  intros.
  unfold fromZ_ls.
  remember (x mod 2 ^ Z.of_nat n) as z.
  destruct x.
  subst.
  simpl.
  reflexivity.
  destruct z. 
  rewrite fromPosZ_mod_eq.
  rewrite <- Heqz.
  apply fromPosZ_ls_0_eq.

  rewrite Heqz.
  apply fromPosZ_mod_eq.
  (* contradiction *)
  assert (0 <= Z.neg p0).
  rewrite Heqz.
  apply Zdiv.Z_mod_nonneg_nonneg; lia.
  lia.

  rewrite fromNegZ_ls_pos_opp.
  rewrite Pos2Z.opp_neg.
  rewrite <- Z.opp_succ.
  rewrite Z.succ_pred.
  rewrite Pos2Z.opp_pos.
  rewrite fromPosZ_mod_eq.
  rewrite <- Heqz.
  destruct z.
  apply fromPosZ_ls_0_eq.
  reflexivity.
  
 (* contradiction *)
  assert (0 <= Z.neg p0).
  rewrite Heqz.
  apply Z.mod_pos_bound.
  lia.
  lia.

Qed.

Theorem addB_ls_0_l : forall n z,
  addB_ls (repeat false n) (fromZ_ls n z) = (fromZ_ls n z).

  intros.
  unfold addB_ls, adcB_ls.
  rewrite adcBmain_ls_zero_eq_gen.
  unfold splitmsb_ls.
  rewrite seq_rev_eq.
  rewrite rev_app_distr.
  simpl.
  rewrite seq_rev_eq.
  apply rev_involutive.
  symmetry.
  apply fromZ_ls_length.

Qed.

Theorem addB_ls_0_r : forall n z,
  addB_ls (fromZ_ls n z) (repeat false n) = (fromZ_ls n z).

  intros.
  rewrite addB_ls_comm.
  apply addB_ls_0_l.
  rewrite fromZ_ls_length.
  rewrite repeat_length.
  reflexivity.
Qed.

Theorem intToBv_add_equiv : forall (n : Nat) (x y : Z), 
  intToBv n (x + y) = bvAdd n (intToBv n x) (intToBv n y).

  intros.
  unfold bvAdd.
  listify.
  f_equal.

  rewrite (fromZ_ls_mod_eq _ x).
  rewrite (fromZ_ls_mod_eq _ y).
  rewrite (fromZ_ls_mod_eq _ (x + y)).
  rewrite <- Zdiv.Zplus_mod_idemp_r.
  rewrite <- Zdiv.Zplus_mod_idemp_l.
  remember (x mod 2 ^ Z.of_nat n) as z1.
  remember ((y mod 2 ^ Z.of_nat n)) as z2.

  destruct z1.
  rewrite fromZ_ls_0_eq.
  rewrite addB_ls_0_l.
  rewrite Z.add_0_l.
  rewrite <- fromZ_ls_mod_eq.
  reflexivity.

  destruct z2.
  rewrite fromZ_ls_0_eq.
  rewrite addB_ls_0_r.
  rewrite Z.add_0_r.
  rewrite <- fromZ_ls_mod_eq.
  reflexivity.

  unfold addB_ls, adcB_ls.
  simpl.
  rewrite <- fromPosZ_add_eq; try lia.
  rewrite <- fromZ_ls_mod_eq.
  simpl.
  reflexivity.
  assert (0 <= Z.neg p0).
  rewrite Heqz2.
  apply Z.mod_pos_bound; lia.
  lia.
  assert (0 <= Z.neg p).
  rewrite Heqz1.
  apply Z.mod_pos_bound; lia.
  lia.
Qed.

Theorem twos_complement_equiv : forall n v,
    (n > 0)%nat ->
    -Z.pow 2 (Z.of_nat (pred n)) < sbvToInt _ v ->
    sbvToInt n (bvAdd n (bvXor n v (replicate n bool true)) (intToBv n 1)) = Z.opp (sbvToInt _ v).

  intros.

  rewrite <- sbvToInt_bvNeg_equiv.
  unfold bvNeg.
  f_equal.
  eapply eq_if_to_list_eq.
  
  rewrite bvAdd_comm.
  Local Transparent bvAdd.
  unfold bvAdd.
  repeat rewrite <- bitsToBv_ls_eq.
  f_equal.
  repeat rewrite addB_ls_eq.
  unfold addB_ls.
  repeat rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  Local Transparent bvSub  sbbB.
  unfold bvSub.
  unfold sbbB.
  simpl.
  rewrite <- bitsToBv_ls_eq.
  f_equal.
  specialize (@adcB_ls_eq _ true (bvToBITS (intToBv n 0)) (invB (bvToBITS v))); intros.
  remember (adcB 1 (bvToBITS (intToBv n 0)) (invB (bvToBITS v))) as z.
  destruct z.
  simpl.
  assert (tuple.tval b0 = snd (adcB_ls 1 (tuple.tval (bvToBITS (intToBv n 0))) (tuple.tval (invB (bvToBITS v))))).
  destruct (adcB_ls 1 (tuple.tval (bvToBITS (intToBv n 0))) (tuple.tval (invB (bvToBITS v)))).
  simpl in *.
  congruence.
  rewrite H2.
  rewrite intToBv_0_eq_replicate.
  rewrite intToBv_1_to_list_eq_pred; try lia.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_repeat_id.
  rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  rewrite <- replicate_repeat_eq.
  rewrite rev_repeat_id.
  replace (repeat false n) with (false :: repeat false (pred n)).
  rewrite adcB_ls_carry_in_eq.
  f_equal.
  f_equal.
  rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  repeat rewrite <- seq_rev_eq.
  rewrite seq.map_rev.
  repeat rewrite seq_rev_eq.
  f_equal.
  unfold bvXor, bvZipWith.
  rewrite zipWith_ls_eq.
  rewrite <- replicate_repeat_eq.
  rewrite zipWith_ls_eq_map.
  apply map_xor_1_eq_negb.
  rewrite length_to_list.
  reflexivity.
  rewrite length_to_list.
  rewrite repeat_length.
  reflexivity.
  destruct n; trivial; lia.
  lia.
Qed.


Theorem bvAdd_replicate_0 : forall n v,
  bvAdd _ (replicate n bool false) v = v.

  intros.
  apply eq_if_to_list_eq.
  unfold bvAdd.
  rewrite <- bitsToBv_ls_eq.
  rewrite addB_ls_eq.
  rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  rewrite <- replicate_repeat_eq.
  rewrite rev_repeat_id.
  unfold addB_ls, adcB_ls.
  rewrite adcBmain_ls_zero_eq_gen.
  rewrite splitmsb_ls_app_eq.
  simpl.
  unfold bitsToBv_ls.
  rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  apply rev_involutive.

  symmetry.
  apply tuple_tval_length.
Qed.

Theorem adcB_ls_same_l_if : forall x y1 y2 c,
  length x = length y1 ->
  length x = length y2 ->
  snd (adcB_ls c x y1) = snd (adcB_ls c x y2) ->
  y1 = y2.

  induction x; intros; destruct y1; destruct y2; simpl in *; try lia; trivial.
  
  unfold adcB_ls in *.
  simpl in *.
  remember (fullAdder c a b) as z.
  destruct z.
  remember (fullAdder c a b0) as z.
  destruct z.
  rewrite splitmsb_ls_cons_eq in H1.
  rewrite splitmsb_ls_cons_eq in H1.
  simpl in *.
  inversion H1; clear H1; subst.
  destruct c; destruct a; destruct b; destruct b0; simpl in *; repeat pairInv; f_equal; eapply IHx; try lia; eauto.
  apply adcBmain_length_nz; lia.
  apply adcBmain_length_nz; lia.

Qed.

Theorem bvAdd_same_l_if : forall n x y1 y2,
  (bvAdd n x y1) = (bvAdd n x y2) ->
  y1 = y2.

  intros.
  apply eq_impl_to_list_eq in H.
  apply eq_if_to_list_eq.
  unfold bvAdd in *.
  repeat rewrite <- bitsToBv_ls_eq in *.
  repeat rewrite addB_ls_eq in *.
  repeat rewrite bvToBITS_ls_equiv in *.
  unfold bvToBITS_ls, bitsToBv_ls in *.
  unfold addB_ls in *.
  apply eq_if_rev_eq.
  eapply adcB_ls_same_l_if; [idtac | idtac | apply eq_if_rev_eq; eauto].
  repeat rewrite rev_length.
  repeat rewrite length_to_list.
  reflexivity.
  repeat rewrite rev_length.
  repeat rewrite length_to_list.
  reflexivity.
Qed.

Local Transparent bvMul.

Definition zeroExtend_ls (ls : list bool) n :=
  ls ++ (repeat false n).

Theorem zeroExtend_ls_eq : forall n1 n2 (p2 : spec.BITS n2),
  tuple.tval (spec.zeroExtendAux n1 p2) = zeroExtend_ls (tuple.tval p2) n1.

  induction n1; intros; simpl in *;
  unfold zeroExtend_ls in *; simpl in *.
  rewrite app_nil_r.
  reflexivity.

  unfold spec.joinmsb0.
  match goal with
  | [|- tuple.tval (spec.joinmsb (?a, ?b)) = _ ] =>
    specialize (@joinmsb_ls_eq _ b a); intros
  end.
  transitivity (tuple.tval (spec.zeroExtendAux n1 p2) ++ [0%bool]).
  apply H.
  rewrite IHn1.
  rewrite repeat_cons.
  rewrite <- app_assoc.
  reflexivity.

Qed.

Fixpoint fullmulB_ls (p1 p2 : list bool) : list bool :=
  match p1 with
  | nil => (repeat false (length p2))
  | b1 :: p1' =>
    if b1 
      then addB_ls (false :: fullmulB_ls p1' p2) (zeroExtend_ls p2 (S (length p1')))
      else false :: (fullmulB_ls p1' p2)
  end.

Theorem spec_zero_eq_repeat : forall n,
  tuple.tval (spec.zero n) = repeat false n.  

  induction n; intros; simpl in *; trivial.
  f_equal. eauto.

Qed.


Theorem fullMulB_ls_eq : forall n1 p1 n2 p2,
  tuple.tval (@fullmulB n1 n2 p1 p2) = fullmulB_ls (tuple.tval p1) (tuple.tval p2).

  induction n1; intros; simpl in *.
  destruct p1.
  destruct tval.
  simpl.
  rewrite fromNat0.
  rewrite tuple_tval_length.
  rewrite <- ssrnat.plusE.
  rewrite spec_zero_eq_repeat.
  reflexivity.

  inversion i.

  destruct (bits_cons_decomp p1).
  destruct H.
  subst.
  unfold spec.consB.
  rewrite tuple_head_cons.
  repeat rewrite tuple_behead_cons.
  destruct x.

  rewrite addB_ls_eq.
  unfold spec.joinmsb0.
  rewrite joinmsb_ls_eq.
  rewrite zeroExtend_ls_eq.
  simpl.
  unfold zeroExtend_ls.
  rewrite repeat_S_rev.
  rewrite tuple_tval_length.
  rewrite <- app_assoc.
  rewrite IHn1.
  reflexivity.

  simpl.
  f_equal.
  eauto.
Qed.

Theorem spec_low_ls_eq : forall n2 n1 (b : spec.BITS (ssrnat.addn n2 n1)) ,
  tuple.tval (spec.low n2 b) = firstn n2 (tuple.tval b).

  induction n2; intros; simpl in *; trivial.
  destruct (bits_cons_decomp b).
  destruct H.
  subst.
  simpl.
  unfold spec.consB.
  rewrite tuple_head_cons.
  rewrite tuple_behead_cons.
  f_equal.
  eauto.

Qed.

Theorem fromPosZ_ls_2_eq : forall n,
  (n >= 2)%nat ->
  (fromPosZ_ls n 2) = [false; true] ++ (repeat false (pred (pred n))).

  intros.
  destruct n; simpl; try lia.
  destruct n; simpl; try lia.
  rewrite fromPosZ_ls_0_eq.
  reflexivity.

Qed.

Theorem fullmulB_ls_0_eq : forall n ls2,
  fullmulB_ls (repeat 0%bool n) ls2  = 
  repeat false (n + length ls2).

  induction n; intros; simpl in *; trivial.

  f_equal.
  eauto.

Qed.

Theorem bvMul_2_shiftl_equiv : forall (n : nat) (v : bitvector n), 
  (n >= 2)%nat ->
  bvMul n (intToBv n 2) v = shiftL n bool 0%bool v 1.

  intros.
  apply eq_if_to_list_eq.
  unfold bvMul.
  repeat rewrite <- bitsToBv_ls_eq.
  rewrite shiftL_to_list_eq.
  unfold mulB.
  rewrite spec_low_ls_eq.
  rewrite fullMulB_ls_eq.
  rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  rewrite <- intToBv_ls_eq.
  rewrite bvToBITS_ls_equiv.
  unfold intToBv_ls, bvToBITS_ls, bitsToBv_ls.
  rewrite rev_involutive.
  unfold fromZ_ls.
  rewrite fromPosZ_ls_2_eq.
  simpl.
  destruct n; simpl; try lia.
  destruct n; simpl; try lia.
  rewrite fullmulB_ls_0_eq.

  rewrite rev_length.
  rewrite length_to_list.
  replace (0%bool :: repeat 0%bool (n + S (S n))) with (repeat 0%bool (S n + S (S n))).
  unfold addB_ls, adcB_ls.
  rewrite adcBmain_ls_zero_eq_gen.
  rewrite splitmsb_ls_app_eq.
  simpl.
  unfold zeroExtend_ls.
  rewrite repeat_length.
  
  match goal with
  | [|- context[match rev ?a ++ _ with | []  => _ | _ ::_  => _ end]] => remember a as z
  end.
  assert (length z = (S (S n))).
  subst.
  apply length_to_list.
  destruct z using rev_ind.
  simpl in *. lia.

  clear IHz.
  rewrite rev_app_distr.
  simpl.
  unfold shiftL1_ls, shiftin_ls.
  destruct z. simpl in *; lia.
  simpl.
  assert (n = length z).
  simpl in *.
  rewrite app_length in *.
  simpl in *.
  lia.
  subst.
  rewrite firstn_app_1.
  rewrite firstn_app_1.
  rewrite <- (rev_length z).
  rewrite firstn_all.
  rewrite rev_involutive.
  reflexivity.
  rewrite rev_length.
  lia.
  rewrite app_length.
  rewrite rev_length.
  simpl.
  lia.

  unfold zeroExtend_ls.
  rewrite app_length.
  rewrite rev_length.
  repeat rewrite repeat_length.
  rewrite length_to_list.
  lia.

  reflexivity.
  trivial.

Qed.

Theorem intToBv_mod_eq : forall n x,
  intToBv n (x mod (Z.pow 2 (Z.of_nat n))) = intToBv n x.

  intros.
  apply eq_if_to_list_eq.
  repeat rewrite <- intToBv_ls_eq.
  unfold intToBv_ls.
  f_equal.
  
  remember (x mod 2 ^ Z.of_nat n) as z.
  unfold fromZ_ls.
  destruct z.
  destruct x.
  trivial.
  unfold zero_ls.
  rewrite fromPosZ_mod_eq.
  rewrite <- Heqz.
  symmetry.
  apply fromPosZ_ls_0_eq.
  rewrite fromNegZ_ls_pos_opp.
  rewrite <- Z.opp_succ.
  rewrite Z.succ_pred.
  rewrite Z.opp_involutive.
  rewrite fromPosZ_mod_eq.
  rewrite <- Heqz.
  symmetry.
  apply fromPosZ_ls_0_eq.

  destruct x.
  rewrite Heqz.
  rewrite <- fromPosZ_mod_eq.
  apply fromPosZ_ls_0_eq.
  rewrite Heqz.
  rewrite <- fromPosZ_mod_eq.
  reflexivity.
  rewrite fromNegZ_ls_pos_opp.
  rewrite Heqz.
  rewrite Z.opp_pred.
  rewrite Z.pred_succ.
  rewrite Z.opp_involutive.
  symmetry.
  apply fromPosZ_mod_eq.

  assert (0 <= Z.neg p).
  rewrite Heqz.
  apply Z.mod_pos_bound.
  lia.
  lia.

Qed.


Theorem intToBb_bvToInt_id : forall n x,
  intToBv n (bvToInt n x) = x.

  intros.
  rewrite <- bvToInt_ls_equiv.
  listify.
  unfold bvToInt_ls.
  unfold bvToBITS_ls.
  unfold fromZ_ls.
  remember (toPosZ_ls (rev (to_list x)) ) as z.
  destruct z.
  symmetry in Heqz.
  apply toPosZ_ls_0_impl in Heqz.
  eapply eq_if_rev_eq.
  rewrite Heqz.
  rewrite rev_involutive.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  rewrite Heqz.
  erewrite fromPosZ_ls_toPosZ_ls_eq_gen.
  apply rev_involutive.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.

  assert (0 <= Z.neg p).
  rewrite Heqz.
  eapply toPosZ_ls_nonneg.
  lia.
Qed.

Theorem fromZ_ls_toZ_ls_id : forall x, 
  length x <> O ->
  rev (fromZ_ls (length x) (toZ_ls (rev x))) = x.

  intros.
  unfold toZ_ls.
  unfold fromZ_ls.
  remember (splitmsb_ls (rev x)) as z.
  destruct z.
  destruct b.
  remember (- Z.succ (toNegZ_ls l)) as z.
  destruct z.
  (* contradictions *)
  specialize (toNegZ_ls_nonneg l); intros.
  lia.
  specialize (toNegZ_ls_nonneg l); intros.
  lia.

  rewrite Heqz0.
  rewrite Z.opp_involutive.
  rewrite Z.pred_succ.
  replace (Datatypes.length x) with (Datatypes.length l + 1)%nat.
  rewrite fromNegZ_ls_app.
  rewrite <- fromNegZ_mod_eq.
  rewrite fromNegZ_ls_toNegZ_ls_eq.
  rewrite Z.div_small.
  simpl.
  unfold joinlsb_ls.
  simpl.
  unfold splitmsb_ls in *.
  rewrite seq_rev_eq in *.
  rewrite rev_involutive in *.
  destruct x; simpl in *; try lia; pairInv.
  rewrite rev_app_distr in *.
  simpl in *.
  rewrite seq_rev_eq in *.
  rewrite rev_involutive in *.
  reflexivity.
  intuition idtac.
  apply toNegZ_ls_nonneg.
  apply toNegZ_ls_upper_bound.
  unfold splitmsb_ls in *.
  rewrite seq_rev_eq in *.
  rewrite rev_involutive in *.
  destruct x; simpl in *; try lia; pairInv.
  rewrite seq_rev_eq in *.
  rewrite rev_length.
  lia.

  remember (toPosZ_ls l) as z.
  destruct z.
  symmetry in Heqz0.
  apply toPosZ_ls_0_impl in Heqz0.
  unfold zero_ls.
  unfold splitmsb_ls in *.
  rewrite seq_rev_eq in *.
  rewrite rev_involutive in *.
  destruct x. simpl in *. 
  trivial.
  pairInv.
  rewrite seq_rev_eq in *.
  replace (Datatypes.length (0%bool :: x)) with (Datatypes.length x + 1)%nat.
  rewrite repeat_app.
  simpl.
  rewrite rev_app_distr.
  simpl.
  f_equal.
  apply eq_if_rev_eq.
  rewrite Heqz0.
  rewrite rev_involutive.
  rewrite rev_length.
  reflexivity.
  simpl.
  lia.

  rewrite Heqz0.
  replace (Datatypes.length x) with (Datatypes.length l + 1)%nat.
  rewrite fromPosZ_ls_app.
  rewrite <- fromPosZ_mod_eq.
  rewrite fromPosZ_ls_toPosZ_ls_eq.
  rewrite Z.div_small.
  simpl.
  unfold joinlsb_ls.
  simpl.
  unfold splitmsb_ls in *.
  rewrite seq_rev_eq in *.
  rewrite rev_involutive in *.
  destruct x; simpl in *; try lia; pairInv.
  rewrite rev_app_distr in *.
  simpl in *.
  rewrite seq_rev_eq in *.
  rewrite rev_involutive in *.
  reflexivity.
  intuition idtac.
  apply toPosZ_ls_nonneg.
  apply toPosZ_ls_upper_bound.
  unfold splitmsb_ls in *.
  rewrite seq_rev_eq in *.
  rewrite rev_involutive in *.
  destruct x; simpl in *; try lia; pairInv.
  rewrite seq_rev_eq in *.
  rewrite rev_length.
  lia.

  (* contradiction *)
  assert (0 <= Z.neg p).
  rewrite Heqz0.
  apply toPosZ_ls_nonneg.
  lia.

Qed.


Theorem fromZ_ls_toZ_ls_id_gen : forall n x, 
  n <> O ->
  n = length x ->
  rev (fromZ_ls n (toZ_ls (rev x))) = x.

  intros; subst.
  apply fromZ_ls_toZ_ls_id.
  trivial.

Qed.
  
Theorem intToBv_sbvToInt_id : forall n x,
  intToBv n (sbvToInt n x) = x.

  intros.
  rewrite <- sbvToInt_ls_equiv.
  listify.
  destruct n.
  simpl.
  rewrite (Vec_0_nil _ x).
  reflexivity.
  unfold sbvToInt_ls.
  unfold bvToBITS_ls.
  apply fromZ_ls_toZ_ls_id_gen.
  lia.
  rewrite length_to_list.
  reflexivity.

Qed.


Theorem bvToInt_bvAdd_equiv : forall n (v1 v2 : bitvector n),
  (bvToInt n (bvAdd _ v1 v2)) =
  (((bvToInt _ v1) + (sbvToInt _ v2)) mod (Z.pow 2 (Z.of_nat n)))%Z.

  intros.
  rewrite <- (@bvToInt_intToBv_id n ((bvToInt n v1 + sbvToInt n v2) mod 2 ^ Z.of_nat n)).
  rewrite intToBv_mod_eq.
  rewrite intToBv_add_equiv.
  f_equal.
  f_equal.
  symmetry.
  apply intToBb_bvToInt_id.
  symmetry.
  apply intToBv_sbvToInt_id.
  apply Z.mod_pos_bound.
  lia.
Qed.

Theorem bvToInt_sbvAdd_equiv : forall n (v1 v2 : bitvector n),
  (bvToInt n (bvAdd _ v1 v2)) =
  (((sbvToInt _ v1) + (sbvToInt _ v2)) mod (Z.pow 2 (Z.of_nat n)))%Z.

  intros.
  rewrite <- (@bvToInt_intToBv_id n ((sbvToInt n v1 + sbvToInt n v2) mod 2 ^ Z.of_nat n)).
  rewrite intToBv_mod_eq.
  rewrite intToBv_add_equiv.
  f_equal.
  f_equal.
  symmetry.
  apply intToBv_sbvToInt_id.
  symmetry.
  apply intToBv_sbvToInt_id.
  apply Z.mod_pos_bound.
  lia.
Qed.

Theorem bvToInt_bvAdd_small_equiv : forall n (v1 v2 : bitvector n),
  (* (sbvToInt _ v2 <= bvToInt _ v1)%Z -> *)
  (0 <= (bvToInt _ v1) + (sbvToInt _ v2) < Z.pow 2 (Z.of_nat n))%Z->
  (bvToInt n (bvAdd _ v1 v2)) =
  ((bvToInt _ v1) + (sbvToInt _ v2))%Z.

  intros.
  rewrite bvToInt_bvAdd_equiv.
  apply Zdiv.Zmod_small.
  trivial.
Qed.



Theorem bvToInt_bvSub_small_equiv : forall n v1 v2,
  (0 <= (bvToInt _ v1) - (sbvToInt _ v2) < Z.pow 2 (Z.of_nat n))%Z->
  (- 2 ^ Z.of_nat (pred n) < sbvToInt n v2)%Z ->
  (bvToInt n (bvSub v1 v2)) =
  ((bvToInt _ v1) - (sbvToInt _ v2))%Z.

  intros.
  rewrite bvSub_eq_bvAdd_neg.
  rewrite <- Z.add_opp_r.
  rewrite bvToInt_bvAdd_small_equiv.
  rewrite sbvToInt_bvNeg_equiv.
  reflexivity.
  lia.
  
  rewrite sbvToInt_bvNeg_equiv.
  rewrite Z.add_opp_r.
  trivial.
  lia.
Qed.

Definition signedModPow n z :=
  let z' := z mod (Z.pow 2 (Z.of_nat (S n))) in
  if (ZArith_dec.Z_ge_lt_dec z' (Z.pow 2 (Z.of_nat n))) then (Z.sub z' (Z.pow 2 (Z.of_nat (S n)))) else z'.


Theorem mod_eq_impl_signedModPow_eq : forall n x y,
  (x mod (Z.pow 2 (Z.of_nat (S n)))) = (y mod (Z.pow 2 (Z.of_nat (S n)))) ->
  signedModPow n x = signedModPow n y.

  intros.
  unfold signedModPow.
  rewrite H.
  reflexivity.

Qed.

Theorem signedModPow_id : forall n x,
  -Z.pow 2 (Z.of_nat n) <= x < Z.pow 2 (Z.of_nat n) ->
  signedModPow n x = x.

  intros.
  unfold signedModPow.
  destruct (ZArith_dec.Z_ge_lt_dec (x mod 2 ^ Z.of_nat (S n)) (2 ^ Z.of_nat n)).
  assert ( x < 0).
  destruct (ZArith_dec.Z_lt_ge_dec x 0); trivial.
  rewrite Z.mod_small in g.
  lia.
  intuition idtac.
  lia.
  eapply Z.lt_le_trans; eauto.
  eapply Z.pow_le_mono_r; lia.

  rewrite <- Zdiv.Z_mod_nz_opp_r.
  apply Z.opp_inj.
  rewrite <- Zdiv.Zmod_opp_opp.
  rewrite Z.opp_involutive.
  apply Z.mod_small.
  intuition idtac.
  apply Z.opp_nonneg_nonpos.
  lia. 
  apply Z.opp_lt_mono.
  rewrite Z.opp_involutive.
  eapply Z.lt_le_trans.
  apply (Z.opp_lt_mono (2 ^ Z.of_nat n) (2 ^ Z.of_nat (S n))).
  apply Z.pow_lt_mono_r; lia.
  lia.
  lia.

  assert (x >= 0).
  destruct (ZArith_dec.Z_ge_lt_dec x 0); trivial.
  rewrite <- (Z.opp_involutive x) in l.
  rewrite Z.mod_opp_l_nz in l.
  rewrite Z.mod_small in l.
  assert (2 * (2 ^ Z.of_nat (n)) - 2^(Z.of_nat n) < 2^(Z.of_nat n)).
  eapply Z.le_lt_trans; eauto.
  apply Z.sub_le_mono.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite Z.pow_succ_r.
  reflexivity.
  lia.
  lia.
  lia.
  intuition idtac.
  lia.
  apply Z.opp_lt_mono.
  rewrite Z.opp_involutive.
  eapply Z.lt_le_trans.
  apply (Z.opp_lt_mono (2 ^ Z.of_nat n) (2 ^ Z.of_nat (S n))).
  apply Z.pow_lt_mono_r; lia.
  lia.
  lia.
  rewrite Z.mod_small.
  lia.
  intuition idtac.
  lia.
  apply Z.opp_lt_mono.
  rewrite Z.opp_involutive.
  eapply Z.lt_le_trans.
  apply (Z.opp_lt_mono (2 ^ Z.of_nat n) (2 ^ Z.of_nat (S n))).
  apply Z.pow_lt_mono_r; lia.
  lia.

  apply Z.mod_small.
  intuition idtac.
  lia.
  eapply Z.lt_le_trans.
  eauto.
  eapply Z.pow_le_mono_r; lia.

Qed.

Theorem toNegZ_ls_ones_complement : forall ls,
  toNegZ_ls ls = Z.pred ((Z.pow 2 (Z.of_nat (length ls))) - (toPosZ_ls ls)).

  induction ls; intros.
  trivial.
  simpl.
  rewrite IHls.
  destruct a.
  rewrite Z.double_spec.
  repeat rewrite <- Z.add_opp_l.
  repeat rewrite <- Z.add_pred_l.
  rewrite Z.mul_add_distr_l.
  f_equal.
  lia.

  rewrite Z.pow_pos_fold.
  rewrite Znat.Zpos_P_of_succ_nat.
  rewrite <- Z.add_1_l.
  rewrite Z.pow_add_r.
  reflexivity.
  lia.
  lia.

  rewrite Z.double_spec.
  repeat rewrite <- Z.add_opp_l.
  repeat rewrite <- Z.add_pred_l.
  rewrite Z.mul_add_distr_l.
  rewrite <- Z.add_succ_l.
  f_equal.
  lia.
  
  rewrite Z.pow_pos_fold.
  rewrite Znat.Zpos_P_of_succ_nat.
  rewrite <- Z.add_1_l.
  rewrite Z.pow_add_r.
  reflexivity.
  lia.
  lia.

Qed.

Theorem sbvToInt_signedModPow_eq : forall n v,
  sbvToInt (S n) v = signedModPow n (bvToInt (S n) v).

  intros.
  rewrite <- sbvToInt_ls_equiv.
  rewrite <- bvToInt_ls_equiv.
  unfold sbvToInt_ls, bvToInt_ls.
  unfold toZ_ls.
  unfold bvToBITS_ls.
  unfold splitmsb_ls.
  rewrite seq_rev_eq.
  rewrite rev_involutive.
  destruct (Vec_S_cons _ _ v).
  destruct H.
  subst.
  rewrite to_list_cons.
  simpl.
  repeat rewrite seq_rev_eq.
  rewrite toPosZ_ls_app.
  simpl.
  rewrite rev_length.
  rewrite length_to_list.
  destruct x.
  rewrite Z.mul_1_l.
  rewrite toNegZ_ls_ones_complement.
  rewrite rev_length.
  rewrite length_to_list.
  rewrite Z.succ_pred.
  unfold signedModPow.
  destruct (ZArith_dec.Z_ge_lt_dec ((toPosZ_ls (rev (to_list x0)) +  2 ^ Z.of_nat n) mod 2 ^ Z.of_nat (S n)) (2 ^ Z.of_nat n)).
  rewrite Z.mod_small.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_l.
  rewrite Z.pow_add_r.
  lia.
  lia.
  lia.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_l.
  rewrite Z.pow_add_r.
  assert (0 <= toPosZ_ls (rev (to_list x0)) < Z.pow 2 (Z.of_nat n)).
  intuition idtac.
  apply toPosZ_ls_nonneg.
  eapply Z.lt_le_trans.
  apply toPosZ_ls_upper_bound.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  lia.
  lia.
  lia.

  assert (0 <= toPosZ_ls (rev (to_list x0)) < Z.pow 2 (Z.of_nat n)).
  intuition idtac.
  apply toPosZ_ls_nonneg.
  eapply Z.lt_le_trans.
  apply toPosZ_ls_upper_bound.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
  rewrite Z.mod_small in l.
  lia.  
  rewrite Znat.Nat2Z.inj_succ.
  rewrite <- Z.add_1_l.
  rewrite Z.pow_add_r.
  lia.
  lia.
  lia.

  rewrite Z.mul_0_l.
  rewrite Z.add_0_r.
  rewrite signedModPow_id.  
  reflexivity.
  intuition idtac.
  eapply Z.le_trans; [idtac | apply toPosZ_ls_nonneg].
  lia.
  eapply Z.lt_le_trans.
  apply toPosZ_ls_upper_bound.
  rewrite rev_length.
  rewrite length_to_list.
  reflexivity.
Qed.


Theorem sbvToInt_bvSub_equiv : forall n (v1 v2 : Vec n _),
  (n > 1)%nat -> 
    (-(Z.pow 2 (Z.of_nat (pred (pred n)))) <= (sbvToInt _ v1) < Z.pow 2 (Z.of_nat (pred (pred n))))%Z ->
   (-(Z.pow 2 (Z.of_nat (pred (pred n)))) <= (sbvToInt _ v2) < Z.pow 2 (Z.of_nat (pred (pred n))))%Z ->
  sbvToInt _ (bvSub v1 v2) = ((sbvToInt _ v1) - (sbvToInt _ v2)).

  intros.
  destruct n.
  lia.
  replace ((sbvToInt _ v1) - (sbvToInt _ v2)) with (signedModPow n ((sbvToInt _ v1) - (sbvToInt _ v2))).
  rewrite sbvToInt_signedModPow_eq.
  apply mod_eq_impl_signedModPow_eq.
  rewrite bvSub_eq_bvAdd_neg.
  rewrite bvToInt_sbvAdd_equiv.
  rewrite Zdiv.Zmod_mod.
  rewrite <- Z.add_opp_r.
  rewrite sbvToInt_bvNeg_equiv.
  reflexivity.
  eapply Z.lt_le_trans; [idtac | apply H1].
  apply (Z.opp_lt_mono (2 ^ Z.of_nat (pred (pred (S n))))).
  apply Z.pow_lt_mono_r.
  lia.
  lia.
  lia.
  apply signedModPow_id.
  simpl in *. 
  assert (2 ^ Z.of_nat n = 2 * (2 ^ Z.of_nat (pred n))).
  destruct n.
  lia.
  rewrite Znat.Nat2Z.inj_succ.
  rewrite Z.pow_succ_r.
  trivial.
  lia.
  lia.

Qed.

Theorem map_repeat_eq : forall (A B : Type)(f : A -> B) n (a : A),
  map f (repeat a n) = repeat (f a) n.

  induction n; intros; simpl in *; trivial.
  f_equal.
  eauto.

Qed.

Theorem sbvToInt_sign_extend_equiv : forall n1 n2 x,
    n1 <> O ->
    sbvToInt _
  (append
     (if sawAt n1 Bool x 0%nat
      then
       ecCompl (bitvector n2) (PLogicWord n2)
         (ecZero (bitvector n2) (intToBv n2 0))
      else ecZero (bitvector n2) (intToBv n2 0)) x) = 
  sbvToInt n1 x.

  intros.
  rewrite intToBv_0_eq_replicate.
  unfold ecCompl, ecZero.
  simpl.
  repeat rewrite <- sbvToInt_ls_equiv.
  destruct n2.
  destruct n1.
  lia.
  unfold sbvToInt_ls.
  simpl. 
  unfold bvToBITS_ls. 
  rewrite (toList_append_equiv _ (if sawAt (S n1) Bool x 0 then bvNot 0 (replicate 0 bool 0%bool) else replicate 0 bool 0%bool) x).
  destruct (sawAt (S n1) Bool x 0).
  unfold bvNot.
  rewrite toList_map_equiv.
  rewrite (Vec_0_nil _ (replicate 0 bool 0%bool)).
  rewrite to_list_nil.
  simpl.
  reflexivity.
  rewrite (Vec_0_nil _ (replicate 0 bool 0%bool)).
  rewrite to_list_nil.
  simpl.
  reflexivity.

  destruct n1.
  lia.
  unfold sbvToInt_ls.
  simpl.
  unfold bvToBITS_ls.
  rewrite (toList_append_equiv _ (if sawAt (S n1) Bool x 0 then bvNot (S n2) (replicate (S n2) bool 0%bool) else replicate (S n2) bool 0%bool) x).
  destruct (Vec_S_cons _ _ x).
  destruct H0.
  subst.
  rewrite sawAt_nth_equiv; try lia.
  repeat rewrite to_list_cons.
  unfold nth.
  destruct x0.
  unfold bvNot.
  rewrite toList_map_equiv.
  rewrite <- replicate_repeat_eq.
  simpl.
  unfold toZ_ls.
  unfold splitmsb_ls.
  repeat rewrite seq_rev_eq.
  repeat rewrite rev_app_distr.
  repeat rewrite rev_involutive.
  simpl.
  repeat rewrite seq_rev_eq.
  repeat rewrite rev_app_distr.
  simpl.
  rewrite map_repeat_eq.
  simpl.
  rewrite rev_repeat_id.
  rewrite toNegZ_app_repeat_0_eq.
  rewrite toNegZ_app_1_eq.
  reflexivity.

  rewrite <- replicate_repeat_eq.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_repeat_id.
  unfold toZ_ls, splitmsb_ls.
  repeat rewrite seq_rev_eq.
  repeat rewrite rev_app_distr.
  repeat rewrite rev_involutive.
  simpl.
  repeat rewrite seq_rev_eq.
  repeat rewrite rev_app_distr.
  repeat rewrite rev_involutive.
  rewrite toPosZ_app_repeat_0_eq.
  simpl.
  apply toPosZ_app_0_eq.
Qed.

Theorem shrB_ls_equiv : forall n (y : spec.BITS n), 
  (tuple.tval (operations.shrB y)) = (rev (shiftR1_ls false (rev (tuple.tval y)))).

  intros.
  unfold operations.shrB.
  destruct n.
  destruct y.
  destruct tval; simpl in *; try lia.
  reflexivity.
  inversion i.

  unfold spec.joinmsb0.
  rewrite joinmsb_ls_eq.
  rewrite droplsb_ls_eq.
  unfold shiftR1_ls, shiftout_ls.
  simpl.
  destruct y.
  destruct tval.
  simpl in *.
  inversion i.

  simpl.
  replace (Datatypes.length (rev tval ++ [b])) with (Datatypes.length (0%bool :: rev tval ++ [b]) - 1)%nat.
  rewrite <- skipn_rev.
  simpl.
  rewrite rev_app_distr.
  rewrite rev_involutive.
  simpl.
  reflexivity.
  rewrite app_length.
  simpl.
  rewrite app_length.
  simpl.
  lia.
Qed.


Theorem shrBn_ls_equiv : forall n x (y : spec.BITS n), 
  (tuple.tval (operations.shrBn y x)) = rev (shiftR_ls false (rev (tuple.tval y)) x).

  induction x; intros; simpl in *.
  rewrite rev_involutive.
  reflexivity.
  rewrite shrB_ls_equiv.
  rewrite IHx.
  rewrite rev_involutive.
  reflexivity.

Qed.


Theorem bvShr_shiftR_equiv : forall x n v,
  bvShr n v x = shiftR n _ false v x.

  Local Transparent bvShr.

  intros.
  apply eq_if_to_list_eq.
  rewrite shiftR_ls_equiv.
  unfold bvShr.
  rewrite <- bitsToBv_ls_eq.
  rewrite shrBn_ls_equiv.
  rewrite bvToBITS_ls_equiv.
  unfold bvToBITS_ls.
  rewrite rev_involutive.
  unfold bitsToBv_ls.
  rewrite rev_involutive.
  reflexivity.

  Local Opaque bvShr.

Qed.

Theorem bvUDiv_nat_equiv : forall  n v1 v2,
  bvUDiv n v1 v2 = bvNat _ (Nat.div (bvToNat _ v1) (bvToNat _ v2)).

  Local Transparent bvUDiv.

  intros.
  unfold bvUDiv.
  unfold bvNat.
  rewrite Znat.Nat2Z.inj_div.
  repeat rewrite bvToNat_toZ_equiv.
  reflexivity.

Qed.



