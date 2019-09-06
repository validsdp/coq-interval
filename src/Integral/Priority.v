(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2019, Inria

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

From Coq Require Import List Arith ZArith Psatz.
From mathcomp.ssreflect Require Import ssrfun ssrbool fintype.

Section Permut.

Context {T : Type}.

Fixpoint onth n (l : list T) :=
  match l, n with
  | nil, _ => None
  | v :: _, O => Some v
  | _ :: l, S n => onth n l
  end.

Lemma onth_app_l :
  forall n p q,
  n < length p ->
  onth n (p ++ q) = onth n p.
Proof.
intros n p q.
revert n.
induction p as [|v p IH].
easy.
intros [|n] ; simpl.
easy.
intros H.
apply lt_S_n in H.
now apply IH.
Qed.

Lemma onth_app_r :
  forall n p q,
  length p <= n ->
  onth n (p ++ q) = onth (n - length p) q.
Proof.
intros n p q.
revert n.
induction p as [|v p IH].
intros n _.
now rewrite Nat.sub_0_r.
intros [|n] ; simpl.
easy.
intros H.
apply le_S_n in H.
now apply IH.
Qed.

Inductive permut (p q : list T) : Prop :=
  | Permut (Hl : length p = length q)
     (f : ordinal (length p) -> ordinal (length p))
     (Hf : injective f)
     (Hpq : forall n : ordinal _, onth n p = onth (f n) q).

Lemma permut_refl :
  forall p, permut p p.
Proof.
intros p.
now apply Permut with (f := fun n => n).
Qed.

Lemma permut_sym :
  forall p q, permut p q -> permut q p.
Proof.
intros p q [Hl f Hf Hpq].
revert f Hf Hpq.
rewrite Hl.
intros f Hf Hpq.
apply Permut with (f := invF Hf).
now apply eq_sym.
apply can_inj with (g := f).
apply f_invF.
intros n.
rewrite <- (f_invF Hf n) at 1.
apply eq_sym, Hpq.
Qed.

Lemma permut_trans :
  forall q p r,
  permut p q -> permut q r -> permut p r.
Proof.
intros q p r [Hl1 f1 Hf1 Hpq] [Hl2 f2 Hf2 Hqr].
revert f1 Hf1 Hpq f2 Hf2 Hqr.
rewrite <- Hl1.
intros f1 Hf1 Hpq f2 Hf2 Hqr.
apply Permut with (f := fun k => f2 (f1 k)).
now apply eq_trans with (length q).
now apply inj_comp.
intros n.
now rewrite <- Hqr.
Qed.

Lemma injective_split :
  forall n n1 n2 n3 n4 (H1 : n = n1 + n2) (H2 : n3 + n4 = n) f,
  injective f ->
  injective (fun k : ordinal n => cast_ord H2 (unsplit (f (split (cast_ord H1 k))))).
Proof.
intros n n1 n2 n3 n4 H1 H2 f Hf.
apply inj_comp with (f := cast_ord H2).
apply cast_ord_inj.
apply inj_comp with (f := @unsplit _ _).
eapply can_inj.
apply unsplitK.
apply inj_comp with (1 := Hf).
apply inj_comp with (f := @split _ _).
eapply can_inj.
apply splitK.
apply cast_ord_inj.
Qed.

Lemma permut_app_l :
  forall p q r,
  permut q r ->
  permut (p ++ q) (p ++ r).
Proof.
intros p q r [Hl f Hf H1].
assert (H2: length (p ++ q) = length p + length q).
  apply app_length.
simple refine (Permut _ _ _ _ _ _).
- rewrite 2!app_length.
  now apply f_equal.
- intros k.
  apply (cast_ord (esym H2)).
  apply unsplit.
  destruct (split (cast_ord H2 k)) as [k'|k'].
  now left.
  right.
  now apply f.
- apply injective_split with (f := fun k => match k with inl k' => inl k' | inr k' => inr (f k') end).
  clear -Hf.
  intros [k1|k1] [k2|k2] ; try easy.
  intros H.
  apply f_equal.
  injection H.
  apply Hf.
- simpl.
  intros n.
  case splitP ; simpl ; change ssrnat.addn with plus ; intros k ->.
  assert (Hk: k < length p).
    eapply elimT.
    now apply ssrnat.ltP.
    easy.
  now rewrite 2!onth_app_l.
  rewrite 2!onth_app_r by lia.
  rewrite 2!minus_plus.
  apply H1.
Qed.

Lemma permut_app :
  forall p q,
  permut (p ++ q) (q ++ p).
Proof.
intros l1 l2.
assert (H1: length l2 + length l1 = length (l1 ++ l2)).
  rewrite app_length.
  apply plus_comm.
assert (H2: length (l1 ++ l2) = length l1 + length l2).
  apply app_length.
simple refine (Permut _ _ _ _ _ _).
- rewrite 2!app_length.
  apply plus_comm.
- intros k.
  apply (cast_ord H1).
  apply unsplit.
  destruct (split (cast_ord H2 k)) as [k'|k'].
  now right.
  now left.
- apply injective_split with (f := fun k => match k with inl k' => inr k' | inr k' => inl k' end).
  clear.
  intros [k1|k1] [k2|k2] ; try easy ; intros H ; injection H ; apply f_equal.
- simpl.
  intros n.
  case splitP ; simpl ; change ssrnat.addn with plus ; intros k Hk.
  rewrite onth_app_l.
  rewrite onth_app_r by lia.
  rewrite minus_plus.
  now rewrite <- Hk.
  eapply elimT.
  now apply ssrnat.ltP.
  now rewrite Hk.
  rewrite onth_app_r by lia.
  rewrite onth_app_l.
  now rewrite Hk, minus_plus.
  cut (n < length l1 + length l2). lia.
  eapply elimT.
  apply ssrnat.ltP.
  now rewrite <- app_length.
Qed.

Lemma permut_app_r :
  forall p q r,
  permut p r ->
  permut (p ++ q) (r ++ q).
Proof.
intros p q r H.
apply permut_trans with (q ++ r).
apply permut_trans with (q ++ p).
apply permut_app.
now apply permut_app_l.
apply permut_app.
Qed.

Lemma permut_cons :
  forall h p q,
  permut p q ->
  permut (h :: p) (h :: q).
Proof.
intros h p q [Hl f Hf Hpq].
assert (H1: 1 + length p = length (h :: p)) by easy.
simple refine (Permut _ _ _ _ _ _).
- simpl.
  now apply f_equal.
- intros k.
  apply (cast_ord H1).
  apply unsplit.
  destruct (split (cast_ord (esym H1) k)) as [k'|k'].
  now left.
  right.
  now apply f.
- apply injective_split with (f := fun k => match k with inl k' => inl k' | inr k' => inr (f k') end).
  clear -Hf.
  intros [k1|k1] [k2|k2] ; try easy ; intros H.
  apply f_equal.
  injection H.
  apply Hf.
- simpl.
  intros n.
  case splitP ; simpl ; change ssrnat.addn with plus ; intros k ->.
  clear.
  now destruct k as [[|k] Hk].
  apply Hpq.
Qed.

Lemma permut_insert :
  forall p q r v,
  permut r (p ++ q) ->
  permut (v :: r) (p ++ v :: q).
Proof.
intros p q r v Hr.
apply permut_trans with (v :: p ++ q).
now apply permut_cons.
change (permut (((v :: nil) ++ p) ++ q) (p ++ (v :: nil) ++ q)).
rewrite app_assoc.
apply permut_app_r.
apply permut_app.
Qed.

End Permut.

Section Pairing.

Context {T : Type}.

Inductive ptree := PTsome (v : T) (l : list ptree).
Inductive pheap := PHnone | PHsome (t : ptree).

Theorem ptree_ind' :
  forall P : ptree -> Prop,
  (forall v l, Forall P l -> P (PTsome v l)) ->
  forall t, P t.
Proof.
intros P H.
fix IH 1.
intros [v l].
apply H.
induction l ; constructor.
apply IH.
apply IHl.
Qed.

Fixpoint ptree_to_list (p : ptree) : list T :=
  match p with
  | PTsome v l => v :: flat_map ptree_to_list l
  end.

Fixpoint pheap_to_list (p : pheap) : list T :=
  match p with
  | PHnone => nil
  | PHsome p => ptree_to_list p
  end.

Variable le : T -> T -> bool.

Definition ptree_meld (p1 p2 : ptree) : ptree :=
  match p1, p2 with
  | PTsome v1 l1, PTsome v2 l2 =>
    if le v1 v2 then PTsome v1 (p2 :: l1)
    else PTsome v2 (p1 :: l2)
  end.

Theorem ptree_meld_correct :
  forall p1 p2,
  permut (ptree_to_list (ptree_meld p1 p2)) (ptree_to_list p1 ++ ptree_to_list p2).
Proof.
intros [v1 l1] [v2 l2].
unfold ptree_meld.
case le ; simpl.
- apply permut_cons.
  apply (permut_app (v2 :: flat_map _ _)).
- apply permut_insert with (p := v1 :: flat_map _ _).
  apply permut_refl.
Qed.

Definition ptree_insert (p : ptree) (v : T) :=
  ptree_meld p (PTsome v nil).

Theorem ptree_insert_correct :
  forall p v,
  permut (ptree_to_list (ptree_insert p v)) (v :: ptree_to_list p).
Proof.
intros [v1 l1] v.
unfold ptree_insert.
eapply permut_trans.
apply ptree_meld_correct.
apply (permut_app _ (v :: nil)).
Qed.

Definition pheap_insert (p : pheap) (v : T) : ptree :=
  match p with
  | PHnone => PTsome v nil
  | PHsome p => ptree_insert p v
  end.

Theorem pheap_insert_correct :
  forall p v,
  permut (ptree_to_list (pheap_insert p v)) (v :: pheap_to_list p).
Proof.
intros [|p] v.
apply permut_refl.
apply ptree_insert_correct.
Qed.

Fixpoint ptree_merge_pairs (p1 : ptree) (l : list ptree) : ptree :=
  match l with
  | nil => p1
  | p2 :: nil => ptree_meld p1 p2
  | p2 :: p3 :: l' => ptree_meld (ptree_meld p1 p2) (ptree_merge_pairs p3 l')
  end.

Lemma list_ind2 :
  forall A (P : list A -> Prop),
  P nil ->
  (forall v, P (v :: nil)) ->
  (forall v w l, P l -> P (v :: w :: l)) ->
  forall l, P l.
Proof.
intros A P H0 H1 H12.
fix aux 1.
intros [|v [|w l]].
easy.
easy.
apply H12.
apply aux.
Qed.

Theorem ptree_merge_pairs_correct :
  forall p l,
  permut (ptree_to_list (ptree_merge_pairs p l)) (ptree_to_list p ++ flat_map ptree_to_list l).
Proof.
intros p l.
revert p.
induction l as [|v|v w l IH] using list_ind2 ; simpl ; intros p.
rewrite app_nil_r.
apply permut_refl.
rewrite app_nil_r.
apply ptree_meld_correct.
eapply permut_trans.
apply ptree_meld_correct.
rewrite app_assoc.
eapply permut_trans.
apply permut_app_r.
apply ptree_meld_correct.
now apply permut_app_l.
Qed.

Definition ptree_pop (p : ptree) : T * pheap :=
  match p with
  | PTsome v l => (v,
    match l with
    | nil => PHnone
    | lh :: lt => PHsome (ptree_merge_pairs lh lt)
    end)
  end.

Theorem ptree_pop_correct :
  forall p,
  match ptree_pop p with
  | (v, PHnone) => ptree_to_list p = v :: nil
  | (v, PHsome q) => permut (ptree_to_list p) (v :: ptree_to_list q)
  end.
Proof.
intros [v [|l]].
easy.
simpl.
apply permut_cons.
apply permut_sym.
apply ptree_merge_pairs_correct.
Qed.

Fixpoint ptree_fold {A} (f : A -> T -> A) (p : ptree) (acc : A) : A :=
  match p with
  | PTsome v l => fold_left (fun acc q => ptree_fold f q acc) l (f acc v)
  end.

Theorem ptree_fold_correct :
  forall A (f : A -> T -> A) acc p,
  ptree_fold f p acc = fold_left f (ptree_to_list p) acc.
Proof.
intros A f acc p.
revert acc.
induction p as [v l IH] using ptree_ind'.
simpl.
intros acc.
generalize (f acc v).
clear acc.
induction IH as [|q l H1 _ H2] ; simpl ; intros acc.
easy.
rewrite fold_left_app.
rewrite H2.
now apply f_equal.
Qed.

End Pairing.

Arguments ptree : clear implicits.
Arguments pheap : clear implicits.