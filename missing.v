Require Import Reals.
Require Import ZArith.

Axiom Ratan: R -> R.

Lemma Rplus_le_reg_r :
  forall r r1 r2 : R,
  (r1 + r <= r2 + r)%R -> (r1 <= r2)%R.
intros.
apply Rplus_le_reg_l with r.
do 2 rewrite (Rplus_comm r).
exact H.
Qed.

Lemma Rmult_le_compat_neg_r :
  forall r r1 r2 : R,
  (r <= 0)%R -> (r1 <= r2)%R -> (r2 * r <= r1 * r)%R.
intros.
rewrite (Rmult_comm r2).
rewrite (Rmult_comm r1).
apply Rmult_le_compat_neg_l.
exact H.
exact H0.
Qed.

Lemma Rmult_eq_compat_r :
  forall r r1 r2 : R,
  r1 = r2 -> (r1 * r)%R = (r2 * r)%R.
intros.
rewrite (Rmult_comm r1).
rewrite (Rmult_comm r2).
apply Rmult_eq_compat_l.
exact H.
Qed.

Lemma Rmult_eq_reg_r :
  forall r r1 r2 : R,
  (r1 * r)%R = (r2 * r)%R -> r <> 0%R -> r1 = r2.
intros.
apply Rmult_eq_reg_l with (2 := H0).
do 2 rewrite (Rmult_comm r).
exact H.
Qed.

Lemma minus_IZR :
  forall n m : Z,
  IZR (n - m) = (IZR n - IZR m)%R.
intros.
unfold Zminus.
rewrite plus_IZR.
rewrite Ropp_Ropp_IZR.
apply refl_equal.
Qed.

Lemma Rmin_Rle :
  forall r1 r2 r,
  (Rmin r1 r2 <= r)%R <-> (r1 <= r)%R \/ (r2 <= r)%R.
intros.
unfold Rmin.
split.
case (Rle_dec r1 r2) ; intros.
left. exact H.
right. exact H.
intros [H|H] ; case (Rle_dec r1 r2) ; intros H0.
exact H.
apply Rle_trans with (2 := H).
apply Rlt_le.
apply Rnot_le_lt with (1 := H0).
apply Rle_trans with r2 ; assumption.
exact H.
Qed.

Lemma Rle_Rinv_pos :
  forall x y : R,
  (0 < x)%R -> (x <= y)%R -> (/y <= /x)%R.
intros.
apply Rle_Rinv.
exact H.
apply Rlt_le_trans with x ; assumption.
exact H0.
Qed.

Lemma Rle_Rinv_neg :
  forall x y : R,
  (y < 0)%R -> (x <= y)%R -> (/y <= /x)%R.
intros.
apply Ropp_le_cancel.
repeat rewrite Ropp_inv_permute.
apply Rle_Rinv.
auto with real.
apply Rlt_le_trans with (Ropp y).
auto with real.
auto with real.
auto with real.
apply Rlt_dichotomy_converse.
left. exact H.
apply Rlt_dichotomy_converse.
left.
apply Rle_lt_trans with y ; assumption.
Qed.

Lemma Rmult_le_pos_pos :
  forall x y : R,
  (0 <= x)%R -> (0 <= y)%R -> (0 <= x * y)%R.
exact Rmult_le_pos.
Qed.

Lemma Rmult_le_pos_neg :
  forall x y : R,
  (0 <= x)%R -> (y <= 0)%R -> (x * y <= 0)%R.
intros.
rewrite <- (Rmult_0_r x).
apply Rmult_le_compat_l ; assumption.
Qed.

Lemma Rmult_le_neg_pos :
  forall x y : R,
  (x <= 0)%R -> (0 <= y)%R -> (x * y <= 0)%R.
intros.
rewrite <- (Rmult_0_l y).
apply Rmult_le_compat_r ; assumption.
Qed.

Lemma Rmult_le_neg_neg :
  forall x y : R,
  (x <= 0)%R -> (y <= 0)%R -> (0 <= x * y)%R.
intros.
rewrite <- (Rmult_0_r x).
apply Rmult_le_compat_neg_l ; assumption.
Qed.

Lemma Zpower_pos_powerRZ :
  forall n m,
  IZR (Zpower_pos n m) = powerRZ (IZR n) (Zpos m).
intros.
rewrite Zpower_pos_nat.
simpl.
induction (nat_of_P m).
apply refl_equal.
unfold Zpower_nat.
simpl.
rewrite mult_IZR.
apply Rmult_eq_compat_l.
exact IHn0.
Qed.

Lemma Zlt_0_Zpower_pos :
  forall a b, (0 < a)%Z ->
  (0 < Zpower_pos a b)%Z.
intros.
apply lt_IZR.
rewrite Zpower_pos_powerRZ.
apply powerRZ_lt.
apply (IZR_lt 0).
exact H.
Qed.

(*
Lemma Zlt_0_Zpower_pos_le :
  forall a b, (0 <= a)%Z -> (0 <= b)%Z ->
  (0 < Zpowe a b)%Z.
*)

Lemma Zlt_0_Zpower :
  forall a b, (0 < a)%Z -> (0 <= b)%Z ->
  (0 < Zpower a b)%Z.
intros a b H.
case b ; intros ; simpl.
exact (refl_equal _).
apply Zlt_0_Zpower_pos.
exact H.
elim H0.
exact (refl_equal _).
Qed.

Lemma Zpower_le_exp_compat :
  forall u a b,
  Zlt 0 u -> Zle a b ->
  (u^a <= u^b)%Z.
intros until 1.
unfold Zpower.
case b ; case a ; intros ;
  try discriminate ;
  try ( elim H0 ; split ; fail ).
apply (Zlt_le_succ 0).
exact (Zlt_0_Zpower u (Zpos p) H H0).
change (Zpower u (Zpos p) <= Zpower u (Zpos p0))%Z.
cutrewrite (Zpos p0 = Zpos p + (Zpos p0 - Zpos p))%Z.
assert (0 <= Zpos p0 - Zpos p)%Z.
apply Zle_minus_le_0.
exact H0.
assert (0 <= Zpos p)%Z.
apply Zlt_le_weak.
apply Zgt_lt.
apply Zgt_pos_0.
rewrite Zpower_exp ; [ idtac | exact (Zle_ge _ _ H2) | exact (Zle_ge _ _ H1) ].
pattern (u ^ Zpos p)%Z at 1 ; rewrite <- Zmult_1_r.
apply Zmult_le_compat_l.
apply (Zlt_le_succ 0).
exact (Zlt_0_Zpower _ _ H H1).
apply Zlt_le_weak.
apply (Zlt_0_Zpower _ _ H H2).
ring.
apply Zlt_le_weak.
apply Zlt_0_Zpower_pos.
exact H.
Qed.

Lemma Rabs_def1_le :
  forall x a,
  (x <= a)%R -> (-a <= x)%R ->
  (Rabs x <= a)%R.
intros.
case (Rcase_abs x) ; intros.
rewrite (Rabs_left _ r).
rewrite <- (Ropp_involutive a).
apply Ropp_le_contravar.
exact H0.
rewrite (Rabs_right _ r).
exact H.
Qed.

Lemma Rabs_def2_le :
  forall x a,
  (Rabs x <= a)%R ->
  (-a <= x <= a)%R.
intros x a H.
assert (0 <= a)%R.
apply Rle_trans with (2 := H).
apply Rabs_pos.
generalize H. clear H.
unfold Rabs.
case (Rcase_abs x) ; split.
rewrite <- (Ropp_involutive x).
apply Ropp_le_contravar.
exact H.
apply Rlt_le.
apply Rlt_le_trans with (1 := r).
exact H0.
generalize (Rge_le _ _ r).
clear r.
intro.
apply Rle_trans with (2 := H1).
rewrite <- Ropp_0.
apply Ropp_le_contravar.
exact H0.
exact H.
Qed.

Fixpoint P2R (p : positive) :=
  match p with
  | xH => 1%R
  | xO xH => 2%R
  | xO t => (2 * P2R t)%R
  | xI xH => 3%R
  | xI t => (1 + 2 * P2R t)%R
  end.

Definition Z2R n :=
  match n with
  | Zpos p => P2R p
  | Zneg p => Ropp (P2R p)
  | Z0 => R0
  end.

Lemma P2R_INR :
  forall n, P2R n = INR (nat_of_P n).
induction n ; simpl ; try (
  rewrite IHn ;
  rewrite <- (mult_INR 2) ;
  rewrite <- (nat_of_P_mult_morphism 2) ;
  change (2 * n)%positive with (xO n)).
(* xI *)
rewrite (Rplus_comm 1).
change (nat_of_P (xO n)) with (Pmult_nat n 2).
case n ; intros ; simpl ; try apply refl_equal.
case (Pmult_nat p 4) ; intros ; try apply refl_equal.
rewrite Rplus_0_l.
apply refl_equal.
apply Rplus_comm.
(* xO *)
case n ; intros ; apply refl_equal.
(* xH *)
apply refl_equal.
Qed.

Lemma Z2R_IZR :
  forall n, Z2R n = IZR n.
intro.
case n ; intros ; simpl.
apply refl_equal.
apply P2R_INR.
apply Ropp_eq_compat.
apply P2R_INR.
Qed.

Lemma plus_Z2R :
  forall m n, (Z2R (m + n) = Z2R m + Z2R n)%R.
intros.
repeat rewrite Z2R_IZR.
apply plus_IZR.
Qed.

Lemma minus_Z2R :
  forall m n, (Z2R (m - n) = Z2R m - Z2R n)%R.
intros.
repeat rewrite Z2R_IZR.
apply minus_IZR.
Qed.

Lemma mult_Z2R :
  forall m n, (Z2R (m * n) = Z2R m * Z2R n)%R.
intros.
repeat rewrite Z2R_IZR.
apply mult_IZR.
Qed.

Lemma le_Z2R :
  forall m n, (Z2R m <= Z2R n)%R -> (m <= n)%Z.
intros m n.
repeat rewrite Z2R_IZR.
apply le_IZR.
Qed.

Lemma Z2R_le :
  forall m n, (m <= n)%Z -> (Z2R m <= Z2R n)%R.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_le.
Qed.

Lemma lt_Z2R :
  forall m n, (Z2R m < Z2R n)%R -> (m < n)%Z.
intros m n.
repeat rewrite Z2R_IZR.
apply lt_IZR.
Qed.

Lemma Z2R_lt :
  forall m n, (m < n)%Z -> (Z2R m < Z2R n)%R.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_lt.
Qed.

Theorem derivable_bounded_pos:
  forall f f' : R -> R, forall a b : R,
  (forall c, (a <= c <= b)%R -> derivable_pt_lim f c (f' c) /\ (0 <= f' c)%R) ->
  forall c, (a <= c <= b)%R -> (f a <= f c <= f b)%R.
intros.
split.
(* left *)
destruct (proj1 H0) as [H1|H1].
apply Rplus_le_reg_r with (-f a)%R.
rewrite Rplus_opp_r.
fold (Rminus (f c) (f a)).
assert (forall d, (a <= d <= c)%R -> derivable_pt_lim f d (f' d)).
intros.
refine (proj1 (H _ _)).
split.
exact (proj1 H2).
apply Rle_trans with (1 := proj2 H2) (2 := proj2 H0).
destruct (MVT_cor2 _ _ _ _ H1 H2) as (d, (H3, (H4, H5))).
rewrite H3.
apply Rmult_le_pos_pos.
refine (proj2 (H _ _)).
split.
apply Rlt_le with (1 := H4).
apply Rle_trans with (2 := proj2 H0).
apply Rlt_le with (1 := H5).
rewrite <- (Rplus_opp_r a).
unfold Rminus.
apply Rplus_le_compat_r.
exact (proj1 H0).
apply Req_le.
apply f_equal.
exact H1.
(* right *)
destruct (proj2 H0) as [H1|H1].
apply Rplus_le_reg_r with (-f c)%R.
rewrite Rplus_opp_r.
fold (Rminus (f b) (f c)).
assert (forall d, (c <= d <= b)%R -> derivable_pt_lim f d (f' d)).
intros.
refine (proj1 (H _ _)).
split.
apply Rle_trans with (1 := proj1 H0) (2 := proj1 H2).
exact (proj2 H2).
destruct (MVT_cor2 _ _ _ _ H1 H2) as (d, (H3, (H4, H5))).
rewrite H3.
apply Rmult_le_pos_pos.
refine (proj2 (H _ _)).
split.
apply Rle_trans with (1 := proj1 H0).
apply Rlt_le with (1 := H4).
apply Rlt_le with (1 := H5).
rewrite <- (Rplus_opp_r c).
unfold Rminus.
apply Rplus_le_compat_r.
exact (proj2 H0).
apply Req_le.
apply f_equal.
exact H1.
Qed.

Theorem derivable_bounded_neg:
  forall f f' : R -> R, forall a b : R,
  (forall c, (a <= c <= b)%R -> derivable_pt_lim f c (f' c) /\ (f' c <= 0)%R) ->
  forall c, (a <= c <= b)%R -> (f b <= f c <= f a)%R.
intros.
cut ((opp_fct f) a <= (opp_fct f) c <= (opp_fct f) b)%R.
unfold opp_fct.
intros (H1, H2).
split ; apply Ropp_le_cancel ; assumption.
apply (derivable_bounded_pos (opp_fct f) (opp_fct f')) with (2 := H0).
intros.
unfold opp_fct at 2 3.
split.
apply derivable_pt_lim_opp.
exact (proj1 (H _ H1)).
rewrite <- Ropp_0.
apply Ropp_le_contravar.
exact (proj2 (H _ H1)).
Qed.

Theorem derivable_pt_lim_eq :
  forall f g,
 (forall x, f x = g x) ->
  forall x l,
  derivable_pt_lim f x l -> derivable_pt_lim g x l.
intros f g H x l.
unfold derivable_pt_lim.
intros.
destruct (H0 _ H1) as (delta, H2).
exists delta.
intros.
do 2 rewrite <- H.
apply H2 ; assumption.
Qed.

Theorem derivable_pt_lim_eq_close :
  forall f g x l delta, (0 < delta)%R ->
 (forall h, (Rabs h < delta)%R -> f (x + h)%R = g (x + h)%R) ->
  derivable_pt_lim f x l -> derivable_pt_lim g x l.
intros f g x l delta1 Hd Heq Hf eps Heps.
destruct (Hf eps Heps) as (delta2, H0).
clear Hf.
assert (0 < Rmin delta1 delta2)%R.
apply Rmin_pos.
exact Hd.
exact (cond_pos delta2).
exists (mkposreal (Rmin delta1 delta2) H).
intros.
rewrite <- Heq.
pattern x at 2 ; rewrite <- Rplus_0_r.
rewrite <- Heq.
rewrite Rplus_0_r.
apply H0.
exact H1.
apply Rlt_le_trans with (1 := H2).
simpl.
apply Rmin_r.
rewrite Rabs_R0.
exact Hd.
apply Rlt_le_trans with (1 := H2).
simpl.
apply Rmin_l.
Qed.

Definition locally_true x (P : R -> Prop) :=
  exists delta, (0 < delta)%R /\
  forall h, (Rabs h < delta)%R -> P (x + h)%R.

Theorem continuity_pt_lt :
  forall f x y,
  (f x < y)%R ->
  continuity_pt f x ->
  locally_true x (fun u => (f u < y)%R).
intros.
assert (0 < y - f x)%R.
apply Rplus_lt_reg_r with (f x).
rewrite Rplus_0_r.
replace (f x + (y - f x))%R with y. 2: ring.
exact H.
destruct (H0 _ H1) as (delta, (Hdelta, H2)).
clear H0.
exists delta.
split.
exact Hdelta.
intros.
case (Req_dec h 0) ; intro H3.
rewrite H3.
rewrite Rplus_0_r.
exact H.
generalize (H2 (x + h)%R). clear H2.
unfold R_met, R_dist, D_x, no_cond.
simpl.
intro.
apply Rplus_lt_reg_r with (- f x)%R.
do 2 rewrite (Rplus_comm (- f x)).
apply Rle_lt_trans with (1 := RRle_abs (f (x + h) - f x)%R).
apply H2.
assert (x + h - x = h)%R. ring.
split.
split.
exact I.
intro H5.
elim H3.
rewrite <- H4.
rewrite <- H5.
exact (Rplus_opp_r _).
rewrite H4.
exact H0.
Qed.

Theorem continuity_pt_gt :
  forall f x y,
  (y < f x)%R ->
  continuity_pt f x ->
  locally_true x (fun u => (y < f u)%R).
intros.
generalize (Ropp_lt_contravar _ _ H).
clear H. intro H.
generalize (continuity_pt_opp _ _ H0).
clear H0. intro H0.
destruct (continuity_pt_lt (opp_fct f) _ _ H H0) as (delta, (Hdelta, H1)).
exists delta.
split.
exact Hdelta.
intros.
apply Ropp_lt_cancel.
exact (H1 _ H2).
Qed.

Theorem continuity_pt_ne :
  forall f x y,
  f x <> y ->
  continuity_pt f x ->
  locally_true x (fun u => f u <> y).
intros.
destruct (Rdichotomy _ _ H) as [H1|H1].
destruct (continuity_pt_lt _ _ _ H1 H0) as (delta, (Hdelta, H2)).
exists delta.
split.
exact Hdelta.
intros.
apply Rlt_not_eq.
exact (H2 _ H3).
destruct (continuity_pt_gt _ _ _ H1 H0) as (delta, (Hdelta, H2)).
exists delta.
split.
exact Hdelta.
intros.
apply Rgt_not_eq.
exact (H2 _ H3).
Qed.
