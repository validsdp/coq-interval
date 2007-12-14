Require Import Bool.
Require Import Reals.
Require Import missing.
Require Import xreal.
Require Import definitions.
Require Import generic.
Require Import generic_proof.
Require Import float_sig.
Require Import interval.

Inductive f_interval (A : Set) : Set :=
  | Inan : f_interval A
  | Ibnd (l u : A) : f_interval A.

Implicit Arguments Inan [A].
Implicit Arguments Ibnd [A].

Module FloatInterval (F : FloatOps with Definition even_radix := true).

Definition type := f_interval F.type.
Definition bound_type := F.type.
Definition precision := F.precision.

Definition convert_bound x := FtoX (F.toF x).
Definition convert xi :=
  match xi with
  | Inan => interval.Inan
  | Ibnd l u => interval.Ibnd (convert_bound l) (convert_bound u)
  end.

Definition nai := @Inan F.type.
Definition bnd := @Ibnd F.type.

Lemma bnd_correct :
  forall l u,
  convert (bnd l u) = interval.Ibnd (convert_bound l) (convert_bound u).
split.
Qed.

Lemma nai_correct :
  convert nai = interval.Inan.
split.
Qed.

Definition bounded xi :=
  match xi with
  | Ibnd xl xu => F.real xl && F.real xu
  | _ => false
  end.

Definition lower_bounded xi :=
  match xi with
  | Ibnd xl _ => F.real xl
  | _ => false
  end.

Definition upper_bounded xi :=
  match xi with
  | Ibnd _ xu => F.real xu
  | _ => false
  end.

Definition subset xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    match F.cmp xl yl with
    | Xund => negb (F.real yl)
    | Xlt => false
    | _ => true
    end &&
    match F.cmp xu yu with
    | Xund => negb (F.real yu)
    | Xgt => false
    | _ => true
    end
  | _, Inan => true
  | _, _ => false
  end.

Definition join xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.min xl yl) (F.max xu yu)
  | _, _ => Inan
  end.

Definition meet xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    let l :=
      match F.real xl, F.real yl with
      | false, false => F.nan
      | false, true => yl
      | true, false => xl
      | true, true => F.max xl yl
      end in
    let u :=
      match F.real xu, F.real yu with
      | false, false => F.nan
      | false, true => yu
      | true, false => xu
      | true, true => F.min xu yu
      end in
    Ibnd l u
  | _, _ => Inan
  end.

Definition lower_extent xi :=
  match xi with
  | Ibnd _ xu => Ibnd F.nan xu
  | _ => Inan
  end.

Definition upper_extent xi :=
  match xi with
  | Ibnd xl _ => Ibnd xl F.nan
  | _ => Inan
  end.

Definition whole := Ibnd F.nan F.nan.

Definition lower xi :=
  match xi with
  | Ibnd xl _ => xl
  | _ => F.nan
  end.

Definition upper xi :=
  match xi with
  | Ibnd _ xu => xu
  | _ => F.nan
  end.

Definition fromZ n := let f := F.fromZ n in Ibnd f f.

Definition midpoint xi :=
  match xi with
  | Inan => F.nan
  | Ibnd xl xu =>
    match F.cmp xl F.zero, F.cmp xu F.zero with
    | Xund, Xund => F.zero
    | Xeq, Xeq => F.zero
    | Xlt, Xund => F.zero
    | Xund, Xgt => F.zero
    | Xeq, Xund => F.fromZ 1%Z
    | Xund, Xeq => F.fromZ (-1)%Z
    | Xgt, Xund => F.scale xl (F.ZtoS 1%Z)
    | Xund, Xlt => F.scale xu (F.ZtoS 1%Z)
    | _, _ => F.scale2 (F.add_exact xl xu) (F.ZtoS (-1)%Z)
    end
  end.

Definition extension f fi := forall b x,
  contains (convert b) x -> contains (convert (fi b)) (f x).

Definition extension_2 f fi := forall bx by x y,
  contains (convert bx) x ->
  contains (convert by) y ->
  contains (convert (fi bx by)) (f x y).

Definition sign_large_ xl xu :=
  match F.cmp xl F.zero, F.cmp xu F.zero with
  | Xeq, Xeq => Xeq
  | _, Xlt => Xlt
  | _, Xeq => Xlt
  | Xgt, _ => Xgt
  | Xeq, _ => Xgt
  | _, _ => Xund
  end.

Definition sign_large xi :=
  match xi with
  | Ibnd xl xu => sign_large_ xl xu
  | Inan => Xund
  end.

Definition sign_strict xl xu :=
  match F.cmp xl F.zero, F.cmp xu F.zero with
  | Xeq, Xeq => Xeq
  | _, Xlt => Xlt
  | Xgt, _ => Xgt
  | _, _ => Xund
  end.

Definition neg xi :=
  match xi with
  | Ibnd xl xu => Ibnd (F.neg xu) (F.neg xl)
  | Inan => Inan
  end.

Definition abs xi :=
  match xi with
  | Ibnd xl xu =>
    match sign_large_ xl xu with
    | Xgt => xi
    | Xeq => Ibnd F.zero F.zero
    | Xlt => Ibnd (F.neg xu) (F.neg xl)
    | Xund => Ibnd F.zero (F.max (F.neg xl) xu)
    end
  | Inan => Inan
  end.

Definition scale xi d :=
  match xi with
  | Ibnd xl xu => Ibnd (F.scale xl d) (F.scale xu d)
  | Inan => Inan
  end.

Definition scale2 xi d :=
  match xi with
  | Ibnd xl xu => Ibnd (F.scale2 xl d) (F.scale2 xu d)
  | Inan => Inan
  end.

Definition sqrt prec xi :=
  match xi with
  | Ibnd xl xu =>
    match F.cmp xl F.zero with
    | Xeq => Ibnd F.zero (F.sqrt rnd_UP prec xu)
    | Xgt => Ibnd (F.sqrt rnd_DN prec xl) (F.sqrt rnd_UP prec xu)
    | _ => Inan
    end
  | Inan => Inan
  end.

Definition add prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.add rnd_DN prec xl yl) (F.add rnd_UP prec xu yu)
  | _, _ => Inan
  end.

Definition sub prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.sub rnd_DN prec xl yu) (F.sub rnd_UP prec xu yl)
  | _, _ => Inan
  end.

Definition mul_mixed prec xi y :=
  match xi with
  | Ibnd xl xu =>
    match F.cmp y F.zero with
    | Xlt => Ibnd (F.mul rnd_DN prec xu y) (F.mul rnd_UP prec xl y)
    | Xeq => Ibnd F.zero F.zero
    | Xgt => Ibnd (F.mul rnd_DN prec xl y) (F.mul rnd_UP prec xu y)
    | Xund => Inan
    end
  | Inan => Inan
  end.

Definition div_mixed_r prec xi y :=
  match xi with
  | Ibnd xl xu =>
    match F.cmp y F.zero with
    | Xlt => Ibnd (F.div rnd_DN prec xu y) (F.div rnd_UP prec xl y)
    | Xgt => Ibnd (F.div rnd_DN prec xl y) (F.div rnd_UP prec xu y)
    | _ => Inan
    end
  | Inan => Inan
  end.

Definition sqr prec xi :=
  match xi with
  | Ibnd xl xu =>
    match sign_large_ xl xu with
    | Xund =>
      let xm := F.max (F.abs xl) (F.abs xu) in
      Ibnd F.zero (F.mul rnd_UP prec xm xm)
    | Xeq => Ibnd F.zero F.zero
    | Xlt => Ibnd (F.mul rnd_DN prec xu xu) (F.mul rnd_UP prec xl xl)
    | Xgt => Ibnd (F.mul rnd_DN prec xl xl) (F.mul rnd_UP prec xu xu)
    end
  | _ => Inan
  end.

Definition mul prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    match sign_large_ xl xu, sign_large_ yl yu with
    | Xeq, _ => Ibnd F.zero F.zero
    | _, Xeq => Ibnd F.zero F.zero
    | Xgt, Xgt => Ibnd (F.mul rnd_DN prec xl yl) (F.mul rnd_UP prec xu yu)
    | Xlt, Xlt => Ibnd (F.mul rnd_DN prec xu yu) (F.mul rnd_UP prec xl yl)
    | Xgt, Xlt => Ibnd (F.mul rnd_DN prec xu yl) (F.mul rnd_UP prec xl yu)
    | Xlt, Xgt => Ibnd (F.mul rnd_DN prec xl yu) (F.mul rnd_UP prec xu yl)
    | Xgt, Xund => Ibnd (F.mul rnd_DN prec xu yl) (F.mul rnd_UP prec xu yu)
    | Xlt, Xund => Ibnd (F.mul rnd_DN prec xl yu) (F.mul rnd_UP prec xl yl)
    | Xund, Xgt => Ibnd (F.mul rnd_DN prec xl yu) (F.mul rnd_UP prec xu yu)
    | Xund, Xlt => Ibnd (F.mul rnd_DN prec xu yl) (F.mul rnd_UP prec xl yl)
    | Xund, Xund => Ibnd (F.min (F.mul rnd_DN prec xl yu) (F.mul rnd_DN prec xu yl))
                         (F.max (F.mul rnd_UP prec xl yl) (F.mul rnd_UP prec xu yu))
    end
  | _, _ => Inan
  end.

Definition Fdivz mode prec x y :=
  if F.real y then F.div mode prec x y else F.zero.

Definition inv prec xi :=
  match xi with
  | Ibnd xl xu =>
    match sign_strict xl xu with
    | Xund => Inan
    | Xeq => Inan
    | _ => let one := F.fromZ 1 in
      Ibnd (Fdivz rnd_DN prec one xu) (Fdivz rnd_UP prec one xl)
    end
  | _ => Inan
  end.

Definition div prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    match sign_strict xl xu, sign_strict yl yu with
    | _, Xund => Inan
    | _, Xeq => Inan
    | Xeq, _ => Ibnd F.zero F.zero
    | Xgt, Xgt => Ibnd (Fdivz rnd_DN prec xl yu) (F.div rnd_UP prec xu yl)
    | Xlt, Xlt => Ibnd (Fdivz rnd_DN prec xu yl) (F.div rnd_UP prec xl yu)
    | Xgt, Xlt => Ibnd (F.div rnd_DN prec xu yu) (Fdivz rnd_UP prec xl yl)
    | Xlt, Xgt => Ibnd (F.div rnd_DN prec xl yl) (Fdivz rnd_UP prec xu yu)
    | Xund, Xgt => Ibnd (F.div rnd_DN prec xl yl) (F.div rnd_UP prec xu yl)
    | Xund, Xlt => Ibnd (F.div rnd_DN prec xu yu) (F.div rnd_UP prec xl yu)
    end
  | _, _ => Inan
  end.

Ltac convert_clean :=
  repeat
  match goal with
  | H: context [FtoX (F.toF ?v)] |- _
    => change (FtoX (F.toF v)) with (convert_bound v) in H
  | |- context [FtoX (F.toF ?v)]
    => change (FtoX (F.toF v)) with (convert_bound v)
  end.

Ltac xreal_tac v :=
  convert_clean ;
  let X := fresh "X" in
  case_eq (convert_bound v) ;
  [ intros X ; try exact I
  | let r := fresh "r" in
    intros r X ; try rewrite X in * ].

Ltac xreal_tac2 :=
  convert_clean ;
  match goal with
  | H: convert_bound ?v = Xreal _ |- context [convert_bound ?v] =>
    rewrite H
  | |- context [convert_bound ?v] => xreal_tac v
  end.

Ltac bound_tac :=
  try rewrite round_correct_real ;
  match goal with
  | |- (round_real ?r rnd_DN ?p ?v <= ?w)%R =>
    apply Rle_trans with v ;
    [ apply (correctly_rounded_lower r p) ;
      rewrite <- round_correct_real ;
      apply round_correctly
    | idtac ]
  | |- (?w <= round_real ?r rnd_UP ?p ?v)%R =>
    apply Rle_trans with v ;
    [ idtac
    | apply (correctly_rounded_upper r p) ;
      rewrite <- round_correct_real ;
      apply round_correctly ]
  end.

Lemma real_correct :
  forall (A : Set) x (y1 y2 : A),
  (if F.real x then y1 else y2) = match convert_bound x with Xnan => y2 | _ => y1 end.
intros.
generalize (F.real_correct x).
unfold convert_bound.
case (F.toF x) ; intros ; rewrite H ; apply refl_equal.
Qed.

Lemma subset_correct :
  forall xi yi : type,
  subset xi yi = true -> interval.subset (convert xi) (convert yi).
intros xi yi.
case xi ; case yi ; try (simpl ; intros ; try exact I ; discriminate).
intros yl yu xl xu H.
destruct (andb_prop _ _ H) as (H1, H2).
split.
(* lower bound *)
generalize H1. clear.
repeat rewrite F.cmp_correct.
repeat rewrite Fcmp_correct.
unfold le_lower, le_upper, convert_bound.
case (FtoX (F.toF xl)) ; simpl.
unfold negb. rewrite real_correct.
intros. now xreal_tac2.
intros xrl.
xreal_tac2.
split.
generalize (Rcompare_correct xrl r).
case (Rcompare xrl r) ; intros ; simpl ; now auto with real.
(* upper bound *)
generalize H2. clear.
repeat rewrite F.cmp_correct.
repeat rewrite Fcmp_correct.
unfold le_upper, convert_bound.
case (FtoX (F.toF xu)) ; simpl.
unfold negb. rewrite real_correct.
intros. now xreal_tac2.
intros xru.
xreal_tac2.
split.
generalize (Rcompare_correct xru r).
case (Rcompare xru r) ; intros ; now auto with real.
Qed.

Lemma sign_large_correct :
  forall xl xu x,
  contains (convert (Ibnd xl xu)) (Xreal x) ->
  match sign_large_ xl xu with
  | Xeq => x = R0 /\ FtoX (F.toF xl) = Xreal R0 /\ FtoX (F.toF xu) = Xreal R0
  | Xlt => (x <= 0)%R /\ (match FtoX (F.toF xl) with Xreal rl => (rl <= 0)%R | _=> True end) /\ (exists ru, FtoX (F.toF xu) = Xreal ru /\ (ru <= 0)%R)
  | Xgt => (0 <= x)%R /\ (match FtoX (F.toF xu) with Xreal ru => (0 <= ru)%R | _=> True end) /\ (exists rl, FtoX (F.toF xl) = Xreal rl /\ (0 <= rl)%R)
  | Xund =>
    match FtoX (F.toF xl) with Xreal rl => (rl <= 0)%R | _=> True end /\
    match FtoX (F.toF xu) with Xreal ru => (0 <= ru)%R | _=> True end
  end.
intros xl xu x (Hxl, Hxu).
unfold sign_large_.
do 2 rewrite F.cmp_correct.
rewrite F.zero_correct.
generalize Hxl Hxu.
clear.
unfold convert_bound.
case (F.toF xl) ; [ idtac | idtac | intros sl ml el ; case sl ] ;
  ( case (F.toF xu) ; [ idtac | idtac | intros su mu eu ; case su ] ) ; simpl ;
  intros ; repeat split ; try exact I ; try assumption ;
  try refl_exists ; try apply Rle_refl ;
  try ( try apply Rle_trans with (2 := Hxl) ; apply Rlt_le ; apply FtoR_Rpos ) ;
  try ( try apply Rle_trans with (1 := Hxu) ; apply Rlt_le ; apply FtoR_Rneg ).
apply Rle_antisym ; assumption.
apply Rle_trans with x ; assumption.
apply Rle_trans with (1 := Hxl).
apply Rle_trans with (1 := Hxu).
apply Rlt_le.
apply FtoR_Rneg.
Qed.

Lemma sign_strict_correct :
  forall xl xu x,
  contains (convert (Ibnd xl xu)) (Xreal x) ->
  match sign_strict xl xu with
  | Xeq => x = R0 /\ FtoX (F.toF xl) = Xreal R0 /\ FtoX (F.toF xu) = Xreal R0
  | Xlt => (x < 0)%R /\ (match FtoX (F.toF xl) with Xreal rl => (rl < 0)%R | _=> True end) /\ (exists ru, FtoX (F.toF xu) = Xreal ru /\ (ru < 0)%R)
  | Xgt => (0 < x)%R /\ (match FtoX (F.toF xu) with Xreal ru => (0 < ru)%R | _=> True end) /\ (exists rl, FtoX (F.toF xl) = Xreal rl /\ (0 < rl)%R)
  | Xund =>
    match FtoX (F.toF xl) with Xreal rl => (rl <= 0)%R | _=> True end /\
    match FtoX (F.toF xu) with Xreal ru => (0 <= ru)%R | _=> True end
  end.
intros xl xu x (Hxl, Hxu).
unfold sign_strict.
do 2 rewrite F.cmp_correct.
rewrite F.zero_correct.
generalize Hxl Hxu.
clear.
unfold convert_bound.
case_eq (F.toF xl) ; [ idtac | idtac | intros sl ml el ; case sl ] ;
  ( case_eq (F.toF xu) ; [ idtac | idtac | intros su mu eu ; case su ] ) ; simpl ;
  intros ; repeat split ; try exact I ; try assumption ;
  try refl_exists ; try apply Rle_refl ;
  try ( try apply Rlt_le_trans with (2 := Hxl) ; try apply Rlt_le ; apply FtoR_Rpos ) ;
  try ( try apply Rle_lt_trans with (1 := Hxu) ; try apply Rlt_le ; apply FtoR_Rneg ).
apply Rle_antisym ; assumption.
apply Rle_lt_trans with (1 := Hxl).
apply Rle_lt_trans with (1 := Hxu).
apply FtoR_Rneg.
apply Rlt_le_trans with (2 := Hxu).
apply Rlt_le_trans with (2 := Hxl).
apply FtoR_Rpos.
apply Rle_lt_trans with (1 := Hxl).
apply Rle_lt_trans with (1 := Hxu).
apply FtoR_Rneg.
Qed.

Theorem midpoint_correct :
  forall xi,
  (exists x, contains (convert xi) (Xreal x)) ->
  contains (convert xi) (convert_bound (midpoint xi)).
intros [ | xl xu].
intros _.
exact I.
intros (x, (Hxl, Hxu)).
assert (Hr: (1 <= P2R (F.radix * 1))%R).
rewrite P2R_INR.
apply (le_INR 1).
apply lt_le_S.
apply lt_O_nat_of_P.
(* . *)
simpl.
repeat rewrite F.cmp_correct.
repeat rewrite Fcmp_correct.
xreal_tac xl ; xreal_tac xu ; simpl ;
  change (convert_bound F.zero) with (FtoX (F.toF F.zero)) ;
  rewrite F.zero_correct ; simpl.
split ; split.
(* infinite lower *)
generalize (Rcompare_correct r 0).
case (Rcompare r 0) ; intro H ; unfold convert_bound.
rewrite H.
rewrite F.fromZ_correct.
split.
exact I.
apply (Z2R_le (-1) 0).
intro H0.
discriminate H0.
rewrite F.scale_correct.
rewrite Fscale_correct.
unfold convert_bound in X0.
rewrite X0.
simpl.
split.
exact I.
pattern r at 2 ; rewrite <- Rmult_1_r.
apply Rmult_le_compat_neg_l.
exact (Rlt_le _ _ H).
exact Hr.
rewrite F.zero_correct.
split ; auto with real.
(* infinite upper *)
generalize (Rcompare_correct r 0).
case (Rcompare r 0) ; intro H ; unfold convert_bound.
rewrite H.
rewrite F.fromZ_correct.
split ; auto with real.
rewrite F.zero_correct.
split ; auto with real.
rewrite F.scale_correct.
rewrite Fscale_correct.
unfold convert_bound in X.
rewrite X.
simpl.
split.
pattern r at 1 ; rewrite <- Rmult_1_r.
apply Rmult_le_compat_l.
exact (Rlt_le _ _ H).
exact Hr.
exact I.
(* finite bounds *)
assert (
  match FtoX (F.toF (F.scale2 (F.add_exact xl xu) (F.ZtoS (-1)))) with
  | Xnan => False
  | Xreal x0 => (r <= x0 <= r0)%R
  end).
rewrite F.scale2_correct. 2: apply refl_equal.
rewrite Fscale2_correct. 2: apply F.even_radix_correct.
rewrite F.add_exact_correct.
rewrite Fadd_exact_correct.
unfold convert_bound in *.
rewrite X, X0.
simpl.
pattern r at 1 ; rewrite <- eps2.
pattern r0 at 3 ; rewrite <- eps2.
rewrite Rmult_plus_distr_r.
split.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
auto with real.
eapply Rle_trans ; eassumption.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
auto with real.
eapply Rle_trans ; eassumption.
(* finite bounds 2 *)
generalize (Rcompare_correct r 0).
case (Rcompare r 0) ; intro H0 ;
  generalize (Rcompare_correct r0 0) ;
  case (Rcompare r0 0) ; intro H1 ;
  try exact H.
unfold convert_bound.
rewrite F.zero_correct.
simpl.
rewrite H0, H1.
split ; apply Rle_refl.
Qed.

Theorem neg_correct :
  extension Xneg neg.
intros [ | xl xu] [ | x] ; simpl ; trivial.
intros (Hxl, Hxu).
unfold convert_bound.
split ; rewrite F.neg_correct ; rewrite Fneg_correct ;
  unfold Xneg ; [ xreal_tac xu | xreal_tac xl ] ;
  apply Ropp_le_contravar ; assumption.
Qed.

Theorem abs_correct :
  extension Xabs abs.
intros [ | xl xu] [ | x] Hx ; trivial ; [ elim Hx | idtac ].
simpl.
generalize (sign_large_correct _ _ _ Hx).
case (sign_large_ xl xu) ; intros.
(* zero *)
rewrite (proj1 H).
rewrite Rabs_R0.
simpl.
unfold convert_bound.
rewrite F.zero_correct.
split ; exact (Rle_refl R0).
(* negative *)
rewrite (Rabs_left1 _ (proj1 H)).
exact (neg_correct _ _ Hx).
(* positive *)
rewrite (Rabs_right _ (Rle_ge _ _ (proj1 H))).
exact Hx.
(* both *)
clear H.
simpl.
unfold convert_bound.
rewrite F.zero_correct.
split.
exact (Rabs_pos x).
(* - upper *)
rewrite F.max_correct.
rewrite Fmax_correct.
rewrite F.neg_correct.
rewrite Fneg_correct.
unfold contains, convert, convert_bound in Hx.
destruct Hx as (Hxl, Hxu).
do 2 xreal_tac2.
simpl.
apply <- Rmax_Rle.
unfold Rabs.
destruct (Rcase_abs x) as [H|H].
left.
apply Ropp_le_contravar.
exact Hxl.
right.
exact Hxu.
Qed.

Theorem add_correct :
  forall prec,
  extension_2 Xadd (add prec).
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ; trivial.
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold convert_bound.
split ;
  rewrite F.add_correct ; rewrite Fadd_correct ;
  do 2 xreal_tac2 ; unfold Xadd ; bound_tac ;
  apply Rplus_le_compat ; assumption.
Qed.

Theorem sub_correct :
  forall prec,
  extension_2 Xsub (sub prec).
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ; trivial.
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold convert_bound.
split ;
  rewrite F.sub_correct ; rewrite Fsub_correct ;
  do 2 xreal_tac2 ; unfold Xsub ; bound_tac ;
  unfold Rminus ; apply Rplus_le_compat ;
  try apply Ropp_le_contravar ; assumption.
Qed.

(*
Theorem mul_mixed_correct :
  forall prec xi yf x,
  bnd xi x ->
  bnd (mul_mixed prec xi yf) (Xmul x (FtoX (F.toF yf))).
intros prec [ | xl xu] yf [x | ] ; trivial.
2: intro H ; elim H.
intros (Hxl, Hxu).
unfold mul_mixed.
rewrite F.cmp_correct.
rewrite F.zero_correct.
case_eq (F.toF yf) ; simpl.
trivial.
intros _.
rewrite F.zero_correct.
simpl.
rewrite Rmult_0_r.
split ; apply Rle_refl.
intros s m e.
case s ; simpl ; intros Hy ;
  do 2 rewrite F.mul_correct ;
  do 2 rewrite Fmul_correct ;
  rewrite Hy ; simpl ; clear Hy ;
  [ (* y negative *)
    split ; xreal_tac2 ;
    unfold Xmul ; bound_tac ;
    ( apply Rmult_le_compat_neg_r ;
      [ apply Rlt_le ; apply FtoR_Rneg
      | assumption ] )
  | (* y positive *)
    split ; xreal_tac2 ;
    unfold Xmul ; bound_tac ;
    ( apply Rmult_le_compat_r ;
      [ apply Rlt_le ; apply FtoR_Rpos
      | assumption ] ) ].
Qed.
*)

Lemma is_zero_float :
  forall r s m e,
  is_zero (FtoR r s m e) = false.
intros.
generalize (is_zero_correct (FtoR r s m e)).
case (is_zero (FtoR r s m e)) ; [ idtac | trivial ].
case s ; simpl ; intros.
elim Rlt_not_eq with (2 := H).
apply FtoR_Rneg.
elim Rgt_not_eq with (2 := H).
unfold Rgt.
apply FtoR_Rpos.
Qed.

Lemma is_positive_float :
  forall r s m e,
  is_positive (FtoR r s m e) = negb s.
intros.
generalize (is_positive_correct (FtoR r s m e)).
case (is_positive (FtoR r s m e)) ; case s ; simpl ; trivial ; intro H.
elim Rlt_not_ge with (1 := H).
left.
unfold Rgt.
apply FtoR_Rneg.
elim Rgt_not_le with (2 := H).
unfold Rgt.
apply FtoR_Rpos.
Qed.

Lemma is_negative_float :
  forall r s m e,
  is_negative (FtoR r s m e) = s.
intros.
generalize (is_negative_correct (FtoR r s m e)).
case (is_negative (FtoR r s m e)) ; case s ; simpl ; trivial ; intro H.
elim Rlt_not_ge with (1 := H).
left.
unfold Rgt.
apply FtoR_Rpos.
elim Rgt_not_le with (2 := H).
unfold Rgt.
apply FtoR_Rneg.
Qed.

(*
Theorem div_mixed_r_correct :
  forall prec xi yf x,
  bnd xi x ->
  bnd (div_mixed_r prec xi yf) (Xdiv x (FtoX (F.toF yf))).
intros prec [ | xl xu] yf [x | ] ; trivial.
2: intro H ; elim H.
intros (Hxl, Hxu).
unfold div_mixed_r.
rewrite F.cmp_correct.
rewrite F.zero_correct.
case_eq (F.toF yf) ; simpl ; trivial.
intros s m e.
rewrite is_zero_float.
case s ; unfold bnd ; intros Hy ;
  do 2 rewrite F.div_correct ;
  do 2 rewrite Fdiv_correct with (1 := F.radix_correct) ;
  rewrite Hy ; unfold FtoX at 3 6, Xdiv ;
  [ (* y negative *)
    rewrite (is_zero_float F.radix true m e) ;
    split ; xreal_tac2 ; bound_tac ;
    unfold Rdiv ; simpl ;
    ( apply Rmult_le_compat_neg_r ;
      [ apply Rlt_le ;
        apply Rinv_lt_0_compat ;
        apply FtoR_Rneg
      | assumption ] )
  | (* y positive *)
    rewrite (is_zero_float F.radix false m e) ;
    split ; xreal_tac2 ; bound_tac ;
    unfold Rdiv ; simpl ;
    ( apply Rmult_le_compat_r ;
      [ apply Rlt_le ;
        apply Rinv_0_lt_compat ;
        apply FtoR_Rpos
      | assumption ] ) ].
Qed.
*)

Theorem sqrt_correct :
  forall prec, extension Xsqrt (sqrt prec).
intros prec [ | xl xu] [ | x] ; simpl ; trivial.
intro.
elim H.
intros (Hxl, Hxu).
rewrite F.cmp_correct.
rewrite Fcmp_correct.
rewrite F.zero_correct.
generalize Hxl. clear Hxl.
unfold convert_bound.
case_eq (FtoX (F.toF xl)) ; [ split | idtac ].
intros rl Hrl Hxl.
simpl.
generalize (is_negative_correct x).
case (is_negative x) ; intro H.
rewrite Rcompare_correct_lt.
exact I.
apply Rle_lt_trans with (1 := Hxl) (2 := H).
generalize (Rcompare_correct rl 0).
unfold contains, convert, convert_bound.
case (Rcompare rl 0) ; intros ; simpl ; try exact I ;
  repeat ( rewrite F.sqrt_correct ; rewrite Fsqrt_correct ).
(* xl zero *)
rewrite F.zero_correct.
simpl.
split.
apply sqrt_positivity.
exact H.
unfold convert_bound in Hxu.
xreal_tac xu.
simpl.
case_eq (is_negative r).
intros _.
exact I.
intros H1.
bound_tac.
apply sqrt_le_1.
exact H.
apply Rle_trans with (1 := H) (2 := Hxu).
exact Hxu.
(* xl positive *)
rewrite Hrl.
split.
simpl.
unfold is_negative, Rsign.
rewrite (Rcompare_correct_gt _ _ H0).
bound_tac.
apply sqrt_le_1.
exact (Rlt_le _ _ H0).
exact H.
exact Hxl.
unfold convert_bound in Hxu.
xreal_tac xu.
simpl.
unfold is_negative, Rsign.
rewrite Rcompare_correct_gt.
bound_tac.
apply sqrt_le_1.
exact H.
apply Rle_trans with (1 := H) (2 := Hxu).
exact Hxu.
apply Rlt_le_trans with (1 := H0).
apply Rle_trans with (1 := Hxl) (2 := Hxu).
Qed.

Lemma Xmin_swap_nan : forall x, Xmin x Xnan = Xnan.
intros x.
case x ; intros ; apply refl_equal.
Qed.

Lemma Xmax_swap_nan : forall x, Xmax x Xnan = Xnan.
intros x.
case x ; intros ; apply refl_equal.
Qed.

Ltac clear_complex_aux :=
  match goal with
  | H: Rle _ _ |- _ =>
    generalize H ; clear H ; try clear_complex_aux
  | H: (Rle _ _) /\ _ |- _ =>
    generalize (proj1 H) ;
    destruct H as (_, H) ;
    try clear_complex_aux
  | H: Rlt _ _ |- _ =>
    generalize H ; clear H ; try clear_complex_aux
  | H: (Rlt _ _) /\ _ |- _ =>
    generalize (proj1 H) ;
    destruct H as (_, H) ;
    try clear_complex_aux
  | H: ex (fun r : R => _ /\ _) |- _ =>
    let a := fresh "a" in
    let K := fresh in
    destruct H as (a, (K, H)) ;
    injection K ; clear K ; intro K ;
    rewrite <- K in H ;
    clear K a ; try clear_complex_aux
  | H: _ /\ _ |- _ =>
    destruct H as (_, H) ;
    try clear_complex_aux
  | H: _ |- _ =>
    clear H ; try clear_complex_aux
  end.

Ltac clear_complex :=
  clear_complex_aux ; clear ; intros.

Hint Local Resolve Rle_trans : mulauto.
Hint Local Resolve Rmult_le_compat_l : mulauto.
Hint Local Resolve Rmult_le_compat_r : mulauto.
Hint Local Resolve Rmult_le_compat_neg_l : mulauto.
Hint Local Resolve Rmult_le_compat_neg_r : mulauto.

Theorem mul_correct :
  forall prec,
  extension_2 Xmul (mul prec).
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ;
  try ( intros ; exact I ) ;
  try ( intros H1 H2 ; try elim H1 ; elim H2 ; fail ).
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold bnd, contains, convert, convert_bound.
(* case study on sign of xi *)
generalize (sign_large_correct xl xu x (conj Hxl Hxu)).
case (sign_large_ xl xu) ; intros Hx0 ; simpl in Hx0 ;
  (* case study on sign of yi *)
  try ( generalize (sign_large_correct yl yu y (conj Hyl Hyu)) ;
        case (sign_large_ yl yu) ; intros Hy0 ; simpl in Hy0 ) ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F.zero_correct ; simpl ;
        try ( rewrite (proj1 Hx0) ; rewrite Rmult_0_l ) ;
        try ( rewrite (proj1 Hy0) ; rewrite Rmult_0_r ) ;
        split ; apply Rle_refl ) ;
  (* remove rounding operators *)
  try ( split ; rewrite F.mul_correct ; rewrite Fmul_correct ;
        do 2 xreal_tac2 ; unfold Xmul ; bound_tac ;
        clear_complex ) ;
  (* solve by transivity *)
  try ( eauto with mulauto ; fail ).
(* multiplication around zero *)
rewrite F.min_correct.
rewrite Fmin_correct.
rewrite F.max_correct.
rewrite Fmax_correct.
do 4 rewrite F.mul_correct.
do 4 rewrite Fmul_correct.
do 4 xreal_tac2 ;
  unfold Xmul ;
  try rewrite Xmin_swap_nan ;
  try rewrite Xmax_swap_nan ;
  try ( split ; simpl ; exact I ).
do 4 rewrite round_correct_real.
simpl.
clear_complex.
destruct (Rle_or_lt x 0) as [Hx|Hx].
split ;
  [ apply <- Rmin_Rle | apply <- Rmax_Rle ] ;
  left ; bound_tac ;
  eauto with mulauto.
generalize (Rlt_le _ _ Hx).
clear Hx. intro Hx.
split ;
  [ apply <- Rmin_Rle | apply <- Rmax_Rle ] ;
  right ; bound_tac ;
  eauto with mulauto.
Qed.

Ltac simpl_is_zero :=
  unfold is_zero, Rsign ;
  match goal with
  | H: Rlt ?v R0 /\ _ |- context [Rcompare ?v R0] =>
    rewrite (Rcompare_correct_lt _ _ (proj1 H))
  | H: _ /\ (Rlt ?v R0 /\ _) |- context [Rcompare ?v R0] =>
    rewrite (Rcompare_correct_lt _ _ (proj1 (proj2 H)))
  | H: Rlt R0 ?v /\ _ |- context [Rcompare ?v R0] =>
    rewrite (Rcompare_correct_gt _ _ (proj1 H))
  | H: _ /\ (Rlt R0 ?v /\ _) |- context [Rcompare ?v R0] =>
    rewrite (Rcompare_correct_gt _ _ (proj1 (proj2 H)))
  end.

Hint Local Resolve Rlt_le : mulauto.
Hint Local Resolve Rinv_lt_0_compat : mulauto.
Hint Local Resolve Rinv_0_lt_compat : mulauto.
Hint Local Resolve Rle_Rinv_pos : mulauto.
Hint Local Resolve Rle_Rinv_neg : mulauto.

Hint Local Resolve Rlt_le : mulauto2.
Hint Local Resolve Rinv_lt_0_compat : mulauto2.
Hint Local Resolve Rinv_0_lt_compat : mulauto2.
Hint Local Resolve Rmult_le_pos_pos : mulauto2.
Hint Local Resolve Rmult_le_neg_pos : mulauto2.
Hint Local Resolve Rmult_le_pos_neg : mulauto2.
Hint Local Resolve Rmult_le_neg_neg : mulauto2.

Theorem div_correct :
  forall prec,
  extension_2 Xdiv (div prec).
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ;
  try ( intros ; exact I ) ;
  try ( intros H1 H2 ; try elim H1 ; elim H2 ; fail ).
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold bnd, contains, convert, convert_bound.
(* case study on sign of xi *)
generalize (sign_strict_correct xl xu x (conj Hxl Hxu)).
case (sign_strict xl xu) ; intros Hx0 ; simpl in Hx0 ;
  (* case study on sign of yi *)
  try ( generalize (sign_strict_correct yl yu y (conj Hyl Hyu)) ;
        case (sign_strict yl yu) ; intros Hy0 ; simpl in Hy0 ) ;
  try exact I ; try simpl_is_zero ; unfold Rdiv ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F.zero_correct ; simpl ;
        rewrite (proj1 Hx0) ; rewrite Rmult_0_l ;
        split ; apply Rle_refl ) ;
  (* simplify Fdivz *)
  try ( unfold Fdivz ;
        rewrite real_correct ;
        try xreal_tac yl ; xreal_tac yu ) ;
  unfold convert_bound ;
  try rewrite F.zero_correct ;
  split ;
  (* remove rounding operators *)
  try ( rewrite F.div_correct ;
        rewrite Fdiv_correct with (1 := F.radix_correct) ;
        do 2 xreal_tac2 ; unfold Xdiv, Rdiv ;
        match goal with |- context [is_zero ?v] => case (is_zero v) ; try exact I end ;
        bound_tac ) ;
  clear_complex ;
  (* solve by comparing to zero *)
  try ( simpl ; eauto with mulauto2 ; fail ) ;
  (* solve by transivity *)
  eauto 8 with mulauto.
Qed.

Axiom inv_correct : forall prec, extension Xinv (inv prec).
Axiom sqr_correct : forall prec, extension Xsqr (sqr prec).

End FloatInterval.
