(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

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

From Coq Require Import ZArith Reals.
From Flocq Require Import Raux.

Require Import Xreal.
Require Import Basic.
Require Import Generic.
Require Import Generic_proof.
Require Import Sig.

Module Type Radix.
  Parameter val : radix.
End Radix.

Module Radix2 <: Radix.
  Definition val := radix2.
End Radix2.

Module Radix10 <: Radix.
  Definition val := Build_radix 10 (refl_equal _).
End Radix10.

Module GenericFloat (Rad : Radix) <: FloatOps.

  Definition radix := Rad.val.
  Definition sensible_format := match radix_val radix with Zpos (xO _) => true | _ => false end.
  Definition type := float radix.
  Definition toF (x : type) := x.
  Definition toX (x : type) := FtoX x.
  Definition toR x := proj_val (toX x).
  Definition fromF (x : type) := x.
  Definition precision := positive.
  Definition sfactor := Z.
  Definition prec := fun x : positive => x.
  Definition ZtoS := fun x : Z => x.
  Definition StoZ := fun x : Z => x.
  Definition PtoP := fun x : positive => x.
  Definition incr_prec := Pplus.
  Definition zero := @Fzero radix.
  Definition nan := @Fnan radix.
  Definition mag := @Fmag radix.
  Definition cmp (x y : type) := match Fcmp x y with Xlt => Lt | Xgt => Gt | _ => Eq end.
  Definition min := @Fmin radix.
  Definition max := @Fmax radix.
  Definition round := @Fround radix.
  Definition neg := @Fneg radix.
  Definition abs := @Fabs radix.
  Definition scale := @Fscale radix.
  Definition scale2 := @Fscale2 radix.
  Definition div2 := @Fdiv2 radix.
  Definition add_exact := @Fadd_exact radix.
  Definition add := @Fadd radix.
  Definition sub := @Fsub radix.
  Definition mul := @Fmul radix.
  Definition div := @Fdiv radix.
  Definition sqrt := @Fsqrt radix.
  Definition nearbyint := @Fnearbyint_exact radix.
  Definition zero_correct := refl_equal (Xreal R0).
  Definition nan_correct := refl_equal Xnan.
  Definition min_correct := @Fmin_correct radix.
  Definition max_correct := @Fmax_correct radix.
  Definition neg_correct := @Fneg_correct radix.
  Definition abs_correct := @Fabs_correct radix.
  Definition scale_correct := @Fscale_correct radix.
  Definition scale2_correct := @Fscale2_correct radix.
  Definition add_exact_correct := @Fadd_exact_correct radix.
  Definition add_correct := @Fadd_correct radix.
  Definition sub_correct := @Fsub_correct radix.
  Definition mul_correct := @Fmul_correct radix.
  Definition div_correct := @Fdiv_correct radix.
  Definition sqrt_correct := @Fsqrt_correct radix.
  Definition nearbyint_correct := @Fnearbyint_exact_correct radix.

  Definition fromZ n : float radix := match n with Zpos p => Float false p Z0 | Zneg p => Float true p Z0 | Z0 => Fzero end.

  Lemma fromZ_correct : forall n, FtoX (toF (fromZ n)) = Xreal (IZR n).
  Proof.
    intros. case n ; split.
  Qed.

  Definition real (f : float radix) := match f with Fnan => false | _ => true end.

  Lemma real_correct :
    forall f, real f = match toX f with Xnan => false | _ => true end.
  Proof.
  intros f.
  now case f.
  Qed.

  Lemma cmp_correct :
    forall x y,
    toX x = Xreal (toR x) ->
    toX y = Xreal (toR y) ->
    cmp x y = Rcompare (toR x) (toR y).
  Proof.
  intros x y Rx Ry.
  unfold cmp.
  rewrite Fcmp_correct.
  unfold toX in Rx, Ry.
  rewrite Rx, Ry.
  simpl.
  now case Rcompare.
  Qed.

  Lemma div2_correct :
    forall x, sensible_format = true ->
    (1 / 256 <= Rabs (toR x))%R ->
    toX (div2 x) = Xdiv (toX x) (Xreal 2).
  Proof.
  intros x Hf _.
  unfold div2, Fdiv2.
  rewrite scale2_correct; [|easy].
  simpl; unfold Z.pow_pos; simpl.
  rewrite Xdiv_split.
  unfold Xinv, Xinv'.
  now rewrite is_zero_false.
  Qed.

End GenericFloat.
