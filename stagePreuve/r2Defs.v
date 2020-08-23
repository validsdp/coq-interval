Require Import Reals Psatz Floats.
From Flocq Require Import Core Plus_error Mult_error IEEE754.PrimFloat BinarySingleNaN Relative.

Existing Instance Hprec.
Existing Instance Hmax.

Local Open Scope float_scope.

Definition Eps64 := Eval compute in ldexp 1 (-53)%Z.
Definition R_Eps64 := bpow radix2 (-53)%Z.
Definition iEps64 := Eval compute in ldexp 1 (53)%Z.
Definition R_iEps64 := bpow radix2 53%Z.
Definition Eta64 := Eval compute in ldexp 1 (-1074)%Z.
Definition R_Eta64 := bpow radix2 (-1074)%Z.
Definition Phi64 := Eval compute in (Eps64 * (1 + (2 * Eps64)))%float.
Definition R_Phi64 := succ radix2 (FLT_exp emin prec) R_Eps64.

Definition c0 := Eval compute in 0.5%float * 1/(Eps64 * Eps64) * Eta64.
Definition R_c0 := bpow radix2 (-969)%Z.
Definition c1 := Eval compute in (iEps64 * Eta64)%float. (* Plus petit normal *)
Definition R_c1 := bpow radix2 (-1021)%Z.
Definition clb := Eval compute in 0.5%float * c1.
Definition R_clb := bpow radix2 (-1022)%Z.
Definition crb := Eval compute in 2%float * c1.
Definition R_crb := bpow radix2 (-1020)%Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Definition round_flt := (round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt := (ulp radix2 (FLT_exp emin prec)).
Notation cexp := (cexp radix2 (FLT_exp emin prec)).
Notation pred_flt := (pred radix2 (FLT_exp emin prec)).
Notation succ_flt := (succ radix2 (FLT_exp emin prec)).
Notation bpow_2 := (bpow radix2).
Definition R_ufp (x: R) := bpow_2 (mag radix2 x - 1).

Definition B_UP_R (c : R) :=
  round_flt (c + round_flt(round_flt (R_Phi64 * Rabs c) + R_Eta64)).
Definition B_DN_R (c : R) :=
  round_flt (c - round_flt(round_flt (R_Phi64 * Rabs c) + R_Eta64)).

Definition C_UP_R (c : R) :=
let ac := Rabs c in
  if Rlt_bool ac R_c0 then
    if Rlt_bool ac R_c1 then
      round_flt (c + R_Eta64)%R (* Else if *)
    else
      let C := round_flt (R_iEps64 * c)%R in 
      round_flt (R_Eps64 * round_flt (C + round_flt (R_Phi64 * Rabs C)))%R (* Scaling *)
  else
    round_flt (c + round_flt (R_Phi64 * ac))%R. (* Normal *)

Definition C_DN_R (c : R) :=
let ac := Rabs c in
  if Rlt_bool ac R_c0 then
    if Rlt_bool ac R_c1 then
      round_flt (c - R_Eta64)%R (* Else if *)
    else
      let C := round_flt (R_iEps64 * c)%R in 
      round_flt (R_Eps64 * round_flt (C - round_flt (R_Phi64 * Rabs C)))%R (* Scaling *)
  else
    round_flt (c - round_flt (R_Phi64 * ac))%R. (* Normal *)

Lemma B_UP_R_opp: forall u, format u -> (u <> 0)%R ->
(B_UP_R (-u) = - B_DN_R (u))%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold B_UP_R.
unfold B_DN_R.
unfold round_flt.
rewrite <- round_NE_opp.
f_equal.
rewrite Ropp_minus_distr.
rewrite Rabs_Ropp.
lra.
Qed.

Lemma B_DN_R_opp: forall u, format u -> (u <> 0)%R ->
(B_DN_R (-u) = - B_UP_R (u))%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold B_UP_R.
unfold B_DN_R.
unfold round_flt.
rewrite <- round_NE_opp.
f_equal.
rewrite Ropp_plus_distr.
rewrite Rabs_Ropp.
lra.
Qed.