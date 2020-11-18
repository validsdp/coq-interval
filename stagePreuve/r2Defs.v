(* ref papier Rump, Zimmerman, Boldo, Melquiond
   Computing predecessor and successor in roundingto nearest
   https://doi.org/10.1007/s10543-009-0218-z *)

Require Import Reals Psatz Floats.
From Flocq Require Import Core Plus_error Mult_error IEEE754.PrimFloat BinarySingleNaN Relative.

Existing Instance Hprec.
Existing Instance Hmax.

Local Open Scope float_scope.

Definition u := Eval compute in ldexp 1 (-53)%Z.
Definition R_u := bpow radix2 (-53)%Z.

Definition inv_u := Eval compute in ldexp 1 (53)%Z.
(* u^-1 in paper *)
Definition R_inv_u := bpow radix2 53%Z.

Definition eta := Eval compute in ldexp 1 (-1074)%Z.
Definition R_eta := bpow radix2 (-1074)%Z.

Definition succ_u := Eval compute in (u * (1 + (2 * u)))%float.
Definition R_succ_u := succ radix2 (FLT_exp emin prec) R_u.

Definition c0 := Eval compute in 0.5%float * 1/(u * u) * eta.
(* R_c0 = 1/2 u^-2 eta in paper *)
Definition R_c0 := bpow radix2 (-969)%Z.

Definition c1 := Eval compute in (inv_u * eta)%float. (* Borne binade minimale *)
Definition R_c1 := bpow radix2 (-1021)%Z.

Definition half_c1 := Eval compute in 0.5%float * c1.
Definition R_half_c1 := bpow radix2 (-1022)%Z.

Definition two_c1 := Eval compute in 2%float * c1.
Definition R_two_c1 := bpow radix2 (-1020)%Z.

Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Definition round_flt := (round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt := (ulp radix2 (FLT_exp emin prec)).
Notation cexp := (cexp radix2 (FLT_exp emin prec)).
Notation pred_flt := (pred radix2 (FLT_exp emin prec)).
Notation succ_flt := (succ radix2 (FLT_exp emin prec)).
Notation bpow_2 := (bpow radix2).
Definition R_ufp (x: R) := bpow_2 (mag radix2 x - 1).

(* algorithm 1 in paper *)
Definition B_UP_R (c : R) :=
  round_flt (c + round_flt(round_flt (R_succ_u * Rabs c) + R_eta)).
Definition B_DN_R (c : R) :=
  round_flt (c - round_flt(round_flt (R_succ_u * Rabs c) + R_eta)).

(* algorithm 2 in paper *)
Definition C_UP_R (c : R) :=
(* R_c0 = 1/2 u^-2 eta in paper *)
(* R_c1 = u^-1 eta in paper *)
(* inv_u = u^-1 in paper *)
(* round_flt = fl(.) in paper *)
let abs_c := Rabs c in
  if Rlt_bool abs_c R_c0 then
    if Rlt_bool abs_c R_c1 then
      round_flt (c + R_eta)%R (* Else if *)
    else
      let C := round_flt (R_inv_u * c)%R in 
      round_flt (R_u * round_flt (C + round_flt (R_succ_u * Rabs C)))%R (* Scaling *)
  else
    round_flt (c + round_flt (R_succ_u * abs_c))%R. (* Normal *)

Definition C_DN_R (c : R) :=
let abs_c := Rabs c in
  if Rlt_bool abs_c R_c0 then
    if Rlt_bool abs_c R_c1 then
      round_flt (c - R_eta)%R (* Else if *)
    else
      let C := round_flt (R_inv_u * c)%R in 
      round_flt (R_u * round_flt (C - round_flt (R_succ_u * Rabs C)))%R (* Scaling *)
  else
    round_flt (c - round_flt (R_succ_u * abs_c))%R. (* Normal *)

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

(********************************************************************)
