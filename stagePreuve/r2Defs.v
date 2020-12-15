(* ref papier Rump, Zimmerman, Boldo, Melquiond
   Computing predecessor and successor in roundingto nearest
   https://doi.org/10.1007/s10543-009-0218-z *)

Require Import Reals Psatz Floats.
From Flocq Require Import Core Plus_error Mult_error IEEE754.PrimFloat BinarySingleNaN Relative.

Local Open Scope R_scope.

Section r2Defs.

(* "We require beta to be even and greater than one" (p. 2) *)
Variable beta : radix.
Hypothesis beta_even : Z.even beta = true.

Variables emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round := (round beta (FLT_exp emin prec) ZnearestE).
Notation ulp := (ulp beta (FLT_exp emin prec)).
Notation cexp := (cexp beta (FLT_exp emin prec)).
Notation pred := (pred beta (FLT_exp emin prec)).
Notation succ := (succ beta (FLT_exp emin prec)).
Notation bpow := (bpow beta).

Definition ufp (x: R) := bpow (mag beta x - 1).

Definition u := / 2 * bpow (1 - prec).

(* u^-1 in paper *)
Definition inv_u := bpow prec.

Definition eta := bpow emin.

Definition succ_u := succ u.

(* c0 = 1/2 u^-2 eta in paper *)
Definition c0 := / 2 * / (u * u) * eta.
Definition c1 := inv_u * eta.
Definition half_c1 := / 2 * c1.
Definition two_c1 := 2 * c1.

(* algorithm 1 in paper *)
Definition B_UP_R (c : R) :=
  round (c + round (round  (succ_u * Rabs c) + eta)).
Definition B_DN_R (c : R) :=
  round (c - round (round (succ_u * Rabs c) + eta)).

(* algorithm 2 in paper *)
Definition C_UP_R (c : R) :=
  (* c0 = 1/2 u^-2 eta in paper *)
  (* c1 = u^-1 eta in paper *)
  (* inv_u = u^-1 in paper *)
  (* round = fl(.) in paper *)
  let abs_c := Rabs c in
  if Rlt_bool abs_c c0 then
    if Rlt_bool abs_c c1 then
      round (c + eta)%R (* Else if *)
    else
      let C := round (inv_u * c)%R in
      round (u * round (C + round (succ_u * Rabs C)))%R (* Scaling *)
  else
    round (c + round (succ_u * abs_c))%R. (* Normal *)

Definition C_DN_R (c : R) :=
  let abs_c := Rabs c in
  if Rlt_bool abs_c c0 then
    if Rlt_bool abs_c c1 then
      round (c - eta)%R (* Else if *)
    else
      let C := round (inv_u * c)%R in
      round (u * round (C - round (succ_u * Rabs C)))%R (* Scaling *)
  else
    round (c - round (succ_u * abs_c))%R. (* Normal *)

Lemma B_UP_R_opp: forall u, format u -> (u <> 0)%R ->
  (B_UP_R (-u) = - B_DN_R (u))%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold B_UP_R.
unfold B_DN_R.
unfold round.
Admitted. (*
rewrite <- round_NE_opp.
f_equal.
rewrite Ropp_minus_distr.
rewrite Rabs_Ropp.
lra.
Qed.
*)

Lemma B_DN_R_opp: forall u, format u -> (u <> 0)%R ->
  (B_DN_R (-u) = - B_UP_R (u))%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold B_UP_R.
unfold B_DN_R.
unfold round.
Admitted. (*
rewrite <- round_NE_opp.
f_equal.
rewrite Ropp_plus_distr.
rewrite Rabs_Ropp.
lra.
Qed.
*)

End r2Defs.
