Require Import Reals Psatz Floats.
From Flocq Require Import Core Plus_error IEEE754.PrimFloat BinarySingleNaN.

Existing Instance Hprec.
Existing Instance Hmax.

Local Open Scope float_scope.

Definition Eps64 := Eval compute in ldexp 1 (-53)%Z.
Definition iEps64 := Eval compute in (1 / Eps64)%float.
Definition Eta64 := Eval compute in ldexp 1 (-1074)%Z.
Definition Phi64 := Eval compute in (Eps64 * (1 + (2 * Eps64)))%float.
Definition Fmin64 := Eval compute in ((Eta64/Eps64)/2)%float.
Definition tFmin64 := Eval compute in (2 * Fmin64)%float.

Definition c0 := Eval compute in 0.5%float * 1/(Eps64 * Eps64) * Eta64.
Definition c1 := Eval compute in (iEps64 * Eta64)%float.

Definition C_UP_prim (c : PrimFloat.float) :=
let ac := abs c in
  if ac < c0 then
    if ac < c1 then
      c + Eta64
    else
      let C := (iEps64 * c) in 
      Eps64 * (C + (Phi64 * abs C))
  else
    c + (Phi64 * ac).

Variable emin : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt := (round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt := (ulp radix2 (FLT_exp emin prec)).
Notation cexp := (cexp radix2 (FLT_exp emin prec)).
Notation pred_flt := (pred radix2 (FLT_exp emin prec)).

Lemma succDef: B2Prim (Bsucc (B754_finite s m e e0)) = 

Theorem Rump2009_2_3: forall u : PrimFloat.float,
  (PrimFloat.is_finite u) = true -> (C_UP u) = (next_up u).
Proof.
intro u.
intro uFinite.
apply Prim2B_inj.
rewrite next_up_equiv.
rewrite is_finite_equiv in uFinite.
assert (bu : u = B2Prim (Prim2B u)).
  symmetry.
  apply B2Prim_Prim2B.
induction (Prim2B u).
{
  rewrite bu.
  apply B2Prim_inj.
  rewrite B2Prim_Prim2B.
  induction s;compute;reflexivity.
}
easy.
easy.
{
  rewrite bu;
    apply B2Prim_inj;
    rewrite B2Prim_Prim2B;
    unfold C_UP.
  set (c := (B2Prim (B754_finite s m e e0))).
  
  case_eq (c0 <= abs c).
  intro ineq1.
  admit.
  case_eq (abs c < c1).
  intros ineq2 ineq1.
  admit.
  intros ineq2 ineq1.
  admit.

  set (c := (B2Prim (B754_finite true m e e0))).
  case_eq (c0 <= abs c).
  admit.
  case_eq (abs c < c1).
  admit.
  admit.
}
Admitted.


Lemma FLT_format_double: forall u, format u -> format (2*u).
Proof with auto with typeclass_instances.
intros u Fu.
apply generic_format_FLT.
apply FLT_format_generic in Fu...
destruct Fu as [uf H1 H2 H3].
exists (Float radix2 (Fnum uf) (Fexp uf+1)).
rewrite H1; unfold F2R; simpl.
rewrite bpow_plus, bpow_1.
simpl;ring.
easy.
apply Z.le_trans with (1:=H3).
apply Zle_succ.
Qed.