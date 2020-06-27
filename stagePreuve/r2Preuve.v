Require Import Reals Psatz Floats.
From Flocq Require Import Core Plus_error IEEE754.PrimFloat BinarySingleNaN.

Existing Instance Hprec.
Existing Instance Hmax.

Local Open Scope float_scope.

Definition Eps64 := Eval compute in ldexp 1 (-53)%Z.
Definition R_Eps64 := bpow radix2 (-53)%Z.
Definition iEps64 := Eval compute in (1 / Eps64)%float.
Definition R_iEps64 := bpow radix2 53%Z.
Definition Eta64 := Eval compute in ldexp 1 (-1074)%Z.
Definition R_Eta64 := bpow radix2 (-1074)%Z.
Definition Phi64 := Eval compute in (Eps64 * (1 + (2 * Eps64)))%float.
Definition R_Phi64 := succ radix2 (FLT_exp emin prec) R_Eps64.
Definition Fmin64 := Eval compute in ((Eta64/Eps64)/2)%float.
Definition tFmin64 := Eval compute in (2 * Fmin64)%float.

Definition c0 := Eval compute in 0.5%float * 1/(Eps64 * Eps64) * Eta64.
Definition R_c0 := bpow radix2 (-969)%Z.
Definition c1 := Eval compute in (iEps64 * Eta64)%float.
Definition R_c1 := bpow radix2 (-1021)%Z.

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

Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt := (round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt := (ulp radix2 (FLT_exp emin prec)).
Notation cexp := (cexp radix2 (FLT_exp emin prec)).
Notation pred_flt := (pred radix2 (FLT_exp emin prec)).

Definition Prim2R (x : PrimFloat.float) := B2R (Prim2B x).

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

Lemma C_UP_R_def: forall u, format u -> C_UP_R u = succ radix2 (FLT_exp emin prec) u.
Proof with auto with typeclass_instances.
intros u form.
apply FLT_format_generic in form...
destruct form as [uf H1 H2 H3].
unfold succ.
case Rle_bool_spec; intro Hu0.
{
  unfold C_UP_R.
  case Rlt_bool_spec; intro Huc0.
  {
    case Rlt_bool_spec; intro Hcu1.
    {
      assert (round_flt (u + R_Eta64) = (u + R_Eta64)%R) as Hsubnormal.
      admit. (* u est un sous-normal *)
      rewrite Hsubnormal.
      apply f_equal2; [reflexivity|].
      unfold ulp_flt.
      case Req_bool_spec; intro Huz; unfold R_Eta64.
      {
        admit. (* Trivial *) (* ça ne me semble pas totalement trivial ?,
        il faut utiliser ineq2, negligible_exp_FLT et la def de fexp *)
      }
      apply f_equal2; [reflexivity|].
      unfold cexp.
      admit. (* Trivial (FAIT EN PAPIER) *) 
    }
    unfold ulp_flt.
    case Req_bool_spec; intro Hu.
    {
      exfalso.
      revert Hcu1.
      apply Rlt_not_le.
      rewrite Hu.
      rewrite Rabs_R0.
      compute.
      lra.
    }
    admit. (* Preuve Scaling *)
  }
  unfold ulp_flt.
  case Req_bool_spec; intro Hu.
  {
    exfalso.
    revert Huc0.
    apply Rlt_not_le.
    rewrite Hu.
    rewrite Rabs_R0.
    compute.
    lra.
  }
  unfold cexp.
  admit. (* Preuve normale *)
}
admit. (* Preuve négative *)
Admitted.

(* Lemma FLT_format_double: forall u, format u -> format (2*u).
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
Qed. *)