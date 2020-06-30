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
Definition clb := Eval compute in 0.5%float * c1.
Definition R_clb := bpow radix2 (-1022)%Z.
Definition crb := Eval compute in 2%float * c1.
Definition R_crb := bpow radix2 (-1020)%Z.

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
Definition round_flt := (round radix2 (FLT_exp emin prec) ZnearestE).
Notation ulp_flt := (ulp radix2 (FLT_exp emin prec)) (only parsing).
Notation cexp := (cexp radix2 (FLT_exp emin prec)).
Notation pred_flt := (pred radix2 (FLT_exp emin prec)).

Definition Prim2R (x : PrimFloat.float) := B2R (Prim2B x).

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

Theorem R2_2_UP: forall u, format u -> (Rabs u < R_clb \/ Rabs u > R_crb)%R ->
  B_UP_R u = succ radix2 (FLT_exp emin prec) u.
Admitted.

Theorem R2_2_DN: forall u, format u -> (Rabs u < R_clb \/ Rabs u > R_crb)%R ->
  B_DN_R u = pred radix2 (FLT_exp emin prec) u.
Admitted.

Check fun a : @float radix2 => @Float radix2 (Fnum a +1) (Fexp a).

Eval compute in emin.

Lemma C_UP_R_def: forall u, format u -> C_UP_R u = succ radix2 (FLT_exp emin prec) u.
Proof with auto with typeclass_instances.
intros u form.
apply FLT_format_generic in form...
destruct form as [uf H1 H2 H3] eqn:H'.
unfold succ.
case Rle_bool_spec; intro Hu0.
{
  unfold C_UP_R.
  case Rlt_bool_spec; intro Huc0.
  {
    case Rlt_bool_spec; intro Hcu1.
    {
      assert (round_flt (u + R_Eta64) = (u + R_Eta64)%R) as Hsubnormal.
      {
        apply round_generic...
        apply FLT_format_plus_small...
        {
          rewrite H1.
          apply generic_format_FLT.
          constructor 1 with uf...
        }
        {
          apply generic_format_FLT.
          unfold R_Eta64.
          apply FLT_format_bpow...
          easy.
        }
        rewrite Rabs_pos_eq.
        2:{
          compute.
          lra.
        }
        unfold R_c1 in Hcu1.
        unfold R_Eta64.
        simpl (prec + emin)%Z.
        apply Rabs_lt_inv in Hcu1.
        destruct Hcu1 as [Hcu1 Hcu1'].
        destruct Hu0.
        2:{
          rewrite <-H.
          rewrite Rplus_0_l.
          apply bpow_le.
          easy.
        }
        replace (bpow radix2 (-1074)) with (ulp radix2 (FLT_exp emin prec) u).
        {
          apply id_p_ulp_le_bpow...
          apply generic_format_FLT...
        }
        apply ulp_FLT_small...
        simpl (-1074 + prec)%Z.
        now apply Rabs_lt.
      }
      rewrite Hsubnormal.
      apply f_equal2; [reflexivity|].
      unfold R_Eta64.
      symmetry.
      now apply ulp_FLT_small.
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
  set (eps := round_flt (R_Phi64 * Rabs u)).
  set (eps' := round_flt (eps + R_Eta64)).
  assert (Rle_bool eps eps' = true).
  {
    apply Rle_bool_true.
    unfold eps'.
    rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE eps) at 1.
    {
      apply round_le...
      rewrite <- (Rplus_0_r eps) at 1.
      apply Rplus_le_compat_l.
      compute; lra.
    }
    apply generic_format_round...
  }
  set (csup' := B_UP_R u).
  assert (Rle_bool (round_flt (u + eps)) csup' = true).
  {
    unfold csup'.
  }
  unfold cexp.
  admit. (* Preuve normale *)
}
admit. (* Preuve négative *)
Admitted.

Lemma C_DN_R_def: forall u, format u -> C_DN_R u = pred radix2 (FLT_exp emin prec) u.
Proof with auto with typeclass_instances.
intros u form.
apply FLT_format_generic in form...
destruct form as [uf H1 H2 H3].
unfold pred.
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