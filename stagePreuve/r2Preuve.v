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
Notation ulp_flt := (ulp radix2 (FLT_exp emin prec)).
Notation cexp := (cexp radix2 (FLT_exp emin prec)).
Notation pred_flt := (pred radix2 (FLT_exp emin prec)).
Notation succ_flt := (succ radix2 (FLT_exp emin prec)).
Definition R_ufp (x: R) := (R_iEps64 * 1/2 * (ulp radix2 (FLT_exp emin prec) x))%R.

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

Lemma round_subnormal_plus_eta: forall u, format u -> (Rabs u < R_c1)%R -> (round_flt(u + R_Eta64) = u + R_Eta64)%R.
Proof with auto with typeclass_instances.
intros u form Hineq.
apply FLT_format_generic in form...
destruct form as [uf H1 H2 H3] eqn:H'.
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
case (Rle_dec (u + R_Eta64) 0); intros HAddPos.
{
  apply Ropp_le_contravar in HAddPos.
  rewrite Ropp_0 in HAddPos.
  rewrite <- Rabs_Ropp.
  rewrite Rabs_pos_eq; [|assumption].
  rewrite Ropp_plus_distr.
  unfold R_Eta64.
  simpl (prec + emin)%Z.
  apply Rabs_lt_inv in Hineq.
  unfold R_c1 in Hineq.
  case (Rle_dec (u) 0); intros Hpos.
  {
    destruct Hineq as [HineqL HineqS].
    apply Ropp_lt_contravar in HineqL.
    rewrite Ropp_involutive in HineqL.
    apply Rlt_le in HineqL.
    assert (-u + - bpow radix2 (-1074) <= bpow radix2 (-1021) + - bpow radix2 (-1074))%R by lra.
    apply Rle_trans with (bpow radix2 (-1021) + - bpow radix2 (-1074))%R...
    compute; lra.
  }
  apply Rnot_le_gt in Hpos.
  compute; lra.
}
apply Rnot_le_gt in HAddPos.
rewrite Rabs_pos_eq.
2:{
  apply Rgt_lt in HAddPos.
  apply Rlt_le in HAddPos.
  assumption.
}
unfold R_c1 in Hineq.
unfold R_Eta64.
simpl (prec + emin)%Z.
apply Rabs_lt_inv in Hineq.
destruct Hineq as [HineqS HineqL].
case (Rle_dec (u) 0); intros Hpos.
{
  apply Rge_le.
  apply Rge_trans with (bpow radix2 (-1074)); compute; lra.
}
apply Rnot_le_gt in Hpos.
replace (bpow radix2 (-1074)) with (ulp radix2 (FLT_exp emin prec) u).
{
  apply id_p_ulp_le_bpow...
  apply generic_format_FLT...
}
apply ulp_FLT_small...
simpl (-1074 + prec)%Z.
now apply Rabs_lt.
Qed.

Lemma round_subnormal_minus_eta: forall u, format u -> (Rabs u < R_c1)%R ->
  (round_flt (u - R_Eta64) = u - R_Eta64)%R.
Proof with auto with typeclass_instances.
intros u form Hineq.
apply FLT_format_generic in form...
destruct form as [uf H1 H2 H3] eqn:H'.
apply round_generic...
apply FLT_format_plus_small...
{
  rewrite H1.
  apply generic_format_FLT.
  constructor 1 with uf...
}
{
  apply generic_format_opp.
  apply generic_format_FLT.
  unfold R_Eta64.
  apply FLT_format_bpow...
  easy.
}
case (Rle_dec (u - R_Eta64) 0); intros HAddPos.
{
  apply Ropp_le_contravar in HAddPos.
  rewrite Ropp_0 in HAddPos.
  rewrite <- Rabs_Ropp.
  rewrite Rabs_pos_eq; [|assumption].
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  unfold R_Eta64.
  simpl (prec + emin)%Z.
  apply Rabs_lt_inv in Hineq.
  unfold R_c1 in Hineq.
  case (Rle_dec (u) 0); intros Hpos.
  {
    destruct Hineq as [HineqL HineqS].
    apply Ropp_lt_contravar in HineqL.
    rewrite Ropp_involutive in HineqL.
    destruct Hpos.
    2:{
      rewrite H.
      compute; lra.
    }
    replace (bpow radix2 (-1074)) with (ulp radix2 (FLT_exp emin prec) (-u)).
    set (u' := (-u)%R).
    {
      apply id_p_ulp_le_bpow...
      {
        apply Ropp_lt_contravar in H.
        unfold u'.
        now rewrite Ropp_0 in H.
      }
      apply generic_format_opp.
      now apply generic_format_FLT.
    }
    apply ulp_FLT_small...
    simpl (-1074 + prec)%Z.
    apply Ropp_lt_contravar in HineqS.
    now apply Rabs_lt.
  }
  apply Rnot_le_gt in Hpos.
  compute; lra.
}
apply Rnot_le_gt in HAddPos.
rewrite Rabs_pos_eq.
2:{
  apply Rgt_lt in HAddPos.
  apply Rlt_le in HAddPos.
  assumption.
}
unfold R_c1 in Hineq.
unfold R_Eta64.
simpl (prec + emin)%Z.
apply Rabs_lt_inv in Hineq.
destruct Hineq as [HineqS HineqL].
case (Rle_dec (u) 0).
{
  intro Hpos.
  apply Rge_le.
  apply Rge_trans with (bpow radix2 (-1074)); compute; lra.
}
intro Hpos.
apply Rnot_le_gt in Hpos.
replace (bpow radix2 (-1074)) with (ulp radix2 (FLT_exp emin prec) u).
{
  assert (u - ulp_flt u <= u + ulp_flt u)%R.
  {
    apply Rplus_le_compat_l.
    pose proof ulp_ge_0 radix2 (FLT_exp emin prec) u as ulp_pos.
    lra.
  }
  apply Rle_trans with (u + ulp radix2 (FLT_exp emin prec) u)%R.
  apply H.
  apply id_p_ulp_le_bpow...
  apply generic_format_FLT...
}
apply ulp_FLT_small...
simpl (-1074 + prec)%Z.
now apply Rabs_lt.
Qed.

Theorem R2_2_UP: forall u, format u -> (Rabs u < R_clb \/ Rabs u > R_crb)%R ->
  B_UP_R u = succ radix2 (FLT_exp emin prec) u.
Proof with auto with typeclass_instances.
intros u form Hinterval.
destruct Hinterval as [Hsubnorm|Hnorm].
{
  unfold B_UP_R.
  assert (round_flt (R_Phi64 * Rabs u) = 0%R).
  {
    case (Req_dec u 0); intros Hzero.
    {
      rewrite Hzero.
      rewrite Rabs_R0.
      rewrite Rmult_0_r.
      apply round_0...
    }
    admit. (* Non trivial *)
  }
  rewrite H.
  rewrite Rplus_0_l.
  assert (round_flt R_Eta64 = R_Eta64)%R as etaForm.
  {
    apply round_generic...
    unfold R_Eta64.
    apply generic_format_bpow...
    simpl; easy.
  }
  rewrite etaForm.
  rewrite round_subnormal_plus_eta...
  {
    unfold succ.
    case Rle_bool_spec; intros Hpos.
    {
      apply f_equal2; [reflexivity|].
      unfold R_Eta64.
      symmetry.
      apply ulp_FLT_small...
      unfold R_clb in Hsubnorm.
      simpl (-1074 + prec)%Z.
      apply Rlt_trans with (bpow radix2 (-1022))...
      now apply bpow_lt.
    }
    unfold pred_pos.

    assert (forall x, x - - u = x + u)%R as mm_eq_p.
    unfold Rminus.
    now rewrite Ropp_involutive.

    case Req_bool_spec; intros Hu_bpow; rewrite Ropp_minus_distr; rewrite mm_eq_p; rewrite Rplus_comm; apply f_equal2...
    {
      rewrite mag_opp.
      assert (FLT_exp emin prec (mag radix2 u - 1) = emin)%R as Hsmall_exp.
      {
        assert (mag radix2 u <= (-1021))%Z as Hu_small.
        {
          unfold R_clb in Hsubnorm.
          apply mag_le_bpow; [lra|].
          apply Rlt_trans with (bpow radix2 (-1022))%Z...
          now apply bpow_lt.
        }
        unfold emin.
        simpl (3-emax-prec)%Z.
        admit. (* Non trivial *)
      }
      now rewrite Hsmall_exp.
    }
    rewrite ulp_FLT_small...
    rewrite Rabs_Ropp.
    simpl (emin+prec)%Z.
    unfold R_clb in Hsubnorm.
    apply Rlt_trans with (bpow radix2 (-1022))...
    now apply bpow_lt.
  }
  unfold R_c1.
  unfold R_clb in Hsubnorm.
  apply Rlt_trans with (bpow radix2 (-1022))...
  now apply bpow_lt.
}
admit. (* Preuve principale *)
Admitted.

Theorem R2_2_DN: forall u, format u -> (Rabs u < R_clb \/ Rabs u > R_crb)%R ->
  B_DN_R u = pred radix2 (FLT_exp emin prec) u.
Proof with auto with typeclass_instances.
intros u form Hinterval.
destruct Hinterval as [Hsubnorm|Hnorm].
{
  unfold B_DN_R.
  assert (round_flt (R_Phi64 * Rabs u) = 0%R).
  admit.
  rewrite H.
  rewrite Rplus_0_l.
  assert (round_flt R_Eta64 = R_Eta64).
  unfold R_Eta64.
  {
    apply round_generic...
    apply generic_format_bpow.
    simpl.
    easy.
  }
  assert (round_flt R_Eta64 = R_Eta64)%R as etaForm.
  {
    apply round_generic...
    unfold R_Eta64.
    apply generic_format_bpow...
    simpl; easy.
  }
  rewrite etaForm.
  rewrite round_subnormal_minus_eta...
  {
    unfold pred_flt.
    unfold succ_flt.
    case Rle_bool_spec; intros Hpos.
    {
      rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      assert ((u + - ulp radix2 (FLT_exp emin prec) (- u)) = (u - ulp radix2 (FLT_exp emin prec) (- u)))%R.
      {
        now unfold Rminus.
      }
      rewrite H1.
      apply f_equal2; [reflexivity|].
      unfold R_Eta64.
      symmetry.
      apply ulp_FLT_small...
      unfold R_clb in Hsubnorm.
      simpl (-1074 + prec)%Z.
      rewrite Rabs_Ropp.
      apply Rlt_trans with (bpow radix2 (-1022))...
      now apply bpow_lt.
    }
    unfold pred_pos.
    rewrite !Ropp_involutive.
    case Req_bool_spec; intros Hu_bpow; apply f_equal2...
    {
      assert (FLT_exp emin prec (mag radix2 u - 1) = emin)%R as Hsmall_exp.
      {
        assert (mag radix2 u <= (-1021))%Z as Hu_small.
        {
          unfold R_clb in Hsubnorm.
          apply mag_le_bpow; [lra|].
          apply Rlt_trans with (bpow radix2 (-1022))%Z...
          now apply bpow_lt.
        }
        unfold emin.
        simpl (3-emax-prec)%Z.
        admit. (* Non trivial *)
      }
      now rewrite Hsmall_exp.
    }
    rewrite ulp_FLT_small...
    simpl (emin+prec)%Z.
    unfold R_clb in Hsubnorm.
    apply Rlt_trans with (bpow radix2 (-1022))...
    now apply bpow_lt.
  }
  unfold R_c1.
  unfold R_clb in Hsubnorm.
  apply Rlt_trans with (bpow radix2 (-1022))...
  now apply bpow_lt.
}
unfold B_DN_R.
unfold pred_flt.
admit. (* Preuve principale *)
Admitted.

Lemma C_UP_R_1st_spec: forall u, format u -> (Rabs u >= R_c0)%R -> round_flt(u + round_flt(R_Phi64 * Rabs u)) = succ_flt u.
Proof with auto with typeclass_instances.
intros u form Hineq.
set (eps := round_flt (R_Phi64 * Rabs u)).
set (csup' := succ radix2 (FLT_exp emin prec) u).
set (csup := round_flt (u + eps)).
unfold C_UP_R.
assert (csup <= csup')%R as ineq1.
{
  unfold csup'.
  rewrite <- R2_2_UP...
  {
    unfold B_UP_R.
    fold eps.
    apply round_le...
    apply Rplus_le_compat_l.
    rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE eps) at 1...
    {
      apply round_le...
      rewrite <- (Rplus_0_r eps) at 1.
      apply Rplus_le_compat_l.
      compute; lra.
    }
    apply generic_format_round...
  }
  right.
  apply Rge_gt_trans with R_c0...
  compute; lra.
}
apply Rle_antisym; [assumption|].
apply round_N_ge_midp...
{
  unfold csup'.
  apply generic_format_succ...
}
unfold csup'.
rewrite pred_succ...
Eval compute in Phi64.
assert (R_Eps64 * (R_ufp u) < eps)%R as r210.
{
  assert (R_Phi64 * u >= R_Eps64 * succ_flt u)%R as r14.
  {
    assert (R_Phi64 = R_Eps64 * (1 + 2 * R_Eps64))%R.
    {
      admit.
    }
    rewrite H.
    assert (R_Eps64 * succ_flt u <= R_Eps64 * (1+2*R_Eps64) * u)%R.
    {
      admit.
    }
    apply Rle_ge in H0...
  }
  unfold eps.
  rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (R_Eps64 * R_ufp u))...
  fold round_flt.
  2:{
    unfold R_ufp.
    unfold R_Eps64.
    unfold R_iEps64.
    assert (1/2 = bpow radix2 (-1))%R.
    compute; lra.
    admit. (* Non trivial *)
  }
  admit. (* Non trivial *)
}
apply (Rplus_lt_compat_l u) in r210.
apply Rle_lt_trans with (u + R_Eps64 * R_ufp u )%R; [| assumption ].
unfold R_ufp.
case (Rle_dec 0 u); intros Hpos.
{
  rewrite succ_eq_pos...
  apply (@Rmult_le_reg_r 2 _ _ Rlt_R0_R2).
  field_simplify.
  apply Rplus_le_compat_l.
  rewrite <- Rmult_1_r at 1.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  apply ulp_ge_0.
  unfold R_Eps64.
  unfold R_iEps64.
  rewrite <- bpow_plus.
  simpl.
  lra.
}
admit. (* Plus tard *)
Admitted.

Theorem C_UP_R_spec: forall u, format u -> C_UP_R u = succ_flt u.
Proof with auto with typeclass_instances.
intros u form.
apply FLT_format_generic in form...
destruct form as [uf H1 H2 H3] eqn:H'.
unfold C_UP_R.
case Rlt_bool_spec; intro Huc0.
{
  case Rlt_bool_spec; intro Hcu1.
  {
    rewrite round_subnormal_plus_eta...
    2:{
      apply generic_format_FLT...
    }
    unfold succ.
    case (Rle_bool 0 u) eqn:Hpos.
    {
      apply f_equal2; [reflexivity|].
      unfold R_Eta64.
      symmetry.
      now apply ulp_FLT_small.
    }
    unfold pred_pos.
    admit. (* Non trivial *)
  }
  set (u' := (R_iEps64 * u)%R).
  rewrite C_UP_R_1st_spec with (round_flt u').
  2:{
    apply generic_format_round...
  }
  2:{
    unfold u'.
    assert (round_flt (R_iEps64 * u) = R_iEps64 * u)%R as norm.
    {
      apply round_generic...
      admit. (* Élémentaire : R_iEps64 est une puissance de 2 *)
    }
    rewrite norm.
    unfold R_c0.
    unfold R_iEps64.
    apply Rle_ge.
    unfold R_c1 in Hcu1.
    assert (( bpow radix2 (-53)%Z * bpow radix2 (-969)%Z <=  bpow radix2 (-53)%Z * bpow radix2 53%Z * Rabs u)%R ->(bpow radix2 (-969)%Z <= bpow radix2 53%Z * Rabs u)%R).
    admit. (* Trivial : Multiplication des deux côtés *)
    rewrite Rabs_mult.
    rewrite Rabs_pos_eq at 1.
    2:{
      apply bpow_ge_0.
    }
    apply H.
    rewrite <- bpow_plus.
    rewrite <- bpow_plus.
    simpl (-53 + -969)%Z.
    simpl (-53 + 53)%Z.
    simpl (bpow radix2 0).
    rewrite Rmult_1_l.
    apply Rle_trans with (bpow radix2 (-1021)).
    now apply bpow_le.
    assumption.
  }
  admit. (* Preuve Scaling, relativement trivial *)
}
apply C_UP_R_1st_spec.
apply generic_format_FLT...
now apply Rle_ge.
Admitted.

Lemma C_DN_R_1st_spec: forall u, format u -> (Rabs u >= R_c0)%R -> round_flt(u - round_flt(R_Phi64 * Rabs u)) = pred_flt u.
Proof with auto with typeclass_instances.
intros u form Hineq.
set (eps := round_flt (R_Phi64 * Rabs u)).
set (cinf' := pred_flt u).
set (cinf := round_flt (u - eps)).
assert (cinf' <= cinf)%R as ineq1.
{
  unfold cinf'.
  rewrite <- R2_2_DN...
  {
    unfold B_DN_R.
    fold eps.
    apply round_le...
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE eps) at 1...
    {
      apply round_le...
      rewrite <- (Rplus_0_r eps) at 1.
      apply Rplus_le_compat_l.
      compute; lra.
    }
    apply generic_format_round...
  }
  right.
  apply Rge_gt_trans with R_c0...
  compute; lra.
}
apply Rle_antisym; [|assumption].
apply round_N_le_midp; unfold cinf'...
apply generic_format_pred...
rewrite succ_pred...
assert (R_Eps64 * (R_ufp u) < eps)%R as r210.
{
  assert (R_Phi64 * u >= R_Eps64 * succ_flt u)%R as r14.
  {
    assert (R_Phi64 = R_Eps64 * (1 + 2 * R_Eps64))%R.
    {
      admit.
    }
    rewrite H.
    assert (R_Eps64 * succ_flt u <= R_Eps64 * (1+2*R_Eps64) * u)%R.
    {
      admit.
    }
    apply Rle_ge in H0...
  }
}
apply Ropp_lt_contravar in r210.
apply (Rplus_lt_compat_l u) in r210.
apply Rlt_le_trans with (u - R_Eps64 * R_ufp u )%R; [assumption|].
admit.
Admitted.

Theorem C_DN_R_spec: forall u, format u -> C_DN_R u = pred_flt u.
Proof with auto with typeclass_instances.
intros u form.
apply FLT_format_generic in form...
destruct form as [uf H1 H2 H3].
unfold C_DN_R.
case Rlt_bool_spec; intro Huc0.
{
  case Rlt_bool_spec; intro Hcu1.
  {
    rewrite round_subnormal_minus_eta...
    2:{
      apply generic_format_FLT...
      constructor 1 with uf...
    }
    unfold pred_flt.
    unfold succ_flt.
    destruct (Rle_bool 0 (-u)) eqn:Hpos.
    {
      rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      rewrite ulp_opp.
      assert ((u + - ulp radix2 (FLT_exp emin prec) u) = (u - ulp radix2 (FLT_exp emin prec) u))%R...
      rewrite H.
      apply f_equal2; [reflexivity|].
      unfold R_Eta64.
      symmetry.
      now apply ulp_FLT_small.
    }
    rewrite Ropp_involutive.
    rewrite Ropp_involutive.
    unfold pred_pos.
    case Req_bool_spec; intro Hbpow_u.
    {
      admit. (* Non trivial, non difficile *)
    }
    rewrite ulp_FLT_small...
  }
  set (u' := (R_iEps64 * u)%R).
  rewrite C_DN_R_1st_spec with (round_flt u').
  2:{
    apply generic_format_round...
  }
  2:{
    unfold u'.
    assert (round_flt (R_iEps64 * u) = R_iEps64 * u)%R as norm.
    admit. (* Trivial *)
    rewrite norm.
    unfold R_c0.
    unfold R_iEps64.
    apply Rle_ge.
    unfold R_c1 in Hcu1.
    assert (( bpow radix2 (-53)%Z * bpow radix2 (-969)%Z <=  bpow radix2 (-53)%Z * bpow radix2 53%Z * Rabs u)%R ->(bpow radix2 (-969)%Z <= bpow radix2 53%Z * Rabs u)%R).
    admit. (* Trivial *)
    rewrite Rabs_mult.
    rewrite Rabs_pos_eq at 1.
    2:{
      apply bpow_ge_0.
    }
    apply H.
    rewrite <- bpow_plus.
    rewrite <- bpow_plus.
    simpl (-53 + -969)%Z.
    simpl (-53 + 53)%Z.
    assert (bpow radix2 0 * Rabs u = Rabs u)%R. admit.
    rewrite H0.
    apply Rle_trans with R_c1.
    compute; lra.
    fold R_c1 in Hcu1.
    assumption.
  }
  admit. (* Preuve Scaling, relativement trivial *)
}
apply C_DN_R_1st_spec.
{
  apply generic_format_FLT...
  constructor 1 with uf...
}
now apply Rle_ge.
Admitted.