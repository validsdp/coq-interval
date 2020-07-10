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
Notation bpow_2 := (bpow radix2).
Definition R_ufp (x: R) := ((R_iEps64 * (ulp radix2 (FLT_exp emin prec) x))/2)%R.

Lemma ulp_to_ufp: forall x, (ulp_flt x = 2 * R_Eps64 * R_ufp (x))%R.
Proof with auto with typeclass_instances.
intros u.
apply (Rmult_eq_reg_l (1/2)%R); [|lra].
apply (Rmult_eq_reg_l R_iEps64).
field_simplify.
unfold R_ufp.
unfold R_iEps64 at 2.
unfold R_Eps64 at 1.
rewrite <- bpow_plus.
simpl.
field_simplify.
easy.
unfold R_iEps64.
pose proof (bpow_gt_0 radix2 53).
lra.
Qed.

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

Lemma ufp_le_id: forall u, format u -> (u <> 0)%R ->
  (R_ufp u <= Rabs u)%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold R_ufp.
unfold ulp.
rewrite Req_bool_false...
Admitted.

Lemma ufp_gt_0: forall u, (u <> 0)%R -> (0 < R_ufp u)%R.
Proof with auto with typeclass_instances.
intros u Hnot_zero.
unfold R_ufp.
apply Rmult_lt_0_compat; [|lra].
apply Rmult_lt_0_compat; [apply bpow_gt_0|].
unfold ulp.
rewrite Req_bool_false...
apply bpow_gt_0.
Qed.

Lemma flt_mag_small: forall u, (u <> 0)%R -> (Rabs u < R_c1)%R ->
  FLT_exp emin prec (mag radix2 u - 1) = emin.
Proof with auto with typeclass_instances.
intros u Hnzero Hineq.
assert (mag radix2 u <= (-1021))%Z as Hu_small.
{
  unfold R_c1 in Hineq.
  apply mag_le_bpow...
}
unfold emin.
simpl (3-emax-prec)%Z.
unfold FLT_exp.
destruct (Zmax_spec (mag radix2 u - 1 - prec) (-1074))%Z.
{
  exfalso.
  revert H.
  apply Decidable.not_and_iff.
  intro Hu_big.
  contradict Hu_big.
  assert ((mag radix2 u - 1 - prec <= -1074) -> ~ (mag radix2 u - 1 - prec >= -1074))%Z.
  admit. (* Trivial *)
  apply H.
  apply Zplus_le_reg_r with prec.
  apply Zplus_le_reg_r with 1%Z.
  ring_simplify.
  simpl.
  now apply Z.le_trans with (-1021)%Z.
}
destruct H.
now rewrite H0.
Admitted.

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

Lemma bpow_cexp_u_le_eps_m_u: forall u, format u -> (u <> 0)%R ->
  (bpow_2 (cexp u) <= 2 * Rabs u * R_Eps64)%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold cexp.
unfold FLT_exp.
case (Z_le_dec (mag radix2 u - prec)%Z emin); intros Hmax.
{
  rewrite Z.max_r...
  apply Zplus_le_reg_r in Hmax.
  unfold emax in Hmax.
  simpl in Hmax.
  rewrite <- (ulp_FLT_small radix2 emin prec u).
  {
    apply (Rmult_le_reg_l R_iEps64); [apply bpow_gt_0|].
    apply (Rmult_le_reg_r (1/2)); [lra|].
    field_simplify.
    assert (R_iEps64 * ulp_flt u / 2 = R_ufp u)%R as ufp_rewrite...
    rewrite ufp_rewrite.
    rewrite Rmult_comm.
    rewrite <- Rmult_assoc.
    unfold R_iEps64.
    unfold R_Eps64.
    rewrite <- bpow_plus.
    simpl.
    rewrite Rmult_1_l.
    apply ufp_le_id...
  }
  simpl (emin + prec)%Z.
  pose proof (bpow_mag_gt radix2 u).
  assert (bpow_2 (mag radix2 u) <= bpow_2 (-1021))%R.
  apply bpow_le...
  apply Rlt_le_trans with (bpow_2 (mag radix2 u))...
}
assert (emin <= mag radix2 u - prec)%Z as Hmax'.
omega.
rewrite Z.max_l...
apply Zplus_le_reg_r in Hmax'.
unfold emax in Hmax'.
simpl in Hmax'.
assert (-prec = -1 + 1 - 53)%Z.
{
  unfold prec; omega.
}
unfold Z.sub.
rewrite H.
unfold Z.sub.
rewrite Z.add_assoc.
rewrite Z.add_assoc.
simpl (- (53))%Z.
rewrite bpow_plus.
rewrite bpow_plus.
assert (bpow_2 1 = 2)%R as bpow1_eq_2...
rewrite bpow1_eq_2.
fold R_Eps64.
apply Rmult_le_compat_r; [apply bpow_ge_0|].
rewrite Rmult_comm.
apply Rmult_le_compat_l; [lra|].
apply bpow_mag_le...
Qed.

Theorem R2_1_UP_pos: forall u, format u -> (u > 0)%R ->
  (succ_flt u <= B_UP_R u)%R.
Proof with auto with typeclass_instances.
intros u form Hpos.
unfold B_UP_R.
set (eps := (round_flt (round_flt (R_Phi64 * Rabs u) + R_Eta64))%R).
assert (R_Eps64 * (R_ufp u) < eps)%R as r209.
{
  assert (round_flt(R_Eps64 * succ_flt u) <= round_flt (R_Phi64 * Rabs u))%R as r14.
  {
    apply round_le...
    apply Rge_le.
    assert (R_Phi64 = R_Eps64 * (1 + 2 * R_Eps64))%R as phi_eps.
    {
      unfold R_Phi64.
      unfold succ.
      rewrite Rle_bool_true...
      2:{
        unfold R_Eps64.
        now apply bpow_ge_0.
      }
      unfold ulp.
      rewrite Req_bool_false...
      2:{
        unfold R_Eps64.
        compute; lra.
      }
      unfold cexp.
      unfold R_Eps64.
      rewrite mag_bpow; simpl (-53 + 1)%Z.
      unfold FLT_exp.
      unfold emin.
      simpl Z.max.
      ring_simplify.
      rewrite Rplus_comm with (2 * bpow_2 (-53) ^ 2)%R (bpow_2 (-53))%R.
      apply Rplus_eq_compat_l.
      rewrite Z.max_l; [|easy].
      assert (-105 = (-53) + (-53 + 1))%Z.
      easy.
      rewrite H.
      rewrite !bpow_plus.
      rewrite <- Rmult_assoc.
      rewrite bpow_1.
      assert (IZR radix2 = 2)%R.
      now compute.
      rewrite H0.
      now field_simplify.
    }
    apply Rle_ge.
    rewrite phi_eps.
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l; [apply bpow_ge_0|].
    unfold succ.
    rewrite Rle_bool_true; [|lra]...
    rewrite Rabs_pos_eq; [|lra]...
    unfold ulp.
    rewrite Req_bool_false; [|lra]...
    field_simplify.
    rewrite (Rplus_comm (2 * u * R_Eps64) (u)).
    apply Rplus_le_compat_l.
    rewrite <- (Rabs_pos_eq u) at 2...
    2:{
      lra.
    }
    apply bpow_cexp_u_le_eps_m_u...
    lra.
  }
  unfold eps.
  apply Rlt_le_trans with (round_flt (R_Phi64 * Rabs u))%R.
  2:{
    rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (round_flt (R_Phi64 * Rabs u))) at 1...
    fold round_flt.
    2:{
      apply generic_format_round...
    }
    apply round_le...
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    apply bpow_ge_0.
  }
  unfold round_flt in r14 at 1.
  rewrite (round_generic radix2 (FLT_exp emin prec) ZnearestE (R_Eps64 * succ_flt u)%R) in r14.
  2:{
    admit. (* Puissance de 2 *)
  }
  apply Rlt_le_trans with (R_Eps64 * succ_flt u)%R...
  apply Rmult_lt_compat_l; [apply bpow_gt_0|].
  apply Rle_lt_trans with (Rabs u).
  apply ufp_le_id; [|lra]...
  rewrite !Rabs_pos_eq...
  {
    apply succ_gt_id; lra.
  }
  apply Rle_trans with u.
  lra.
  lra.
}
apply round_N_ge_midp...
apply generic_format_succ...
rewrite pred_succ...
apply Rle_lt_trans with (u + R_Eps64 * R_ufp u)%R.
unfold R_ufp.
{
  rewrite succ_eq_pos; [|lra]...
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
now apply Rplus_lt_compat_l.
Admitted.


Theorem R2_1_DN_pos: forall u, format u -> (u > 0)%R ->
  (B_DN_R u <= pred_flt u)%R.
Proof with auto with typeclass_instances.
intros u form Hpos.
unfold B_DN_R.
set (eps := (round_flt (round_flt (R_Phi64 * Rabs u) + R_Eta64))%R).
assert (R_Eps64 * (R_ufp u) < eps)%R as r209.
{
  assert (round_flt(R_Eps64 * succ_flt u) <= round_flt (R_Phi64 * Rabs u))%R as r14.
  {
    apply round_le...
    apply Rge_le.
    assert (R_Phi64 = R_Eps64 * (1 + 2 * R_Eps64))%R as phi_eps.
    {
      unfold R_Phi64.
      unfold succ.
      rewrite Rle_bool_true...
      2:{
        unfold R_Eps64.
        now apply bpow_ge_0.
      }
      unfold ulp.
      rewrite Req_bool_false...
      2:{
        unfold R_Eps64.
        compute; lra.
      }
      unfold cexp.
      unfold R_Eps64.
      rewrite mag_bpow; simpl (-53 + 1)%Z.
      unfold FLT_exp.
      unfold emin.
      simpl Z.max.
      ring_simplify.
      rewrite Rplus_comm with (2 * bpow_2 (-53) ^ 2)%R (bpow_2 (-53))%R.
      apply Rplus_eq_compat_l.
      rewrite Z.max_l; [|easy].
      assert (-105 = (-53) + (-53 + 1))%Z.
      easy.
      rewrite H.
      rewrite !bpow_plus.
      rewrite <- Rmult_assoc.
      rewrite bpow_1.
      assert (IZR radix2 = 2)%R.
      now compute.
      rewrite H0.
      now field_simplify.
    }
    apply Rle_ge.
    rewrite phi_eps.
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l; [apply bpow_ge_0|].
    unfold succ.
    rewrite Rle_bool_true; [|lra]...
    rewrite Rabs_pos_eq; [|lra]...
    unfold ulp.
    rewrite Req_bool_false; [|lra]...
    field_simplify.
    rewrite (Rplus_comm (2 * u * R_Eps64) (u)).
    apply Rplus_le_compat_l.
    rewrite <- (Rabs_pos_eq u) at 2...
    2:{
      lra.
    }
    apply bpow_cexp_u_le_eps_m_u...
    lra.
  }
  unfold eps.
  apply Rlt_le_trans with (round_flt (R_Phi64 * Rabs u))%R.
  2:{
    rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (round_flt (R_Phi64 * Rabs u))) at 1...
    fold round_flt.
    2:{
      apply generic_format_round...
    }
    apply round_le...
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    apply bpow_ge_0.
  }
  unfold round_flt in r14 at 1.
  rewrite (round_generic radix2 (FLT_exp emin prec) ZnearestE (R_Eps64 * succ_flt u)%R) in r14.
  2:{
    admit. (* Puissance de 2 *)
  }
  apply Rlt_le_trans with (R_Eps64 * succ_flt u)%R...
  apply Rmult_lt_compat_l; [apply bpow_gt_0|].
  apply Rle_lt_trans with (Rabs u).
  apply ufp_le_id; [|lra]...
  rewrite !Rabs_pos_eq...
  {
    apply succ_gt_id; lra.
  }
  apply Rle_trans with u.
  lra.
  lra.
}
apply round_N_le_midp...
apply generic_format_pred...
rewrite succ_pred...
apply Ropp_lt_contravar in r209.
apply (Rplus_lt_compat_l u) in r209.
apply Rlt_le_trans with (u - R_Eps64 * R_ufp u )%R; [assumption|].
rewrite pred_eq_pos; [|lra]...
unfold pred_pos.
admit.
Admitted.

Lemma B_UP_R_opp: forall u, format u -> (u <> 0)%R ->
  (B_UP_R (-u) = - B_DN_R (u))%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold B_UP_R.
unfold B_DN_R.
enough (- u + round_flt (round_flt (R_Phi64 * Rabs (- u)) + R_Eta64) = -(u - round_flt (round_flt (R_Phi64 * Rabs u) + R_Eta64)))%R.
2:{
  rewrite Ropp_minus_distr.
  rewrite Rabs_Ropp.
  lra.
}
admit. (* Trivial *)
Admitted.

Lemma B_DN_R_opp: forall u, format u -> (u <> 0)%R ->
  (B_DN_R (-u) = - B_UP_R (u))%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold B_UP_R.
unfold B_DN_R.
enough (- u + round_flt (round_flt (R_Phi64 * Rabs (- u)) + R_Eta64) = -(u - round_flt (round_flt (R_Phi64 * Rabs u) + R_Eta64)))%R.
2:{
  rewrite Ropp_minus_distr.
  rewrite Rabs_Ropp.
  lra.
}
admit. (* Trivial *)
Admitted.

Theorem R2_1_UP: forall u, format u -> (u <> 0)%R ->
  (succ_flt u <= B_UP_R u)%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
case (Rle_dec 0 u); intros Hpos.
{
  apply R2_1_UP_pos...
  lra.
}
rewrite <- (Ropp_involutive u).
set (u' := (-u)%R).
assert (u' > 0)%R as Hup_pos.
{
  unfold u'.
  lra.
}
assert (format u') as Hform_up.
{
  unfold u'.
  apply generic_format_opp...
}
rewrite succ_opp.
rewrite B_UP_R_opp...
apply Ropp_le_contravar.
apply R2_1_DN_pos...
lra.
Qed.

Theorem R2_1_DN: forall u, format u -> (u <> 0)%R ->
  (B_DN_R u <= pred_flt u)%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
case (Rle_dec 0 u); intros Hpos.
{
  apply R2_1_DN_pos...
  lra.
}
rewrite <- (Ropp_involutive u).
set (u' := (-u)%R).
assert (u' > 0)%R as Hup_pos.
{
  unfold u'.
  lra.
}
assert (format u') as Hform_up.
{
  unfold u'.
  apply generic_format_opp...
}
rewrite pred_opp.
rewrite B_DN_R_opp...
apply Ropp_le_contravar.
apply R2_1_UP_pos...
lra.
Qed.

Theorem R2_2_UP_pos: forall u, format u -> (u > 0)%R -> (Rabs u < R_clb \/ Rabs u > R_crb)%R ->
  B_UP_R u = succ radix2 (FLT_exp emin prec) u.
Proof with auto with typeclass_instances.
intros u form Hpos Hinterval.
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
    admit. (* Non trivial : Arrondi vers 0 *)
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
    rewrite Rle_bool_true; [|lra]...
    apply f_equal2; [reflexivity|].
    unfold R_Eta64.
    symmetry.
    apply ulp_FLT_small...
    unfold R_clb in Hsubnorm.
    simpl (-1074 + prec)%Z.
    apply Rlt_trans with (bpow radix2 (-1022))...
    now apply bpow_lt.
  }
  unfold R_c1.
  unfold R_clb in Hsubnorm.
  apply Rlt_trans with (bpow radix2 (-1022))...
  now apply bpow_lt.
}
apply Rle_antisym; [|apply R2_1_UP]...
2:{
  lra.
}
unfold B_UP_R.
set (eps := (round_flt (round_flt (R_Phi64 * Rabs u) + R_Eta64))%R).
assert (eps <= (5*R_Eps64*R_ufp(u))/2)%R as r214.
{
  admit. (* Non trivial *)
}
apply round_N_le_midp...
apply generic_format_succ...
assert (succ_flt u + R_Eps64 * R_ufp u <= (succ_flt u + succ_flt (succ_flt u))/2)%R as interm_ineq.
{
  set (u' := succ_flt u).
  rewrite succ_eq_pos...
  2:{
    unfold u'.
    apply Rle_trans with u.
    lra.
    apply succ_ge_id.
  }
  apply (Rplus_le_reg_r (-u')).
  field_simplify.
  unfold R_ufp.
  admit. (* Trivial *)
}
apply Rle_lt_trans with (succ_flt u + (R_Eps64 * R_ufp u)/2)%R.
{
  rewrite succ_eq_pos; [|lra].
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite ulp_to_ufp.
  now field_simplify.
}
apply Rlt_le_trans with (succ_flt u + R_Eps64 * R_ufp u)%R...
{
  apply Rplus_lt_compat_l.
  apply (Rmult_lt_reg_r 2); [lra|].
  field_simplify.
  apply Rmult_lt_compat_r; [apply ufp_gt_0; lra|].
  rewrite <- Rmult_1_l at 1; apply Rmult_lt_compat_r; [apply bpow_gt_0|].
  lra.
}
Admitted.

Theorem R2_2_DN_pos: forall u, format u -> (u > 0)%R -> (Rabs u < R_clb \/ Rabs u > R_crb)%R ->
  B_DN_R u = pred radix2 (FLT_exp emin prec) u.
Proof with auto with typeclass_instances.
intros u form Hpos Hinterval.
destruct Hinterval as [Hsubnorm|Hnorm].
{
  unfold B_DN_R.
  assert (round_flt (R_Phi64 * Rabs u) = 0%R).
  admit.
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
  rewrite round_subnormal_minus_eta...
  {
    rewrite pred_eq_pos.
    assert ((u + - ulp radix2 (FLT_exp emin prec) (- u)) = (u - ulp radix2 (FLT_exp emin prec) (- u)))%R as pm_eq_m.
    {
      now unfold Rminus.
    }
    unfold pred_pos.
    case Req_bool_spec; intros Hu_bpow; apply f_equal2...
    {
      rewrite flt_mag_small...
      lra.
      unfold R_clb in Hsubnorm.
      unfold R_c1.
      apply Rlt_trans with (bpow_2 (-1022))%R...
      now apply bpow_lt.
    }
    rewrite ulp_FLT_small...
    simpl (emin+prec)%Z.
    unfold R_clb in Hsubnorm.
    apply Rlt_trans with (bpow radix2 (-1022))...
    now apply bpow_lt.
    lra.
    }
  unfold R_c1.
  unfold R_clb in Hsubnorm.
  apply Rlt_trans with (bpow radix2 (-1022))...
  now apply bpow_lt.
}
apply Rle_antisym; [apply R2_1_DN|]...
1:{
  lra.
}
unfold B_DN_R.
set (eps := (round_flt (round_flt (R_Phi64 * Rabs u) + R_Eta64))%R).
assert (eps <= (5*R_Eps64*R_ufp(u))/2)%R as r214.
{
  admit. (* Non trivial *)
}
apply round_N_ge_midp...
apply generic_format_pred...
Admitted.

Theorem R2_2_UP: forall u, format u -> (Rabs u < R_clb \/ Rabs u > R_crb)%R ->
  B_UP_R u = succ radix2 (FLT_exp emin prec) u.
Proof with auto with typeclass_instances.
intros u form Hinterval.
case (Rle_dec 0 u); intros Hpos.
{
  apply R2_2_UP_pos...
  admit. (* Trivial *)
}
rewrite <- (Ropp_involutive u).
set (u' := (-u)%R).
assert (u' > 0)%R as Hup_pos.
{
  unfold u'.
  lra.
}
assert (format u') as Hform_up.
{
  unfold u'.
  apply generic_format_opp...
}
rewrite succ_opp.
rewrite B_UP_R_opp...
apply Ropp_eq_compat.
apply R2_2_DN_pos...
admit. (* Trivial *)
Admitted.

Theorem R2_2_DN: forall u, format u -> (Rabs u < R_clb \/ Rabs u > R_crb)%R ->
  B_DN_R u = pred radix2 (FLT_exp emin prec) u.
Proof with auto with typeclass_instances.
intros u form Hinterval.
case (Rle_dec 0 u); intros Hpos.
{
  apply R2_2_DN_pos...
  admit. (* Trivial *)
}
rewrite <- (Ropp_involutive u).
set (u' := (-u)%R).
assert (u' > 0)%R as Hup_pos.
{
  unfold u'.
  lra.
}
assert (format u') as Hform_up.
{
  unfold u'.
  apply generic_format_opp...
}
rewrite pred_opp.
rewrite B_DN_R_opp...
apply Ropp_eq_compat.
apply R2_2_UP_pos...
admit. (* Trivial *)
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
assert (R_Eps64 * (R_ufp u) < eps)%R as r210.
{
  assert (round_flt(R_Eps64 * succ_flt u) <= round_flt (R_Phi64 * Rabs u))%R as r14.
  {
    apply round_le...
    apply Rge_le.
    assert (R_Phi64 = R_Eps64 * (1 + 2 * R_Eps64))%R as phi_eps.
    {
      unfold R_Phi64.
      unfold succ.
      rewrite Rle_bool_true...
      2:{
        unfold R_Eps64.
        now apply bpow_ge_0.
      }
      unfold ulp.
      rewrite Req_bool_false...
      2:{
        unfold R_Eps64.
        compute; lra.
      }
      unfold cexp.
      unfold R_Eps64.
      rewrite mag_bpow; simpl (-53 + 1)%Z.
      unfold FLT_exp.
      unfold emin.
      simpl Z.max.
      ring_simplify.
      rewrite Rplus_comm with (2 * bpow_2 (-53) ^ 2)%R (bpow_2 (-53))%R.
      apply Rplus_eq_compat_l.
      rewrite Z.max_l; [|easy].
      assert (-105 = (-53) + (-53 + 1))%Z.
      easy.
      rewrite H.
      rewrite !bpow_plus.
      rewrite <- Rmult_assoc.
      rewrite bpow_1.
      assert (IZR radix2 = 2)%R.
      now compute.
      rewrite H0.
      now field_simplify.
    }
    rewrite phi_eps.
    assert (R_Eps64 * succ_flt u <= R_Eps64 * (u + 2 * R_Eps64 * Rabs u))%R as major_ineq.
    {
      rewrite Rmult_assoc.
      apply Rmult_le_compat_l.
      {
        apply bpow_ge_0.
      }
      unfold succ.
      case Rle_bool_spec; intros Hpos.
      {
        unfold ulp.
        rewrite Req_bool_false.
        2:{
          rewrite Rabs_pos_eq in Hineq...
          admit. (* Élémentaire *)
        }
        unfold cexp.
        unfold R_Eps64.
        apply Rplus_le_compat_l.
        unfold FLT_exp.
        rewrite Z.max_l.
        2:{
          admit. (* Non difficile *)
        }
        unfold prec.
        assert (mag radix2 u - 53 = ((mag radix2 u - 1) + (- 53 + 1)))%Z as prec_decomp.
        omega.
        rewrite prec_decomp.
        rewrite !bpow_plus.
        fold R_Eps64.
        assert (bpow_2 1 = 2)%R as bpow1_eq_2...
        rewrite bpow1_eq_2.
        apply Rle_trans with (Rabs u * (R_Eps64 * 2))%R.
        {
          apply Rmult_le_compat_r.
          compute; lra.
          apply bpow_mag_le.
          admit. (* Élémentaire *)
        }
        lra.
      }
      unfold pred_pos.
      case Req_bool_spec; intros Hu_bpow.
      {
        rewrite Ropp_minus_distr.
        unfold Rminus.
        rewrite Ropp_involutive.
        unfold FLT_exp.
        rewrite Z.max_l.
        2:{
          unfold R_c0 in Hineq.
          apply Rge_le in Hineq.
          apply Zplus_le_reg_r with prec.
          apply Zplus_le_reg_r with (1)%Z.
          simpl.
          assert (mag radix2 (- u) - 1 - prec + prec + 1 = mag radix2 (- u))%Z as simp_decomp.
          omega.
          rewrite simp_decomp.
          apply mag_ge_bpow.
          simpl (-1020 - 1)%Z.
          rewrite Rabs_Ropp.
          apply Rle_trans with (bpow_2 (-969)%Z)...
          now apply bpow_le.
        }
        apply Rplus_le_reg_r with (-u)%R.
        rewrite <- Rabs_Ropp.
        rewrite Rabs_pos_eq; [|lra].
        field_simplify.
        unfold prec.
        unfold Z.sub; simpl.
        rewrite Z.add_comm.
        rewrite bpow_plus.
        fold R_Eps64.
        rewrite mag_opp.
        unfold R_c0 in Hineq.
        assert (bpow_2 (mag radix2 u - 1) <= Rabs u)%R as Hbpow_le_abs.
        apply bpow_mag_le.
        admit. (* Trivial *)
        apply Rle_trans with (R_Eps64 * (Rabs u))%R.
        {
          apply Rmult_le_compat_l; [apply bpow_ge_0|]...
        }
        rewrite <- Rabs_Ropp.
        rewrite Rabs_pos_eq; [|lra].
        rewrite Rmult_comm.
        apply Rmult_le_compat_r; [apply bpow_ge_0|].
        lra.
      }
      field_simplify.
      apply Rplus_le_compat_l.
      unfold ulp.
      rewrite Req_bool_false...
      2:{
        admit. (* Trivial *)
      }
      unfold cexp.
      unfold FLT_exp.
      rewrite Z.max_l.
      2:{
        admit. (* Plus tard, élémentaire *)
      }
      assert (mag radix2 u - 53 = ((mag radix2 u - 1) + (- 53 + 1)))%Z as prec_decomp.
      omega.
      rewrite mag_opp.
      unfold prec.
      rewrite prec_decomp.
      rewrite !bpow_plus.
      fold R_Eps64.
      assert (bpow_2 1 = 2)%R as bpow1_eq_2...
      rewrite bpow1_eq_2.
      assert (bpow_2 (mag radix2 u - 1) <= Rabs u)%R as Hbpow_le_abs.
      apply bpow_mag_le.
      admit. (* Trivial *)
      rewrite (Rmult_comm (2 * R_Eps64) (Rabs u)).
      rewrite (Rmult_comm (2) (R_Eps64)).
      apply Rmult_le_compat_r...
      unfold R_Eps64.
      compute; lra.
    }
    apply Rle_ge in major_ineq...
  }
  unfold eps.
  unfold round_flt in r14 at 1.
  rewrite (round_generic radix2 (FLT_exp emin prec) ZnearestE (R_Eps64 * succ_flt u)%R) in r14.
  2:{
    admit. (* Puissance de 2 *)
  }
  apply Rlt_le_trans with (R_Eps64 * succ_flt u)%R...
  apply Rmult_lt_compat_l; [apply bpow_gt_0|].
  apply Rle_lt_trans with u; [|apply succ_gt_id; admit].
  admit. (* ufp <= u *)
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
apply Rnot_le_gt in Hpos.
apply (@Rmult_le_reg_r 2 _ _ Rlt_R0_R2).
field_simplify.
unfold R_Eps64.
unfold R_iEps64.
rewrite <- bpow_plus.
simpl.
rewrite Rmult_1_l.
apply Rplus_le_reg_r with (-u)%R.
field_simplify.
unfold succ_flt.
rewrite Rle_bool_false...
unfold pred_pos.
case Req_bool_spec; intros Hu_bpow; field_simplify; apply Rplus_le_compat_l.
2:{
  rewrite ulp_opp; lra.
}

unfold ulp.
rewrite Req_bool_false.
{
  unfold cexp.
  apply bpow_le.
  rewrite mag_opp.
  unfold FLT_exp.
  apply Z.max_le_compat_r.
  omega.
}
lra.
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
    case (Rle_bool_spec); intros Hpos.
    {
      apply Rplus_eq_compat_l.
      unfold R_Eta64.
      symmetry.
      now apply ulp_FLT_small.
    }
    unfold pred_pos.
    case (Req_bool_spec); intros Hu_bpow; field_simplify; apply Rplus_eq_compat_l.
    {
      rewrite mag_opp.
      rewrite flt_mag_small...
      admit.
    }
    rewrite ulp_opp.
    rewrite ulp_FLT_small...
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
      unfold R_Phi64.
      unfold succ.
      rewrite Rle_bool_true...
      2:{
        unfold R_Eps64.
        now apply bpow_ge_0.
      }
      unfold ulp.
      rewrite Req_bool_false...
      2:{
        unfold R_Eps64.
        compute; lra.
      }
      unfold cexp.
      unfold R_Eps64.
      rewrite mag_bpow; simpl (-53 + 1)%Z.
      unfold FLT_exp.
      unfold emin.
      simpl Z.max.
      ring_simplify.
      rewrite Rplus_comm with (2 * bpow_2 (-53) ^ 2)%R (bpow_2 (-53))%R.
      apply Rplus_eq_compat_l.
      rewrite Z.max_l; [|easy].
      assert (-105 = (-53) + (-53 + 1))%Z.
      easy.
      rewrite H.
      rewrite !bpow_plus.
      rewrite <- Rmult_assoc.
      rewrite bpow_1.
      assert (IZR radix2 = 2)%R.
      now compute.
      rewrite H0.
      now field_simplify.
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