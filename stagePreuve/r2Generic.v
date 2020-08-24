Require Import Reals Psatz Floats.
Require Import r2Defs.
From Flocq Require Import Core Plus_error Mult_error IEEE754.PrimFloat BinarySingleNaN Relative.

Lemma phi_eps: (R_Phi64 = R_Eps64 * (1 + 2 * R_Eps64))%R.
Proof with auto with typeclass_instances.
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
Qed.

Lemma ufp_le_id: forall u, format u -> (u <> 0)%R ->
  (R_ufp u <= Rabs u)%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold R_ufp.
apply bpow_mag_le...
Qed.

Lemma ufp2_gt_id: forall u, format u -> (u <> 0)%R ->
  (2 * R_ufp u > Rabs u)%R.
Proof with auto with typeclass_instances.
intros u form Hnot_zero.
unfold R_ufp.
apply Rlt_gt.
assert (2 = bpow_2 1)%R as bpow1_eq_2.
{
  compute; lra.
}
rewrite bpow1_eq_2.
rewrite <- bpow_plus.
rewrite Zplus_minus.
apply bpow_mag_gt.
Qed.

Lemma ufp_gt_0: forall u, (u <> 0)%R -> (0 < R_ufp u)%R.
Proof with auto with typeclass_instances.
intros u Hnot_zero.
unfold R_ufp.
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
  intro Hge.
  apply Z.ge_le in Hge.
  generalize Hge.
  apply Z.lt_nge.
  apply Zplus_lt_reg_r with prec.
  apply Zplus_lt_reg_r with 1%Z.
  simpl.
  lia.
}
destruct H.
now rewrite H0.
Qed.

Lemma small_mag: forall u, format u -> (0 < Rabs u < R_c1)%R ->
  (mag radix2 (Rabs u) <= (-1021))%Z.
Proof with auto with typeclass_instances.
intros u form Hsmall.
apply mag_le_bpow; [lra|].
fold R_c1.
now rewrite Rabs_right; [|lra].
Qed.

Lemma small_FLT: forall u, format u -> (0 < Rabs u < R_c1)%R ->
  (FLT_exp emin prec (mag radix2 u) = (-1074))%Z.
Proof with auto with typeclass_instances.
intros u form Hsmall.
rewrite <-mag_abs.
unfold FLT_exp.
unfold emin.
simpl.
apply Z.max_r.
unfold prec.
apply Zplus_le_reg_r with 53%Z.
ring_simplify.
apply small_mag...
Qed.

Corollary small_m1_FLT: forall u, format u -> (0 < Rabs u < R_c1)%R ->
  (FLT_exp emin prec (mag radix2 u - 1) = (-1074))%Z.
Proof with auto with typeclass_instances.
intros u form Hsmall.
enough (FLT_exp emin prec (mag radix2 u - 1) = FLT_exp emin prec (mag radix2 u))%Z as FLT_small.
rewrite FLT_small.
apply small_FLT...
unfold FLT_exp.
rewrite !Z.max_r...
{
  unfold emin.
  unfold prec.
  apply Zplus_le_reg_r with 53%Z.
  ring_simplify.
  simpl.
  rewrite <-mag_abs.
  apply small_mag...
}
unfold emin.
unfold prec.
apply Zplus_le_reg_r with 54%Z.
ring_simplify.
simpl.
apply Z.le_trans with (-1021)%Z; [|lia].
rewrite <- mag_abs.
apply small_mag...
Qed.

Lemma succ_small_pos: forall u, format u -> (u >= 0)%R -> (Rabs u < R_c1)%R ->
  (succ_flt u = u + R_Eta64)%R.
Proof with auto with typeclass_instances.
intros u form Hpos Hsmall.
unfold succ.
rewrite Rle_bool_true; [|lra].
now rewrite ulp_FLT_small.
Qed.


Lemma pred_small_pos: forall u, format u -> (u >= 0)%R -> (Rabs u < R_c1)%R ->
  (pred_flt u = u - R_Eta64)%R.
Proof with auto with typeclass_instances.
intros u form Hpos Hsmall.
case (Req_dec 0 u); intros Hzero.
{
  rewrite <- Hzero.
  rewrite pred_0.
  rewrite ulp_FLT_0...
  unfold emin.
  rewrite Rminus_0_l.
  unfold emax.
  unfold prec.
  simpl (3 - 1024 - 53)%Z.
  now unfold R_Eta64.
}
rewrite pred_eq_pos; [|lra].
unfold pred_pos.
case Req_bool_spec; intros Hu_bpow.
{
  rewrite small_m1_FLT...
  split...
  apply Rabs_pos_lt...
}
now rewrite ulp_FLT_small.
Qed.

Lemma succ_small_neg: forall u, format u -> (u < 0)%R -> (Rabs u < R_c1)%R ->
  (succ_flt u = u + R_Eta64)%R.
Proof with auto with typeclass_instances.
intros u form Hneg Hsmall.
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
rewrite pred_small_pos...
2:{
  lra.
}
2:{
  unfold u'.
  now rewrite Rabs_Ropp.
}
now lra.
Qed.

Lemma pred_small_neg: forall u, format u -> (u < 0)%R -> (Rabs u < R_c1)%R ->
(pred_flt u = u - R_Eta64)%R.
Proof with auto with typeclass_instances.
intros u form Hneg Hsmall.
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
rewrite succ_small_pos...
2:{
  lra.
}
2:{
  unfold u'.
  now rewrite Rabs_Ropp.
}
now lra.
Qed.

Lemma succ_small: forall u, format u -> (Rabs u < R_c1)%R ->
  (succ_flt u = u + R_Eta64)%R.
Proof with auto with typeclass_instances.
intros u form Hsmall.
case (Rle_lt_dec 0 u); intros Hsign.
{
  apply succ_small_pos...
  lra.
}
apply succ_small_neg...
Qed.

Lemma pred_small: forall u, format u -> (Rabs u < R_c1)%R ->
(pred_flt u = u - R_Eta64)%R.
Proof with auto with typeclass_instances.
intros u form Hsmall.
case (Rle_lt_dec 0 u); intros Hsign.
{
  apply pred_small_pos...
  lra.
}
apply pred_small_neg...
Qed.

Lemma round_small_plus_eta: forall u, format u -> (Rabs u < R_c1)%R -> (round_flt(u + R_Eta64) = u + R_Eta64)%R.
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
    rewrite <- Rplus_0_r.
    apply Rplus_le_compat_l.
    apply Ropp_le_cancel.
    rewrite Ropp_0.
    rewrite Ropp_involutive.
    apply bpow_ge_0.
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