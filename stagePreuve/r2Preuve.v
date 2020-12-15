Require Import Reals Psatz Floats.
From Flocq Require Import Core Plus_error Mult_error IEEE754.PrimFloat BinarySingleNaN Relative
.
Require Import r2Defs r2Generic.

Local Open Scope R_scope.

Section r2Preuve.

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

Notation u := (u beta prec).
Notation succ_u := (succ_u beta emin prec).
Notation eta := (eta beta emin).

Notation ufp := (ufp beta).
Notation c0 := (c0 beta emin prec).
Notation c1 := (c1 beta emin prec).
Notation half_c1 := (half_c1 beta emin prec).
Notation two_c1 := (two_c1 beta emin prec).

Notation B_UP_R := (B_UP_R beta emin prec).
Notation B_DN_R := (B_DN_R beta emin prec).

Notation C_UP_R := (C_UP_R beta emin prec).
Notation C_DN_R := (C_DN_R beta emin prec).

(* Theorem 2.1 only for c > 0 *)
(* TODO : regarder les admits *)
Theorem R2_1_UP_pos: forall c, format c -> 0 < c -> succ c <= B_UP_R c.
Proof with auto with typeclass_instances.
intros c Fc Pc.
unfold B_UP_R.
rewrite Rabs_pos_eq; [|lra].
(* succ_u is \phi in the paper *)
set (e := (round (round (succ_u * c) + eta))%R).
(* c1 is the smallest positive normalized number *)
case (Rlt_dec c c1); intro Hu_small; [|apply Rnot_lt_le in Hu_small].
{ (* denormalized numbers *)
  rewrite succ_small...
  2:{
    rewrite Rabs_pos_eq...
    lra.
  }
Admitted. (*
  rewrite <- round_small_plus_eta...
  2:{
    rewrite Rabs_pos_eq...
    lra.
  }
  apply round_le...
  apply Rplus_le_compat_l.
  unfold e.
  rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (R_eta)) at 1...
  2:{
    apply generic_format_bpow...
    simpl.
    easy.
  }
  apply round_le...
  apply Rplus_le_reg_r with (-R_eta)%R.
  field_simplify.
  rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (0)) at 1...
  2:{
    apply generic_format_0.
  }
  apply round_le...
  apply Rmult_le_pos...
  {
    unfold R_succ_u.
    apply Rle_trans with R_u; [apply bpow_ge_0|].
    apply succ_ge_id.
  }
  lra.
}
(* normalized numbers (\notin \mathbb{U} in the paper) *)
(* we don't care about the largest positive floating-point number
   since we ignore overflows *)
assert (H_2_9 : (R_u * R_ufp c < e)%R).
{
  assert (Hu_ufpc : format (R_u * R_ufp c)).
  { (* TODO *)
    admit. }
  set (c' := round_flt (R_succ_u * c)).
  assert (H_2_10 : (round_flt (R_succ_u * R_ufp c) <= c')%R).
  {
    apply round_le...  (* 1.2 in the paper *)
    apply Rmult_le_compat_l...
    {
      apply Rle_trans with R_u; [apply bpow_ge_0|apply succ_ge_id].
    }
    rewrite <- Rabs_pos_eq; [|lra].
    apply ufp_le_id...
    apply Rgt_not_eq...
  }

  case (Rle_dec R_c1 (R_ufp c * R_succ_u)%R); intros Hufp_phi_normal.
  {
    unfold eps.
    fold c'.
    apply Rlt_le_trans with (R_succ_u * R_ufp c)%R.
    {
      apply Rmult_lt_compat_r.
      {
        apply bpow_gt_0.
      }
      unfold R_succ_u.
      apply succ_gt_id.
      apply Rgt_not_eq.
      apply bpow_gt_0.
    }
    apply Rle_trans with c'.
    2:{
      rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (c')) at 1...
      2:{
        apply generic_format_round...
      }
      apply round_le...
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat_l.
      apply bpow_ge_0.
    }
    unfold c'.
    rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (R_succ_u * R_ufp c)) at 1...
    {
      apply round_le...
      apply Rmult_le_compat_l.
      {
        apply Rle_trans with R_u; [apply bpow_ge_0|apply succ_ge_id].
      }
      rewrite <- Rabs_pos_eq; [|lra].
      apply ufp_le_id...
      apply Rgt_not_eq...
    }
    (* format c -> c > 0 -> c >= R_c1 -> R_c1 <= R_ufp c * R_succ_u -> format (R_succ_u * R_ufp c) *)
    admit. (* Pas si trivial: succ_u est en exposant négatif, ufp est un exposant valide, donc on est dans le format *)
  }
  apply Rnot_le_gt in Hufp_phi_normal.
  assert (c' >= R_u * R_ufp c)%R as r211.
  {
    apply Rge_trans with (round_flt (R_succ_u * R_ufp c))%R; [apply r210|].
    rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (R_u * R_ufp c))...
    2:{
      (* format c -> c > 0 -> c >= R_c1 -> R_c1 > R_ufp c * R_succ_u -> format (R_u * R_ufp c) *)
      admit. (* Pas si trivial *)
    }
    fold round_flt.
    apply Rle_ge.
    apply round_le...
    apply Rmult_le_compat_r; [|apply succ_ge_id].
    apply Rlt_le.
    apply ufp_gt_0.
    lra.
  }
  case (Rlt_dec c' R_c1); intros Hup_small.
  {
    unfold eps.
    fold c'.
    rewrite round_small_plus_eta...
    2:{
      apply generic_format_round...
    }
    2:{
      rewrite Rabs_pos_eq; [lra|].
      unfold c'.
      rewrite <- (round_0 radix2 (FLT_exp emin prec) ZnearestE).
      apply round_le...
      apply Rmult_le_pos; [|lra].
      apply Rle_trans with R_u; [apply bpow_ge_0|apply succ_ge_id].
    }
    apply Rle_lt_trans with c'.
    {
      apply Rge_le.
      apply r211.
    }
    rewrite <- Rplus_0_r at 1.
    apply Rplus_lt_compat_l.
    apply bpow_gt_0.
  }
  apply Rnot_gt_le in Hup_small.
  apply Rle_ge in Hup_small.
  assert (R_u * R_ufp c < c')%R as r211b.
  {
    apply Rlt_le_trans with R_c1; [|lra].
    apply Rlt_trans with (R_succ_u * R_ufp c)%R...
    {
      apply Rmult_lt_compat_r; [apply ufp_gt_0; lra|apply succ_gt_id].
      apply Rgt_not_eq; apply bpow_gt_0.
    }
    apply Rgt_lt.
    rewrite Rmult_comm...
  }
  assert (c' <= eps)%R as r211c.
  {
    unfold eps.
    rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (c'))...
    2:{
      apply generic_format_round...
    }
    apply round_le...
    fold c'.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    apply bpow_ge_0.
  }
  apply Rlt_le_trans with c'...
}




apply round_N_ge_midp...
apply generic_format_succ...
rewrite pred_succ...
apply Rle_lt_trans with (c + R_u * R_ufp c)%R.
unfold R_ufp.
{
  rewrite succ_eq_pos; [|lra]...
  apply (@Rmult_le_reg_r 2 _ _ Rlt_R0_R2).
  field_simplify.
  apply Rplus_le_compat_l.
  rewrite <- Rmult_1_r at 1.
  rewrite Rmult_assoc.
  (* format c -> c > 0 -> c >= R_c1 -> R_c1 > R_ufp c * R_succ_u -> format (R_u * R_ufp c) *)
Admitted. (*
  apply Rmult_le_compat_l.
  apply ulp_ge_0.
  unfold R_u.
  unfold R_inv_u.
  rewrite <- bpow_plus.
  simpl.
  lra.
}
now apply Rplus_lt_compat_l.
Admitted. *)
*)

Theorem R2_1_DN_pos: forall c, format c -> 0 < c -> B_DN_R c <= pred c.
Proof with auto with typeclass_instances.
intros c form Hpos.
unfold B_DN_R.
set (eps := (round (round (succ_u * Rabs c) + eta))%R).
assert (u * (ufp c) < eps)%R as r209.
{
  assert (round (u * succ c) <= round (succ_u * Rabs c))%R as r14.
  {
    apply round_le...
    rewrite phi_eps.
    rewrite Rmult_assoc.
Admitted. (*
    apply Rmult_le_compat_l; [apply bpow_ge_0|].
    unfold succ.
    rewrite Rle_bool_true; [|lra]...
    rewrite Rabs_pos_eq; [|lra]...
    unfold ulp.
    rewrite Req_bool_false; [|lra]...
    field_simplify.
    rewrite (Rplus_comm (2 * c * R_u) (c)).
    apply Rplus_le_compat_l.
    rewrite <- (Rabs_pos_eq c) at 2...
    2:{
      lra.
    }
    (* format c -> c > 0 -> c >= R_c1 -> R_c1 > R_ufp c * R_succ_u -> format (R_u * R_ufp c) *)
    admit. (*
    apply bpow_cexp_u_le_eps_m_u...
    lra. *)
  }
  unfold eps.
  apply Rlt_le_trans with (round_flt (R_succ_u * Rabs c))%R.
  2:{
    rewrite <- (round_generic radix2 (FLT_exp emin prec) ZnearestE (round_flt (R_succ_u * Rabs c))) at 1...
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
  rewrite (round_generic radix2 (FLT_exp emin prec) ZnearestE (R_u * succ_flt c)%R) in r14.
  2:{
    (* format c -> c > 0 -> round radix2 (FLT_exp emin prec) ZnearestE (R_u * succ_flt c) <=
         round_flt (R_succ_u * Rabs c -> format (R_u * succ_flt c) *)
    admit. (* Puissance de 2 *)
  }
  apply Rlt_le_trans with (R_u * succ_flt c)%R...
  apply Rmult_lt_compat_l; [apply bpow_gt_0|].
  apply Rle_lt_trans with (Rabs c).
  apply ufp_le_id; [|lra]...
  rewrite !Rabs_pos_eq...
  {
    apply succ_gt_id; lra.
  }
  apply Rle_trans with c.
  lra.
  lra.
}
apply round_N_le_midp...
apply generic_format_pred...
rewrite succ_pred...
apply Ropp_lt_contravar in r209.
apply (Rplus_lt_compat_l c) in r209.
apply Rlt_le_trans with (c - R_u * R_ufp c )%R; [assumption|].
rewrite pred_eq_pos; [|lra]...
(*   (c - R_u * R_ufp c <= (pred_pos radix2 (FLT_exp emin prec) c + c) / 2)%R  *)
unfold pred_pos.
admit.
Admitted.

(* Theorem 2.1 only for c <> 0 *)
Theorem R2_1_UP: forall c, format c -> (c <> 0)%R ->
  (succ_flt c <= B_UP_R c)%R.
Proof with auto with typeclass_instances.
intros c form Hnot_zero.
case (Rle_dec 0 c); intros Hpos.
{
  apply R2_1_UP_pos...
  lra.
}
rewrite <- (Ropp_involutive c).
set (c' := (-c)%R).
assert (c' > 0)%R as Hup_pos.
{
  unfold c'.
  lra.
}
assert (format c') as Hform_up.
{
  unfold c'.
  apply generic_format_opp...
}
rewrite succ_opp.
rewrite B_UP_R_opp...
apply Ropp_le_contravar.
apply R2_1_DN_pos...
lra.
Qed.
*)

(* Theorem 2.1 only for c <> 0 *)
Theorem R2_1_DN: forall c, format c -> c <> 0 -> B_DN_R c <= pred c.
Proof with auto with typeclass_instances.
intros c form Hnot_zero.
case (Rle_dec 0 c); intros Hpos.
{
  apply R2_1_DN_pos...
  lra.
}
rewrite <- (Ropp_involutive c).
set (c' := (-c)%R).
assert (c' > 0)%R as Hup_pos.
{
  unfold c'.
  lra.
}
assert (format c') as Hform_up.
{
  unfold c'.
  apply generic_format_opp...
}
rewrite pred_opp.
rewrite B_DN_R_opp...
apply Ropp_le_contravar.
apply R2_1_UP_pos...
lra.
Qed.

(* Theorem 2.2, only for c > 0 *)
(* TODO : regarder les admits *)
Theorem R2_2_UP_pos: forall c, format c -> 0 < c ->
  (Rabs c < half_c1 \/ two_c1 < Rabs c) ->
  B_UP_R c = succ c.
Proof with auto with typeclass_instances.
intros c form Hpos Hinterval.
destruct Hinterval as [Hsubnorm|Hnorm].
{
  unfold B_UP_R.
  assert (round (succ_u * Rabs c) = 0).
  {
    case (Req_dec c 0); intros Hzero.
    {
      rewrite Hzero.
      rewrite Rabs_R0.
      rewrite Rmult_0_r.
      apply round_0...
    }
    (* format c -> c > 0 -> c < R_half_c1 -> round_flt (R_phi64 * c) = 0 *)
    admit. (* Non trivial : Arrondi vers 0 : round_N_small *)
  }
  rewrite H.
  rewrite Rplus_0_l.
  assert (round eta = eta)%R as etaForm.
  {
    apply round_generic...
    unfold eta.
    apply generic_format_bpow...
    admit. (*
    simpl; easy.
    *)
  }
  rewrite etaForm.
  rewrite round_small_plus_eta...
  {
    unfold succ.
    rewrite Rle_bool_true; [|lra]...
    apply f_equal2; [reflexivity|].
    unfold eta.
    symmetry.
    apply ulp_FLT_small...
    unfold half_c1 in Hsubnorm.
Admitted. (*
    simpl (-1074 + prec)%Z.
    apply Rlt_trans with (bpow radix2 (-1022))...
    now apply bpow_lt.
  }
  unfold R_c1.
  unfold R_half_c1 in Hsubnorm.
  apply Rlt_trans with (bpow radix2 (-1022))...
  now apply bpow_lt.
}
apply Rle_antisym; [|apply R2_1_UP]...
2:{
  lra.
}
unfold B_UP_R.
set (eps := (round_flt (round_flt (R_succ_u * Rabs c) + R_eta))%R).
assert (eps <= (5*R_u*R_ufp(c))/2)%R as r214.
{
  assert (c <= 2*(1-R_u)*R_ufp(c))%R as rbi215.
  {
    assert (c <= pred_flt(2*R_ufp(c)))%R as rbeq215.
    {
      apply pred_ge_gt...
      (* ... -> c > R_two_c1 -> format (2 * R_ufp c) *)
      admit. (* Format de ufp *)
      rewrite <- (Rabs_pos_eq c) at 1.
      apply ufp2_gt_id...
      lra.
      lra.
    }
    (* (c <= 2 * (1 - R_u) * R_ufp c)%R *)
    admit.
  }
  (* (eps <= 5 * R_u * R_ufp c / 2)%R *)
  admit. (* Non trivial *)
}
apply round_N_le_midp...
apply generic_format_succ...
assert (succ_flt c + R_u * R_ufp c <= (succ_flt c + succ_flt (succ_flt c))/2)%R as interm_ineq.
{
  set (c' := succ_flt c).
  rewrite succ_eq_pos...
  2:{
    unfold c'.
    apply Rle_trans with c.
    lra.
    apply succ_ge_id.
  }
  apply (Rplus_le_reg_r (-c')).
  field_simplify.
  unfold R_ufp.
  (* (R_u * bpow_2 (mag radix2 c - 1) <= clp_flt c' / 2)%R *)
  admit. (* Trivial *)
}
apply Rle_lt_trans with (succ_flt c + (R_u * R_ufp c)/2)%R.
{
  rewrite succ_eq_pos; [|lra].
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  (* (eps <= ulp_flt c + R_u * R_ufp c / 2)%R *)
  admit. (*
  rewrite ulp_to_ufp.
  now field_simplify. *)
}
apply Rlt_le_trans with (succ_flt c + R_u * R_ufp c)%R...
{
  apply Rplus_lt_compat_l.
  apply (Rmult_lt_reg_r 2); [lra|].
  field_simplify.
  apply Rmult_lt_compat_r; [apply ufp_gt_0; lra|].
  rewrite <- Rmult_1_l at 1; apply Rmult_lt_compat_r; [apply bpow_gt_0|].
  lra.
}
Admitted.
*)

Theorem R2_2_DN_pos: forall c, format c -> 0 < c ->
  (Rabs c < half_c1 \/ Rabs c > two_c1) ->
  B_DN_R c = pred c.
Proof with auto with typeclass_instances.
intros c form Hpos Hinterval.
destruct Hinterval as [Hsubnorm|Hnorm].
{
  unfold B_DN_R.
  assert (round (succ_u * Rabs c) = 0).
  admit.
  rewrite H.
  rewrite Rplus_0_l.
  assert (round eta = eta)%R as etaForm.
  {
    apply round_generic...
    unfold eta.
    apply generic_format_bpow...
Admitted. (*
    simpl; easy.
  }
  rewrite etaForm.
  rewrite round_small_minus_eta...
  {
    rewrite pred_eq_pos.
    assert ((c + - ulp radix2 (FLT_exp emin prec) (- c)) = (c - ulp radix2 (FLT_exp emin prec) (- c)))%R as pm_eq_m.
    {
      now unfold Rminus.
    }
    unfold pred_pos.
    case Req_bool_spec; intros Hu_bpow; apply f_equal2...
    {
      rewrite flt_mag_small...
      lra.
      unfold R_half_c1 in Hsubnorm.
      unfold R_c1.
      apply Rlt_trans with (bpow_2 (-1022))%R...
      now apply bpow_lt.
    }
    rewrite ulp_FLT_small...
    simpl (emin+prec)%Z.
    unfold R_half_c1 in Hsubnorm.
    apply Rlt_trans with (bpow radix2 (-1022))...
    now apply bpow_lt.
    lra.
    }
  unfold R_c1.
  unfold R_half_c1 in Hsubnorm.
  apply Rlt_trans with (bpow radix2 (-1022))...
  now apply bpow_lt.
}
apply Rle_antisym; [apply R2_1_DN|]...
1:{
  lra.
}
unfold B_DN_R.
set (eps := (round_flt (round_flt (R_succ_u * Rabs c) + R_eta))%R).
assert (eps <= (5*R_u*R_ufp(c))/2)%R as r214.
{
  admit. (* Non trivial *)
}
apply round_N_ge_midp...
apply generic_format_pred...
Admitted. *)

(* Theorem 2.2 *)
Theorem R2_2_UP: forall c, format c ->
  (Rabs c < half_c1 \/ Rabs c > two_c1) ->
  B_UP_R c = succ c.
Proof with auto with typeclass_instances.
intros c form Hinterval.
case (Rle_dec 0 c); intros Hpos.
{
  case (Req_dec c 0); intros Hzero.
  {
    unfold B_UP_R.
    rewrite Hzero.
    rewrite Rabs_R0.
    rewrite Rmult_0_r.
    rewrite Rplus_0_l.
    unfold round.
Admitted. (*
    rewrite round_0...
    rewrite Rplus_0_l.
    rewrite round_generic...
    2:{
      apply generic_format_round...
    }
    rewrite succ_0.
    rewrite ulp_FLT_0...
    rewrite round_generic...
    apply generic_format_bpow...
    easy.
  }
  apply R2_2_UP_pos...
  lra.
}
rewrite <- (Ropp_involutive c).
set (c' := (-c)%R).
assert (c' > 0)%R as Hup_pos.
{
  unfold c'.
  lra.
}
assert (format c') as Hform_up.
{
  unfold c'.
  apply generic_format_opp...
}
rewrite succ_opp.
rewrite B_UP_R_opp...
apply Ropp_eq_compat.
apply R2_2_DN_pos...
2:{
  lra.
}
unfold c'.
rewrite Rabs_Ropp...
Qed.
*)

Theorem R2_2_DN: forall c, format c ->
  (Rabs c < half_c1 \/ Rabs c > two_c1) ->
  B_DN_R c = pred c.
Proof with auto with typeclass_instances.
intros c form Hinterval.
case (Rle_dec 0 c); intros Hpos.
{
  apply R2_2_DN_pos...
  admit. (* Trivial *)
}
rewrite <- (Ropp_involutive c).
set (c' := (-c)%R).
assert (c' > 0)%R as Hup_pos.
{
  unfold c'.
  lra.
}
assert (format c') as Hform_up.
{
  unfold c'.
  apply generic_format_opp...
}
rewrite pred_opp.
rewrite B_DN_R_opp...
apply Ropp_eq_compat.
apply R2_2_UP_pos...
unfold c'.
rewrite Rabs_Ropp...
lra.
Admitted.

(* Theorem 2.3, première branche *)
Lemma C_UP_R_1st_spec: forall c, format c ->
  (Rabs c >= c0)%R -> round (c + round (succ_u * Rabs c)) = succ c.
Proof with auto with typeclass_instances.
intros c form Hineq.
set (eps := round (succ_u * Rabs c)).
set (csup' := succ c).
set (csup := round (c + eps)).
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
Admitted. (*
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
assert (R_u * (R_ufp c) < eps)%R as r210.
{
  assert (round_flt(R_u * succ_flt c) <= round_flt (R_succ_u * Rabs c))%R as r14.
  {
    apply round_le...
    apply Rge_le.
    rewrite phi_eps.
    assert (R_u * succ_flt c <= R_u * (c + 2 * R_u * Rabs c))%R as major_ineq.
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
          apply Rgt_not_eq.
          apply Rlt_le_trans with (R_c0).
          apply bpow_gt_0.
          lra.
        }
        unfold cexp.
        unfold R_u.
        apply Rplus_le_compat_l.
        unfold FLT_exp.
        rewrite Z.max_l.
        2:{
          (* format c -> c >= R_c0 -> emi <= mag radix2 c - prec *)
          admit. (* Non difficile *)
        }
        unfold prec.
        assert (mag radix2 c - 53 = ((mag radix2 c - 1) + (- 53 + 1)))%Z as prec_decomp.
        omega.
        rewrite prec_decomp.
        rewrite !bpow_plus.
        fold R_u.
        assert (bpow_2 1 = 2)%R as bpow1_eq_2...
        rewrite bpow1_eq_2.
        apply Rle_trans with (Rabs c * (R_u * 2))%R.
        {
          apply Rmult_le_compat_r.
          compute; lra.
          apply bpow_mag_le.
          apply Rgt_not_eq.
          apply Rge_gt_trans with (R_c0).
          rewrite Rabs_pos_eq in Hineq...
          apply bpow_gt_0.
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
          assert (mag radix2 (- c) - 1 - prec + prec + 1 = mag radix2 (- c))%Z as simp_decomp.
          omega.
          rewrite simp_decomp.
          apply mag_ge_bpow.
          simpl (-1020 - 1)%Z.
          rewrite Rabs_Ropp.
          apply Rle_trans with (bpow_2 (-969)%Z)...
          now apply bpow_le.
        }
        apply Rplus_le_reg_r with (-c)%R.
        rewrite <- Rabs_Ropp.
        rewrite Rabs_pos_eq; [|lra].
        field_simplify.
        unfold prec.
        unfold Z.sub; simpl.
        rewrite Z.add_comm.
        rewrite bpow_plus.
        fold R_u.
        rewrite mag_opp.
        unfold R_c0 in Hineq.
        assert (bpow_2 (mag radix2 c - 1) <= Rabs c)%R as Hbpow_le_abs.
        apply bpow_mag_le.
        lra.
        apply Rle_trans with (R_u * (Rabs c))%R.
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
      rewrite Req_bool_false; [|lra]...
      unfold cexp.
      unfold FLT_exp.
      rewrite Z.max_l.
      2:{
        (* (emin <= mag radix2 (- c) - prec)%Z *)
        admit. (* Plus tard, élémentaire *)
      }
      assert (mag radix2 c - 53 = ((mag radix2 c - 1) + (- 53 + 1)))%Z as prec_decomp by lia.
      rewrite mag_opp.
      unfold prec.
      rewrite prec_decomp.
      rewrite !bpow_plus.
      fold R_u.
      assert (bpow_2 1 = 2)%R as bpow1_eq_2...
      rewrite bpow1_eq_2.
      assert (bpow_2 (mag radix2 c - 1) <= Rabs c)%R as Hbpow_le_abs.
      {
        apply bpow_mag_le; lra.
      }
      rewrite (Rmult_comm (2 * R_u) (Rabs c)).
      rewrite (Rmult_comm (2) (R_u)).
      apply Rmult_le_compat_r...
      unfold R_u.
      apply Rmult_le_pos; [apply bpow_ge_0 | lra].
    }
    apply Rle_ge.
    apply Rle_trans with (R_u * (c + 2 * R_u * Rabs c))%R...
    rewrite !Rmult_assoc.
    apply Rmult_le_compat_l; [apply bpow_ge_0|].
    field_simplify.
    rewrite Rplus_comm.
    apply Rplus_le_compat_l.
    apply RRle_abs.
  }
  unfold eps.
  unfold round_flt in r14 at 1.
  rewrite (round_generic radix2 (FLT_exp emin prec) ZnearestE (R_u * succ_flt c)%R) in r14.
  2:{
    (* format c -> Rabs c >= R_c0 -> format (R_u * succ_flt c) *)
    admit. (* Puissance de 2 *)
  }
  apply Rlt_le_trans with (R_u * succ_flt c)%R...
  apply Rmult_lt_compat_l; [apply bpow_gt_0|].
  apply Rle_lt_trans with c.
  {
    apply Rle_trans with (Rabs c).
    apply ufp_le_id...
    (* c <> 0 *)
    admit.
    (* Rabs c <= c ? (c >= 0 ?) *)
    admit.
  }
  (* c < succ_flt c *)
  admit. (* ufp <= c *)
}
apply (Rplus_lt_compat_l c) in r210.
apply Rle_lt_trans with (c + R_u * R_ufp c )%R; [| assumption ].
unfold R_ufp.
case (Rle_dec 0 c); intros Hpos.
{
  rewrite succ_eq_pos...
  apply (@Rmult_le_reg_r 2 _ _ Rlt_R0_R2).
  field_simplify.
  apply Rplus_le_compat_l.
  rewrite <- Rmult_1_r at 1.
  rewrite Rmult_assoc.
  (* ((succ_flt c + c) / 2 < c + eps)%R *)
  admit. (*
  apply Rmult_le_compat_l.
  apply ulp_ge_0.
  unfold R_u.
  unfold R_inv_u.
  rewrite <- bpow_plus.
  simpl.
  lra. *)
}
apply Rnot_le_gt in Hpos.
apply (@Rmult_le_reg_r 2 _ _ Rlt_R0_R2).
field_simplify.
unfold R_u.
unfold R_inv_u.
(* ((succ_flt c + c) / 2 <= c + R_u * bpow_2 (mag radix2 c - 1))%R *)
Admitted. (*
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
Admitted. *)

(* Theorem 2.3 *)
Theorem C_UP_R_spec: forall c, format c -> C_UP_R c = succ_flt c.
Proof with auto with typeclass_instances.
intros c form.
apply FLT_format_generic in form...
destruct form as [uf H1 H2 H3] eqn:H'.
unfold C_UP_R.
case Rlt_bool_spec; intro Huc0.
{
  case Rlt_bool_spec; intro Hcu1.
  {
    rewrite round_small_plus_eta...
    2:{
      apply generic_format_FLT...
    }
    unfold succ.
    case (Rle_bool_spec); intros Hpos.
    {
      apply Rplus_eq_compat_l.
      unfold R_eta.
      symmetry.
      now apply ulp_FLT_small.
    }
    unfold pred_pos.
    case (Req_bool_spec); intros Hu_bpow; field_simplify; apply Rplus_eq_compat_l.
    {
      rewrite mag_opp.
      rewrite flt_mag_small...
      lra.
    }
    rewrite ulp_opp.
    rewrite ulp_FLT_small...
  }
  set (c' := (R_inv_u * c)%R).
  rewrite C_UP_R_1st_spec with (round_flt c').
  2:{
    apply generic_format_round...
  }
  2:{
    unfold c'.
    assert (round_flt (R_inv_u * c) = R_inv_u * c)%R as norm.
    {
      apply round_generic...
      (* format (R_inv_u * c) *)
      admit. (* Élémentaire : R_inv_u est une puissance de 2 *)
    }
    rewrite norm.
    unfold R_c0.
    unfold R_inv_u.
    apply Rle_ge.
    unfold R_c1 in Hcu1.
    rewrite Rabs_mult.
    rewrite Rabs_pos_eq at 1.
    2:{
      apply bpow_ge_0.
    }
    apply (Rmult_le_reg_l (bpow_2 (-53))%R); [apply bpow_gt_0|].
    rewrite <- Rmult_assoc.
    rewrite <- !bpow_plus.
    simpl (-53 + -969)%Z.
    simpl (-53 + 53)%Z.
    simpl (bpow radix2 0).
    rewrite Rmult_1_l.
    apply Rle_trans with (bpow radix2 (-1021)).
    now apply bpow_le.
    assumption.
  }
  (* round_flt (R_u * succ_flt (round_flt c')) = succ_flt c *)
  admit. (* Preuve Scaling, relativement trivial *)
}
apply C_UP_R_1st_spec.
apply generic_format_FLT...
now apply Rle_ge.
Admitted.
*)

(* Theorem 2.3, première branche *)
Lemma C_DN_R_1st_spec: forall c, format c ->
  (Rabs c >= c0)%R -> round (c - round (succ_u * Rabs c)) = pred c.
Proof with auto with typeclass_instances.
intros c form Hineq.
set (eps := round (succ_u * Rabs c)).
set (cinf' := pred c).
set (cinf := round (c - eps)).
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
Admitted. (*
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
assert (R_u * (R_ufp c) < eps)%R as r210.
{
  assert (R_succ_u * c >= R_u * succ_flt c)%R as r14.
  {
    assert (R_succ_u = R_u * (1 + 2 * R_u))%R.
    {
      unfold R_succ_u.
      unfold succ.
      rewrite Rle_bool_true...
      2:{
        unfold R_u.
        now apply bpow_ge_0.
      }
      unfold ulp.
      rewrite Req_bool_false...
      2:{
        unfold R_u.
        compute; lra.
      }
      unfold cexp.
      unfold R_u.
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
    assert (R_u * succ_flt c <= R_u * (1+2*R_u) * c)%R.
    {
      admit.
    }
    apply Rle_ge in H0...
  }
  unfold eps.
  admit. (* Non fini *)
}
apply Ropp_lt_contravar in r210.
apply (Rplus_lt_compat_l c) in r210.
apply Rlt_le_trans with (c - R_u * R_ufp c )%R; [assumption|].
admit.
Admitted.
*)

(* Theorem 2.3 *)
Theorem C_DN_R_spec: forall c, format c -> C_DN_R c = pred c.
Proof with auto with typeclass_instances.
intros c form.
apply FLT_format_generic in form...
destruct form as [uf H1 H2 H3].
unfold C_DN_R.
case Rlt_bool_spec; intro Huc0.
{
  case Rlt_bool_spec; intro Hcu1.
  {
Admitted.
(*
    rewrite round_small_minus_eta...
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
      assert ((c + - ulp radix2 (FLT_exp emin prec) c) = (c - ulp radix2 (FLT_exp emin prec) c))%R...
      rewrite H.
      apply f_equal2; [reflexivity|].
      unfold R_eta.
      symmetry.
      now apply ulp_FLT_small.
    }
    rewrite !Ropp_involutive.
    unfold pred_pos.
    case Req_bool_spec; intro Hbpow_u.
    {
      admit. (* Non trivial, non difficile *)
    }
    rewrite ulp_FLT_small...
  }
  set (c' := (R_inv_u * c)%R).
  rewrite C_DN_R_1st_spec with (round_flt c').
  2:{
    apply generic_format_round...
  }
  2:{
    unfold c'.
    assert (round_flt (R_inv_u * c) = R_inv_u * c)%R as norm.
    {
      apply round_generic...
      unfold R_inv_u.
      rewrite Rmult_comm.
      apply mult_bpow_pos_exact_FLT.
      apply generic_format_FLT...
      constructor 1 with uf...
      easy.
    }
    rewrite norm.
    unfold R_c0.
    unfold R_inv_u.
    apply Rle_ge.
    unfold R_c1 in Hcu1.
    assert (( bpow radix2 (-53)%Z * bpow radix2 (-969)%Z <=  bpow radix2 (-53)%Z * bpow radix2 53%Z * Rabs c)%R ->(bpow radix2 (-969)%Z <= bpow radix2 53%Z * Rabs c)%R).
    admit. (* fix that *)
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
    assert (bpow radix2 0 * Rabs c = Rabs c)%R. admit.
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
*)

End r2Preuve.
