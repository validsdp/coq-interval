Require Import Fcore_Raux.
Require Import ZArith.
Require Import Bool.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_specific_sig.

Module StdZRadix2 <: FloatCarrier.

Definition radix := radix2.
Definition radix_correct := refl_equal Lt.
Definition smantissa_type := Z.
Definition mantissa_type := positive.
Definition exponent_type := Z.

Definition MtoP := fun (m : positive) => m.
Definition PtoM := fun (m : positive) => m.
Definition MtoZ := fun (m : Z) => m.
Definition ZtoM := fun (m : Z) => m.
Definition EtoZ := fun (e : Z) => e.
Definition ZtoE := fun (e : Z) => e.

Definition exponent_zero := Z0.
Definition exponent_one := Zpos xH.
Definition exponent_neg := Zopp.
Definition exponent_add := Zplus.
Definition exponent_sub := Zminus.
Definition exponent_cmp := Zcompare.
Definition mantissa_zero := Z0.
Definition mantissa_one := xH.
Definition mantissa_add := Pplus.
Definition mantissa_sub := Pminus.
Definition mantissa_mul := Pmult.
Definition mantissa_cmp x y := Pcompare x y Eq.
Definition mantissa_pos := Zpos.
Definition mantissa_neg := Zneg.

Definition valid_mantissa := fun (m : positive) => True.

Definition mantissa_sign m :=
  match m with
  | Zneg p => Mnumber true p
  | Z0 => Mzero
  | Zpos p => Mnumber false p
  end.

Definition mantissa_even m :=
  match m with
  | xO _ => true
  | _ => false
  end.

Definition mantissa_shl m d :=
  match d with Zpos nb => iter_pos nb _ (fun x => xO x) m | _ => xH end.

Definition mantissa_scale2 (m : mantissa_type) (d : exponent_type) := (m, d).

Fixpoint digits_aux m nb { struct m } :=
  match m with
  | xH => nb
  | xO p => digits_aux p (Psucc nb)
  | xI p => digits_aux p (Psucc nb)
  end.

Definition mantissa_digits m := Zpos (digits_aux m xH).

Definition mantissa_split_div m d pos :=
  match Zdiv_eucl (Zpos m) (Zpos d) with
  | (Zpos q, r) => (q, adjust_pos r d pos)
  | _ => (xH, pos_Eq) (* dummy *)
  end.

Definition mantissa_shr_aux v :=
  match v with
  | (xO p, pos_Eq) => (p, pos_Eq)
  | (xO p, _)      => (p, pos_Lo)
  | (xI p, pos_Eq) => (p, pos_Mi)
  | (xI p, _)      => (p, pos_Up)
  | _ => (xH, pos_Eq) (* dummy *)
  end.

Definition mantissa_shr m d pos :=
  match d with
  | Zpos nb =>
    iter_pos nb _ mantissa_shr_aux (m, pos)
  | _ => (xH, pos_Eq) (* dummy *)
  end.

Definition mantissa_div := fun m d => mantissa_split_div m d pos_Eq.

Definition exponent_div2_floor n :=
  match n with
  | Z0 => (Z0, false)
  | Zpos xH => (Z0, true)
  | Zneg xH => (Zneg xH, true)
  | Zpos (xO p) => (Zpos p, false)
  | Zneg (xO p) => (Zneg p, false)
  | Zpos (xI p) => (Zpos p, true)
  | Zneg (xI p) => (Zneg (Psucc p), true)
  end.

Definition mantissa_sqrt m :=
  match Z.sqrtrem (Zpos m) with
  | (Zpos s, r) =>
    let pos :=
      match r with
      | Z0 => pos_Eq
      | Zpos r =>
        match Pcompare r s Eq with
        | Gt => pos_Up
        | _ => pos_Lo
        end
      | Zneg _ => pos_Eq (* dummy *)
      end in
    (s, pos)
  | _ => (xH, pos_Eq) (* dummy *)
  end.

Definition PtoM_correct := fun x : positive => refl_equal x.
Definition ZtoM_correct := fun x : Z => refl_equal x.
Definition ZtoE_correct := fun x : Z => refl_equal x.
Definition exponent_zero_correct := refl_equal Z0.
Definition exponent_one_correct := refl_equal 1%Z.
Definition exponent_neg_correct := fun x => refl_equal (- EtoZ x)%Z.
Definition exponent_add_correct := fun x y => refl_equal (EtoZ x + EtoZ y)%Z.
Definition exponent_sub_correct := fun x y => refl_equal (EtoZ x - EtoZ y)%Z.
Definition exponent_cmp_correct := fun x y => refl_equal (EtoZ x ?= EtoZ y)%Z.
Definition mantissa_zero_correct := refl_equal Z0.
Definition mantissa_pos_correct :=
  fun (x : positive) (_ : True) => refl_equal (Zpos x).
Definition mantissa_neg_correct :=
  fun (x : positive) (_ : True) => refl_equal (Zneg x).
Definition mantissa_one_correct := conj (refl_equal xH) I.
Definition mantissa_add_correct :=
  fun x y (_ _ : True) => conj (refl_equal (MtoP x + MtoP y)%positive) I.
Definition mantissa_sub_correct :=
  fun x y (_ _ : True) (_ : (MtoP y < MtoP x)%positive) => conj (refl_equal (MtoP x - MtoP y)%positive) I.
Definition mantissa_mul_correct :=
  fun x y (Hx Hy : True) => conj (refl_equal (MtoP x * MtoP y)%positive) I.
Definition mantissa_cmp_correct :=
  fun x y (Hx Hy : True) => refl_equal (Zpos (MtoP x) ?= Zpos (MtoP y))%Z.
Definition mantissa_even_correct :=
  fun x (_ : True) => refl_equal (Zeven (Zpos x)).

Lemma mantissa_sign_correct :
  forall x,
  match mantissa_sign x with
  | Mzero => MtoZ x = Z0
  | Mnumber s p => MtoZ x = (if s then Zneg else Zpos) (MtoP p) /\ valid_mantissa p
  end.
intros.
case x ; repeat split.
Qed.

Lemma mantissa_digits_correct :
  forall x, valid_mantissa x ->
  EtoZ (mantissa_digits x) = Zpos (count_digits radix (MtoP x)).
Proof.
intros x _.
rewrite <- digits_conversion.
rewrite <- Fcalc_digits.Z_of_nat_S_digits2_Pnat.
unfold EtoZ, mantissa_digits, MtoP.
rewrite inj_S.
unfold Zsucc.
generalize xH.
induction x ; intros p.
simpl digits_aux.
simpl Fcore_digits.digits2_Pnat.
rewrite inj_S.
unfold Zsucc.
rewrite <- Zplus_assoc.
now rewrite <- Zpos_plus_distr, <- Pplus_one_succ_l.
simpl digits_aux.
simpl Fcore_digits.digits2_Pnat.
rewrite inj_S.
unfold Zsucc.
rewrite <- Zplus_assoc.
now rewrite <- Zpos_plus_distr, <- Pplus_one_succ_l.
apply refl_equal.
Qed.

Lemma mantissa_scale2_correct :
  forall x d, valid_mantissa x ->
  let (x',d') := mantissa_scale2 x d in
  (Z2R (Zpos (MtoP x')) * bpow radix (EtoZ d') = Z2R (Zpos (MtoP x)) * bpow radix2 (EtoZ d))%R /\
  valid_mantissa x'.
Proof.
now intros x d Vx.
Qed.

Lemma mantissa_shl_correct :
  forall x y z, valid_mantissa y ->
  z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x /\
  valid_mantissa (mantissa_shl y z).
Proof.
repeat split.
unfold EtoZ in H0.
rewrite H0.
apply refl_equal.
Qed.

Lemma mantissa_shr_correct :
  forall x y z k, valid_mantissa y -> EtoZ z = Zpos x ->
  (Zpos (shift radix 1 x) <= Zpos (MtoP y))%Z ->
  let (sq,l) := mantissa_shr y z k in
  let (q,r) := Zdiv_eucl (Zpos (MtoP y)) (Zpos (shift radix 1 x)) in
  Zpos (MtoP sq) = q /\
  l = adjust_pos r (shift radix 1 x) k /\
  valid_mantissa sq.
Proof.
intros x y z k _ Ezx.
destruct z as [|z|z] ; try easy.
injection Ezx.
clear Ezx.
unfold MtoP.
intros -> Hy.
unfold mantissa_shr.
rewrite Pos2Nat.inj_iter.
case_eq (nat_iter (Pos.to_nat x) mantissa_shr_aux (y, k)).
intros sq l H1.
generalize (Z.div_str_pos _ _ (conj (refl_equal Lt : (0 < Zpos _)%Z) Hy)).
generalize (Z_div_mod (Z.pos y) (Z.pos (shift radix 1 x)) (eq_refl Gt)).
unfold Zdiv.
case Z.div_eucl.
intros q r [H2 H3] H4.
refine ((fun H => conj (proj1 H) (conj (proj2 H) I)) _).
revert H2 H3 Hy.
change (adjust_pos r (shift radix 1 x) k) with
  (match Z.pos (shift radix 1 x) with Zpos v => adjust_pos r v k | _ => l end).
rewrite shift_correct.
rewrite Zpower_pos_nat.
rewrite Zmult_1_l.
revert sq l q r H1 H4.
induction (Pos.to_nat x) as [|p IHp].
- change (Zpower_nat radix 0) with 1%Z.
  intros sq l q r.
  rewrite Zmult_1_l.
  simpl.
  intros H1.
  injection H1.
  intros <- <-.
  clear H1.
  intros _ H1 H2.
  revert H1.
  assert (H: r = 0%Z) by omega.
  rewrite H, Zplus_0_r.
  split.
  exact H1.
  now destruct k.
- intros sq' l' q' r'.
  simpl nat_iter.
  destruct (nat_iter p mantissa_shr_aux (y, k)) as [sq l].
  specialize (IHp sq l).
  intros H1 H0 H2 H3 Hy.
  revert H2.
  generalize (Zle_lt_trans _ _ _ (proj1 H3) (proj2 H3)).
  case_eq (Zpower_nat radix (S p)) ; try easy.
  intros m'.
  revert H3.
  rewrite Zpower_nat_succ_r.
  revert IHp.
  destruct (Zpower_nat radix p) as [|m|m] ; try easy.
  intros IHp H3 H4 _ H2.
  injection H4.
  intros <-.
  clear H4.
  change (radix_val radix) with 2%Z in H3.
  change (Zpos (xO m)) with (2 * Zpos m)%Z in H2.
  destruct (Zle_or_lt (Zpos m) r') as [Hr|Hr].
  + destruct (IHp (2 * q' + 1)%Z (r' - Zpos m)%Z) as [H4 H5].
    reflexivity.
    clear -H0 ; omega.
    rewrite H2.
    ring.
    clear -Hr H3 ; omega.
    rewrite H2.
    rewrite <- (Zplus_0_l (Zpos m)) at 1.
    apply Zplus_le_compat with (2 := Hr).
    apply Zmult_le_0_compat.
    clear -H3 ; omega.
    now apply Zlt_le_weak.
    clear IHp.
    destruct q' as [|q'|q'] ; try easy.
    clear H0.
    destruct sq as [sq|sq|] ; try easy.
    simpl in H1.
    simpl in H4.
    split.
    injection H4.
    intros <-.
    apply f_equal, sym_eq.
    now destruct l ; injection H1.
    clear H4.
    unfold adjust_pos.
    destruct r' as [|r'|r'] ; try now elim Hr.
    apply sym_eq.
    replace l' with (match l with pos_Eq => pos_Mi | _ => pos_Up end).
    2: clear -H1 ; destruct l ; injection H1 ; easy.
    rewrite H5.
    clear H1 H5.
    destruct (Zcompare_spec (Zpos r') (Zpos m)) as [H|H|H].
    * elim Hr.
      now apply Zcompare_Gt.
    * rewrite (Zeq_minus _ _ H).
      simpl.
      case k ; try easy ; case m ; easy.
    * assert (H': (Zpos r' - Zpos m)%Z = Zpos (r' - m)) by now apply Z.pos_sub_gt.
      rewrite H'.
      unfold adjust_pos.
      clear -H H3.
      destruct m as [m|m|] ;
        case Zcompare ; try easy ; try (case k ; easy).
      clear -H3 H ; omega.
  + destruct (IHp (2 * q')%Z r') as [H4 H5].
    reflexivity.
    clear -H0 ; omega.
    rewrite H2.
    ring.
    clear -Hr H3 ; omega.
    rewrite H2.
    rewrite <- (Zplus_0_r (Zpos m)) at 1.
    apply Zplus_le_compat with (2 := proj1 H3).
    apply Zle_0_minus_le.
    replace (2 * Zpos m * q' - Zpos m)%Z with (Zpos m * (2 * q' - 1))%Z by ring.
    apply Zmult_le_0_compat.
    easy.
    clear -H0 ; omega.
    clear IHp.
    destruct q' as [|q'|q'] ; try easy.
    clear H0.
    destruct sq as [sq|sq|] ; try easy.
    simpl in H1.
    simpl in H4.
    split.
    injection H4.
    intros <-.
    apply f_equal, sym_eq.
    now destruct l ; injection H1.
    clear H4.
    unfold adjust_pos.
    apply sym_eq.
    replace l' with (match l with pos_Eq => pos_Eq | _ => pos_Lo end).
    2: clear -H1 ; destruct l ; injection H1 ; easy.
    rewrite H5.
    clear H1 H5.
    destruct r' as [|r'|r'] ; try now elim (proj1 H3).
    case k ; try easy ; case m ; easy.
    rewrite Zcompare_Lt with (1 := Hr).
    unfold adjust_pos.
    destruct m.
    case Zcompare ; try easy ; case k ; easy.
    case Zcompare ; try easy ; case k ; easy.
    now rewrite Hr.
Qed.

Lemma mantissa_div_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  (Zpos (MtoP y) <= Zpos (MtoP x))%Z ->
  let (q,l) := mantissa_div x y in
  Zpos (MtoP q) = (Zpos (MtoP x) / Zpos (MtoP y))%Z /\
  Fcalc_bracket.inbetween_int (Zpos (MtoP q)) (Z2R (Zpos (MtoP x)) / Z2R (Zpos (MtoP y)))%R (convert_location_inv l) /\
  valid_mantissa q.
Proof.
intros x y _ _.
unfold MtoP.
intros Hxy.
unfold mantissa_div, mantissa_split_div.
generalize (Z_div_mod (Z.pos x) (Z.pos y) (eq_refl Gt)).
destruct Z.div_eucl as [q r].
intros [H1 H2].
assert (H: (0 < q)%Z).
  apply Zmult_lt_reg_r with (Zpos y).
  easy.
  rewrite Zmult_0_l, Zmult_comm.
  apply Zplus_lt_reg_r with r.
  rewrite Zplus_0_l.
  rewrite <- H1.
  now apply Zlt_le_trans with (2 := Hxy).
destruct q as [|q|q] ; try easy.
clear H Hxy.
assert (Hq := Zdiv_unique _ _ _ _ H2 H1).
refine (conj Hq (conj _ I)).
unfold Fcalc_bracket.inbetween_int.
destruct (Zle_or_lt 2 (Zpos y)) as [Hy|Hy].
- assert (H: (1 < Zpos y)%Z) by now apply Zgt_lt, Zle_succ_gt.
  rewrite adjust_pos_correct by assumption.
  rewrite Z2R_plus.
  simpl (Z2R 1).
  rewrite <- (Rinv_r (Z2R (Zpos y))) by now apply (Z2R_neq _ 0).
  apply Fcalc_bracket.new_location_correct ; try assumption.
  now apply Rinv_0_lt_compat, (Z2R_lt 0).
  apply Fcalc_bracket.inbetween_Exact.
  rewrite H1, Z2R_plus, Z2R_mult.
  field.
  now apply (Z2R_neq _ 0).
- rewrite Hq, H1.
  clear H1 Hq.
  cut (Zpos y = 1 /\ r = 0)%Z.
  2: omega.
  clear.
  intros [-> ->].
  simpl.
  apply Fcalc_bracket.inbetween_Exact.
  unfold Rdiv.
  now rewrite Zdiv_1_r, Rinv_1, Rmult_1_r.
Qed.

End StdZRadix2.
