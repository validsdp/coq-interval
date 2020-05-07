From Coq Require Import ZArith Int63 Floats Psatz.
From Flocq Require Import Raux.
From Bignums Require Import BigZ.

Require Import Xreal.
Require Import Basic.
Require Import Sig.
Require Import Interval.Interval.  (* for le_upper/lower, TODO PR: move them? *)

Require Import Specific_bigint.
Require Import Specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.PrimitiveFloats.NativeLayer.
Require Import Flocq.Prop.Mult_error.

Module PrimitiveFloat <: FloatOps.

Definition radix := radix2.
Definition sensible_format := true.

Definition type := PrimFloat.float.

Definition bigZ_of_int x := BigZ.Pos (BigN.N0 x).

Definition toF x : float radix2 :=
  match Prim2SF x with
  | S754_zero _ => Fzero
  | S754_infinity _ | S754_nan => Basic.Fnan
  | S754_finite s m e => Basic.Float s m e
  end.

Definition precision := SFBI2.precision.
Definition sfactor := SFBI2.sfactor.
Definition prec := SFBI2.prec.
Definition PtoP := SFBI2.PtoP.
Definition ZtoS := SFBI2.ZtoS.
Definition StoZ := SFBI2.StoZ.
Definition incr_prec := SFBI2.incr_prec.

Definition zero := zero.
Definition one := one.
Definition nan := nan.

Definition fromZ_default default x :=
  match x with
  | Z0 => zero
  | Zpos x =>
    match (x ?= 9007199254740992)%positive (* 2^53 *) with
    | Lt => of_int63 (Int63.of_pos x)
    | _ => default
    end
  | Zneg x =>
    match (x ?= 9007199254740992)%positive (* 2^53 *) with
    | Lt => (-(of_int63 (Int63.of_pos x)))%float
    | _ => default
    end
  end.

Definition fromZ := fromZ_default nan.

Definition fromZ_UP (p : precision) := fromZ_default infinity.

Definition fromZ_DN (p : precision) := fromZ_default neg_infinity.

Definition fromF (f : float radix) :=
  match f with
  | Basic.Fnan => nan
  | Basic.Fzero => zero
  | Basic.Float s m e =>
    if ((e <=? 971)%Z && (-1074 <=? e)%Z
        && (Pos.size m <=? 53)%positive)%bool then
      let m := of_int63 (Int63.of_pos m) in
      let e := Int63.of_Z (e + FloatOps.shift) in
      let f := ldshiftexp m e in
      if s then (- f)%float else f
    else nan
  end.

Definition classify x :=
  match classify x with
  | NaN => Sig.Fnan
  | PInf => Fpinfty
  | NInf => Fminfty
  | _ => Freal
  end.

Definition real x :=
  match PrimFloat.classify x with
  | PInf | NInf | NaN => false
  | _ => true
  end.

Definition is_nan x :=
  match PrimFloat.classify x with
  | NaN => true
  | _ => false
  end.

Definition bigZ_shift := Eval vm_compute in BigZ.of_Z FloatOps.shift.

Definition mag x :=
  let (_, e) := PrimFloat.frshiftexp x in
  ((BigZ.Pos (BigN.N0 e)) - bigZ_shift)%bigZ.

Definition valid_ub x := negb (x == neg_infinity)%float.

Definition valid_lb x := negb (x == infinity)%float.

Definition Xcomparison_of_float_comparison c :=
  match c with
  | FEq => Xeq
  | FLt => Xlt
  | FGt => Xgt
  | FNotComparable => Xund
  end.

Definition cmp x y := Xcomparison_of_float_comparison (compare x y).

Definition min x y :=
  match (x ?= y)%float with
  | FEq | FLt => x
  | FGt => y
  | FNotComparable => nan
  end.

Definition max x y :=
  match (x ?= y)%float with
  | FEq | FGt => x
  | FLt => y
  | FNotComparable => nan
  end.

Definition neg x := (- x)%float.

Definition abs x := abs x.

Definition scale x e :=
  match e with
  | BigZ.Pos (BigN.N0 e') => ldshiftexp x (e' + Int63.of_Z FloatOps.shift)%int63
  | BigZ.Neg (BigN.N0 e') => ldshiftexp x (-e' + Int63.of_Z FloatOps.shift)%int63
  | _ => nan
  end.

Definition div2 x := (x / 2)%float.

Definition add_UP (_ : precision) x y := next_up (x + y).

Definition add_DN (_ : precision) x y := next_down (x + y).

Definition sub_UP (_ : precision) x y := next_up (x - y).

Definition sub_DN (_ : precision) x y := next_down (x - y).

Definition mul_UP (_ : precision) x y := next_up (x * y).

Definition mul_DN (_ : precision) x y := next_down (x * y).

Definition div_UP (_ : precision) x y := next_up (x / y).

Definition div_DN (_ : precision) x y := next_down (x / y).

Definition sqrt_UP (_ : precision) x := next_up (PrimFloat.sqrt x).

Definition sqrt_DN (_ : precision) x := next_down (PrimFloat.sqrt x).

Definition nearbyint_UP (mode : rounding_mode) (x : type) := nan.  (* TODO *)

Definition nearbyint_DN (mode : rounding_mode) (x : type) := nan.  (* TODO *)

Definition midpoint (x y : type) :=
  let z := ((x + y) / 2)%float in
  if is_infinity z then (x / 2 + y / 2)%float else z.

Definition toX x := FtoX (toF x).
Definition toR x := proj_val (toX x).

Lemma zero_correct : toX zero = Xreal 0.
Proof. reflexivity. Qed.

Lemma one_correct : toX one = Xreal 1.
Proof. compute; apply f_equal; field. Qed.

Lemma nan_correct : classify nan = Sig.Fnan.
Proof. reflexivity. Qed.

Lemma fromZ_correct :
  forall n,
  (Z.abs n <= 256)%Z -> toX (fromZ n) = Xreal (IZR n).
Proof.
intros [ |p|p] Hp; unfold fromZ, fromZ_default; [now simpl| | ].
{ case Pos.compare_spec; intro Hp'.
  { now revert Hp; rewrite Hp'. }
  { unfold toX, toF.
    rewrite of_int63_spec.
    unfold of_pos; rewrite of_pos_rec_spec; [ |now simpl].
    replace (_ mod _)%Z with (Z.pos p).
    2:{ symmetry; apply Zmod_small; split; [now simpl| ].
      simpl; unfold Z.pow_pos; simpl.
      apply Pos2Z.pos_lt_pos.
      now apply (Pos.lt_trans _ _ _ Hp'). }
    rewrite (SpecLayer.binary_normalize_equiv prec_gt_0 Hmax).
    generalize
      (binary_normalize_correct
         _ _ prec_gt_0 Hmax mode_NE (Z.pos p) 0 false).
    rewrite Generic_fmt.round_generic.
    2:{ apply Generic_fmt.valid_rnd_N. }
    2:{ apply FLT.generic_format_FLT.
      set (f := Defs.Float _ _ _).
      apply (FLT.FLT_spec _ _ _ _ f); [reflexivity| |now simpl].
      revert Hp; simpl; intro Hp.
      now apply (Z.le_lt_trans _ _ _ Hp). }
    unfold Defs.F2R; simpl.
    rewrite Rmult_1_r.
    replace (Rlt_bool _ _) with true.
    2:{ symmetry; apply Rlt_bool_true.
      rewrite Rabs_pos_eq; [ |now apply IZR_le].
      apply IZR_lt.
      revert Hp; simpl; intro Hp.
      now apply (Z.le_lt_trans _ _ _ Hp). }
    intros [Bp [Fp _]]; revert Bp Fp.
    case FF2B; simpl; [now intros _ ->|now simpl..| ].
    intros s m e _ <- _.
    unfold Defs.F2R; simpl; unfold FtoR.
    now case e, s; simpl; try rewrite Rmult_1_r; try rewrite <-mult_IZR. }
  lia. }
case Pos.compare_spec; intro Hp'.
{ now revert Hp; rewrite Hp'. }
{ unfold toX, toF.
  rewrite opp_spec.
  rewrite of_int63_spec.
  unfold of_pos; rewrite of_pos_rec_spec; [ |now simpl].
  replace (_ mod _)%Z with (Z.pos p).
  2:{ symmetry; apply Zmod_small; split; [now simpl| ].
    simpl; unfold Z.pow_pos; simpl.
    apply Pos2Z.pos_lt_pos.
    now apply (Pos.lt_trans _ _ _ Hp'). }
  rewrite (SpecLayer.binary_normalize_equiv prec_gt_0 Hmax).
  generalize
    (binary_normalize_correct
       _ _ prec_gt_0 Hmax mode_NE (Z.pos p) 0 false).
  rewrite Generic_fmt.round_generic.
  2:{ apply Generic_fmt.valid_rnd_N. }
  2:{ apply FLT.generic_format_FLT.
    set (f := Defs.Float _ _ _).
    apply (FLT.FLT_spec _ _ _ _ f); [reflexivity| |now simpl].
    revert Hp; simpl; intro Hp.
    now apply (Z.le_lt_trans _ _ _ Hp). }
  unfold Defs.F2R; simpl.
  rewrite Rmult_1_r.
  replace (Rlt_bool _ _) with true.
  2:{ symmetry; apply Rlt_bool_true.
    rewrite Rabs_pos_eq; [ |now apply IZR_le].
    apply IZR_lt.
    revert Hp; simpl; intro Hp.
    now apply (Z.le_lt_trans _ _ _ Hp). }
  intros [Bp [Fp _]]; revert Bp Fp.
  case FF2B; simpl; [ |now simpl..| ].
  { intros _ H; destruct (Qreals.IZR_nz _ (eq_sym H)). }
  change (IZR (Z.neg p)) with (- IZR (Z.pos p))%R.
  intros s m e _ <- _.
  unfold Defs.F2R; simpl; unfold FtoR.
  case e, s; simpl; try rewrite Rmult_1_r;
    try rewrite Ropp_mult_distr_l;
    try rewrite <-mult_IZR;
    try rewrite <-opp_IZR;
    try (now simpl).
    try (now simpl; rewrite <-mult_IZR).
    now rewrite <-mult_IZR. }
lia.
Qed.

Lemma fromZ_UP_correct :
  forall p n,
  valid_ub (fromZ_UP p n) = true /\ le_upper (Xreal (IZR n)) (toX (fromZ_UP p n)).
Proof.
intros prec [ |p|p]; unfold fromZ_UP, fromZ_default.
{ now compute; split; [ |right]. }
{ case Pos.compare_spec; intro Hp.
  { now compute. }
  { unfold toX, toF.
    rewrite <-(SF2Prim_Prim2SF (of_int63 (of_pos p))) at 1.
    rewrite of_int63_spec.
    unfold of_pos; rewrite of_pos_rec_spec; [ |now simpl].
    replace (_ mod _)%Z with (Z.pos p).
    2:{ symmetry; apply Zmod_small; split; [now simpl| ].
      simpl; unfold Z.pow_pos; simpl.
      apply Pos2Z.pos_lt_pos.
      now apply (Pos.lt_trans _ _ _ Hp). }
    rewrite (SpecLayer.binary_normalize_equiv prec_gt_0 Hmax).
    generalize
      (binary_normalize_correct
         _ _ prec_gt_0 Hmax mode_NE (Z.pos p) 0 false).
    rewrite Generic_fmt.round_generic.
    2:{ apply Generic_fmt.valid_rnd_N. }
    2:{ apply FLT.generic_format_FLT.
      set (f := Defs.Float _ _ _).
      apply (FLT.FLT_spec _ _ _ _ f); [reflexivity| |now simpl].
      revert Hp; simpl; intro Hp.
      now apply (Z.lt_le_trans _ _ _ (Pos2Z.pos_lt_pos _ _ Hp)). }
    unfold Defs.F2R; simpl.
    rewrite Rmult_1_r.
    replace (Rlt_bool _ _) with true.
    2:{ symmetry; apply Rlt_bool_true.
      rewrite Rabs_pos_eq; [ |now apply IZR_le].
      apply IZR_lt.
      revert Hp; simpl; intro Hp.
      now apply (Z.lt_le_trans _ _ _ (Pos2Z.pos_lt_pos _ _ Hp)). }
    intros [Bp [Fp _]]; revert Bp Fp.
    case FF2B; [ |now simpl..| ].
    { now intros [ | ] <- _; (compute; split; [ |right]). }
    intros s m e He.
    unfold valid_ub.
    rewrite eqb_spec.
    rewrite Prim2SF_SF2Prim; [ |now apply valid_binary_B2SF].
    intros <- _; simpl.
    split; [now compute| ].
    unfold Defs.F2R; simpl; unfold FtoR.
    now case e, s; simpl; try rewrite Rmult_1_r; try rewrite <-mult_IZR;
      apply Rle_refl. }
  now split. }
case Pos.compare_spec; intro Hp.
{ now compute. }
{ unfold toX, toF.
  rewrite <-(SF2Prim_Prim2SF (of_int63 (of_pos p))) at 1.
  rewrite opp_spec.
  rewrite of_int63_spec.
  unfold of_pos; rewrite of_pos_rec_spec; [ |now simpl].
  replace (_ mod _)%Z with (Z.pos p).
  2:{ symmetry; apply Zmod_small; split; [now simpl| ].
    simpl; unfold Z.pow_pos; simpl.
    apply Pos2Z.pos_lt_pos.
    now apply (Pos.lt_trans _ _ _ Hp). }
  rewrite (SpecLayer.binary_normalize_equiv prec_gt_0 Hmax).
  generalize
    (binary_normalize_correct
       _ _ prec_gt_0 Hmax mode_NE (Z.pos p) 0 false).
  rewrite Generic_fmt.round_generic.
  2:{ apply Generic_fmt.valid_rnd_N. }
  2:{ apply FLT.generic_format_FLT.
    set (f := Defs.Float _ _ _).
    apply (FLT.FLT_spec _ _ _ _ f); [reflexivity| |now simpl].
    revert Hp; simpl; intro Hp.
    now apply (Z.lt_le_trans _ _ _ (Pos2Z.pos_lt_pos _ _ Hp)). }
  unfold Defs.F2R; simpl.
  rewrite Rmult_1_r.
  replace (Rlt_bool _ _) with true.
  2:{ symmetry; apply Rlt_bool_true.
    rewrite Rabs_pos_eq; [ |now apply IZR_le].
    apply IZR_lt.
    revert Hp; simpl; intro Hp.
    now apply (Z.lt_le_trans _ _ _ (Pos2Z.pos_lt_pos _ _ Hp)). }
  intros [Bp [Fp _]]; revert Bp Fp.
  change (IZR (Z.neg p)) with (- IZR (Z.pos p))%R.
  case FF2B; [ |now simpl..| ].
  { now intros [ | ] <- _; (compute; split; [ |right]);
      try change R0 with 0%R; try rewrite Ropp_0. }
  intros s m e He.
  unfold valid_ub.
  rewrite eqb_spec, opp_spec.
  rewrite Prim2SF_SF2Prim; [ |now apply valid_binary_B2SF].
  intros <- _; simpl.
  split; [now compute| ].
  unfold Defs.F2R; simpl; unfold FtoR.
  case e, s; simpl; try rewrite Rmult_1_r; try rewrite <-mult_IZR;
    try rewrite Ropp_mult_distr_l;
    try rewrite <-mult_IZR;
    try rewrite <-opp_IZR;
    try (now simpl);
    try (now simpl; rewrite <-mult_IZR);
    try simpl;
    try apply Rle_refl.
  case Z.pow_pos; try rewrite Ropp_0; simpl; try apply Rle_refl;
    try (intro m'; apply Rle_refl).
  case Z.pow_pos; try rewrite Ropp_0; simpl; try apply Rle_refl;
    try (intro m'; apply Rle_refl). }
now split.
Qed.

Lemma fromZ_DN_correct :
  forall p n,
  valid_lb (fromZ_DN p n) = true /\ le_lower (toX (fromZ_DN p n)) (Xreal (IZR n)).
Proof.
intros prec [ |p|p]; unfold fromZ_DN, fromZ_default.
{ now compute; split; [ |right]. }
{ case Pos.compare_spec; intro Hp.
  { now compute. }
  { unfold toX, toF.
    rewrite <-(SF2Prim_Prim2SF (of_int63 (of_pos p))) at 1.
    rewrite of_int63_spec.
    unfold of_pos; rewrite of_pos_rec_spec; [ |now simpl].
    replace (_ mod _)%Z with (Z.pos p).
    2:{ symmetry; apply Zmod_small; split; [now simpl| ].
      simpl; unfold Z.pow_pos; simpl.
      apply Pos2Z.pos_lt_pos.
      now apply (Pos.lt_trans _ _ _ Hp). }
    rewrite (SpecLayer.binary_normalize_equiv prec_gt_0 Hmax).
    generalize
      (binary_normalize_correct
         _ _ prec_gt_0 Hmax mode_NE (Z.pos p) 0 false).
    rewrite Generic_fmt.round_generic.
    2:{ apply Generic_fmt.valid_rnd_N. }
    2:{ apply FLT.generic_format_FLT.
      set (f := Defs.Float _ _ _).
      apply (FLT.FLT_spec _ _ _ _ f); [reflexivity| |now simpl].
      revert Hp; simpl; intro Hp.
      now apply (Z.lt_le_trans _ _ _ (Pos2Z.pos_lt_pos _ _ Hp)). }
    unfold Defs.F2R; simpl.
    rewrite Rmult_1_r.
    replace (Rlt_bool _ _) with true.
    2:{ symmetry; apply Rlt_bool_true.
      rewrite Rabs_pos_eq; [ |now apply IZR_le].
      apply IZR_lt.
      revert Hp; simpl; intro Hp.
      now apply (Z.lt_le_trans _ _ _ (Pos2Z.pos_lt_pos _ _ Hp)). }
    intros [Bp [Fp _]]; revert Bp Fp.
    case FF2B; [ |now simpl..| ].
    { now intros [ | ] <- _; (compute; split; [ |right]). }
    intros s m e He.
    unfold valid_lb.
    rewrite eqb_spec.
    rewrite Prim2SF_SF2Prim; [ |now apply valid_binary_B2SF].
    intros <- _; simpl.
    split; [now compute| ].
    unfold Defs.F2R; simpl; unfold FtoR.
    now case e, s; simpl; try rewrite Rmult_1_r; try rewrite <-mult_IZR;
      apply Rle_refl. }
  now split. }
case Pos.compare_spec; intro Hp.
{ now compute. }
{ unfold toX, toF.
  rewrite <-(SF2Prim_Prim2SF (of_int63 (of_pos p))) at 1.
  rewrite opp_spec.
  rewrite of_int63_spec.
  unfold of_pos; rewrite of_pos_rec_spec; [ |now simpl].
  replace (_ mod _)%Z with (Z.pos p).
  2:{ symmetry; apply Zmod_small; split; [now simpl| ].
    simpl; unfold Z.pow_pos; simpl.
    apply Pos2Z.pos_lt_pos.
    now apply (Pos.lt_trans _ _ _ Hp). }
  rewrite (SpecLayer.binary_normalize_equiv prec_gt_0 Hmax).
  generalize
    (binary_normalize_correct
       _ _ prec_gt_0 Hmax mode_NE (Z.pos p) 0 false).
  rewrite Generic_fmt.round_generic.
  2:{ apply Generic_fmt.valid_rnd_N. }
  2:{ apply FLT.generic_format_FLT.
    set (f := Defs.Float _ _ _).
    apply (FLT.FLT_spec _ _ _ _ f); [reflexivity| |now simpl].
    revert Hp; simpl; intro Hp.
    now apply (Z.lt_le_trans _ _ _ (Pos2Z.pos_lt_pos _ _ Hp)). }
  unfold Defs.F2R; simpl.
  rewrite Rmult_1_r.
  replace (Rlt_bool _ _) with true.
  2:{ symmetry; apply Rlt_bool_true.
    rewrite Rabs_pos_eq; [ |now apply IZR_le].
    apply IZR_lt.
    revert Hp; simpl; intro Hp.
    now apply (Z.lt_le_trans _ _ _ (Pos2Z.pos_lt_pos _ _ Hp)). }
  intros [Bp [Fp _]]; revert Bp Fp.
  change (IZR (Z.neg p)) with (- IZR (Z.pos p))%R.
  case FF2B; [ |now simpl..| ].
  { now intros [ | ] <- _; (compute; split; [ |right]);
      try change R0 with 0%R; try rewrite Ropp_involutive, Ropp_0. }
  intros s m e He.
  unfold valid_lb.
  rewrite eqb_spec, opp_spec.
  rewrite Prim2SF_SF2Prim; [ |now apply valid_binary_B2SF].
  intros <- _; simpl.
  split; [now compute| ].
  unfold Defs.F2R; simpl; unfold FtoR.
  case e, s; simpl; try rewrite Rmult_1_r; try rewrite <-mult_IZR;
    try rewrite Ropp_mult_distr_l;
    try rewrite <-mult_IZR;
    try rewrite <-opp_IZR;
    try (now simpl);
    try (now simpl; rewrite <-mult_IZR);
    try simpl;
    try apply Rle_refl.
  case Z.pow_pos; try rewrite Ropp_0; simpl; try apply Rle_refl;
    try (intro m'; apply Rle_refl).
  case Z.pow_pos; try rewrite Ropp_0; simpl; try apply Rle_refl;
    try (intro m'; apply Rle_refl). }
now split.
Qed.

Lemma classify_correct :
  forall f, real f = match classify f with Freal => true | _ => false end.
Proof. now intro f; unfold real, classify; case PrimFloat.classify. Qed.

Lemma real_correct :
  forall f, real f = match toX f with Xnan => false | _ => true end.
Proof.
intro f.
unfold real.
rewrite classify_spec.
unfold SF64classify, SFclassify.
unfold toX, toF, FtoX.
case Prim2SF; [now intros [ | ]..|reflexivity| ].
now intros [ | ] m e; case Pos.eqb.
Qed.

Lemma is_nan_correct :
  forall f, is_nan f = match classify f with Sig.Fnan => true | _ => false end.
Proof. now intro f; unfold is_nan, classify; case PrimFloat.classify. Qed.

Lemma valid_lb_correct :
  forall f, valid_lb f = match classify f with Fpinfty => false | _ => true end.
Proof.
intro f.
unfold valid_lb.
rewrite eqb_spec.
unfold classify.
rewrite classify_spec.
unfold SF64classify, SFclassify.
case Prim2SF; [now intros [ | ]..|now simpl| ].
now intros [ | ] m e; case Pos.eqb.
Qed.

Lemma valid_ub_correct :
  forall f, valid_ub f = match classify f with Fminfty => false | _ => true end.
Proof.
intro f.
unfold valid_ub.
rewrite eqb_spec.
unfold classify.
rewrite classify_spec.
unfold SF64classify, SFclassify.
case Prim2SF; [now intros [ | ]..|now simpl| ].
now intros [ | ] m e; case Pos.eqb.
Qed.

Lemma cmp_correct :
  forall x y,
  cmp x y =
  match classify x, classify y with
  | Sig.Fnan, _ | _, Sig.Fnan => Xund
  | Fminfty, Fminfty => Xeq
  | Fminfty, _ => Xlt
  | _, Fminfty => Xgt
  | Fpinfty, Fpinfty => Xeq
  | _, Fpinfty => Xlt
  | Fpinfty, _ => Xgt
  | Freal, Freal => Xcmp (toX x) (toX y)
  end.
Proof.
intros x y.
unfold cmp.
rewrite compare_spec.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
rewrite <-!(B2SF_Prim2B nan_pl).
set (fx := Prim2B _ x).
set (fy := Prim2B _ y).
rewrite SpecLayer.SFcompare_Bcompare.
generalize (Bcompare_correct _ _ fx fy).
case fx; [intros [ | ]..|intros [ | ] plx|intros [ | ] mx ex Hx];
  (case fy; [intros [ | ]..|intros [ | ] ply|intros [ | ] my ey Hy]);
  intro Hcmp;
  try rewrite (Hcmp eq_refl eq_refl);
  simpl; unfold Defs.F2R; simpl;
  try rewrite !FtoR_split;
  simpl; unfold Defs.F2R; simpl;
  repeat (replace
         match (if match _ with 53%positive => true | _ => _ end then _ else _)
         with PInf | NInf | NaN => _ | _ => Freal end
       with Freal;
          [ |now case match _ with 53%positive => true | _ => _ end]);
  try reflexivity;
  now case Rcompare.
Qed.

Definition float_comparison_of_Xcomparison c :=
  match c with
  | Xeq => FEq
  | Xlt => FLt
  | Xgt => FGt
  | Xund => FNotComparable
  end.

Lemma compare_cmp x y : compare x y = float_comparison_of_Xcomparison (cmp x y).
Proof. now unfold cmp; case compare. Qed.

Lemma min_correct :
  forall x y,
  match classify x, classify y with
  | Sig.Fnan, _ | _, Sig.Fnan => classify (min x y) = Sig.Fnan
  | Fminfty, _ | _, Fminfty => classify (min x y) = Fminfty
  | Fpinfty, _ => min x y = y
  | _, Fpinfty => min x y = x
  | Freal, Freal => toX (min x y) = Xmin (toX x) (toX y)
  end.
Proof.
intros x y.
unfold min.
rewrite compare_cmp, cmp_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
set (fx := Prim2SF x).
set (fy := Prim2SF y).
rewrite <-(SF2Prim_Prim2SF x).
rewrite <-(SF2Prim_Prim2SF y).
generalize (Prim2SF_valid x).
generalize (Prim2SF_valid y).
fold fx; fold fy.
case fx; [intros [ | ]..| |intros [ | ] mx ex];
  (case fy; [intros [ | ]..| |intros [ | ] my ey]);
  intros vx vy;
  try (set (sf := SF2Prim _));
  try (set (sf' := SF2Prim _));
  simpl;
  try reflexivity;
  repeat (replace
         match (if match _ with 53%positive => true | _ => _ end then _ else _)
         with PInf | NInf | NaN => _ | _ => Freal end
       with Freal;
          [ |now case match _ with 53%positive => true | _ => _ end]);
  try reflexivity;
  rewrite Rmin_compare;
  case Rcompare;
  simpl;
  unfold sf; try unfold sf';
  now repeat rewrite Prim2SF_SF2Prim.
Qed.

(* TODO: move in Flocq.Raux *)
Lemma Rmax_compare x y :
  Rmax x y = match Rcompare x y with Lt => y | _ => x end.
Proof.
rewrite <-(Ropp_involutive (Rmax _ _)) at 1.
rewrite Ropp_Rmax.
rewrite Rmin_compare.
case Rcompare_spec; case Rcompare_spec; lra.
Qed.

Lemma max_correct :
  forall x y,
  match classify x, classify y with
  | Sig.Fnan, _ | _, Sig.Fnan => classify (max x y) = Sig.Fnan
  | Fpinfty, _ | _, Fpinfty => classify (max x y) = Fpinfty
  | Fminfty, _ => max x y = y
  | _, Fminfty => max x y = x
  | Freal, Freal => toX (max x y) = Xmax (toX x) (toX y)
  end.
Proof.
intros x y.
unfold max.
rewrite compare_cmp, cmp_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
set (fx := Prim2SF x).
set (fy := Prim2SF y).
rewrite <-(SF2Prim_Prim2SF x).
rewrite <-(SF2Prim_Prim2SF y).
generalize (Prim2SF_valid x).
generalize (Prim2SF_valid y).
fold fx; fold fy.
case fx; [intros [ | ]..| |intros [ | ] mx ex];
  (case fy; [intros [ | ]..| |intros [ | ] my ey]);
  intros vx vy;
  try (set (sf := SF2Prim _));
  try (set (sf' := SF2Prim _));
  simpl;
  try reflexivity;
  repeat (replace
         match (if match _ with 53%positive => true | _ => _ end then _ else _)
         with PInf | NInf | NaN => _ | _ => Freal end
       with Freal;
          [ |now case match _ with 53%positive => true | _ => _ end]);
  try reflexivity;
  rewrite Rmax_compare;
  case Rcompare;
  simpl;
  unfold sf; try unfold sf';
  now repeat rewrite Prim2SF_SF2Prim.
Qed.

Lemma neg_correct :
  forall x,
  match classify x with
  | Freal => toX (neg x) = Xneg (toX x)
  | Sig.Fnan => classify (neg x) = Sig.Fnan
  | Fminfty => classify (neg x) = Fpinfty
  | Fpinfty => classify (neg x) = Fminfty
  end.
Proof.
intro x.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
unfold neg.
rewrite opp_spec.
case Prim2SF; [intros [ | ]..| |intros [ | ] mx ex];
  try reflexivity;
  simpl;
  try (rewrite Ropp_0; reflexivity);
  unfold FtoR;
  repeat (replace
         match (if match _ with 53%positive => true | _ => _ end then _ else _)
         with PInf | NInf | NaN => _ | _ => Freal end
       with Freal;
          [ |now case match _ with 53%positive => true | _ => _ end]);
  case ex => [ |pex|pex];
  unfold Rdiv;
  try rewrite Ropp_mult_distr_l;
  try rewrite <-opp_IZR;
  now try rewrite Zopp_mult_distr_l.
Qed.

Lemma abs_correct :
  forall x, toX (abs x) = Xabs (toX x) /\ (valid_ub (abs x) = true).
Proof.
intro x.
unfold abs.
unfold toX, toF.
rewrite <-(SF2Prim_Prim2SF (PrimFloat.abs x)) at 2.
generalize (Prim2SF_valid (PrimFloat.abs x)).
rewrite abs_spec.
rewrite valid_ub_correct.
unfold classify.
rewrite classify_spec.
intro H.
rewrite (Prim2SF_SF2Prim _ H).
set (fx := Prim2SF x).
case fx; [intros [ | ]..| |intros [ | ] mx ex];
  simpl;
  try rewrite Rabs_R0;
  try (now split);
  repeat (replace
         match (if match _ with 53%positive => true | _ => _ end then _ else _)
         with PInf | NInf | NaN => _ | _ => Freal end
       with Freal;
          [ |now case match _ with 53%positive => true | _ => _ end]);
  now rewrite Generic_proof.FtoR_abs.
Qed.

Lemma toX_Prim2B x :
  toX x =
  match Prim2B nan_pl x with
  | B754_zero _ => Xreal 0
  | B754_finite s m e _ => Xreal (FtoR radix2 s m e)
  | _ => Xnan
  end.
Proof. now unfold toX, toF; rewrite <-!(B2SF_Prim2B nan_pl); case Prim2B. Qed.

Lemma toX_B2Prim x :
  toX (B2Prim x) =
  match x with
  | B754_zero _ => Xreal 0
  | B754_finite s m e _ => Xreal (FtoR radix2 s m e)
  | _ => Xnan
  end.
Proof. now unfold toX, toF; rewrite Prim2SF_B2Prim; case x. Qed.

Lemma Bdiv2_correct x :
  is_finite FloatOps.prec emax x = true ->
  let x2 := Bdiv _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE
                 x (Prim2B nan_pl 2) in
  B2R FloatOps.prec emax x2 =
    Generic_fmt.round radix2
      (FLT.FLT_exp (3 - emax - FloatOps.prec) FloatOps.prec)
      (round_mode mode_NE)
      (B2R FloatOps.prec emax x / 2)
  /\ is_finite FloatOps.prec emax x2 = true
  /\ Bsign FloatOps.prec emax x2 = Bsign FloatOps.prec emax x
  /\ (Rabs (B2R FloatOps.prec emax x2) <= Rabs (B2R FloatOps.prec emax x))%R.
Proof.
set (b2 := Prim2B _ 2).
assert (Hb2 : { H | b2 = B754_finite false 4503599627370496 (-51) H }).
{ now compute; set (H := NativeLayer.Prim2B_obligation_1 _ _); exists H. }
assert (Nz2 : B2R FloatOps.prec emax b2 <> 0%R).
{ compute; lra. }
case x => [sx|sx|s pl Hpl|sx mx ex Hmex];
  [ |intro H; discriminate H..| ]; intros _ x2.
{ unfold x2.
  elim Hb2 => Hb2f ->.
  simpl; unfold Rdiv; rewrite Rabs_R0, Rmult_0_l.
  rewrite Generic_fmt.round_0; [ |now apply Generic_fmt.valid_rnd_N].
  now split; [ |split; [ |split; [case sx|right]]]. }
generalize (Bdiv_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE
                         (B754_finite sx mx ex Hmex) b2 Nz2).
fold x2.
set (fexp := FLT.FLT_exp _ _).
set (m := round_mode _).
set (rx := B2R _ _ (B754_finite sx mx ex _)).
replace (B2R _ _ _) with 2%R; [ |compute; lra].
cut ((Rabs (Generic_fmt.round radix2 fexp m (rx / 2)) <= Rabs rx)%R).
{ intro Hrx2rx.
  rewrite Rlt_bool_true.
  2:{ generalize (abs_B2R_lt_emax _ _ (B754_finite false mx ex Hmex)).
    apply Rle_lt_trans.
    revert Hrx2rx.
    unfold rx, B2R; rewrite <-!FtoR_split.
    now rewrite !Generic_proof.FtoR_abs. }
  simpl.
  intros [-> [Fx2 Sx2]].
  split; [reflexivity|split; [exact Fx2|split; [ |exact Hrx2rx]]].
  now rewrite Sx2; [case sx|revert Fx2; case x2]. }
case (Rlt_or_le rx 0) => Hrx.
{ rewrite (Rabs_left1 rx); [ |now apply Rlt_le].
  rewrite Rabs_left1.
  { apply Ropp_le_contravar.
    rewrite <-(Generic_fmt.round_generic radix2 fexp m rx) at 1.
    { apply Generic_fmt.round_le.
      { now apply FLT.FLT_exp_valid. }
      { now apply Generic_fmt.valid_rnd_N. }
      lra. }
    apply generic_format_B2R. }
  rewrite <-(Generic_fmt.round_0 radix2 fexp m).
  apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  lra. }
rewrite (Rabs_pos_eq _ Hrx).
rewrite Rabs_pos_eq.
{ rewrite <-(Generic_fmt.round_generic radix2 fexp m rx) at 2.
  { apply Generic_fmt.round_le.
    { now apply FLT.FLT_exp_valid. }
    { now apply Generic_fmt.valid_rnd_N. }
    lra. }
  apply generic_format_B2R. }
rewrite <-(Generic_fmt.round_0 radix2 fexp m).
apply Generic_fmt.round_le.
{ now apply FLT.FLT_exp_valid. }
{ now apply Generic_fmt.valid_rnd_N. }
lra.
Qed.

Lemma div2_correct :
  forall x, sensible_format = true ->
  (1 / 256 <= Rabs (toR x))%R ->
  toX (div2 x) = Xdiv (toX x) (Xreal 2).
Proof.
intros x _.
unfold toR.
rewrite (toX_Prim2B x).
set (bx := Prim2B _ x).
unfold div2.
rewrite <-(B2Prim_Prim2B nan_pl x).
rewrite <-(B2Prim_Prim2B nan_pl 2).
fold bx.
set (b2 := Prim2B _ 2).
rewrite (FPdiv_Bdiv (fun _ _ => ex_nan)).
rewrite toX_B2Prim.
case bx => [sx|sx|s pl Hpl|sx mx ex Hmex]; clear x bx;
  try (simpl; change R0 with 0%R; rewrite Rabs_R0; intro H; exfalso; lra); [ ].
pose (bx := B754_finite sx mx ex Hmex).
intro Hx.
unfold Xdiv, Xdiv'; rewrite is_zero_false; [ |lra].
elim (Bdiv2_correct bx eq_refl).
fold b2.
set (x2 := Bdiv _ _ _ _ _ _ _ _).
intros Rx2 [Fx2 _]; revert Rx2 Fx2.
rewrite Generic_fmt.round_generic.
2:{ now apply Generic_fmt.valid_rnd_N. }
2:{ unfold Rdiv; change (/ 2)%R with (bpow radix2 (-1)).
  apply mult_bpow_exact_FLT.
  { apply generic_format_B2R. }
  rewrite Z.le_sub_le_add_l, <-Z.le_sub_le_add_r; simpl.
  apply mag_ge_bpow.
  unfold B2R.
  revert Hx.
  rewrite <-FtoR_split.
  apply Rle_trans.
  compute; lra. }
unfold B2R at 2, bx; rewrite <-FtoR_split => <-.
case x2 => [sx2|sx2|s pl Hpl|sx2 mx2 ex2 Hmex2];
  [reflexivity|intro H; discriminate H..|intros _].
now unfold B2R; rewrite <-FtoR_split.
Qed.

Lemma valid_ub_next_up x : valid_ub (next_up x) = true.
Proof.
rewrite valid_ub_correct.
rewrite <-(B2Prim_Prim2B nan_pl x).
set (bx := Prim2B _ x).
rewrite (FPnext_up_Bsucc (fun _ => ex_nan)).
unfold classify.
rewrite classify_spec.
rewrite Prim2SF_B2Prim.
set (sx := Bsucc _ _ _ _ _ _ _).
case_eq sx; [intros [ | ]..|intros [ | ] pl Hpl|intros [ | ] mx ex Hme];
  intros Hsx; simpl;
  try reflexivity;
  repeat (replace
         match (if match _ with 53%positive => true | _ => _ end then _ else _)
         with PInf | NInf | NaN => _ | _ => Freal end
       with Freal;
          [ |now case match _ with 53%positive => true | _ => _ end]);
  try reflexivity; [ ].
exfalso.
revert Hsx; unfold sx.
generalize (Bsucc_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) bx).
case bx; [intros [ | ]..|intros s pl Hpl|intros ssx mx ex Hex];
  try (intros H H'; discriminate H'); [ ].
intro H; generalize (H eq_refl); clear H.
case Rlt_bool => [[_ [H _]]|H] H';
  revert H; rewrite H'; simpl; intro H; discriminate H.
Qed.

Lemma le_upper_succ_finite x s m e :
  Prim2SF x = S754_finite s m e ->
  le_upper
    (@FtoX radix2 (Basic.Float s m e))
    (@FtoX
       radix2
       match SF64succ (S754_finite s m e) with
       | S754_zero _ => Fzero
       | S754_finite s m e => Basic.Float s m e
       | _ => Basic.Fnan
       end).
Proof.
intro Hx.
unfold SF64succ.
rewrite <-Hx.
rewrite <-(B2SF_Prim2B nan_pl).
rewrite (SpecLayer.SFsucc_Bsucc prec_gt_0 Hmax Hemax (fun _ => ex_nan)).
set (b_x := Prim2B _ _).
assert (Fx : is_finite FloatOps.prec emax b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
generalize (Bsucc_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_x Fx).
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 s m e).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s'|s'|s' pl Hpl|s' m' e'] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool.
2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity false) eq_refl).
  now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
set (b_s := Bsucc _ _ _ _ _ _ _).
case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
{ intros [Rs _]; revert Rs; simpl => ->.
  rewrite Hrx.
  apply Ulp.succ_ge_id. }
{ now case ss. }
{ now case ss. }
intros [Rs _]; revert Rs; simpl.
rewrite <-FtoR_split => ->.
rewrite Hrx.
apply Ulp.succ_ge_id.
Qed.

Lemma add_UP_correct :
  forall p x y, valid_ub x = true -> valid_ub y = true
    -> (valid_ub (add_UP p x y) = true
       /\ le_upper (Xadd (toX x) (toX y)) (toX (add_UP p x y))).
Proof.
intros p x y.
unfold add_UP.
intros Vx Vy; split; [now rewrite valid_ub_next_up| ]; revert Vx Vy.
rewrite !valid_ub_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
rewrite next_up_spec, add_spec.
case_eq (Prim2SF x); [intros sx|intros [ | ]| |intros sx mx ex]; intro Hx;
  try (intros H; discriminate H); intros _.
{ rewrite Xadd_0_l.
  case_eq (Prim2SF y); [intros [ | ]|intros [ | ]| |intros sy my ey]; intro Hy;
    try (intros H; discriminate H); intros _;
    try (replace (SF64add _ _) with (Prim2SF y); [rewrite Hy]);
    try (now simpl);
    [case sx; compute; lra..|apply (le_upper_succ_finite _ _ _ _ Hy)]. }
{ now intros _; case Prim2SF; [intros [ | ]|intros [ | ]| | ]. }
{ now intros _; case Prim2SF; [intros [ | ]|intros [ | ]| | ]. }
case_eq (Prim2SF y); [intros sy|intros [ | ]| |intros sy my ey]; intro Hy;
  try (intros H; discriminate H); intros _.
{ rewrite Xadd_0_r.
  apply (le_upper_succ_finite _ _ _ _ Hx). }
{ now case sx. }
{ now case sx. }
rewrite <-Hx, <-Hy.
rewrite <-!(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
set (b_y := Prim2B _ y).
unfold SF64add.
rewrite (SpecLayer.SFadd_Bplus prec_gt_0 Hmax (fun _ _ => ex_nan) b_x b_y).
unfold SF64succ.
set (b_xpy := Bplus _ _ _ _ _ _ _ _).
rewrite (SpecLayer.SFsucc_Bsucc prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xpy).
generalize (Bsucc_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xpy).
assert (Fx : is_finite _ _ b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Fy : is_finite _ _ b_y = true).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
generalize (Bplus_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE b_x b_y Fx Fy).
fold b_xpy.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 sx mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
assert (Hry : B2R FloatOps.prec emax b_y = FtoR radix2 sy my ey).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool_spec => Hb.
{ intros [Rxpy [Fxpy Sxpy]].
  intro H; generalize (H Fxpy); clear H.
  case Rlt_bool.
  2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity false) eq_refl).
    now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
  set (b_s := Bsucc _ _ _ _ _ _ _).
  case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
  { intros [Rs _]; revert Rs; simpl => ->.
    rewrite Rxpy, Hrx, Hry.
    apply Ulp.succ_round_ge_id.
    { now apply FLT.FLT_exp_valid. }
    now apply Generic_fmt.valid_rnd_N. }
  { now case ss. }
  { now case ss. }
  intros [Rs _]; revert Rs; simpl.
  rewrite <-FtoR_split => ->.
  rewrite Rxpy, Hrx, Hry.
  apply Ulp.succ_round_ge_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
change (binary_overflow _ _ _ _)
  with (F754_infinity (Bsign FloatOps.prec emax b_x)).
intros [Hxpy Sxy] _.
revert Hxpy.
case_eq b_xpy; [intro sxpy..|intros s pls Hpls|intros sxpy mxpy expy Hexpy];
  intro Hxpy;
  try (intro H; discriminate H); [simpl].
case sxpy; [ |now simpl].
unfold SpecLayer.B2SF, SpecLayer.FF2SF, B2FF.
unfold FtoX.
unfold le_upper.
intro H; inversion H as (Hsx); clear H.
assert (Hsx' : Bsign FloatOps.prec emax b_x = sx).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
assert (Hsy' : Bsign FloatOps.prec emax b_y = sy).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
revert Hsx Sxy.
rewrite !Hsx', Hsy'.
intro Hsx''; rewrite <-Hsx''; intro Hsy''.
revert Hb; rewrite Hrx, Hry, <-Hsx'', <-Hsy''.
set (sum := (_ + _)%R).
rewrite Rabs_left1.
2:{ set (fexp := FLT.FLT_exp _ _).
  set (rnd := round_mode _).
  rewrite <-(Generic_fmt.round_0 radix2 fexp rnd).
  apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  unfold sum.
  generalize (Generic_proof.FtoR_Rneg radix2 mx ex).
  generalize (Generic_proof.FtoR_Rneg radix2 my ey).
  lra. }
rewrite <-(Ropp_involutive (bpow _ _)).
intro H; apply Ropp_le_cancel in H; revert H.
unfold round_mode.
set (c := fun _ => _).
elim (Relative.error_N_FLT radix2 (3 - emax - FloatOps.prec) _ prec_gt_0 c sum).
intros eps [eta [Heps [Heta [Hepseta ->]]]].
intro Hb.
case (Req_dec eta 0) => Heta0.
{ revert Hb.
  rewrite Heta0, Rplus_0_r.
  intro Hb.
  apply Rle_trans with (-bpow radix2 emax / (1 + eps))%R.
  { apply (Rmult_le_reg_r (1 + eps)).
    { revert Heps; compute; case Rcase_abs; lra. }
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r; [exact Hb| ].
    revert Heps; compute; case Rcase_abs; lra. }
  apply (Rmult_le_reg_r (1 + eps)).
  { generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r.
  2:{ generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  apply Rle_trans with (FtoR radix2 true (9007199254740992 - 1) 971
                        * (1 + /2 * bpow radix2 (-FloatOps.prec + 1)))%R.
  { compute; lra. }
  apply Rmult_le_compat_neg_l; [compute; lra| ].
  apply Rplus_le_compat_l.
  generalize (Rabs_le_inv _ _ Heps); intros [_ H]; exact H. }
revert Hb.
elim (Rmult_integral _ _ Hepseta); [ |lra]; intros ->.
rewrite Rplus_0_r, Rmult_1_r.
generalize (Rabs_le_inv _ _ Heta); compute; lra.
Qed.

Lemma valid_lb_next_down x : valid_lb (next_down x) = true.
Proof.
rewrite valid_lb_correct.
rewrite <-(B2Prim_Prim2B nan_pl x).
set (bx := Prim2B _ x).
rewrite (FPnext_down_Bpred (fun _ => ex_nan)).
unfold classify.
rewrite classify_spec.
rewrite Prim2SF_B2Prim.
set (px := Bpred _ _ _ _ _ _ _).
case_eq px; [intros [ | ]..|intros [ | ] pl Hpl|intros [ | ] mx ex Hme];
  intros Hpx; simpl;
  try reflexivity;
  repeat (replace
         match (if match _ with 53%positive => true | _ => _ end then _ else _)
         with PInf | NInf | NaN => _ | _ => Freal end
       with Freal;
          [ |now case match _ with 53%positive => true | _ => _ end]);
  try reflexivity; [ ].
exfalso.
revert Hpx; unfold px.
generalize (Bpred_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) bx).
case bx; [intros [ | ]..|intros s pl Hpl|intros ssx mx ex Hex];
  try (intros H H'; discriminate H'); [ ].
intro H; generalize (H eq_refl); clear H.
case Rlt_bool => [[_ [H _]]|H] H';
  revert H; rewrite H'; simpl; intro H; discriminate H.
Qed.

Lemma le_lower_pred_finite x s m e :
  Prim2SF x = S754_finite s m e ->
  le_lower
    (@FtoX
       radix2
       match SF64pred (S754_finite s m e) with
       | S754_zero _ => Fzero
       | S754_finite s m e => Basic.Float s m e
       | _ => Basic.Fnan
       end)
    (@FtoX radix2 (Basic.Float s m e)).
Proof.
intro Hx.
unfold SF64pred.
rewrite <-Hx.
rewrite <-(B2SF_Prim2B nan_pl).
rewrite (SpecLayer.SFpred_Bpred prec_gt_0 Hmax Hemax (fun _ => ex_nan)).
set (b_x := Prim2B _ _).
assert (Fx : is_finite FloatOps.prec emax b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
generalize (Bpred_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_x Fx).
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 s m e).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s'|s'|s' pl Hpl|s' m' e'] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool.
2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity true) eq_refl).
  now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
set (b_s := Bpred _ _ _ _ _ _ _).
case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
{ intros [Rs _]; revert Rs; simpl => ->.
  rewrite Hrx.
  apply Ropp_le_contravar.
  apply Ulp.pred_le_id. }
{ now case ss. }
{ now case ss. }
intros [Rs _]; revert Rs; simpl.
rewrite <-FtoR_split => ->.
rewrite Hrx.
apply Ropp_le_contravar.
apply Ulp.pred_le_id.
Qed.

Lemma add_DN_correct :
  forall p x y, valid_lb x = true -> valid_lb y = true
    -> (valid_lb (add_DN p x y) = true
       /\ le_lower (toX (add_DN p x y)) (Xadd (toX x) (toX y))).
Proof.
intros p x y.
unfold add_DN.
intros Vx Vy; split; [now rewrite valid_lb_next_down| ]; revert Vx Vy.
rewrite !valid_lb_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
rewrite next_down_spec, add_spec.
case_eq (Prim2SF x); [intros sx|intros [ | ]| |intros sx mx ex]; intro Hx;
  try (intros H; discriminate H); intros _.
{ rewrite Xadd_0_l.
  case_eq (Prim2SF y); [intros [ | ]|intros [ | ]| |intros sy my ey]; intro Hy;
    try (intros H; discriminate H); intros _;
    try (replace (SF64add _ _) with (Prim2SF y); [rewrite Hy]);
    try (now simpl);
    [case sx; compute; lra..|apply (le_lower_pred_finite _ _ _ _ Hy)]. }
{ now intros _; case Prim2SF; [intros [ | ]|intros [ | ]| | ]. }
{ now intros _; case Prim2SF; [intros [ | ]|intros [ | ]| | ]. }
case_eq (Prim2SF y); [intros sy|intros [ | ]| |intros sy my ey]; intro Hy;
  try (intros H; discriminate H); intros _.
{ rewrite Xadd_0_r.
  apply (le_lower_pred_finite _ _ _ _ Hx). }
{ now case sx. }
{ now case sx. }
rewrite <-Hx, <-Hy.
rewrite <-!(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
set (b_y := Prim2B _ y).
unfold SF64add.
rewrite (SpecLayer.SFadd_Bplus prec_gt_0 Hmax (fun _ _ => ex_nan) b_x b_y).
unfold SF64pred.
set (b_xpy := Bplus _ _ _ _ _ _ _ _).
rewrite (SpecLayer.SFpred_Bpred prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xpy).
generalize (Bpred_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xpy).
assert (Fx : is_finite _ _ b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Fy : is_finite _ _ b_y = true).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
generalize (Bplus_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE b_x b_y Fx Fy).
fold b_xpy.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 sx mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
assert (Hry : B2R FloatOps.prec emax b_y = FtoR radix2 sy my ey).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool_spec => Hb.
{ intros [Rxpy [Fxpy Sxpy]].
  intro H; generalize (H Fxpy); clear H.
  case Rlt_bool.
  2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity true) eq_refl).
    now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
  set (b_s := Bpred _ _ _ _ _ _ _).
  case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
  { intros [Rs _]; revert Rs; simpl => ->.
    rewrite Rxpy, Hrx, Hry.
    apply Ropp_le_contravar.
    apply Ulp.pred_round_le_id.
    { now apply FLT.FLT_exp_valid. }
    now apply Generic_fmt.valid_rnd_N. }
  { now case ss. }
  { now case ss. }
  intros [Rs _]; revert Rs; simpl.
  rewrite <-FtoR_split => ->.
  rewrite Rxpy, Hrx, Hry.
  apply Ropp_le_contravar.
  apply Ulp.pred_round_le_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
change (binary_overflow _ _ _ _)
  with (F754_infinity (Bsign FloatOps.prec emax b_x)).
intros [Hxpy Sxy] _.
revert Hxpy.
case_eq b_xpy; [intro sxpy..|intros s pls Hpls|intros sxpy mxpy expy Hexpy];
  intro Hxpy;
  try (intro H; discriminate H); [simpl].
case sxpy; [now simpl| ].
unfold SpecLayer.B2SF, SpecLayer.FF2SF, B2FF.
unfold FtoX.
unfold le_lower.
intro H; inversion H as (Hsx); clear H.
assert (Hsx' : Bsign FloatOps.prec emax b_x = sx).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
assert (Hsy' : Bsign FloatOps.prec emax b_y = sy).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
revert Hsx Sxy.
rewrite !Hsx', Hsy'.
intro Hsx''; rewrite <-Hsx''; intro Hsy''.
revert Hb; rewrite Hrx, Hry, <-Hsx'', <-Hsy''.
set (sum := (_ + _)%R).
rewrite Rabs_pos_eq.
2:{ set (fexp := FLT.FLT_exp _ _).
  set (rnd := round_mode _).
  rewrite <-(Generic_fmt.round_0 radix2 fexp rnd).
  apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  unfold sum.
  generalize (Generic_proof.FtoR_Rpos radix2 mx ex).
  generalize (Generic_proof.FtoR_Rpos radix2 my ey).
  lra. }
intro H; apply Ropp_le_contravar; revert H.
unfold round_mode.
set (c := fun _ => _).
elim (Relative.error_N_FLT radix2 (3 - emax - FloatOps.prec) _ prec_gt_0 c sum).
intros eps [eta [Heps [Heta [Hepseta ->]]]].
intro Hb.
case (Req_dec eta 0) => Heta0.
{ revert Hb.
  rewrite Heta0, Rplus_0_r.
  intro Hb.
  apply Rle_trans with (bpow radix2 emax / (1 + eps))%R.
  2:{ apply (Rmult_le_reg_r (1 + eps)).
    { revert Heps; compute; case Rcase_abs; lra. }
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r; [exact Hb| ].
    revert Heps; compute; case Rcase_abs; lra. }
  apply (Rmult_le_reg_r (1 + eps)).
  { generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r.
  2:{ generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  apply Rle_trans with (FtoR radix2 false (9007199254740992 - 1) 971
                        * (1 + /2 * bpow radix2 (-FloatOps.prec + 1)))%R.
  2:{ compute; lra. }
  apply Rmult_le_compat_l; [compute; lra| ].
  apply Rplus_le_compat_l.
  generalize (Rabs_le_inv _ _ Heps); intros [_ H]; exact H. }
revert Hb.
elim (Rmult_integral _ _ Hepseta); [ |lra]; intros ->.
rewrite Rplus_0_r, Rmult_1_r.
generalize (Rabs_le_inv _ _ Heta); compute; lra.
Qed.

Lemma sub_UP_correct :
  forall p x y, valid_ub x = true -> valid_lb y = true
    -> (valid_ub (sub_UP p x y) = true
       /\ le_upper (Xsub (toX x) (toX y)) (toX (sub_UP p x y))).
Proof.
intros p x y.
unfold sub_UP.
intros Vx Vy; split; [now rewrite valid_ub_next_up| ]; revert Vx Vy.
rewrite valid_ub_correct, valid_lb_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
rewrite next_up_spec, sub_spec.
case_eq (Prim2SF x); [intros sx|intros [ | ]| |intros sx mx ex]; intro Hx;
  try (intros H; discriminate H); intros _.
{ rewrite Xsub_split.
  rewrite Xadd_0_l.
  case_eq (Prim2SF y); [intros [ | ]|intros [ | ]| |intros sy my ey]; intro Hy;
    try (intros H; discriminate H); intros _;
    try (replace (SF64add _ _) with (Prim2SF y); [rewrite Hy]);
    try (now simpl);
    [case sx; compute; lra..| ].
  rewrite <-Generic_proof.Fneg_correct.
  assert (Hy' : Prim2SF (opp y) = S754_finite (negb sy) my ey).
  { now rewrite opp_spec, Hy. }
  apply (le_upper_succ_finite _ _ _ _ Hy'). }
{ now intros _; case Prim2SF; [intros [ | ]|intros [ | ]| | ]. }
{ now intros _; case Prim2SF; [intros [ | ]|intros [ | ]| | ]. }
case_eq (Prim2SF y); [intros sy|intros [ | ]| |intros sy my ey]; intro Hy;
  try (intros H; discriminate H); intros _.
{ rewrite Xsub_split.
  rewrite <-Generic_proof.Fneg_correct.
  rewrite Xadd_0_r.
  apply (le_upper_succ_finite _ _ _ _ Hx). }
{ now case sx. }
{ now case sx. }
rewrite <-Hx, <-Hy.
rewrite <-!(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
set (b_y := Prim2B _ y).
unfold SF64sub.
rewrite (SpecLayer.SFsub_Bminus prec_gt_0 Hmax (fun _ _ => ex_nan) b_x b_y).
unfold SF64succ.
set (b_xpy := Bminus _ _ _ _ _ _ _ _).
rewrite (SpecLayer.SFsucc_Bsucc prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xpy).
generalize (Bsucc_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xpy).
assert (Fx : is_finite _ _ b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Fy : is_finite _ _ b_y = true).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
generalize (Bminus_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE b_x b_y Fx Fy).
fold b_xpy.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 sx mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
assert (Hry : B2R FloatOps.prec emax b_y = FtoR radix2 sy my ey).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool_spec => Hb.
{ intros [Rxpy [Fxpy Sxpy]].
  intro H; generalize (H Fxpy); clear H.
  case Rlt_bool.
  2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity false) eq_refl).
    now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
  set (b_s := Bsucc _ _ _ _ _ _ _).
  case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
  { intros [Rs _]; revert Rs; simpl => ->.
    rewrite Rxpy, Hrx, Hry.
    apply Ulp.succ_round_ge_id.
    { now apply FLT.FLT_exp_valid. }
    now apply Generic_fmt.valid_rnd_N. }
  { now case ss. }
  { now case ss. }
  intros [Rs _]; revert Rs; simpl.
  rewrite <-FtoR_split => ->.
  rewrite Rxpy, Hrx, Hry.
  apply Ulp.succ_round_ge_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
change (binary_overflow _ _ _ _)
  with (F754_infinity (Bsign FloatOps.prec emax b_x)).
intros [Hxpy Sxy] _.
revert Hxpy.
case_eq b_xpy; [intro sxpy..|intros s pls Hpls|intros sxpy mxpy expy Hexpy];
  intro Hxpy;
  try (intro H; discriminate H); [simpl].
case sxpy; [ |now simpl].
unfold SpecLayer.B2SF, SpecLayer.FF2SF, B2FF.
unfold FtoX.
unfold le_upper.
intro H; inversion H as (Hsx); clear H.
assert (Hsx' : Bsign FloatOps.prec emax b_x = sx).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
assert (Hsy' : Bsign FloatOps.prec emax b_y = sy).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
revert Hsx Sxy.
rewrite !Hsx', Hsy'.
intro Hsx''; rewrite <-Hsx'', <-(Bool.negb_involutive true); intro Hsy''.
apply ssrbool.negb_inj in Hsy''.
revert Hb; rewrite Hrx, Hry, <-Hsx'', <-Hsy''.
set (sum := (_ - _)%R).
rewrite Rabs_left1.
2:{ set (fexp := FLT.FLT_exp _ _).
  set (rnd := round_mode _).
  rewrite <-(Generic_fmt.round_0 radix2 fexp rnd).
  apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  unfold sum.
  generalize (Generic_proof.FtoR_Rneg radix2 mx ex).
  generalize (Generic_proof.FtoR_Rpos radix2 my ey).
  simpl.
  lra. }
rewrite <-(Ropp_involutive (bpow _ _)).
intro H; apply Ropp_le_cancel in H; revert H.
unfold round_mode.
set (c := fun _ => _).
elim (Relative.error_N_FLT radix2 (3 - emax - FloatOps.prec) _ prec_gt_0 c sum).
intros eps [eta [Heps [Heta [Hepseta ->]]]].
intro Hb.
case (Req_dec eta 0) => Heta0.
{ revert Hb.
  rewrite Heta0, Rplus_0_r.
  intro Hb.
  apply Rle_trans with (-bpow radix2 emax / (1 + eps))%R.
  { apply (Rmult_le_reg_r (1 + eps)).
    { revert Heps; compute; case Rcase_abs; lra. }
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r; [exact Hb| ].
    revert Heps; compute; case Rcase_abs; lra. }
  apply (Rmult_le_reg_r (1 + eps)).
  { generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r.
  2:{ generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  apply Rle_trans with (FtoR radix2 true (9007199254740992 - 1) 971
                        * (1 + /2 * bpow radix2 (-FloatOps.prec + 1)))%R.
  { compute; lra. }
  apply Rmult_le_compat_neg_l; [compute; lra| ].
  apply Rplus_le_compat_l.
  generalize (Rabs_le_inv _ _ Heps); intros [_ H]; exact H. }
revert Hb.
elim (Rmult_integral _ _ Hepseta); [ |lra]; intros ->.
rewrite Rplus_0_r, Rmult_1_r.
generalize (Rabs_le_inv _ _ Heta); compute; lra.
Qed.

Lemma sub_DN_correct :
  forall p x y, valid_lb x = true -> valid_ub y = true
    -> (valid_lb (sub_DN p x y) = true
       /\ le_lower (toX (sub_DN p x y)) (Xsub (toX x) (toX y))).
Proof.
intros p x y.
unfold sub_DN.
intros Vx Vy; split; [now rewrite valid_lb_next_down| ]; revert Vx Vy.
rewrite valid_ub_correct, valid_lb_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
rewrite next_down_spec, sub_spec.
case_eq (Prim2SF x); [intros sx|intros [ | ]| |intros sx mx ex]; intro Hx;
  try (intros H; discriminate H); intros _.
{ rewrite Xsub_split.
  rewrite Xadd_0_l.
  case_eq (Prim2SF y); [intros [ | ]|intros [ | ]| |intros sy my ey]; intro Hy;
    try (intros H; discriminate H); intros _;
    try (replace (SF64add _ _) with (Prim2SF y); [rewrite Hy]);
    try (now simpl);
    [case sx; compute; lra..| ].
  rewrite <-Generic_proof.Fneg_correct.
  assert (Hy' : Prim2SF (opp y) = S754_finite (negb sy) my ey).
  { now rewrite opp_spec, Hy. }
  apply (le_lower_pred_finite _ _ _ _ Hy'). }
{ now intros _; case Prim2SF; [intros [ | ]|intros [ | ]| | ]. }
{ now intros _; case Prim2SF; [intros [ | ]|intros [ | ]| | ]. }
case_eq (Prim2SF y); [intros sy|intros [ | ]| |intros sy my ey]; intro Hy;
  try (intros H; discriminate H); intros _.
{ rewrite Xsub_split.
  rewrite <-Generic_proof.Fneg_correct.
  rewrite Xadd_0_r.
  apply (le_lower_pred_finite _ _ _ _ Hx). }
{ now case sx. }
{ now case sx. }
rewrite <-Hx, <-Hy.
rewrite <-!(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
set (b_y := Prim2B _ y).
unfold SF64sub.
rewrite (SpecLayer.SFsub_Bminus prec_gt_0 Hmax (fun _ _ => ex_nan) b_x b_y).
unfold SF64pred.
set (b_xmy := Bminus _ _ _ _ _ _ _ _).
rewrite (SpecLayer.SFpred_Bpred prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xmy).
generalize (Bpred_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xmy).
assert (Fx : is_finite _ _ b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Fy : is_finite _ _ b_y = true).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
generalize (Bminus_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE b_x b_y Fx Fy).
fold b_xmy.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 sx mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
assert (Hry : B2R FloatOps.prec emax b_y = FtoR radix2 sy my ey).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool_spec => Hb.
{ intros [Rxmy [Fxmy Sxmy]].
  intro H; generalize (H Fxmy); clear H.
  case Rlt_bool.
  2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity true) eq_refl).
    now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
  set (b_s := Bpred _ _ _ _ _ _ _).
  case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
  { intros [Rs _]; revert Rs; simpl => ->.
    rewrite Rxmy, Hrx, Hry.
    apply Ropp_le_contravar.
    apply Ulp.pred_round_le_id.
    { now apply FLT.FLT_exp_valid. }
    now apply Generic_fmt.valid_rnd_N. }
  { now case ss. }
  { now case ss. }
  intros [Rs _]; revert Rs; simpl.
  rewrite <-FtoR_split => ->.
  rewrite Rxmy, Hrx, Hry.
  apply Ropp_le_contravar.
  apply Ulp.pred_round_le_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
change (binary_overflow _ _ _ _)
  with (F754_infinity (Bsign FloatOps.prec emax b_x)).
intros [Hxmy Sxy] _.
revert Hxmy.
case_eq b_xmy; [intro sxmy..|intros s pls Hpls|intros sxmy mxmy exmy Hexmy];
  intro Hxmy;
  try (intro H; discriminate H); [simpl].
case sxmy; [now simpl| ].
unfold SpecLayer.B2SF, SpecLayer.FF2SF, B2FF.
unfold FtoX.
unfold le_lower, le_upper.
intro H; inversion H as (Hsx); clear H.
assert (Hsx' : Bsign FloatOps.prec emax b_x = sx).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
assert (Hsy' : Bsign FloatOps.prec emax b_y = sy).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
revert Hsx Sxy.
rewrite !Hsx', Hsy'.
intro Hsx''; rewrite <-Hsx'', <-(Bool.negb_involutive false); intro Hsy''.
apply ssrbool.negb_inj in Hsy''.
revert Hb; rewrite Hrx, Hry, <-Hsx'', <-Hsy''.
unfold negb.
set (sum := (_ - _)%R).
rewrite Rabs_pos_eq.
2:{ set (fexp := FLT.FLT_exp _ _).
  set (rnd := round_mode _).
  rewrite <-(Generic_fmt.round_0 radix2 fexp rnd).
  apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  unfold sum.
  generalize (Generic_proof.FtoR_Rpos radix2 mx ex).
  generalize (Generic_proof.FtoR_Rneg radix2 my ey).
  lra. }
unfold round_mode.
set (c := fun _ => _).
elim (Relative.error_N_FLT radix2 (3 - emax - FloatOps.prec) _ prec_gt_0 c sum).
intros eps [eta [Heps [Heta [Hepseta ->]]]].
intro Hb.
case (Req_dec eta 0) => Heta0.
{ revert Hb.
  rewrite Heta0, Rplus_0_r.
  intro Hb.
  apply Ropp_le_contravar.
  apply Rle_trans with (bpow radix2 emax / (1 + eps))%R.
  2: { apply (Rmult_le_reg_r (1 + eps)).
    { revert Heps; compute; case Rcase_abs; lra. }
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r; [exact Hb| ].
    revert Heps; compute; case Rcase_abs; lra. }
  apply (Rmult_le_reg_r (1 + eps)).
  { generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r.
  2:{ generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  apply Rle_trans with (FtoR radix2 false (9007199254740992 - 1) 971
                        * (1 + /2 * bpow radix2 (-FloatOps.prec + 1)))%R.
  2:{ compute; lra. }
  apply Rmult_le_compat_l; [compute; lra| ].
  apply Rplus_le_compat_l.
  generalize (Rabs_le_inv _ _ Heps); intros [_ H]; exact H. }
revert Hb.
elim (Rmult_integral _ _ Hepseta); [ |lra]; intros ->.
rewrite Rplus_0_r, Rmult_1_r.
generalize (Rabs_le_inv _ _ Heta); compute; lra.
Qed.

Definition is_non_neg x :=
  valid_ub x = true
  /\ match toX x with Xnan => True | Xreal r => (0 <= r)%R end.

Definition is_pos x :=
  valid_ub x = true
  /\ match toX x with Xnan => True | Xreal r => (0 < r)%R end.

Definition is_non_pos x :=
  valid_lb x = true
  /\ match toX x with Xnan => True | Xreal r => (r <= 0)%R end.

Definition is_neg x :=
  valid_lb x = true
  /\ match toX x with Xnan => True | Xreal r => (r < 0)%R end.

Definition is_non_neg_real x :=
  match toX x with Xnan => False | Xreal r => (0 <= r)%R end.

Definition is_pos_real x :=
  match toX x with Xnan => False | Xreal r => (0 < r)%R end.

Definition is_non_pos_real x :=
  match toX x with Xnan => False | Xreal r => (r <= 0)%R end.

Definition is_neg_real x :=
  match toX x with Xnan => False | Xreal r => (r < 0)%R end.

Lemma mul_UP_correct :
  forall p x y,
    ((is_non_neg x /\ is_non_neg y)
     \/ (is_non_pos x /\ is_non_pos y)
     \/ (is_non_pos_real x /\ is_non_neg_real y)
     \/ (is_non_neg_real x /\ is_non_pos_real y))
    -> (valid_ub (mul_UP p x y) = true
        /\ le_upper (Xmul (toX x) (toX y)) (toX (mul_UP p x y))).
Proof.
intros p x y.
unfold mul_UP.
intro H; split; [now rewrite valid_ub_next_up| ]; revert H.
unfold toX, toF.
rewrite next_up_spec, mul_spec.
unfold is_non_neg, is_non_pos, is_non_pos_real, is_non_neg_real.
rewrite !valid_lb_correct, !valid_ub_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
case_eq (Prim2SF x); [intros sx|intros sx| |intros sx mx ex]; intro Hx;
  [..|reflexivity| ].
{ intros _.
  case_eq (Prim2SF y); [intros sy|intros sy| |intros sy my ey]; intro Hy;
    [ |reflexivity..| ]; simpl; rewrite Rmult_0_l; lra. }
{ simpl; intros [H|[H|[H|H]]]; [ | |now destruct H..]; revert H;
    intros [[H1 _] [H2 H3]];
    (revert H1; case sx; try (now intro H; discriminate H); [intros _]);
    (revert H3 H2;
     case_eq (Prim2SF y); [intros sy|intros sy| |intros [ | ] my ey]; intro Hy;
     try reflexivity;
     try (generalize (Generic_proof.FtoR_Rneg radix2 my ey); simpl; lra);
     try (generalize (Generic_proof.FtoR_Rpos radix2 my ey); simpl; lra); [intros _]);
    now (case sy; try (now intro H; discriminate H)). }
case_eq (Prim2SF y); [intros sy|intros sy| |intros sy my ey]; intro Hy;
  [..|reflexivity| ].
{ intros _; simpl; rewrite Rmult_0_r; lra. }
{ simpl; intros [H|[H|[H|H]]]; [ | |now destruct H..]; revert H;
    intros [[H1 H2] [H3 _]];
    (revert H3; case sy; try (now intro H; discriminate H); [intros _]);
    revert H2 H1;
    case sx;
    try (generalize (Generic_proof.FtoR_Rneg radix2 mx ex); simpl; lra);
    try (generalize (Generic_proof.FtoR_Rpos radix2 mx ex); simpl; lra). }
intros _.  (* x and y finite now, don't need the big hypothesis anymore *)
rewrite <-Hx, <-Hy.
rewrite <-!(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
set (b_y := Prim2B _ y).
unfold SF64mul.
rewrite (SpecLayer.SFmul_Bmult prec_gt_0 Hmax (fun _ _ => ex_nan) b_x b_y).
unfold SF64succ.
set (b_xmy := Bmult _ _ _ _ _ _ _ _).
rewrite (SpecLayer.SFsucc_Bsucc prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xmy).
generalize (Bsucc_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xmy).
assert (Fx : is_finite _ _ b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Fy : is_finite _ _ b_y = true).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
generalize (Bmult_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE b_x b_y).
fold b_xmy.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 sx mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
assert (Hry : B2R FloatOps.prec emax b_y = FtoR radix2 sy my ey).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool_spec => Hb.
{ rewrite Fx, Fy.
  intros [Rxmy [Fxmy Sxmy]].
  intro H; generalize (H Fxmy); clear H.
  case Rlt_bool.
  2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity false) eq_refl).
    now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
  set (b_s := Bsucc _ _ _ _ _ _ _).
  case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
  { intros [Rs _]; revert Rs; simpl=> ->.
    rewrite Rxmy, Hrx, Hry.
    apply Ulp.succ_round_ge_id.
    { now apply FLT.FLT_exp_valid. }
    now apply Generic_fmt.valid_rnd_N. }
  { now case ss. }
  { now case ss. }
  intros [Rs _]; revert Rs; simpl.
  rewrite <-FtoR_split => ->.
  rewrite Rxmy, Hrx, Hry.
  apply Ulp.succ_round_ge_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
set (sxmy' := xorb _ _).
change (binary_overflow _ _ _ _) with (F754_infinity sxmy').
intros Hxmy _; revert Hxmy.
case_eq b_xmy; [intro sxmy..|intros s pls Hpls|intros sxmy mxmy exmy Hexmy];
  intro Hxmy;
  try (intro H; discriminate H); [ ].
intro Hsxmy'.
assert (Hsxmy : sxmy = sxmy').
{ revert Hsxmy'.
  case sxmy, sxmy'; simpl; try reflexivity; intro H; discriminate H. }
rewrite Hsxmy.
case_eq sxmy'; [ |now simpl].
unfold sxmy'; clear sxmy' sxmy Hxmy Hsxmy' Hsxmy.
revert Hb; rewrite Hrx, Hry; intro Hb.
set (s_b_x := Bsign _ _ b_x).
set (s_b_y := Bsign _ _ b_y).
assert (Hs_b_x : s_b_x = sx).
{ unfold s_b_x, b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
assert (Hs_b_y : s_b_y = sy).
{ unfold s_b_y, b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
rewrite Hs_b_x, Hs_b_y; clear s_b_x s_b_y Hs_b_x Hs_b_y.
intro Hsxy.
revert Hb.
unfold le_upper, FtoX, Xmul.
set (prod := (_ * _)%R).
rewrite Rabs_left1.
2:{ set (fexp := FLT.FLT_exp _ _).
  set (rnd := round_mode _).
  rewrite <-(Generic_fmt.round_0 radix2 fexp rnd).
  apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  revert Hsxy.
  case sx, sy; try (intro H; discriminate H); intros _.
  { pose (Hl := Generic_proof.FtoR_Rneg radix2 mx ex).
    pose (Hr := Generic_proof.FtoR_Rpos radix2 my ey).
    rewrite <-(Rmult_0_l (FtoR radix2 false my ey)).
    apply Rmult_le_compat_r; auto with real. }
  pose (Hl := Generic_proof.FtoR_Rpos radix2 mx ex).
  pose (Hr := Generic_proof.FtoR_Rneg radix2 my ey).
  rewrite <-(Rmult_0_r (FtoR radix2 false mx ex)).
  apply Rmult_le_compat_l; auto with real. }
rewrite <-(Ropp_involutive (bpow _ _)).
intro H; apply Ropp_le_cancel in H; revert H.
unfold round_mode.
set (c := fun _ => _).
elim (Relative.error_N_FLT radix2 (3 - emax - FloatOps.prec) _ prec_gt_0 c prod).
intros eps [eta [Heps [Heta [Hepseta ->]]]].
intro Hb.
case (Req_dec eta 0) => Heta0.
{ revert Hb.
  rewrite Heta0, Rplus_0_r.
  intro Hb.
  apply Rle_trans with (-bpow radix2 emax / (1 + eps))%R.
  { apply (Rmult_le_reg_r (1 + eps)).
    { revert Heps; compute; case Rcase_abs; lra. }
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r; [exact Hb| ].
    revert Heps; compute; case Rcase_abs; lra. }
  apply (Rmult_le_reg_r (1 + eps)).
  { generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r.
  2:{ generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  apply Rle_trans with (FtoR radix2 true (9007199254740992 - 1) 971
                        * (1 + /2 * bpow radix2 (-FloatOps.prec + 1)))%R.
  { compute; lra. }
  apply Rmult_le_compat_neg_l; [compute; lra| ].
  apply Rplus_le_compat_l.
  generalize (Rabs_le_inv _ _ Heps); intros [_ H]; exact H. }
revert Hb.
elim (Rmult_integral _ _ Hepseta); [ |lra]; intros ->.
rewrite Rplus_0_r, Rmult_1_r.
generalize (Rabs_le_inv _ _ Heta); compute; lra.
Qed.

Lemma mul_DN_correct :
  forall p x y,
    ((is_non_neg_real x /\ is_non_neg_real y)
     \/ (is_non_pos_real x /\ is_non_pos_real y)
     \/ (is_non_neg x /\ is_non_pos y)
     \/ (is_non_pos x /\ is_non_neg y))
    -> (valid_lb (mul_DN p x y) = true
        /\ le_lower (toX (mul_DN p x y)) (Xmul (toX x) (toX y))).
Proof.
intros p x y.
unfold mul_DN.
intro H; split; [now rewrite valid_lb_next_down| ]; revert H.
unfold toX, toF.
rewrite next_down_spec, mul_spec.
unfold is_non_neg, is_non_pos, is_non_pos_real, is_non_neg_real.
rewrite !valid_lb_correct, !valid_ub_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
unfold le_lower.
case_eq (Prim2SF x); [intros sx|intros sx| |intros sx mx ex]; intro Hx;
  [..|reflexivity| ].
{ intros _.
  case_eq (Prim2SF y); [intros sy|intros sy| |intros sy my ey]; intro Hy;
    [ |reflexivity..| ]; simpl; rewrite Rmult_0_l; lra. }
{ simpl; intros [H|[H|[H|H]]]; [now destruct H..| | ]; revert H;
    intros [[H1 _] [H2 H3]];
    (revert H1; case sx; try (now intro H; discriminate H); [intros _]);
    (revert H3 H2;
     case_eq (Prim2SF y); [intros sy|intros sy| |intros [ | ] my ey]; intro Hy;
     try reflexivity;
     try (intro H; exfalso; revert H;
          generalize (Generic_proof.FtoR_Rpos radix2 my ey); simpl; lra);
     try (intro H; exfalso; revert H;
          generalize (Generic_proof.FtoR_Rneg radix2 my ey); simpl; lra));
    now (case sy; try (now intro H; discriminate H)). }
case_eq (Prim2SF y); [intros sy|intros sy| |intros sy my ey]; intro Hy;
  [..|reflexivity| ].
{ intros _; simpl; rewrite Rmult_0_r; lra. }
{ simpl; intros [H|[H|[H|H]]]; [now destruct H..| | ]; revert H;
    intros [[H1 H2] [H3 _]];
    (revert H3; case sy; try (now intro H; discriminate H); [intros _]);
    revert H2 H1;
    case sx;
    try (intro H; exfalso; revert H;
         generalize (Generic_proof.FtoR_Rneg radix2 mx ex); simpl; lra);
    try (intro H; exfalso; revert H;
         generalize (Generic_proof.FtoR_Rpos radix2 mx ex); simpl; lra);
    now intros _ _. }
intros _.  (* x and y finite now, don't need the big hypothesis anymore *)
rewrite <-Hx, <-Hy.
rewrite <-!(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
set (b_y := Prim2B _ y).
unfold SF64mul.
rewrite (SpecLayer.SFmul_Bmult prec_gt_0 Hmax (fun _ _ => ex_nan) b_x b_y).
unfold SF64pred.
set (b_xmy := Bmult _ _ _ _ _ _ _ _).
rewrite (SpecLayer.SFpred_Bpred prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xmy).
generalize (Bpred_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xmy).
assert (Fx : is_finite _ _ b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Fy : is_finite _ _ b_y = true).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
generalize (Bmult_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE b_x b_y).
fold b_xmy.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 sx mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
assert (Hry : B2R FloatOps.prec emax b_y = FtoR radix2 sy my ey).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool_spec => Hb.
{ rewrite Fx, Fy.
  intros [Rxmy [Fxmy Sxmy]].
  intro H; generalize (H Fxmy); clear H.
  case Rlt_bool.
  2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity true) eq_refl).
    now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
  set (b_s := Bpred _ _ _ _ _ _ _).
  case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
  { intros [Rs _]; revert Rs; simpl=> ->.
    rewrite Rxmy, Hrx, Hry.
    apply Ropp_le_contravar.
    apply Ulp.pred_round_le_id.
    { now apply FLT.FLT_exp_valid. }
    now apply Generic_fmt.valid_rnd_N. }
  { now case ss. }
  { now case ss. }
  intros [Rs _]; revert Rs; simpl.
  rewrite <-FtoR_split => ->.
  rewrite Rxmy, Hrx, Hry.
  apply Ropp_le_contravar.
  apply Ulp.pred_round_le_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
set (sxmy' := xorb _ _).
change (binary_overflow _ _ _ _) with (F754_infinity sxmy').
intros Hxmy _; revert Hxmy.
case_eq b_xmy; [intro sxmy..|intros s pls Hpls|intros sxmy mxmy exmy Hexmy];
  intro Hxmy;
  try (intro H; discriminate H); [ ].
intro Hsxmy'.
assert (Hsxmy : sxmy = sxmy').
{ revert Hsxmy'.
  case sxmy, sxmy'; simpl; try reflexivity; intro H; discriminate H. }
rewrite Hsxmy.
case_eq sxmy'; [now simpl| ].
unfold sxmy'; clear sxmy' sxmy Hxmy Hsxmy' Hsxmy.
revert Hb; rewrite Hrx, Hry; intro Hb.
set (s_b_x := Bsign _ _ b_x).
set (s_b_y := Bsign _ _ b_y).
assert (Hs_b_x : s_b_x = sx).
{ unfold s_b_x, b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
assert (Hs_b_y : s_b_y = sy).
{ unfold s_b_y, b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
rewrite Hs_b_x, Hs_b_y; clear s_b_x s_b_y Hs_b_x Hs_b_y.
intro Hsxy.
revert Hb.
unfold le_upper, FtoX, Xmul.
set (prod := (_ * _)%R).
rewrite Rabs_pos_eq.
2:{ set (fexp := FLT.FLT_exp _ _).
  set (rnd := round_mode _).
  rewrite <-(Generic_fmt.round_0 radix2 fexp rnd).
  apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  revert Hsxy.
  case sx, sy; try (intro H; discriminate H); intros _.
  { pose (Hl := Generic_proof.FtoR_Rneg radix2 mx ex).
    pose (Hr := Generic_proof.FtoR_Rneg radix2 my ey).
    rewrite <-(Rmult_0_r (FtoR radix2 true mx ex)).
    apply Rmult_le_compat_neg_l; auto with real. }
  pose (Hl := Generic_proof.FtoR_Rpos radix2 mx ex).
  pose (Hr := Generic_proof.FtoR_Rpos radix2 my ey).
  rewrite <-(Rmult_0_r (FtoR radix2 false mx ex)).
  apply Rmult_le_compat_l; auto with real. }
unfold round_mode.
set (c := fun _ => _).
elim (Relative.error_N_FLT radix2 (3 - emax - FloatOps.prec) _ prec_gt_0 c prod).
intros eps [eta [Heps [Heta [Hepseta ->]]]].
intro Hb.
case (Req_dec eta 0) => Heta0.
{ revert Hb.
  rewrite Heta0, Rplus_0_r.
  intro Hb.
  apply Ropp_le_contravar.
  apply Rle_trans with (bpow radix2 emax / (1 + eps))%R.
  2:{ apply (Rmult_le_reg_r (1 + eps)).
    { revert Heps; compute; case Rcase_abs; lra. }
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r; [exact Hb| ].
    revert Heps; compute; case Rcase_abs; lra. }
  apply (Rmult_le_reg_r (1 + eps)).
  { generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r.
  2:{ generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  apply Rle_trans with (FtoR radix2 false (9007199254740992 - 1) 971
                        * (1 + /2 * bpow radix2 (-FloatOps.prec + 1)))%R.
  2:{ compute; lra. }
  apply Rmult_le_compat_l; [compute; lra| ].
  apply Rplus_le_compat_l.
  generalize (Rabs_le_inv _ _ Heps); intros [_ H]; exact H. }
revert Hb.
elim (Rmult_integral _ _ Hepseta); [ |lra]; intros ->.
rewrite Rplus_0_r, Rmult_1_r.
generalize (Rabs_le_inv _ _ Heta); compute; lra.
Qed.

Lemma div_UP_correct :
  forall p x y,
    ((is_non_neg x /\ is_pos_real y)
     \/ (is_non_pos x /\ is_neg_real y)
     \/ (is_non_neg_real x /\ is_neg_real y)
     \/ (is_non_pos_real x /\ is_pos_real y))
    -> (valid_ub (div_UP p x y) = true
        /\ le_upper (Xdiv (toX x) (toX y)) (toX (div_UP p x y))).
Proof.
intros p x y.
unfold div_UP.
intro H; split; [now apply valid_ub_next_up| ]; revert H.
unfold toX, toF.
rewrite next_up_spec, div_spec.
unfold is_non_neg, is_non_pos.
unfold is_pos_real, is_neg_real, is_non_pos_real, is_non_neg_real.
rewrite !valid_lb_correct, !valid_ub_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
case_eq (Prim2SF x); [intros sx|intros sx| |intros sx mx ex]; intro Hx;
  [..|reflexivity| ].
{ case_eq (Prim2SF y); [intros sy|intros sy| |intros sy my ey]; intro Hy;
    [reflexivity| |reflexivity| ]; simpl.
  { now intros [H|[H|H]]; destruct H. }
  intros _; unfold Xdiv', Rdiv; rewrite is_zero_correct_float; lra. }
{ simpl; intros [H|[H|[H|H]]]; [ | |now destruct H..]; revert H;
    intros [[H1 _] H2];
    (revert H1; case sx; try (now intro H; discriminate H); [intros _]);
    (revert H2;
     case_eq (Prim2SF y); [intros sy|intros sy| |intros [ | ] my ey]; intro Hy;
     try reflexivity;
     intro H2; exfalso; revert H2; simpl; try lra;
     try (generalize (Generic_proof.FtoR_Rneg radix2 my ey); simpl; lra);
     try (generalize (Generic_proof.FtoR_Rpos radix2 my ey); simpl; lra)). }
case_eq (Prim2SF y); [intros sy|intros sy| |intros sy my ey]; intro Hy;
  [..|reflexivity| ].
{ intros [H|[H|[H|H]]]; revert H; intros [_ H]; exfalso; revert H; simpl; lra. }
{ now simpl; intros [H|[H|[H|H]]]; destruct H. }
intros _.  (* x and y finite now, don't need the big hypothesis anymore *)
unfold Xdiv, Xdiv', FtoX.
rewrite is_zero_correct_float.
rewrite <-Hx, <-Hy.
rewrite <-!(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
set (b_y := Prim2B _ y).
unfold SF64div.
rewrite (SpecLayer.SFdiv_Bdiv prec_gt_0 Hmax (fun _ _ => ex_nan) b_x b_y).
unfold SF64succ.
set (b_xdy := Bdiv _ _ _ _ _ _ _ _).
rewrite (SpecLayer.SFsucc_Bsucc prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xdy).
generalize (Bsucc_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xdy).
assert (Fx : is_finite _ _ b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Fy : is_finite _ _ b_y = true).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Nzy : B2R FloatOps.prec emax b_y <> 0%R).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B; [intros s..|intros s pl Hpl|intros s m e He];
    [intro H; discriminate H..| ]; intros _; simpl.
  rewrite <-FtoR_split; apply Generic_proof.FtoR_non_neg. }
generalize (Bdiv_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE b_x b_y Nzy).
fold b_xdy.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 sx mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
assert (Hry : B2R FloatOps.prec emax b_y = FtoR radix2 sy my ey).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool_spec => Hb.
{ rewrite Fx.
  intros [Rxdy [Fxdy Sxdy]].
  intro H; generalize (H Fxdy); clear H.
  case Rlt_bool.
  2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity false) eq_refl).
    now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
  set (b_s := Bsucc _ _ _ _ _ _ _).
  case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
  { intros [Rs _]; revert Rs; simpl=> ->.
    rewrite Rxdy, Hrx, Hry.
    apply Ulp.succ_round_ge_id.
    { now apply FLT.FLT_exp_valid. }
    now apply Generic_fmt.valid_rnd_N. }
  { now case ss. }
  { now case ss. }
  intros [Rs _]; revert Rs; simpl.
  rewrite <-FtoR_split => ->.
  rewrite Rxdy, Hrx, Hry.
  apply Ulp.succ_round_ge_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
set (sxdy' := xorb _ _).
change (binary_overflow _ _ _ _) with (F754_infinity sxdy').
intros Hxmy _; revert Hxmy.
case_eq b_xdy; [intro sxdy..|intros s pls Hpls|intros sxdy mxdy exdy Hexdy];
  intro Hxdy;
  try (intro H; discriminate H); [ ].
intro Hsxdy'.
assert (Hsxdy : sxdy = sxdy').
{ revert Hsxdy'.
  case sxdy, sxdy'; simpl; try reflexivity; intro H; discriminate H. }
rewrite Hsxdy.
case_eq sxdy'; [ |now simpl].
unfold sxdy'; clear sxdy' sxdy Hxdy Hsxdy' Hsxdy.
revert Hb; rewrite Hrx, Hry; intro Hb.
set (s_b_x := Bsign _ _ b_x).
set (s_b_y := Bsign _ _ b_y).
assert (Hs_b_x : s_b_x = sx).
{ unfold s_b_x, b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
assert (Hs_b_y : s_b_y = sy).
{ unfold s_b_y, b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
rewrite Hs_b_x, Hs_b_y; clear s_b_x s_b_y Hs_b_x Hs_b_y.
intro Hsxy.
revert Hb.
unfold le_upper, FtoX, Xmul.
set (div := (_ / _)%R).
rewrite Rabs_left1.
2:{ set (fexp := FLT.FLT_exp _ _).
  set (rnd := round_mode _).
  rewrite <-(Generic_fmt.round_0 radix2 fexp rnd).
  apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  revert Hsxy.
  case sx, sy; try (intro H; discriminate H); intros _.
  { pose (Hl := Generic_proof.FtoR_Rneg radix2 mx ex).
    pose (Hr := Rinv_0_lt_compat _ (Generic_proof.FtoR_Rpos radix2 my ey)).
    rewrite <-(Rmult_0_l (/ FtoR radix2 false my ey)).
    apply Rmult_le_compat_r; auto with real. }
  pose (Hl := Generic_proof.FtoR_Rpos radix2 mx ex).
  pose (Hr := Rinv_lt_0_compat _ (Generic_proof.FtoR_Rneg radix2 my ey)).
  rewrite <-(Rmult_0_r (FtoR radix2 false mx ex)).
  apply Rmult_le_compat_l; auto with real. }
rewrite <-(Ropp_involutive (bpow _ _)).
intro H; apply Ropp_le_cancel in H; revert H.
unfold round_mode.
set (c := fun _ => _).
elim (Relative.error_N_FLT radix2 (3 - emax - FloatOps.prec) _ prec_gt_0 c div).
intros eps [eta [Heps [Heta [Hepseta ->]]]].
intro Hb.
case (Req_dec eta 0) => Heta0.
{ revert Hb.
  rewrite Heta0, Rplus_0_r.
  intro Hb.
  apply Rle_trans with (-bpow radix2 emax / (1 + eps))%R.
  { apply (Rmult_le_reg_r (1 + eps)).
    { revert Heps; compute; case Rcase_abs; lra. }
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r; [exact Hb| ].
    revert Heps; compute; case Rcase_abs; lra. }
  apply (Rmult_le_reg_r (1 + eps)).
  { generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r.
  2:{ generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  apply Rle_trans with (FtoR radix2 true (9007199254740992 - 1) 971
                        * (1 + /2 * bpow radix2 (-FloatOps.prec + 1)))%R.
  { compute; lra. }
  apply Rmult_le_compat_neg_l; [compute; lra| ].
  apply Rplus_le_compat_l.
  generalize (Rabs_le_inv _ _ Heps); intros [_ H]; exact H. }
revert Hb.
elim (Rmult_integral _ _ Hepseta); [ |lra]; intros ->.
rewrite Rplus_0_r, Rmult_1_r.
generalize (Rabs_le_inv _ _ Heta); compute; lra.
Qed.

Lemma div_DN_correct :
  forall p x y,
    ((is_non_neg x /\ is_neg_real y)
     \/ (is_non_pos x /\ is_pos_real y)
     \/ (is_non_neg_real x /\ is_pos_real y)
     \/ (is_non_pos_real x /\ is_neg_real y))
    -> (valid_lb (div_DN p x y) = true
        /\ le_lower (toX (div_DN p x y)) (Xdiv (toX x) (toX y))).
Proof.
intros p x y.
unfold div_DN.
intro H; split; [now apply valid_lb_next_down| ]; revert H.
unfold toX, toF.
rewrite next_down_spec, div_spec.
unfold is_non_neg, is_non_pos.
unfold is_pos_real, is_neg_real, is_non_pos_real, is_non_neg_real.
rewrite !valid_lb_correct, !valid_ub_correct.
unfold classify.
rewrite !classify_spec.
unfold toX, toF.
case_eq (Prim2SF x); [intros sx|intros sx| |intros sx mx ex]; intro Hx;
  [..|reflexivity| ].
{ case_eq (Prim2SF y); [intros sy|intros sy| |intros sy my ey]; intro Hy;
    [reflexivity| |reflexivity| ]; simpl.
  { now intros [H|[H|H]]; destruct H. }
  intros _; unfold le_lower, le_upper, Xneg, Xdiv', Rdiv.
  rewrite is_zero_correct_float; lra. }
{ simpl; intros [H|[H|[H|H]]]; [ | |now destruct H..]; revert H;
    intros [[H1 _] H2];
    (revert H1; case sx; try (now intro H; discriminate H); [intros _]);
    (revert H2;
     case_eq (Prim2SF y); [intros sy|intros sy| |intros [ | ] my ey]; intro Hy;
     try reflexivity;
     intro H2; exfalso; revert H2; simpl; try lra;
     try (generalize (Generic_proof.FtoR_Rneg radix2 my ey); simpl; lra);
     try (generalize (Generic_proof.FtoR_Rpos radix2 my ey); simpl; lra)). }
case_eq (Prim2SF y); [intros sy|intros sy| |intros sy my ey]; intro Hy;
  [..|reflexivity| ].
{ intros [H|[H|[H|H]]]; revert H; intros [_ H]; exfalso; revert H; simpl; lra. }
{ now simpl; intros [H|[H|[H|H]]]; destruct H. }
intros _.  (* x and y finite now, don't need the big hypothesis anymore *)
unfold Xdiv, Xdiv', FtoX.
rewrite is_zero_correct_float.
unfold le_lower, Xneg.
rewrite <-Hx, <-Hy.
rewrite <-!(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
set (b_y := Prim2B _ y).
unfold SF64div.
rewrite (SpecLayer.SFdiv_Bdiv prec_gt_0 Hmax (fun _ _ => ex_nan) b_x b_y).
unfold SF64pred.
set (b_xdy := Bdiv _ _ _ _ _ _ _ _).
rewrite (SpecLayer.SFpred_Bpred prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xdy).
generalize (Bpred_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_xdy).
assert (Fx : is_finite _ _ b_x = true).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Fy : is_finite _ _ b_y = true).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  now case Prim2B. }
assert (Nzy : B2R FloatOps.prec emax b_y <> 0%R).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B; [intros s..|intros s pl Hpl|intros s m e He];
    [intro H; discriminate H..| ]; intros _; simpl.
  rewrite <-FtoR_split; apply Generic_proof.FtoR_non_neg. }
generalize (Bdiv_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE b_x b_y Nzy).
fold b_xdy.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 sx mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
assert (Hry : B2R FloatOps.prec emax b_y = FtoR radix2 sy my ey).
{ unfold b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
case Rlt_bool_spec => Hb.
{ rewrite Fx.
  intros [Rxdy [Fxdy Sxdy]].
  intro H; generalize (H Fxdy); clear H.
  case Rlt_bool.
  2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity true) eq_refl).
    now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
  set (b_s := Bpred _ _ _ _ _ _ _).
  case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
  { intros [Rs _]; revert Rs; simpl=> ->.
    rewrite Rxdy, Hrx, Hry.
    apply Ropp_le_contravar.
    apply Ulp.pred_round_le_id.
    { now apply FLT.FLT_exp_valid. }
    now apply Generic_fmt.valid_rnd_N. }
  { now case ss. }
  { now case ss. }
  intros [Rs _]; revert Rs; simpl.
  rewrite <-FtoR_split => ->.
  rewrite Rxdy, Hrx, Hry.
  apply Ropp_le_contravar.
  apply Ulp.pred_round_le_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
set (sxdy' := xorb _ _).
change (binary_overflow _ _ _ _) with (F754_infinity sxdy').
intros Hxmy _; revert Hxmy.
case_eq b_xdy; [intro sxdy..|intros s pls Hpls|intros sxdy mxdy exdy Hexdy];
  intro Hxdy;
  try (intro H; discriminate H); [ ].
intro Hsxdy'.
assert (Hsxdy : sxdy = sxdy').
{ revert Hsxdy'.
  case sxdy, sxdy'; simpl; try reflexivity; intro H; discriminate H. }
rewrite Hsxdy.
case_eq sxdy'; [now simpl| ].
unfold sxdy'; clear sxdy' sxdy Hxdy Hsxdy' Hsxdy.
revert Hb; rewrite Hrx, Hry; intro Hb.
set (s_b_x := Bsign _ _ b_x).
set (s_b_y := Bsign _ _ b_y).
assert (Hs_b_x : s_b_x = sx).
{ unfold s_b_x, b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
assert (Hs_b_y : s_b_y = sy).
{ unfold s_b_y, b_y.
  revert Hy.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  now unfold SpecLayer.B2SF; simpl => H'; inversion H'. }
rewrite Hs_b_x, Hs_b_y; clear s_b_x s_b_y Hs_b_x Hs_b_y.
intro Hsxy.
revert Hb.
unfold le_upper, FtoX, Xmul.
set (div := (_ / _)%R).
rewrite Rabs_pos_eq.
2:{ set (fexp := FLT.FLT_exp _ _).
  set (rnd := round_mode _).
  rewrite <-(Generic_fmt.round_0 radix2 fexp rnd).
  apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  revert Hsxy.
  case sx, sy; try (intro H; discriminate H); intros _.
  { pose (Hl := Generic_proof.FtoR_Rneg radix2 mx ex).
    pose (Hr := Rinv_lt_0_compat _ (Generic_proof.FtoR_Rneg radix2 my ey)).
    rewrite <-(Rmult_0_r (FtoR radix2 true mx ex)).
    apply Rmult_le_compat_neg_l; auto with real. }
  pose (Hl := Generic_proof.FtoR_Rpos radix2 mx ex).
  pose (Hr := Rinv_0_lt_compat _ (Generic_proof.FtoR_Rpos radix2 my ey)).
  rewrite <-(Rmult_0_r (FtoR radix2 false mx ex)).
  apply Rmult_le_compat_l; auto with real. }
unfold round_mode.
set (c := fun _ => _).
elim (Relative.error_N_FLT radix2 (3 - emax - FloatOps.prec) _ prec_gt_0 c div).
intros eps [eta [Heps [Heta [Hepseta ->]]]].
intro Hb.
case (Req_dec eta 0) => Heta0.
{ revert Hb.
  rewrite Heta0, Rplus_0_r.
  intro Hb.
  apply Ropp_le_contravar.
  apply Rle_trans with (bpow radix2 emax / (1 + eps))%R.
  2:{ apply (Rmult_le_reg_r (1 + eps)).
    { revert Heps; compute; case Rcase_abs; lra. }
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r; [exact Hb| ].
    revert Heps; compute; case Rcase_abs; lra. }
  apply (Rmult_le_reg_r (1 + eps)).
  { generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r.
  2:{ generalize (Rabs_le_inv _ _ Heps); compute; lra. }
  apply Rle_trans with (FtoR radix2 false (9007199254740992 - 1) 971
                        * (1 + /2 * bpow radix2 (-FloatOps.prec + 1)))%R.
  2:{ compute; lra. }
  apply Rmult_le_compat_l; [compute; lra| ].
  apply Rplus_le_compat_l.
  generalize (Rabs_le_inv _ _ Heps); intros [_ H]; exact H. }
revert Hb.
elim (Rmult_integral _ _ Hepseta); [ |lra]; intros ->.
rewrite Rplus_0_r, Rmult_1_r.
generalize (Rabs_le_inv _ _ Heta); compute; lra.
Qed.

Lemma sqrt_UP_correct :
  forall p x,
  valid_ub (sqrt_UP p x) = true
  /\ le_upper (Xsqrt (toX x)) (toX (sqrt_UP p x)).
Proof.
intros p x.
unfold sqrt_UP.
split; [now rewrite valid_ub_next_up| ].
unfold toX, toF.
rewrite next_up_spec, sqrt_spec.
case_eq (Prim2SF x); [intros sx|intros [ | ]| |intros [ | ] mx ex]; intro Hx;
  try (now simpl; reflexivity); [ | ].
{ simpl; rewrite sqrt_0; lra. }
rewrite <-Hx.
rewrite <-(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
unfold SF64sqrt.
rewrite (SpecLayer.SFsqrt_Bsqrt prec_gt_0 Hmax (fun _ => ex_nan) b_x).
unfold SF64succ.
set (b_sx := Bsqrt _ _ _ _ _ _ _).
rewrite (SpecLayer.SFsucc_Bsucc prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_sx).
generalize (Bsucc_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_sx).
generalize (Bsqrt_correct _ _ prec_gt_0 Hmax (fun _ => ex_nan) mode_NE b_x).
fold b_sx.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 false mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
intros [Rsx [Fsx Ssx]].
revert Fsx.
set (ma := match b_x with B754_zero _ => _ | _ => _ end).
replace ma with true.
2:{ unfold ma.
  revert Hrx.
  case b_x; [intros [ | ]..|intros s pl Hpl|intros [ | ] m e He];
    simpl; try reflexivity;
      [now generalize (Generic_proof.FtoR_Rpos radix2 mx ex); lra..| ].
  rewrite FtoR_split; simpl; unfold Defs.F2R; simpl.
  set (p1 := (_ * _)%R).
  set (p2 := (_ * _)%R).
  assert (Hp1 : (p1 < 0)%R).
  { unfold p1.
    rewrite Rmult_comm, <-(Rmult_0_r (bpow radix2 e)).
    apply Rmult_lt_compat_l; [apply bpow_gt_0|auto with real]. }
  assert (Hp2 : (0 < p2)%R).
  { unfold p2.
    apply Rmult_lt_0_compat; [auto with real|apply bpow_gt_0]. }
  lra. }
intro Fsx.
intro H; generalize (H Fsx); clear H.
case Rlt_bool.
2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity false) eq_refl).
  now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
set (b_s := Bsucc _ _ _ _ _ _ _).
case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
{ intros [Rs _]; revert Rs; simpl => ->.
  rewrite Rsx, Hrx.
  apply Ulp.succ_round_ge_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
{ now case ss. }
{ now case ss. }
intros [Rs _]; revert Rs; simpl.
rewrite <-FtoR_split => ->.
rewrite Rsx, Hrx.
apply Ulp.succ_round_ge_id.
{ now apply FLT.FLT_exp_valid. }
now apply Generic_fmt.valid_rnd_N.
Qed.

Lemma sqrt_DN_correct :
  forall p x,
    valid_lb x = true
    -> (valid_lb (sqrt_DN p x) = true
        /\ le_lower (toX (sqrt_DN p x)) (Xsqrt (toX x))).
Proof.
intros p x.
unfold sqrt_DN.
intros Vx; split; [now rewrite valid_lb_next_down| ]; revert Vx.
rewrite valid_lb_correct.
unfold classify.
rewrite classify_spec.
unfold toX, toF.
rewrite next_down_spec, sqrt_spec.
case_eq (Prim2SF x); [intros sx|intros [ | ]| |intros [ | ] mx ex]; intro Hx;
  try reflexivity; [ | | ].
{ intros _; apply Ropp_le_contravar; simpl; rewrite sqrt_0; lra. }
{ intro H; discriminate H. }
intros _.
rewrite <-Hx.
rewrite <-(B2SF_Prim2B nan_pl).
set (b_x := Prim2B _ x).
unfold SF64sqrt.
rewrite (SpecLayer.SFsqrt_Bsqrt prec_gt_0 Hmax (fun _ => ex_nan) b_x).
unfold SF64pred.
set (b_sx := Bsqrt _ _ _ _ _ _ _).
rewrite (SpecLayer.SFpred_Bpred prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_sx).
generalize (Bpred_correct _ _ prec_gt_0 Hmax Hemax (fun _ => ex_nan) b_sx).
generalize (Bsqrt_correct _ _ prec_gt_0 Hmax (fun _ => ex_nan) mode_NE b_x).
fold b_sx.
assert (Hrx : B2R FloatOps.prec emax b_x = FtoR radix2 false mx ex).
{ unfold b_x.
  revert Hx.
  rewrite <-(B2SF_Prim2B nan_pl).
  case Prim2B =>[s|s|s pl Hpl|s m e] H; [discriminate H..| ].
  unfold SpecLayer.B2SF; simpl => H'.
  now inversion H'; rewrite <-FtoR_split. }
intros [Rsx [Fsx Ssx]].
revert Fsx.
set (ma := match b_x with B754_zero _ => _ | _ => _ end).
replace ma with true.
2:{ unfold ma.
  revert Hrx.
  case b_x; [intros [ | ]..|intros s pl Hpl|intros [ | ] m e He];
    simpl; try reflexivity;
      [now generalize (Generic_proof.FtoR_Rpos radix2 mx ex); lra..| ].
  rewrite FtoR_split; simpl; unfold Defs.F2R; simpl.
  set (p1 := (_ * _)%R).
  set (p2 := (_ * _)%R).
  assert (Hp1 : (p1 < 0)%R).
  { unfold p1.
    rewrite Rmult_comm, <-(Rmult_0_r (bpow radix2 e)).
    apply Rmult_lt_compat_l; [apply bpow_gt_0|auto with real]. }
  assert (Hp2 : (0 < p2)%R).
  { unfold p2.
    apply Rmult_lt_0_compat; [auto with real|apply bpow_gt_0]. }
  lra. }
intro Fsx.
intro H; generalize (H Fsx); clear H.
case Rlt_bool.
2:{ rewrite <-(B2FF_FF2B FloatOps.prec emax (F754_infinity true) eq_refl).
  now intro H; generalize (B2FF_inj _ _ _ _ H); clear H; intros ->. }
set (b_s := Bpred _ _ _ _ _ _ _).
case_eq b_s; [intro ss..|intros ss pls Hpls|intros ss ms es Hes]; intro Hs.
{ intros [Rs _]; revert Rs; simpl => ->.
  rewrite Rsx, Hrx.
  apply Ropp_le_contravar.
  apply Ulp.pred_round_le_id.
  { now apply FLT.FLT_exp_valid. }
  now apply Generic_fmt.valid_rnd_N. }
{ now case ss. }
{ now case ss. }
intros [Rs _]; revert Rs; simpl.
rewrite <-FtoR_split => ->.
rewrite Rsx, Hrx.
apply Ropp_le_contravar.
apply Ulp.pred_round_le_id.
{ now apply FLT.FLT_exp_valid. }
now apply Generic_fmt.valid_rnd_N.
Qed.

Lemma nearbyint_UP_correct :
  forall mode x,
  valid_ub (nearbyint_UP mode x) = true
  /\ le_upper (Xnearbyint mode (toX x)) (toX (nearbyint_UP mode x)).
Proof. now intros m x; compute. Qed.

Lemma nearbyint_DN_correct :
  forall mode x,
  valid_lb (nearbyint_DN mode x) = true
  /\ le_lower (toX (nearbyint_DN mode x)) (Xnearbyint mode (toX x)).
Proof. now intros m x; compute. Qed.

Lemma midpoint_correct :
  forall x y,
  sensible_format = true ->
  real x = true -> real y = true -> (toR x <= toR y)%R
  -> real (midpoint x y) = true /\ (toR x <= toR (midpoint x y) <= toR y)%R.
Proof.
intros x y _.
rewrite !real_correct.
unfold toR.
rewrite (toX_Prim2B x).
rewrite (toX_Prim2B y).
set (b_x := Prim2B _ x).
set (b_y := Prim2B _ y).
intros Hx Hy Hxy.
unfold midpoint.
fold (div2 x) (div2 y).
rewrite <-(B2Prim_Prim2B nan_pl x).
rewrite <-(B2Prim_Prim2B nan_pl y).
fold b_x b_y.
rewrite <-(B2Prim_Prim2B nan_pl 2).
set (b2 := Prim2B _ 2).
generalize (div2_correct (B2Prim b_y) eq_refl).
generalize (div2_correct (B2Prim b_x) eq_refl).
unfold Xdiv, Xdiv'; rewrite is_zero_false; [ |lra].
unfold div2.
rewrite <-(B2Prim_Prim2B nan_pl 2).
fold b2.
rewrite !(FPdiv_Bdiv (fun _ _ => ex_nan)).
rewrite !(FPadd_Bplus (fun _ _ => ex_nan)).
rewrite (FPdiv_Bdiv (fun _ _ => ex_nan)).
set (bdiv := Bdiv _ _ _ _ _ _).
set (bplus := Bplus _ _ _ _ _ _).
unfold toR; rewrite !toX_B2Prim.
intros Hx2 Hy2.
rewrite is_infinity_spec.
assert (Hb2 : { H | b2 = B754_finite false 4503599627370496 (-51) H }).
{ now compute; set (H := NativeLayer.Prim2B_obligation_1 _ _); exists H. }
assert (Nz2 : B2R FloatOps.prec emax b2 <> 0%R).
{ compute; lra. }
revert Hx Hxy Hx2 Hy2.
case b_x; [intros sx..|intros s pl Hpl|intros sx mx ex Hmex];
  [ |intro H; discriminate H..| ]; intros _.
{ revert Hy.
  case b_y; [intros sy..|intros s pl Hpl|intros sy my ey Hmey];
    [ |intro H; discriminate H..| ]; intros _.
  { revert Hb2; unfold b2; clear b2 Nz2; intro Hb2.
    elim Hb2 => Hb2f ->.
    now case sx, sy; simpl; rewrite toX_B2Prim; simpl;
      (split; [ |split; right]). }
  case sy; [intro Hy; simpl in Hy|intros _ _].
  { generalize (Generic_proof.FtoR_Rneg radix2 my ey); lra. }
  change (bplus (B754_zero sx) _) with (B754_finite false my ey Hmey).
  set (by2 := bdiv (B754_finite false my ey Hmey) b2).
  elim (Bdiv2_correct (B754_finite false my ey Hmey) eq_refl).
  fold bdiv; fold b2; fold by2.
  intros _ [Fy2 [Sy2 Hy2']]; revert Fy2 Sy2 Hy2'.
  case by2 => [sy2|sy2|s pl Hpl|sy2 my2 ey2 Hmey2];
    [ |intro H; discriminate H..| ]; intros _;
    rewrite toX_B2Prim; simpl.
  { intros _ _.
    split; [reflexivity|split; [now right| ]].
    apply Rlt_le, Generic_proof.FtoR_Rpos. }
  intros ->.
  change (Z.pos my) with (cond_Zopp false (Z.pos my)).
  rewrite <-!FtoR_split, !Generic_proof.FtoR_abs.
  intro H; split; [reflexivity|split; [ |exact H]].
  apply Rlt_le, Generic_proof.FtoR_Rpos. }
revert Hy.
case b_y; [intros sy..|intros s pl Hpl|intros sy my ey Hmey];
  [ |intro H; discriminate H..| ]; intros _.
{ case sx; [intros _|intros Hx; simpl in Hx].
  2:{ generalize (Generic_proof.FtoR_Rpos radix2 mx ex); lra. }
  change (bplus _ (B754_zero sy)) with (B754_finite true mx ex Hmex).
  set (bx2 := bdiv (B754_finite true mx ex Hmex) b2).
  elim (Bdiv2_correct (B754_finite true mx ex Hmex) eq_refl).
  fold bdiv; fold b2; fold bx2.
  intros _ [Fx2 [Sx2 Hx2]]; revert Fx2 Sx2 Hx2.
  case bx2 => [sx2|sx2|s pl Hpl|sx2 mx2 ex2 Hmex2];
    [ |intro H; discriminate H..| ]; intros _;
    rewrite toX_B2Prim; simpl.
  { intros _ _.
    split; [reflexivity|split; [ |now right]].
    apply Rlt_le, Generic_proof.FtoR_Rneg. }
  intros ->.
  change (Z.neg mx) with (cond_Zopp true (Z.pos mx)).
  rewrite <-!FtoR_split, !Generic_proof.FtoR_abs.
  intro H; split; [reflexivity|split].
  2:{ apply Rlt_le, Generic_proof.FtoR_Rneg. }
  change true with (negb false).
  rewrite <-!Generic_proof.FtoR_neg.
  now apply Ropp_le_contravar. }
clear x y b_x b_y.
set (b_x := B754_finite sx mx ex Hmex).
set (b_y := B754_finite sy my ey Hmey).
intros Hxy Hx2 Hy2; simpl in Hxy; unfold proj_val in Hx2,Hy2.
generalize (Bplus_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE
                          b_x b_y eq_refl eq_refl).
fold bplus.
case Rlt_bool_spec => Hb.
{ intros [Rxpy [Fxpy Sxpy]].
  elim (Bdiv2_correct (bplus b_x b_y) Fxpy).
  fold bdiv; fold b2.
  intros _ [Fxpy2 _].
  replace (match bdiv _ _ with B754_infinity _ => true | _ => _ end)
    with false; [ |now revert Fxpy2; case bdiv].
  rewrite toX_B2Prim; split; [now revert Fxpy2; case bdiv| ].
  elim (Bdiv2_correct _ Fxpy); fold bdiv b2.
  intros Rxpy2 _.
  set (rx := FtoR _ sx mx ex).
  set (ry := FtoR _ sy my ey).
  revert Rxpy Rxpy2.
  set (fexp := FLT.FLT_exp _ _).
  set (m := round_mode _).
  set (b2r := B2R _ _).
  intros Rxpy Rxpy2.
  rewrite <-(Generic_fmt.round_generic radix2 fexp m rx).
  2:{ unfold rx; rewrite FtoR_split; change (Defs.F2R _) with (b2r b_x).
    apply generic_format_B2R. }
  rewrite <-(Generic_fmt.round_generic radix2 fexp m ry).
  2:{ unfold ry; rewrite FtoR_split; change (Defs.F2R _) with (b2r b_y).
    apply generic_format_B2R. }
  replace rx with ((rx + rx) / 2)%R; [ |lra].
  replace ry with ((ry + ry) / 2)%R; [ |lra].
  unfold proj_val at -2-3.
  replace (proj_val _) with (b2r (bdiv (bplus b_x b_y) b2)).
  2:{ case bdiv => [s|s|s pl Hpl|sb mb eb Hmeb]; [reflexivity..| ].
      now unfold b2r, B2R; rewrite <-FtoR_split. }
  rewrite Rxpy2, Rxpy.
  split;
    (apply Generic_fmt.round_le;
     [now apply FLT.FLT_exp_valid|now apply Generic_fmt.valid_rnd_N| ];
     unfold Rdiv; apply Rmult_le_compat_r; [lra| ]).
  { rewrite <-(Generic_fmt.round_generic radix2 fexp m (rx + rx)).
    { apply Generic_fmt.round_le.
      { now apply FLT.FLT_exp_valid. }
      { now apply Generic_fmt.valid_rnd_N. }
      unfold b2r, B2R, b_x, b_y; rewrite <-!FtoR_split.
      now apply Rplus_le_compat_l. }
    replace (rx + rx)%R with (rx * bpow radix2 1)%R; [ |simpl; lra].
    apply mult_bpow_pos_exact_FLT; [ |lia].
    unfold rx; rewrite FtoR_split; change (Defs.F2R _) with (b2r b_x).
    apply generic_format_B2R. }
  rewrite <-(Generic_fmt.round_generic radix2 fexp m (ry + ry)).
  { apply Generic_fmt.round_le.
    { now apply FLT.FLT_exp_valid. }
    { now apply Generic_fmt.valid_rnd_N. }
    unfold b2r, B2R, b_x, b_y; rewrite <-!FtoR_split.
    now apply Rplus_le_compat_r. }
  replace (ry + ry)%R with (ry * bpow radix2 1)%R; [ |simpl; lra].
  apply mult_bpow_pos_exact_FLT; [ |lia].
  unfold ry; rewrite FtoR_split; change (Defs.F2R _) with (b2r b_y).
  apply generic_format_B2R. }
change (binary_overflow _ _ _ _)
  with (@B2FF FloatOps.prec emax (B754_infinity sx)).
intros [H H']; revert H'; rewrite (B2FF_inj _ _ _ _ H); clear H.
intro Hsxy; simpl in Hsxy.
change (match bdiv _ _ with B754_infinity _ => true | _ => _ end) with true.
rewrite toX_Prim2B.
revert Hb.
set (fexp := FLT.FLT_exp _ _).
set (m := round_mode _).
set (b2r := B2R _ _).
elim (Plus_error.FLT_plus_error_N_ex
        _ _ _ (fun x : Z => negb (Z.even x))
        _ _ (generic_format_B2R _ _ b_x) (generic_format_B2R _ _ b_y)).
change (Generic_fmt.Znearest _) with (round_mode mode_NE).
fold fexp m b2r.
intros eps [Heps ->].
rewrite Rabs_mult.
intro Hb.
assert (R1peps : (0 < Rabs (1 + eps))%R).
{ apply Rabs_gt; right.
  generalize (Rle_trans _ _ _ Heps (Relative.u_rod1pu_ro_le_u_ro _ _)).
  intro H; generalize (Rabs_le_inv _ _ H); compute; lra. }
generalize (Rmult_le_compat_r _ _ _ (Rlt_le _ _ (Rinv_0_lt_compat _ R1peps)) Hb).
rewrite Rmult_assoc, Rinv_r, ?Rmult_1_r; [ |lra].
clear Hb; intro Hb.
generalize (Rle_trans _ _ _ Hb (Rabs_triang _ _)).
clear Hb; intro Hb.
assert (Hb' : (1 / 256
               <= bpow radix2 emax * / Rabs (1 + eps)
                  - (bpow radix2 emax - bpow radix2 (emax - FloatOps.prec)))%R).
{ rewrite Rcomplements.Rle_minus_r.
  apply (Rmult_le_reg_r _ _ _ R1peps).
  rewrite Rmult_assoc, Rinv_l, ?Rmult_1_r; [ |lra].
  refine (Rle_trans _ _ _ (Rmult_le_compat_l _ _ _ _
    (Rle_trans _ _ _ (Rabs_triang _ _) (Rplus_le_compat_l _ _ _ Heps))) _).
  { apply Rplus_le_le_0_compat; [lra| ].
    now apply Rle_0_minus, bpow_le; compute. }
  rewrite (Rabs_pos_eq _ Rle_0_1).
  compute; lra. }
assert (Hx2h : (1 / 256 <= Rabs (FtoR radix2 sx mx ex))%R).
{ apply (Rle_trans _ _ _ Hb').
  apply (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ Hb)).
  rewrite FtoR_split; change (Defs.F2R _) with (b2r b_x).
  apply (Rplus_le_reg_r (- Rabs (b2r b_y))).
  ring_simplify.
  unfold Rminus; rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  generalize (abs_B2R_le_emax_minus_prec _ emax prec_gt_0 b_y).
  fold b2r; lra. }
assert (Hy2h : (1 / 256 <= Rabs (FtoR radix2 sy my ey))%R).
{ apply (Rle_trans _ _ _ Hb').
  apply (Rle_trans _ _ _ (Rplus_le_compat_r _ _ _ Hb)).
  rewrite FtoR_split; change (Defs.F2R _) with (b2r b_y).
  apply (Rplus_le_reg_r (- Rabs (b2r b_x))).
  ring_simplify.
  unfold Rminus; rewrite Rplus_assoc, Rplus_comm.
  apply Rplus_le_compat_r.
  generalize (abs_B2R_le_emax_minus_prec _ emax prec_gt_0 b_x).
  fold b2r; lra. }
specialize (Hx2 Hx2h).
specialize (Hy2 Hy2h).
assert (Fx2 : is_finite FloatOps.prec emax (bdiv b_x b2) = true).
{ revert Hx2; case bdiv => [s|s|s pl Hpl|s m' e Hme];
    [ |intro H; discriminate H..| ]; reflexivity. }
assert (Fy2 : is_finite FloatOps.prec emax (bdiv b_y b2) = true).
{ revert Hy2; case bdiv => [s|s|s pl Hpl|s m' e Hme];
    [ |intro H; discriminate H..| ]; reflexivity. }
generalize (Bplus_correct _ _ prec_gt_0 Hmax (fun _ _ => ex_nan) mode_NE
                          _ _ Fx2 Fy2).
fold b2r bplus fexp m.
replace (b2r (bdiv b_x b2)) with (b2r b_x / 2)%R.
2:{ revert Hx2.
  case bdiv => [s|s|s pl Hpl|s m' e Hme]; [ |intro H; discriminate H..| ].
  { now intro H; inversion H as (H'); simpl; rewrite H', FtoR_split. }
  intro H; inversion H as (H'); revert H'; simpl.
  now rewrite !FtoR_split => ->. }
replace (b2r (bdiv b_y b2)) with (b2r b_y / 2)%R.
2:{ revert Hy2.
  case bdiv => [s|s|s pl Hpl|s m' e Hme]; [ |intro H; discriminate H..| ].
  { now intro H; inversion H as (H'); simpl; rewrite H', FtoR_split. }
  intro H; inversion H as (H'); revert H'; simpl.
  now rewrite !FtoR_split => ->. }
rewrite Rlt_bool_true.
2:{ unfold b_x, b_y; rewrite <-Hsxy.
  case_eq sx => Hsx.
  { apply (Rle_lt_trans _ (Rabs (b2r b_x))).
    2:{ apply abs_B2R_lt_emax. }
    rewrite Rabs_left1.
    2:{ rewrite <-(Generic_fmt.round_0 radix2 fexp m).
      apply Generic_fmt.round_le.
      { now apply FLT.FLT_exp_valid. }
      { now apply Generic_fmt.valid_rnd_N. }
      simpl.
      change (Z.neg mx) with (cond_Zopp true (Z.pos mx)).
      change (Z.neg my) with (cond_Zopp true (Z.pos my)).
      rewrite <-!FtoR_split.
      generalize (Generic_proof.FtoR_Rneg radix2 mx ex).
      generalize (Generic_proof.FtoR_Rneg radix2 my ey).
      lra. }
    rewrite Rabs_left1.
    2:{ simpl.
      rewrite <-FtoR_split, Hsx.
      generalize (Generic_proof.FtoR_Rneg radix2 mx ex).
      lra. }
    apply Ropp_le_contravar.
    rewrite <-(Generic_fmt.round_generic radix2 fexp m (b2r b_x)).
    { apply Generic_fmt.round_le.
      { now apply FLT.FLT_exp_valid. }
      { now apply Generic_fmt.valid_rnd_N. }
      replace (b2r b_x) with (b2r b_x / 2 + b2r b_x / 2)%R by field.
      rewrite <-Hsx; apply Rplus_le_compat_l.
      apply Rmult_le_compat_r; [lra| ].
      now revert Hxy; rewrite !FtoR_split, <-Hsxy. }
    apply generic_format_B2R. }
  apply (Rle_lt_trans _ (Rabs (b2r b_y))).
  2:{ apply abs_B2R_lt_emax. }
  rewrite Rabs_pos_eq.
  2:{ rewrite <-(Generic_fmt.round_0 radix2 fexp m).
    apply Generic_fmt.round_le.
    { now apply FLT.FLT_exp_valid. }
    { now apply Generic_fmt.valid_rnd_N. }
    simpl.
    change (Z.pos mx) with (cond_Zopp false (Z.pos mx)).
    change (Z.pos my) with (cond_Zopp false (Z.pos my)).
    rewrite <-!FtoR_split.
    generalize (Generic_proof.FtoR_Rpos radix2 mx ex).
    generalize (Generic_proof.FtoR_Rpos radix2 my ey).
    lra. }
  rewrite Rabs_pos_eq.
  2:{ simpl.
    rewrite <-FtoR_split, <-Hsxy, Hsx.
    generalize (Generic_proof.FtoR_Rpos radix2 my ey).
    lra. }
  rewrite <-(Generic_fmt.round_generic radix2 fexp m (b2r b_y)).
  { apply Generic_fmt.round_le.
    { now apply FLT.FLT_exp_valid. }
    { now apply Generic_fmt.valid_rnd_N. }
    replace (b2r b_y) with (b2r b_y / 2 + b2r b_y / 2)%R by field.
    rewrite <-Hsx, Hsxy; apply Rplus_le_compat_r.
    apply Rmult_le_compat_r; [lra| ].
    now revert Hxy; rewrite !FtoR_split, Hsxy. }
  apply generic_format_B2R. }
intros [Rx2py2 [Fx2py2 _]].
rewrite Prim2B_B2Prim_notnan.
2:{ revert Fx2py2; case bplus => [s|s|s pl Hpl|s m' e Hme];
      [ |intro H; discriminate H..| ]; reflexivity. }
split.
{ revert Fx2py2; case bplus => [s|s|s pl Hpl|s m' e Hme];
    [ |intro H; discriminate H..| ]; reflexivity. }
unfold proj_val at -2-3.
replace (proj_val _) with (b2r (bplus (bdiv b_x b2) (bdiv b_y b2))).
2:{ now case bplus => [s|s|s pl Hpl|s m' e Hme]; [..|rewrite FtoR_split]. }
rewrite FtoR_split; change (Defs.F2R _) with (b2r b_x).
rewrite FtoR_split; change (Defs.F2R _) with (b2r b_y).
rewrite Rx2py2.
rewrite <-(Generic_fmt.round_generic radix2 fexp m (b2r b_x)) at 1.
2:{ apply generic_format_B2R. }
rewrite <-(Generic_fmt.round_generic radix2 fexp m (b2r b_y)) at 3.
2:{ apply generic_format_B2R. }
split.
{ apply Generic_fmt.round_le.
  { now apply FLT.FLT_exp_valid. }
  { now apply Generic_fmt.valid_rnd_N. }
  replace (b2r b_x) with (b2r b_x / 2 + b2r b_x / 2)%R at 1 by field.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_r; [lra| ].
  now revert Hxy; rewrite !FtoR_split. }
apply Generic_fmt.round_le.
{ now apply FLT.FLT_exp_valid. }
{ now apply Generic_fmt.valid_rnd_N. }
replace (b2r b_y) with (b2r b_y / 2 + b2r b_y / 2)%R at 2 by field.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r; [lra| ].
now revert Hxy; rewrite !FtoR_split.
Qed.

End PrimitiveFloat.
