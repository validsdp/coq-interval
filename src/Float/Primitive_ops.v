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

Module PrimitiveFloat <: FloatOps.

Definition radix := radix2.
Definition sensible_format := true.

Definition type := PrimFloat.float.

Definition bigZ_of_int x := BigZ.Pos (BigN.N0 x).

Definition prim_to_big (x : PrimFloat.float) : SFBI2.type :=
  match classify x with
  | PZero | NZero => Float 0%bigZ 0%bigZ
  | PInf | NInf | NaN => Fnan
  | PNormal | PSubn =>
    let (m, e) := frshiftexp x in
    let m := bigZ_of_int (normfr_mantissa m) in
    let e := (bigZ_of_int e - bigZ_of_int (Int63.of_Z FloatOps.shift + 53)%int63)%bigZ in
    Float m e
  | NNormal | NSubn =>
    let (m, e) := frshiftexp x in
    let m := bigZ_of_int (normfr_mantissa m) in
    let e := (bigZ_of_int e - bigZ_of_int (Int63.of_Z FloatOps.shift + 53)%int63)%bigZ in
    Float (- m)%bigZ e
  end.

Definition toF x := SFBI2.toF (prim_to_big x).

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

Definition fromZ_UP := fromZ_default infinity.

Definition fromZ_DN := fromZ_default neg_infinity.

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

Definition mag x := SFBI2.mag (prim_to_big x).

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
Proof.
Admitted.
(* cette preuve ne passe pas au Qed, à regerder *)
(* now compute; rewrite Rinv_r; [unfold IZR, IPR|lra]. Qed. *)

Lemma nan_correct : classify nan = Sig.Fnan.
Proof. reflexivity. Qed.

(* From ValidSDP Require Import FlocqNativeLayer. *)

Lemma fromZ_correct :
  forall n, sensible_format = true ->
  (Z.abs n <= 256)%Z -> toX (fromZ n) = Xreal (IZR n).
Proof.
Admitted.

Lemma fromZ_UP_correct :
  forall n,
  valid_ub (fromZ_UP n) = true /\ le_upper (Xreal (IZR n)) (toX (fromZ_UP n)).
Proof.
Admitted.

Lemma fromZ_DN_correct :
  forall n,
  valid_lb (fromZ_DN n) = true /\ le_lower (toX (fromZ_DN n)) (Xreal (IZR n)).
Proof.
Admitted.

Lemma classify_correct :
  forall f, real f = match classify f with Freal => true | _ => false end.
Proof.
Admitted.

Lemma real_correct :
  forall f, real f = match toX f with Xnan => false | _ => true end.
Proof.
Admitted.

Lemma is_nan_correct :
  forall f, is_nan f = match classify f with Sig.Fnan => true | _ => false end.
Proof.
Admitted.

Lemma valid_lb_correct :
  forall f, valid_lb f = match classify f with Fpinfty => false | _ => true end.
Proof.
Admitted.

Lemma valid_ub_correct :
  forall f, valid_ub f = match classify f with Fminfty => false | _ => true end.
Proof.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma neg_correct :
  forall x,
  match classify x with
  | Freal => toX (neg x) = Xneg (toX x)
  | Sig.Fnan => classify (neg x) = Sig.Fnan
  | Fminfty => classify (neg x) = Fpinfty
  | Fpinfty => classify (neg x) = Fminfty
  end.
Proof.
Admitted.

Lemma abs_correct :
  forall x, toX (abs x) = Xabs (toX x) /\ (valid_ub (abs x) = true).
Proof.
Admitted.

Lemma div2_correct :
  forall x, sensible_format = true ->
  (1 / 256 <= Rabs (toR x))%R ->
  toX (div2 x) = Xdiv (toX x) (Xreal 2).
Proof.
Admitted.

Lemma add_UP_correct :
  forall p x y, valid_ub x = true -> valid_ub y = true
    -> (valid_ub (add_UP p x y) = true
       /\ le_upper (Xadd (toX x) (toX y)) (toX (add_UP p x y))).
Proof.
Admitted.

Lemma add_DN_correct :
  forall p x y, valid_lb x = true -> valid_lb y = true
    -> (valid_lb (add_DN p x y) = true
       /\ le_lower (toX (add_DN p x y)) (Xadd (toX x) (toX y))).
Proof.
Admitted.

Lemma sub_UP_correct :
  forall p x y, valid_ub x = true -> valid_lb y = true
    -> (valid_ub (sub_UP p x y) = true
       /\ le_upper (Xsub (toX x) (toX y)) (toX (sub_UP p x y))).
Proof.
Admitted.

Lemma sub_DN_correct :
  forall p x y, valid_lb x = true -> valid_ub y = true
    -> (valid_lb (sub_DN p x y) = true
       /\ le_lower (toX (sub_DN p x y)) (Xsub (toX x) (toX y))).
Proof.
Admitted.

Lemma mul_UP_correct :
  forall p x y,
    ((valid_ub x = true /\ valid_ub y = true
      /\ (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
      /\ (match toX y with Xnan => True | Xreal r => (0 <= r)%R end))
     \/ (valid_lb x = true /\ valid_lb y = true
         /\ (match toX x with Xnan => True | Xreal r => (r <= 0)%R end)
         /\ (match toX y with Xnan => True | Xreal r => (r <= 0)%R end))
     \/ (match toX x with Xnan => False | Xreal r => (r <= 0)%R end
        /\ match toX y with Xnan => False | Xreal r => (0 <= r)%R end)
     \/ (match toX x with Xnan => False | Xreal r => (0 <= r)%R end
        /\ match toX y with Xnan => False | Xreal r => (r <= 0)%R end))
    -> (valid_ub (mul_UP p x y) = true
        /\ le_upper (Xmul (toX x) (toX y)) (toX (mul_UP p x y))).
Proof.
Admitted.

Lemma mul_DN_correct :
  forall p x y,
    ((match toX x with Xnan => False | Xreal r => (0 <= r)%R end
      /\ match toX y with Xnan => False | Xreal r => (0 <= r)%R end)
     \/ (match toX x with Xnan => False | Xreal r => (r <= 0)%R end
        /\ match toX y with Xnan => False | Xreal r => (r <= 0)%R end)
     \/ (valid_ub x = true /\ valid_lb y = true
         /\ (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
         /\ (match toX y with Xnan => True | Xreal r => (r <= 0)%R end))
     \/ (valid_lb x = true /\ valid_ub y = true
         /\ (match toX x with Xnan => True | Xreal r => (r <= 0)%R end)
         /\ (match toX y with Xnan => True | Xreal r => (0 <= r)%R end)))
    -> (valid_lb (mul_DN p x y) = true
        /\ le_lower (toX (mul_DN p x y)) (Xmul (toX x) (toX y))).
Proof.
Admitted.

Lemma div_UP_correct :
  forall p x y,
    ((valid_ub x = true
      /\ (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
      /\ (match toX y with Xnan => False | Xreal r => (0 < r)%R end))
     \/ (valid_lb x = true
         /\ (match toX x with Xnan => True | Xreal r => (r <= 0)%R end)
         /\ (match toX y with Xnan => False | Xreal r => (r < 0)%R end))
     \/ (match toX x with Xnan => False | Xreal r => (0 <= r)%R end
        /\ match toX y with Xnan => False | Xreal r => (r < 0)%R end)
     \/ (match toX x with Xnan => False | Xreal r => (r <= 0)%R end
        /\ match toX y with Xnan => False | Xreal r => (0 < r)%R end))
    -> (valid_ub (div_UP p x y) = true
        /\ le_upper (Xdiv (toX x) (toX y)) (toX (div_UP p x y))).
Proof.
Admitted.

Lemma div_DN_correct :
  forall p x y,
    ((valid_ub x = true
      /\ (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
      /\ (match toX y with Xnan => False | Xreal r => (r < 0)%R end))
     \/ (valid_lb x = true
         /\ (match toX x with Xnan => True | Xreal r => (r <= 0)%R end)
         /\ (match toX y with Xnan => False | Xreal r => (0 < r)%R end))
     \/ (match toX x with Xnan => False | Xreal r => (0 <= r)%R end
        /\ match toX y with Xnan => False | Xreal r => (0 < r)%R end)
     \/ (match toX x with Xnan => False | Xreal r => (r <= 0)%R end
        /\ match toX y with Xnan => False | Xreal r => (r < 0)%R end))
    -> (valid_lb (div_DN p x y) = true
        /\ le_lower (toX (div_DN p x y)) (Xdiv (toX x) (toX y))).
Proof.
Admitted.

Lemma sqrt_UP_correct :
  forall p x,
  valid_ub (sqrt_UP p x) = true
  /\ le_upper (Xsqrt (toX x)) (toX (sqrt_UP p x)).
Proof.
Admitted.

Lemma sqrt_DN_correct :
  forall p x,
    valid_lb x = true
    -> (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
    -> (valid_lb (sqrt_DN p x) = true
        /\ le_lower (toX (sqrt_DN p x)) (Xsqrt (toX x))).
Proof.
Admitted.

Lemma nearbyint_UP_correct :
  forall mode x,
  valid_ub (nearbyint_UP mode x) = true
  /\ le_upper (Xnearbyint mode (toX x)) (toX (nearbyint_UP mode x)).
Proof.
Admitted.

Lemma nearbyint_DN_correct :
  forall mode x,
  valid_lb (nearbyint_DN mode x) = true
  /\ le_lower (toX (nearbyint_DN mode x)) (Xnearbyint mode (toX x)).
Proof.
Admitted.

Lemma midpoint_correct :
  forall x y,
  sensible_format = true ->
  real x = true -> real y = true -> (toR x <= toR y)%R
  -> real (midpoint x y) = true /\ (toR x <= toR (midpoint x y) <= toR y)%R.
Proof.
Admitted.

End PrimitiveFloat.
