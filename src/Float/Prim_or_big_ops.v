From Coq Require Import ZArith Int63 Floats.
From Flocq Require Import Raux.
From Bignums Require Import BigZ.

Require Import Xreal.
Require Import Basic.
Require Import Sig.
Require Import Interval.Interval.  (* for le_upper/lower, TODO PR: move them? *)

Require Import Specific_bigint.
Require Import Specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.

Module PrimOrBigFloat <: FloatOps.

Definition radix := radix2.
Definition sensible_format := true.

Variant sum_type :=
  | Fprim : PrimFloat.float -> sum_type
  | Fbig : SFBI2.type -> sum_type.
Definition type := sum_type.

Definition bigZ_of_int x := BigZ.Pos (BigN.N0 x).

Definition prim_to_big (x : PrimFloat.float) : SFBI2.type :=
  match classify x with
  | PZero | NZero => Float 0%bigZ 0%bigZ
  | PInf | NInf | NaN => Fnan
  | PNormal | PSubn =>
    let (m, e) := frshiftexp x in
    let m := bigZ_of_int (normfr_mantissa m) in
    let e := (bigZ_of_int e - bigZ_of_int (PrimFloat.shift + 53)%int63)%bigZ in
    Float m e
  | NNormal | NSubn =>
    let (m, e) := frshiftexp x in
    let m := bigZ_of_int (normfr_mantissa m) in
    let e := (bigZ_of_int e - bigZ_of_int (PrimFloat.shift + 53)%int63)%bigZ in
    Float (- m)%bigZ e
  end.

Definition toF x :=
  match x with
  | Fprim f => SFBI2.toF (prim_to_big f)
  | Fbig f => SFBI2.toF f
  end.

Definition precision := SFBI2.precision.
Definition sfactor := SFBI2.sfactor.
Definition prec := SFBI2.prec.
Definition PtoP := SFBI2.PtoP.
Definition ZtoS := SFBI2.ZtoS.
Definition StoZ := SFBI2.StoZ.
Definition incr_prec := SFBI2.incr_prec.

Definition zero := Fprim zero.
Definition nan := Fbig Fnan.

Definition fromZ x :=
  let f := of_int63 (Int63.of_Z x) in
  let (m, e) := frshiftexp f in
  let m := normfr_mantissa m in
  let i := (bigZ_of_int m * 2 ^ (bigZ_of_int e - bigZ_of_int PrimFloat.shift))%bigZ in
  if (BigZ.of_Z x =? i)%bigZ then Fprim f else Fbig (SFBI2.fromZ x).

Definition Z_size m :=
  match m with
  | Zpos p => Pos.size p
  | Z0 => 1%positive
  | Zneg p => Pos.size p
  end.

Definition fromF f :=
  match f with
  | Basic.Fnan => nan
  | Basic.Fzero => zero
  | Basic.Float s m e =>
    if ((e <=? 971)%Z && (-1074 <=? e)%Z
        && (Pos.size m <=? 53)%positive)%bool then
      let m := of_int63 (Int63.of_pos m) in
      let e := Int63.of_Z (e + Int63.to_Z shift) in
      let f := ldshiftexp m e in
      if s then Fprim (- f)%float else Fprim f
    else Fbig (SFBI2.fromF f)
  end.

Definition real x :=
  match x with
  | Fprim f =>
    match classify f with
    | PInf | NInf | NaN => false
    | _ => true
    end
  | Fbig f => SFBI2.real f
  end.

Definition mag x :=
  match x with
  | Fprim f => SFBI2.mag (prim_to_big f)
  | Fbig f => SFBI2.mag f
  end.

Definition comparison_of_float_comparison c :=
  match c with
  | FEq => Eq
  | FLt => Lt
  | FGt => Gt
  | FNotComparable => Eq
  end.

Definition cmp x y :=
  match x, y with
  | Fprim x, Fprim y => comparison_of_float_comparison (compare x y)
  | Fprim x, Fbig y => SFBI2.cmp (prim_to_big x) y
  | Fbig x, Fprim y => SFBI2.cmp x (prim_to_big y)
  | Fbig x, Fbig y => SFBI2.cmp x y
  end.

Definition min' x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    match compare xf yf with
    | FEq | FLt => x
    | FGt => y
    | FNotComparable => nan
    end
  | Fprim xf, Fbig yb =>
    match SFBI2.cmp (prim_to_big xf) yb with
    | Eq | Lt => x
    | Gt => y
    end
  | Fbig xb, Fprim yf =>
    match SFBI2.cmp xb (prim_to_big yf) with
    | Lt => x
    | Eq | Gt => y
    end
  | Fbig xb, Fbig yb =>
    match SFBI2.cmp xb yb with
    | Eq | Lt => x
    | Gt => y
    end
  end.

Definition min x y := if (real x && real y)%bool then min' x y else nan.

Definition max' x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    match compare xf yf with
    | FEq | FGt => x
    | FLt => y
    | FNotComparable => nan
    end
  | Fprim xf, Fbig yb =>
    match SFBI2.cmp (prim_to_big xf) yb with
    | Eq | Gt => x
    | Lt => y
    end
  | Fbig xb, Fprim yf =>
    match SFBI2.cmp xb (prim_to_big yf) with
    | Gt => x
    | Eq | Lt => y
    end
  | Fbig xb, Fbig yb =>
    match SFBI2.cmp xb yb with
    | Eq | Gt => x
    | Lt => y
    end
  end.

Definition max x y := if (real x && real y)%bool then max' x y else nan.

(* TODO: improve ? *)
Definition round (mode : rounding_mode) (prec : precision) (x : type) : type :=
  match x with
  | Fprim f => Fbig (SFBI2.round mode prec (prim_to_big f))
  | Fbig f => Fbig (SFBI2.round mode prec f)
  end.

Definition neg x :=
  match x with
  | Fprim f => Fprim (- f)%float
  | Fbig f => Fbig (SFBI2.neg f)
  end.

Definition abs x :=
  match x with
  | Fprim f => Fprim (abs f)
  | Fbig f => Fbig (SFBI2.abs f)
  end.

(* TODO: improve ? *)
Definition scale x e :=
  match x with
  | Fprim f => Fbig (SFBI2.scale (prim_to_big f) e)
  | Fbig f => Fbig (SFBI2.scale f e)
  end.

Definition div2 x :=
  match x with
  | Fprim f => Fprim (f / 2)%float
  | Fbig f => Fbig (SFBI2.div2 f)
  end.

Definition add_UP prec x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    let z := (xf + yf)%float in
    (* TODO : benchmark and see whether it would be beneficial to use
       classify to check equality with -oo *)
    match (z ?= neg_infinity)%float with
    | FEq => Fprim z
    | _ => Fprim (next_up z)
    end
  | Fprim xf, Fbig yb => Fbig (SFBI2.add_UP prec (prim_to_big xf) yb)
  | Fbig xb, Fprim yf => Fbig (SFBI2.add_UP prec xb (prim_to_big yf))
  | Fbig xb, Fbig yb => Fbig (SFBI2.add_UP prec xb yb)
  end.

Definition add_DN prec x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    let z := (xf + yf)%float in
    match (z ?= infinity)%float with
    | FEq => Fprim z
    | _ => Fprim (next_down z)
    end
  | Fprim xf, Fbig yb => Fbig (SFBI2.add_DN prec (prim_to_big xf) yb)
  | Fbig xb, Fprim yf => Fbig (SFBI2.add_DN prec xb (prim_to_big yf))
  | Fbig xb, Fbig yb => Fbig (SFBI2.add_DN prec xb yb)
  end.

Definition sub_UP prec x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    let z := (xf - yf)%float in
    match (z ?= neg_infinity)%float with
    | FEq => Fprim z
    | _ => Fprim (next_up z)
    end
  | Fprim xf, Fbig yb => Fbig (SFBI2.sub_UP prec (prim_to_big xf) yb)
  | Fbig xb, Fprim yf => Fbig (SFBI2.sub_UP prec xb (prim_to_big yf))
  | Fbig xb, Fbig yb => Fbig (SFBI2.sub_UP prec xb yb)
  end.

Definition sub_DN prec x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    let z := (xf - yf)%float in
    match (z ?= infinity)%float with
    | FEq => Fprim z
    | _ => Fprim (next_down z)
    end
  | Fprim xf, Fbig yb => Fbig (SFBI2.sub_DN prec (prim_to_big xf) yb)
  | Fbig xb, Fprim yf => Fbig (SFBI2.sub_DN prec xb (prim_to_big yf))
  | Fbig xb, Fbig yb => Fbig (SFBI2.sub_DN prec xb yb)
  end.

Definition mul_UP prec x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    let z := (xf * yf)%float in
    match (z ?= neg_infinity)%float with
    | FEq => Fprim z
    | _ => Fprim (next_up z)
    end
  | Fprim xf, Fbig yb => Fbig (SFBI2.mul_UP prec (prim_to_big xf) yb)
  | Fbig xb, Fprim yf => Fbig (SFBI2.mul_UP prec xb (prim_to_big yf))
  | Fbig xb, Fbig yb => Fbig (SFBI2.mul_UP prec xb yb)
  end.

Definition mul_DN prec x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    let z := (xf * yf)%float in
    match (z ?= infinity)%float with
    | FEq => Fprim z
    | _ => Fprim (next_down z)
    end
  | Fprim xf, Fbig yb => Fbig (SFBI2.mul_DN prec (prim_to_big xf) yb)
  | Fbig xb, Fprim yf => Fbig (SFBI2.mul_DN prec xb (prim_to_big yf))
  | Fbig xb, Fbig yb => Fbig (SFBI2.mul_DN prec xb yb)
  end.

Definition div_UP prec x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    match classify yf with
    | NaN | PInf | NInf => nan
    | PZero | NZero | PNormal | NNormal | PSubn | NSubn =>
      let z := (xf / yf)%float in
      match (z ?= neg_infinity)%float with
      | FEq => Fprim z
      | _ => Fprim (next_up z)
      end
    end
  | Fprim xf, Fbig yb => Fbig (SFBI2.div_UP prec (prim_to_big xf) yb)
  | Fbig xb, Fprim yf => Fbig (SFBI2.div_UP prec xb (prim_to_big yf))
  | Fbig xb, Fbig yb => Fbig (SFBI2.div_UP prec xb yb)
  end.

Definition div_DN prec x y :=
  match x, y with
  | Fprim xf, Fprim yf =>
    match classify yf with
    | NaN | PInf | NInf => nan
    | PZero | NZero | PNormal | NNormal | PSubn | NSubn =>
      let z := (xf / yf)%float in
      match (z ?= infinity)%float with
      | FEq => Fprim z
      | _ => Fprim (next_down z)
      end
    end
  | Fprim xf, Fbig yb => Fbig (SFBI2.div_DN prec (prim_to_big xf) yb)
  | Fbig xb, Fprim yf => Fbig (SFBI2.div_DN prec xb (prim_to_big yf))
  | Fbig xb, Fbig yb => Fbig (SFBI2.div_DN prec xb yb)
  end.

Definition sqrt_UP prec x :=
  match x with
  | Fprim xf => Fprim (next_up (PrimFloat.sqrt xf))
  | Fbig xb => Fbig (SFBI2.sqrt_UP prec xb)
  end.

Definition sqrt_DN prec x :=
  match x with
  | Fprim xf =>
    let z := PrimFloat.sqrt xf in
    match (z ?= infinity)%float with
    | FEq => Fprim z
    | _ => Fprim (next_down z)
    end
  | Fbig xb => Fbig (SFBI2.sqrt_DN prec xb)
  end.

Definition nearbyint mode x :=
  match x with
  | Fprim f => Fbig (SFBI2.nearbyint mode (prim_to_big f))
  | Fbig f => Fbig (SFBI2.nearbyint mode f)
  end.

Definition midpoint (x y : type) :=
  match x, y with
  | Fprim xf, Fprim yf =>
    let z := ((xf + yf) / 2)%float in
    if is_infinity z then Fprim (xf / 2 + yf / 2)%float else Fprim z
  | Fprim xf, Fbig yb => Fbig (SFBI2.div2 (SFBI2.add_exact (prim_to_big xf) yb))
  | Fbig xb, Fprim yf => Fbig (SFBI2.div2 (SFBI2.add_exact xb (prim_to_big yf)))
  | Fbig xb, Fbig yb => Fbig (SFBI2.div2 (SFBI2.add_exact xb yb))
  end.

Definition toX x := FtoX (toF x).
Definition toR x := proj_val (toX x).

Lemma zero_correct : toX zero = Xreal 0.
Proof. reflexivity. Qed.

Lemma nan_correct : toX nan = Xnan.
Proof. reflexivity. Qed.

(* From ValidSDP Require Import FlocqNativeLayer. *)

Lemma fromZ_correct :
  forall n, toX (fromZ n) = Xreal (IZR n).
Proof.
intro n.
unfold fromZ.
case_eq (frshiftexp (of_int63 (of_Z n))); intros m e Hme.
rewrite BigZ.spec_eqb.
case Z.eqb_spec; [ |now intros _; apply SFBI2.fromZ_correct].
rewrite BigZ.spec_of_Z, BigZ.spec_mul, BigZ.spec_pow, BigZ.spec_sub; simpl.
Admitted.
(* rewrite normfr_mantissa_SFnormfr_mantissa. *)
(* intro Hn. *)
(* unfold toX, toF, prim_to_big. *)
(* rewrite classify_SFclassify. *)
(* unfold SF64classify, SFclassify. *)
(* assert (H := frshiftexp_SFfrexp (of_int63 (of_Z n))). *)
(* revert H; rewrite Hme. *)
(* case_eq (Prim2SF (of_int63 (of_Z n))). *)
(* { intros b Hf; simpl. *)
(*   intro H; inversion H; clear H. *)
(*   now revert Hn; rewrite H1; simpl; intro Hn; case b; rewrite Hn. } *)
(* { intros b Hf; simpl. *)
(*   intro H; inversion H; clear H. *)
(*   exfalso. *)
(*   revert Hn; rewrite H1; simpl; intro Hn. *)
(*   now revert Hf; rewrite Hn. } *)
(* { intros Hf; simpl. *)
(*   intro H; inversion H; clear H. *)
(*   exfalso. *)
(*   revert Hn; rewrite H1; simpl; intro Hn. *)
(*   now revert Hf; rewrite Hn. } *)
(* intros b m' _ _ _. *)
(* rewrite Hn, <-normfr_mantissa_SFnormfr_mantissa. *)
(* case b. *)
(* { case (_ =? _)%positive. *)
(*   { *)
(* Search _ normfr_mantissa. *)
    
    
(*     Search _ SFBI2.toF. *)
(* SFBI2.fromZ_correct  forall n : Z, FtoX (SFBI2.toF (SFBI2.fromZ n)) = Xreal (IZR n) *)

(*     unfold SFBI2.toF. *)
  
(* Set Printing All. *)
(* Check BigZ.spec_sub. *)
(* rewrite <-BigZ.spec_sub. *)

  
(*   Search _ normfr_mantissa. *)
(*   Locate "φ". *)
(*   revert Hn. *)
(*   unfold bigZ_of_int. *)
(*   Search _ bigZ_of_int. *)
  
(*   set (p := (_, _)); case_eq p; unfold p. *)
(*   Search _ "pair". *)
(*   Set Printing All. *)
(*   Search _ "pairing". *)
  

(* unfold Prim2EF. *)

(* Search _ classify. *)
(* Search _ EFclassify. *)

(* Search _ of_int63. *)
(* Search _ frshiftexp. *)
(* Print EFfrexp. *)
(* Search _ EFfrexp. *)

(* Search _ frshiftexp. *)

Lemma real_correct :
  forall f,
  real f = match toX f with Xnan => false | _ => true end.
Proof.
Admitted.

Lemma cmp_correct :
  forall x y,
  toX x = Xreal (toR x) ->
  toX y = Xreal (toR y) ->
  cmp x y = Rcompare (toR x) (toR y).
Proof.
Admitted.

Lemma min_correct :
  forall x y, toX (min x y) = Xmin (toX x) (toX y).
Proof.
Admitted.

Lemma max_correct :
  forall x y, toX (max x y) = Xmax (toX x) (toX y).
Proof.
Admitted.

Lemma neg_correct :
  forall x, toX (neg x) = Xneg (toX x).
Proof.
Admitted.

Lemma abs_correct :
  forall x, toX (abs x) = Xabs (toX x).
Proof.
Admitted.

Lemma div2_correct :
  forall x, sensible_format = true ->
  (1 / 256 <= Rabs (toR x))%R ->
  toX (div2 x) = Xdiv (toX x) (Xreal 2).
Proof.
Admitted.

Lemma add_UP_correct :
  forall p x y, le_upper (Xadd (toX x) (toX y)) (toX (add_UP p x y)).
Proof.
Admitted.

Lemma add_DN_correct :
  forall p x y, le_lower (toX (add_DN p x y)) (Xadd (toX x) (toX y)).
Proof.
Admitted.

Lemma sub_UP_correct :
  forall p x y, le_upper (Xsub (toX x) (toX y)) (toX (sub_UP p x y)).
Proof.
Admitted.

Lemma sub_DN_correct :
  forall p x y, le_lower (toX (sub_DN p x y)) (Xsub (toX x) (toX y)).
Proof.
Admitted.

Lemma mul_UP_correct :
  forall p x y, le_upper (Xmul (toX x) (toX y)) (toX (mul_UP p x y)).
Proof.
Admitted.

Lemma mul_DN_correct :
  forall p x y, le_lower (toX (mul_DN p x y)) (Xmul (toX x) (toX y)).
Proof.
Admitted.

Lemma div_UP_correct :
  forall p x y, le_upper (Xdiv (toX x) (toX y)) (toX (div_UP p x y)).
Proof.
Admitted.

Lemma div_DN_correct :
  forall p x y, le_lower (toX (div_DN p x y)) (Xdiv (toX x) (toX y)).
Proof.
Admitted.

Lemma sqrt_UP_correct :
  forall p x, le_upper (Xsqrt (toX x)) (toX (sqrt_UP p x)).
Proof.
Admitted.

Lemma sqrt_DN_correct :
  forall p x, le_lower (toX (sqrt_DN p x)) (Xsqrt (toX x)).
Proof.
Admitted.

Lemma nearbyint_correct :
  forall mode x,
  toX (nearbyint mode x) = Xnearbyint mode (toX x).
Proof.
Admitted.

Lemma midpoint_correct :
  forall x y,
  sensible_format = true ->
  real x = true -> real y = true -> (toR x <= toR y)%R
  -> real (midpoint x y) = true /\ (toR x <= toR (midpoint x y) <= toR y)%R.
Proof.
Admitted.

End PrimOrBigFloat.
