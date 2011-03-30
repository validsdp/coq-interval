Require Import Reals.
Require Import Bool.
Require Import ZArith.
Require Import Fcore_Raux.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Fcalc_div.
Require Import Fcalc_sqrt.

Inductive float (beta : radix) : Set :=
  | Fnan : float beta
  | Fzero : float beta
  | Float : bool -> positive -> Z -> float beta.

Inductive position : Set :=
  pos_Eq | pos_Lo | pos_Mi | pos_Up.

Inductive ufloat (beta : radix) : Set :=
  | Unan : ufloat beta
  | Uzero : ufloat beta
  | Ufloat : bool -> positive -> Z -> position -> ufloat beta.

Definition FtoX beta (f : float beta) :=
  match f with
  | Fzero => Xreal R0
  | Fnan => Xnan
  | Float s m e => Xreal (FtoR beta s m e)
  end.

Implicit Arguments FtoX.

(*
 * Fneg
 *)

Definition Fneg beta (f : float beta) :=
  match f with
  | Float s m e => Float beta (negb s) m e
  | _ => f
  end.

Implicit Arguments Fneg.

(*
 * Fabs
 *)

Definition Fabs beta (f : float beta) :=
  match f with
  | Float s m e => Float beta false m e
  | _ => f
  end.

Implicit Arguments Fabs.

(*
 * Fscale
 *)

Definition Fscale beta (f : float beta) d :=
  match f with
  | Float s m e => Float beta s m (e + d)
  | _ => f
  end.

Implicit Arguments Fscale.

(*
 * Fscale2
 *)

Definition Fscale2 beta (f : float beta) d :=
  match f with
  | Float s m e =>
    match radix_val beta, d with
    | Zpos (xO xH), _ => Float beta s m (e + d)
    | _, Z0 => f
    | _, Zpos nb =>
      Float beta s (iter_pos nb _ (fun x => xO x) m) e
    | Zpos (xO r), Zneg nb =>
      Float beta s (iter_pos nb _ (fun x => Pmult r x) m) (e + d)
    | _, _ => Fnan beta
    end
  | _ => f
  end.

Implicit Arguments Fscale2.

(*
 * Fcmp
 *
 * 1. Compare signs.
 * 2. Compare position of most significant digits.
 * 3. Compare shifted mantissas.
 *)

Definition shift beta m nb :=
  let r := match radix_val beta with Zpos r => r | _ => xH end in
  iter_pos nb _ (Pmult r) m.

Definition Fcmp_aux1 m1 m2 :=
  match Zcompare (Zpos m1) (Zpos m2) with
  | Eq => Xeq
  | Lt => Xlt
  | Gt => Xgt
  end.

Definition Fcmp_aux2 beta m1 e1 m2 e2 :=
  let d1 := count_digits beta m1 in
  let d2 := count_digits beta m2 in
  match Zcompare (e1 + Zpos d1)%Z (e2 + Zpos d2)%Z with
  | Lt => Xlt
  | Gt => Xgt
  | Eq =>
    match Zminus e1 e2 with
    | Zpos nb => Fcmp_aux1 (shift beta m1 nb) m2
    | Zneg nb => Fcmp_aux1 m1 (shift beta m2 nb)
    | Z0 => Fcmp_aux1 m1 m2
    end
  end.

Definition Fcmp beta (f1 f2 : float beta) :=
  match f1, f2 with
  | Fnan, _ => Xund
  | _, Fnan => Xund
  | Fzero, Fzero => Xeq
  | Fzero, Float false _ _ => Xlt
  | Fzero, Float true _ _ => Xgt
  | Float false _ _, Fzero => Xgt
  | Float true _ _, Fzero => Xlt
  | Float false _ _, Float true _ _ => Xgt
  | Float true _ _, Float false _ _ => Xlt
  | Float false m1 e1, Float false m2 e2 => Fcmp_aux2 beta m1 e1 m2 e2
  | Float true m1 e1, Float true m2 e2 => Fcmp_aux2 beta m2 e2 m1 e1
  end.

Implicit Arguments Fcmp.

(*
 * Fmin
 *)

Definition Fmin beta (f1 f2 : float beta) :=
  match Fcmp f1 f2 with
  | Xlt => f1
  | Xeq => f1
  | Xgt => f2
  | Xund => Fnan beta
  end.

Implicit Arguments Fmin.

(*
 * Fmax
 *)

Definition Fmax beta (f1 f2 : float beta) :=
  match Fcmp f1 f2 with
  | Xlt => f2
  | Xeq => f2
  | Xgt => f1
  | Xund => Fnan beta
  end.

Implicit Arguments Fmax.

Definition UtoX beta (f : ufloat beta) :=
  match f with
  | Uzero => Xreal R0
  | Ufloat s m e pos_Eq => Xreal (FtoR beta s m e)
  | _ => Xnan
  end.

Implicit Arguments UtoX.

Definition convert_location l :=
  match l with
  | Fcalc_bracket.loc_Exact => pos_Eq
  | Fcalc_bracket.loc_Inexact l =>
    match l with Lt => pos_Lo | Eq => pos_Mi | Gt => pos_Up end
  end.

Definition float_to_ufloat beta (x : float beta) :=
  match x with
  | Fnan => Unan beta
  | Fzero => Uzero beta
  | Float s m e => Ufloat beta s m e pos_Eq
  end.

Implicit Arguments float_to_ufloat.

Definition adjust_pos r d pos :=
  match r with
  | Z0 =>
    match pos with
    | pos_Eq => pos_Eq
    | _ => match d with xH => pos | _ => pos_Lo end
    end
  | Zneg _ => pos_Eq (* dummy *)
  | Zpos _ =>
    let (hd, mid) :=
      match d with
      | xO p => (p, match pos with pos_Eq => pos_Mi | _ => pos_Up end)
      | xI p => (p, match pos with pos_Eq => pos_Lo | _ => pos end)
      | xH => (xH, pos_Eq) (* dummy *)
      end in
    match Zcompare r (Zpos hd) with
    | Lt => pos_Lo
    | Eq => mid
    | Gt => pos_Up
    end
  end.

(*
 * Fround_none
 *)

Definition Fround_none beta (uf : ufloat beta) :=
  match uf with
  | Uzero => Fzero beta
  | Ufloat s m e pos_Eq => Float beta s m e
  | _ => Fnan beta
  end.

Implicit Arguments Fround_none.

(*
 * Fround_at_prec
 *
 * Assume the position is scaled at exponent ex + min(0, px - p).
 *)

Definition need_change mode m pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | pos_Mi =>
      match m with
      | xO _ => false
      | _ => true
      end
    | _ => false
    end
  end.

Definition need_change_radix beta mode m pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | pos_Mi =>
      match m with
      | xO _ => false
      | _ => match radix_val beta with Zpos (xO _) => false | _ => true end
      end
    | _ => false
    end
  end.

Definition adjust_mantissa mode m pos sign :=
  if need_change mode m pos sign then Psucc m else m.

Definition Fround_at_prec beta mode prec (uf : ufloat beta) :=
  match uf with
  | Unan => Fnan beta
  | Uzero => Fzero beta
  | Ufloat sign m1 e1 pos =>
    match (Zpos (count_digits beta m1) - Zpos prec)%Z with
    | Zpos nb =>
      let d := shift beta xH nb in
      match Zdiv_eucl (Zpos m1) (Zpos d) with
      | (Zpos m2, r) =>
        let pos2 := adjust_pos r d pos in
        let e2 := (e1 + Zpos nb)%Z in
        Float beta sign (adjust_mantissa mode m2 pos2 sign) e2
      | _ => Fnan beta (* dummy *)
      end
    | Z0 => Float beta sign (adjust_mantissa mode m1 pos sign) e1
    | Zneg nb =>
      if need_change_radix beta mode m1 pos sign then
        Float beta sign (Psucc (shift beta m1 nb)) (e1 + Zneg nb)
      else Float beta sign m1 e1
    end
  end.

Implicit Arguments Fround_at_prec.

(*
 * Fround_at_exp
 *
 * Assume the position is scaled at exponent min(ex, e).
 *)

Definition need_change_zero mode pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | _ => false
    end
  end.

Definition Fround_at_exp beta mode e2 (uf : ufloat beta) :=
  match uf with
  | Unan => Fnan beta
  | Uzero => Fzero beta
  | Ufloat sign m1 e1 pos =>
    match (e2 - e1)%Z with
    | Zpos nb =>
      match Zcompare (Zpos (count_digits beta m1)) (Zpos nb) with
      | Gt =>
        let d := shift beta xH nb in
        match Zdiv_eucl (Zpos m1) (Zpos d) with
        | (Zpos m2, r) =>
          let pos2 := adjust_pos r d pos in
          Float beta sign (adjust_mantissa mode m2 pos2 sign) e2
        | _ => Fnan beta (* dummy *)
        end
      | Eq =>
        let d := shift beta xH nb in
        let pos2 := adjust_pos (Zpos m1) d pos in
        if need_change_zero mode pos2 sign then
          Float beta sign xH e2
        else Fzero beta
      | Lt =>
        let pos2 := match pos with pos_Eq => pos_Eq | _ => pos_Lo end in
        if need_change_zero mode pos2 sign then
          Float beta sign xH e2
        else Fzero beta
      end
    | Z0 => Float beta sign (adjust_mantissa mode m1 pos sign) e1
    | Zneg nb =>
      if need_change_radix beta mode m1 pos sign then
        Float beta sign (Psucc (shift beta m1 nb)) e2
      else Float beta sign m1 e1
    end
  end.

Implicit Arguments Fround_at_exp.

(*
 * Fround
 *)

Definition Fround beta mode prec (x : float beta) :=
  Fround_at_prec mode prec (float_to_ufloat x).

Implicit Arguments Fround.

(*
 * Fint_exact
 *)

Definition Fint_exact beta mode (x : float beta) :=
  Fround_at_exp mode 0 (float_to_ufloat x).

Implicit Arguments Fint_exact.

(*
 * Fint
 *)

Definition Fint beta mode prec x :=
  match x with
  | Float sx mx ex =>
    match Zcompare (Zpos (count_digits beta mx) + ex) (Zpos prec) with
    | Gt => Fround_at_prec mode prec
    | _ => Fround_at_exp mode 0
    end (Ufloat beta sx mx ex pos_Eq)
  | _ => x
  end.

Implicit Arguments Fint.

(*
 * Fmul, Fmul_exact
 *)

Definition Fmul_aux beta (x y : float beta) :=
  match x, y with
  | Fnan, _ => Unan beta
  | _, Fnan => Unan beta
  | Fzero, _ => Uzero beta
  | _, Fzero => Uzero beta
  | Float sx mx ex, Float sy my ey =>
    Ufloat beta (xorb sx sy) (Pmult mx my) (ex + ey) pos_Eq
  end.

Implicit Arguments Fmul_aux.

Definition Fmul beta mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fmul_aux x y).

Implicit Arguments Fmul.

Definition Fmul_exact beta (x y : float beta) :=
  Fround_none (Fmul_aux x y).

Implicit Arguments Fmul_exact.

(*
 * Fadd_slow, Fadd_exact
 *
 * 1. Shift the mantissa with the highest exponent to match the other one.
 * 2. Perform the addition/subtraction.
 * 3. Round to p digits.
 *
 * Complexity is fine as long as px <= p and py <= p and exponents are close.
 *)

Definition Fadd_slow_aux1 beta sx sy mx my e :=
  if eqb sx sy then
    Ufloat beta sx (Pplus mx my) e pos_Eq
  else
    match (Zpos mx + Zneg my)%Z with
    | Z0 => Uzero beta
    | Zpos p => Ufloat beta sx p e pos_Eq
    | Zneg p => Ufloat beta sy p e pos_Eq
    end.

Definition Fadd_slow_aux2 beta sx sy mx my ex ey :=
  match Zminus ex ey with
  | Zpos nb => Fadd_slow_aux1 beta sx sy (shift beta mx nb) my ey
  | Zneg nb => Fadd_slow_aux1 beta sx sy mx (shift beta my nb) ex
  | Z0 => Fadd_slow_aux1 beta sx sy mx my ex
  end.

Definition Fadd_slow_aux beta (x y : float beta) :=
  match x, y with
  | Fnan, _ => Unan beta
  | _, Fnan => Unan beta
  | Fzero, Fzero => Uzero beta
  | Fzero, Float sy my ey =>
    Ufloat beta sy my ey pos_Eq
  | Float sx mx ex, Fzero =>
    Ufloat beta sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_slow_aux2 beta sx sy mx my ex ey
  end.

Implicit Arguments Fadd_slow_aux.

Definition Fadd_slow beta mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fadd_slow_aux x y).

Implicit Arguments Fadd_slow.

Definition Fadd_exact beta (x y : float beta) :=
  Fround_none (Fadd_slow_aux x y).

Implicit Arguments Fadd_exact.

(*
 * Fadd_fast
 *
 * 1. Guess a lower bound on the exponent of the result.
 * 2. Truncate the mantissa (at most one) that extends farther.
 * 3. Adjust the mantissa so that the propagated truncation error is inward.
 * 4. Shift the (usually other) mantissa to match it.
 * 5. Perform the addition/subtraction.
 * 6. Round to p digits wrt the position given by the truncation.
 *
 * Complexity is fine as long as, either
 *  . px <= p and py <= p, or
 *  . pv <= p and v has same magnitude than the result.
 *
 * Details:
 *
 *  . Same sign:
 *    Exponent of the result is at least max(u1, u2) - p.
 *    Target exponent e is min(max(e1, e2), max(u1, u2) - p).
 *    1. if either e1 < e or e2 < e (assume e2 < e), then e1 >= e
 *       if u2 <= e, then f2 < b^u2 <= b^e
 *         return rounded f1 at p digits with pos(f2)
 *       otherwise e2 < e < u2
 *       truncate m2 at e, shift m1 at e
 *    2. if e1 >= e and e2 >= e
 *       shift m1 or m2 at min(e1, e2)
 *    Perform addition.
 *
 *  . Opposite signs: (assume u1 > u2 + 1, otherwise full subtraction)
 *    Exponent of the result is at least u1 - p - 1.
 *    Target exponent e is min(max(e1, e2), u1 - p - 1).
 *    1. if u2 < e, then f2 < b^u2 <= b^e / b
 *       return f1 - b^(e - 2)
 *    2. if u2 = e, then change e to e - 1 and continue
 *    3. if e2 < e < u2, then e1 >= e
 *       truncate m2 outward at e, shift m1 at e
 *    4. if e1 < e < u2, then e2 >= e and e < u2 < u1
 *       truncate m1 at e, shift m2 at e
 *    5. if e1 >= e and e2 >= e
 *       shift m1 or m2 at min(e1, e2)
 *    Perform subtraction.
 *)

Definition truncate beta m1 nb :=
  let d := iter_pos nb _ (fun x => Pmult (match radix_val beta with Zpos r => r | _ => xH end) x) xH in
  match Zdiv_eucl (Zpos m1) (Zpos d) with
  | (Zpos m2, r) => (m2, adjust_pos r d pos_Eq)
  | _ => (xH, pos_Lo) (* dummy *)
  end.

Definition Fadd_fast_aux1 beta s m1 m2 e d2 u2 e1 e2 :=
  match Zcompare u2 e with
  | Lt => (* negligible value *)
    Ufloat beta s m1 e1 pos_Lo
  | Eq => (* almost negligible *)
    Ufloat beta s m1 e1 (adjust_pos (Zpos m2) (shift beta xH d2) pos_Eq)
  | Gt =>
    match (e - e2)%Z with
    | Zpos p =>
      let (n2, pos) := truncate beta m2 p in
      let n1 := 
        match (e1 - e)%Z with
        | Zpos q => (shift beta m1 q)
        | Z0 => m1
        | _ => xH (* dummy *)
        end in
      Ufloat beta s (Pplus n1 n2) e pos
    | _ => Unan beta (* dummy *)
    end
  end.

Definition Fsub_fast_aux1 beta s m1 m2 e e1 e2 :=
  match (e - e2)%Z with
  | Zpos p =>
    let (n2, pos) :=
      match truncate beta m2 p with
      | (n, pos_Eq) => (n, pos_Eq)
      | (n, pos_Lo) => (Psucc n, pos_Up)
      | (n, pos_Mi) => (Psucc n, pos_Mi)
      | (n, pos_Up) => (Psucc n, pos_Lo)
      end in
    let n1 := 
      match (e1 - e)%Z with
      | Zpos q => (shift beta m1 q)
      | Z0 => m1
      | _ => xH (* dummy *)
      end in
    Ufloat beta s (Pminus n1 n2) e pos
  | _ => Unan beta (* dummy *)
  end.

Definition Fsub_fast_aux2 beta prec s m1 m2 u1 u2 e1 e2 :=
  let e := Zmin (Zmax e1 e2) (u1 + Zneg (prec + 1)) in
  if Zlt_bool e2 e then
    match Zcompare u2 e with
    | Lt => (* negligible value *)
      Fadd_slow_aux2 beta s (negb s) m1 xH e1 (e - 2)
    | Eq => (* almost negligible *)
      let ee := (e - 1)%Z in
      if Zeq_bool e2 ee then
        let n1 :=
          match (e1 - ee)%Z with
          | Zpos q => (shift beta m1 q)
          | Z0 => m1
          | _ => xH (* dummy *)
          end in
        Ufloat beta s (Pminus n1 m2) ee pos_Eq
      else
        Fsub_fast_aux1 beta s m1 m2 ee e1 e2
    | Gt =>
      Fsub_fast_aux1 beta s m1 m2 e e1 e2
    end
  else if Zlt_bool e1 e then
    match (e - e1)%Z with
    | Zpos p =>
      let (n1, pos) := truncate beta m1 p in
      let n2 := 
        match (e2 - e)%Z with
        | Zpos q => (shift beta m2 q)
        | Z0 => m2
        | _ => xH (* dummy *)
        end in
      Ufloat beta s (Pminus n1 n2) e pos
    | _ => Unan beta (* dummy *)
    end
  else
    Fadd_slow_aux2 beta s (negb s) m1 m2 e1 e2.

Definition Fadd_fast_aux2 beta prec s1 s2 m1 m2 e1 e2 :=
  let d1 := count_digits beta m1 in
  let d2 := count_digits beta m2 in
  let u1 := (e1 + Zpos d1)%Z in
  let u2 := (e2 + Zpos d2)%Z in
  if eqb s1 s2 then
    (* same sign *)
    let e := Zmin (Zmax e1 e2) ((Zmax u1 u2) + Zneg prec) in
    if Zlt_bool e1 e then
      Fadd_fast_aux1 beta s1 m2 m1 e d1 u1 e2 e1
    else if Zlt_bool e2 e then
      Fadd_fast_aux1 beta s1 m1 m2 e d2 u2 e1 e2
    else
      Fadd_slow_aux2 beta s1 s2 m1 m2 e1 e2
  else
    (* opposite sign *)
    if Zlt_bool (u1 + 1)%Z u2 then
      Fsub_fast_aux2 beta prec s2 m2 m1 u2 u1 e2 e1
    else if Zlt_bool (u2 + 1)%Z u1 then
      Fsub_fast_aux2 beta prec s1 m1 m2 u1 u2 e1 e2
    else
      (* massive cancellation possible *)
      Fadd_slow_aux2 beta s1 s2 m1 m2 e1 e2.

Definition Fadd_fast_aux beta prec (x y : float beta) :=
  match x, y with
  | Fnan, _ => Unan beta
  | _, Fnan => Unan beta
  | Fzero, Fzero => Uzero beta
  | Fzero, Float sy my ey =>
    Ufloat beta sy my ey pos_Eq
  | Float sx mx ex, Fzero =>
    Ufloat beta sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_fast_aux2 beta prec sx sy mx my ex ey
  end.

Implicit Arguments Fadd_fast_aux.

Definition Fadd_fast beta mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fadd_fast_aux prec x y).

Implicit Arguments Fadd_fast.

Definition Fadd := Fadd_slow.

Implicit Arguments Fadd.

(*
 * Fsub, Fsub_exact
 *)

Definition Fsub_slow_aux beta (x y : float beta) :=
  match x, y with
  | Fnan, _ => Unan beta
  | _, Fnan => Unan beta
  | Fzero, Fzero => Uzero beta
  | Fzero, Float sy my ey => Ufloat beta (negb sy) my ey pos_Eq
  | Float sx mx ex, Fzero => Ufloat beta sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_slow_aux2 beta sx (negb sy) mx my ex ey
  end.

Implicit Arguments Fsub_slow_aux.

Definition Fsub_slow beta mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fsub_slow_aux x y).

Implicit Arguments Fsub_slow.

Definition Fsub := Fsub_slow.

Implicit Arguments Fsub.

Definition Fsub_exact beta (x y : float beta) :=
  Fround_none (Fsub_slow_aux x y).

Implicit Arguments Fsub_exact.

(*
 * Fdiv
 *
 * 1. Shift dividend mantissa so that it has at least py + p digits.
 * 2. Perform the euclidean division.
 * 3. Compute position with remainder.
 * 4. Round to p digits.
 *
 * Complexity is fine as long as px <= 2p and py <= p.
 *)

Definition Fdiv_aux beta prec (x y : float beta) :=
  match x, y with
  | Fnan, _ => Unan beta
  | _, Fnan => Unan beta
  | _, Fzero => Unan beta
  | Fzero, _ => Uzero beta
  | Float sx mx ex, Float sy my ey =>
    match Fdiv_core beta (Zpos prec) (Zpos mx) ex (Zpos my) ey with
    | (Zpos m, e, l) =>
      Ufloat beta (xorb sx sy) m e (convert_location l)
    | _ => Unan beta (* dummy *)
    end
  end.

Implicit Arguments Fdiv_aux.

Definition Fdiv beta mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fdiv_aux prec x y).

Implicit Arguments Fdiv.

(*
 * Frem
 *
 * 1. Shift mantissas so that dividend and divisor have the same exponents.
 * 2. Perform the euclidean division.
 * 3. Adjust quotient to closest integer (tie breaking to even).
 * 4. Scale remainder to common exponent.
 * 5. Round remainder to p digits.
 *)

Definition Frem_aux1 beta mx my s e :=
  let (q1, r1) := Zdiv_eucl (Zpos mx) (Zpos my) in
  let (q2, r2) :=
    match
      match my with
      | xH => false
      | xO p =>
        match Zcompare r1 (Zpos p) with
        | Lt => false
        | Eq =>
          match q1 with
          | Z0 => false
          | Zpos (xO _) => false
          | _ => true
          end
        | Gt => true
        end
      | xI p =>
        match Zcompare r1 (Zpos p) with
        | Lt => false
        | Eq => false
        | Gt => true
        end
      end
    with
    | false => (q1, r1)
    | true => (q1 + 1, r1 - Zpos my)%Z
    end in
 (match q2 with
  | Zpos p => Float beta s p 0
  | Z0 => Fzero beta
  | _ => Fnan beta (* dummy *)
  end,
  match r2 with
  | Zpos p => Ufloat beta s p e pos_Eq
  | Z0 => Uzero beta
  | Zneg p => Ufloat beta (negb s) p e pos_Eq
  end).

Definition Frem_aux beta (x y : float beta) :=
  match x, y with
  | Fnan, _ => (Fnan beta, Unan beta)
  | _, Fnan => (Fnan beta, Unan beta)
  | _, Fzero => (Fnan beta, Unan beta)
  | Fzero, _ => (Fzero beta, Uzero beta)
  | Float sx mx ex, Float sy my ey =>
    let s := xorb sx sy in
    match (ex - ey)%Z with
    | Zpos nb => Frem_aux1 beta (shift beta mx nb) my s ey
    | Z0 => Frem_aux1 beta mx my s ex
    | Zneg nb => Frem_aux1 beta mx (shift beta my nb) s ex
    end
  end.

Implicit Arguments Frem_aux.

Definition Frem beta mode prec (x y : float beta) :=
  let (q, r) := Frem_aux x y in
  (q, Fround_at_prec mode prec r).

Implicit Arguments Frem.

(*
 * Fsqrt
 *
 * 1. Shift the mantissa so that it has at least 2p-1 digits;
 *    shift it one digit more if the new exponent is not even.
 * 2. Compute the square root s (at least p digits) of the new
 *    mantissa, and its remainder r.
 * 3. Current position: r == 0  =>  Eq,
 *                      r <= s  =>  Lo,
 *                      r >= s  =>  Up.
 * 4. Round to p digits.
 *
 * Complexity is fine as long as p1 <= 2p-1.
 *)

Definition Fsqrt_aux beta prec (f : float beta) :=
  match f with
  | Float false m e =>
    match Fsqrt_core beta (Zpos prec) (Zpos m) e with
    | (Zpos m, e, l) =>
      Ufloat beta false m e (convert_location l)
    | _ => Unan beta (* dummy *)
    end
  | Float true _ _ => Unan beta
  | Fzero => Uzero beta
  | Fnan => Unan beta
  end.

Implicit Arguments Fsqrt_aux.

Definition Fsqrt beta mode prec (x : float beta) :=
  Fround_at_prec mode prec (Fsqrt_aux prec x).

Implicit Arguments Fsqrt.

(*
 * Fmag
 *)

Definition Fmag beta (x : float beta) :=
  match x with
  | Float _ m e => Zplus e (Zpos (count_digits beta m))
  | _ => Z0
  end.