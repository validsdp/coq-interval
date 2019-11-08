(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

From Coq Require Import Reals ZArith Psatz.
From Coquelicot Require Import Coquelicot.

Require Import Stdlib.
Require Import Coquelicot.
Require Import Xreal.
From Coq Require Import List.
Require Import Basic.
Require Import Sig.
Require Import Interval.
Require Import Float_full.
Require Import Integral.
Require Import Eval.
Require Import Bertrand.
Require Import Tree.
Require Import Prog.
Require Import Reify.
Require Import Refine.

Module IntervalTactic (F : FloatOps with Definition sensible_format := true).

Inductive interval_tac_parameters : Set :=
  | i_prec (p : positive)
  | i_bisect (v : R)
  | i_bisect_diff (v : R)
  | i_bisect_taylor (v : R)
  | i_degree (d : nat)
  | i_depth (d : nat)
  | i_fuel (f : positive)
  | i_native_compute
  | i_delay.

Module Private.

Module I := FloatIntervalFull F.
Module J := IntervalExt I.
Module F' := FloatExt F.
Module A := IntervalAlgos I.
Module T := Tree.Bnd I.
Module R := Reify.Bnd I.
Module BI := BertrandInterval F I.
Module IR := IntegralRefiner I.
Module IT := IntegralTaylor I.
Module IU := IntegralTactic F I.

Definition reify_var : R.
Proof. exact 0%R. Qed.

Ltac get_RInt_vars y i f :=
  let fapp := eval cbv beta in (f reify_var) in
  let vars := constr:(reify_var :: @nil R) in
  let vars := get_vars fapp vars in
  let vars := match get_vars fapp vars with reify_var :: ?vars => vars end in
  let vars := constr:(i :: vars) in
  let vars := match get_vars y vars with i :: ?vars => vars end in
  vars.

Ltac reify_RInt :=
  match goal with
  | |- eval_goal ?g' ?y =>
    let g := fresh "__goal" in
    set (g := g') ;
    match y with
    | context [RInt ?f ?u ?v] =>
      let i := constr:(RInt f u v) in
      let vars := get_RInt_vars y i f in
      let vars := get_vars u vars in
      let vars := get_vars v vars in
      reify_partial y (i :: vars) ;
      apply eq_ind ;
      erewrite <- RInt_ext by (
        let t := fresh "t" in
        intros t _ ;
        let fapp := eval cbv beta in (f t) in
        reify_partial fapp (t :: vars) ;
        exact (fun H => H)) ;
      reify_partial u vars ;
      intros <- ;
      reify_partial v vars ;
      intros <- ;
      find_hyps vars
    end
  end.

Ltac reify_RInt_gen_infty :=
  match goal with
  | |- eval_goal ?g' ?y =>
    let g := fresh "__goal" in
    set (g := g') ;
    match y with
    | context [RInt_gen ?fm (at_point ?u) (Rbar_locally p_infty)] =>
      let i := constr:(RInt_gen fm (at_point u) (Rbar_locally p_infty)) in
      let f :=
        lazymatch fm with
        | (fun x => @?f x * _)%R => f
        | (fun x => @?f x / _)%R => f
        | (fun x => @?f x * / _)%R => f
        | _ => fail "Unsupported integrand"
        end in
      let vars := get_RInt_vars y i f in
      let vars := get_vars u vars in
      reify_partial y (i :: vars) ;
      apply eq_ind ;
      erewrite <- RInt_gen_ext_eq by (
        let t := fresh "t" in
        intros t ;
        apply (f_equal (fun x => Rmult x _)) ;
        let fapp := eval cbv beta in (f t) in
        reify_partial fapp (t :: vars) ;
        exact (fun H => H)) ;
      reify_partial u vars ;
      intros <- ;
      find_hyps vars
    end
  end.

Ltac reify_RInt_gen_zero :=
  match goal with
  | |- eval_goal ?g' ?y =>
    let g := fresh "__goal" in
    set (g := g') ;
    match y with
    | context [RInt_gen ?fm (at_right 0) (at_point ?v)] =>
      let i := constr:(RInt_gen fm (at_right 0) (at_point v)) in
      let f :=
        lazymatch fm with
        | (fun x => @?f x * _)%R => f
        | (fun x => @?f x / _)%R => f
        | (fun x => @?f x * / _)%R => f
        | _ => fail "Unsupported integrand"
        end in
      let vars := get_RInt_vars y i f in
      let vars := get_vars v vars in
      reify_partial y (i :: vars) ;
      apply eq_ind ;
      erewrite <- RInt_gen_ext_eq by (
        let t := fresh "t" in
        intros t ;
        apply (f_equal (fun x => Rmult x _)) ;
        let fapp := eval cbv beta in (f t) in
        reify_partial fapp (t :: vars) ;
        exact (fun H => H)) ;
      reify_partial v vars ;
      intros <- ;
      find_hyps vars
    end
  end.

Definition compute_inputs prec hyps consts :=
  R.merge_hyps prec hyps ++ map (T.eval_bnd prec) consts.

Theorem app_merge_hyps_eval_bnd :
  forall prec vars hyps consts,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  exists bp,
  map A.interval_from_bp bp = compute_inputs prec hyps consts /\
  map A.real_from_bp bp = vars ++ map (fun c => eval c nil) consts.
Proof.
intros prec vars hyps consts He.
unfold compute_inputs.
assert (exists bp1,
    map A.interval_from_bp bp1 = R.merge_hyps prec hyps /\
    map A.real_from_bp bp1 = vars) as [bp1 [<- <-]].
  revert vars He.
  induction (R.merge_hyps prec hyps) as [|h t IH].
    intros [|vars].
    now exists nil.
    easy.
  intros [|v vars].
  easy.
  intros [H1 H2].
  destruct (IH vars H2) as [bp [<- <-]].
  now exists (cons (A.Bproof v h H1) bp).
assert (exists bp2,
    map A.interval_from_bp bp2 = map (T.eval_bnd prec) consts /\
    map A.real_from_bp bp2 = map (fun c => eval c nil) consts) as [bp2 [<- <-]].
  clear.
  induction consts as [|h t IH].
    now exists nil.
  simpl.
  destruct IH as [bp [<- <-]].
  now exists (cons (A.Bproof _ _ (T.eval_bnd_correct prec h)) bp).
rewrite <- 2!map_app.
now exists (bp1 ++ bp2).
Qed.

Definition eval_bnd prec hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  R.eval_goal_bnd prec g (nth 0 (A.BndValuator.eval prec prog bounds) I.nai).

Theorem eval_bnd_correct :
  forall prec vars hyps prog consts g,
  eval_bnd prec hyps prog consts g = true ->
  eval_hyps hyps vars
    (eval_goal g (nth 0 (eval_real prog (vars ++ map (fun c => eval c nil) consts)) 0%R)).
Proof.
intros prec vars hyps prog consts g H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply (R.eval_goal_bnd_correct prec) with (2 := H).
destruct (app_merge_hyps_eval_bnd _ _ _ consts H') as [bp [<- <-]].
apply A.BndValuator.eval_correct'.
Qed.

Definition eval_bnd_contains prec hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  I.subset (nth 0 (A.BndValuator.eval prec prog bounds) I.nai) b.

Theorem eval_bnd_contains_correct :
  forall prec vars hyps prog consts b,
  eval_bnd_contains prec hyps prog consts b = true ->
  eval_hyps hyps vars
    (contains (I.convert b) (Xreal (nth 0 (eval_real prog (vars ++ map (fun c => eval c nil) consts)) 0%R))).
Proof.
intros prec vars hyps prog consts b H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
eapply subset_contains.
apply I.subset_correct, H.
destruct (app_merge_hyps_eval_bnd _ _ _ consts H') as [bp [<- <-]].
apply A.BndValuator.eval_correct'.
Qed.

Definition eval_bnd_plain prec hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  nth 0 (A.BndValuator.eval prec prog bounds) I.nai.

Theorem eval_bisect_aux :
  forall prec depth var0 vars hyps prog consts g fi,
  (forall bp xi x, contains (I.convert xi) (Xreal x) ->
   contains (I.convert (fi xi (map A.interval_from_bp bp)))
     (Xreal (nth 0 (eval_real prog (x :: map A.real_from_bp bp)) 0))) ->
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun b => R.eval_goal_bnd prec g (fi b bounds)) depth = true ->
  eval_hyps hyps (var0 :: vars)
    (eval_goal g (eval_real' prog (var0 :: vars) consts)).
Proof.
intros prec depth var0 vars hyps prog consts g fi Hfi.
simpl.
intros H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply A.bisect_1d_correct' with (P := fun x => eval_goal g (eval_real' prog (x :: vars) consts)) (2 := H).
intros x xi Ix.
apply (R.eval_goal_bnd_correct prec).
destruct hyps as [|hx hyps].
easy.
destruct H' as [H1 H2].
unfold eval_real'.
change (tl _) with (compute_inputs prec hyps consts).
simpl.
destruct (app_merge_hyps_eval_bnd _ _ _ consts H2) as [bp [<- <-]].
now apply Hfi.
unfold compute_inputs.
destruct R.merge_hyps as [|vi t].
easy.
simpl in H' |- *.
rewrite I.lower_correct, I.upper_correct; [|now exists var0..].
Admitted.
(* now destruct I.convert. *)
(* Qed. *)

Theorem eval_bisect_contains_aux :
  forall prec depth var0 vars hyps prog consts b fi,
  (forall bp xi x, contains (I.convert xi) (Xreal x) ->
   contains (I.convert (fi xi (map A.interval_from_bp bp)))
     (Xreal (nth 0 (eval_real prog (x :: map A.real_from_bp bp)) 0))) ->
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun xi => I.subset (fi xi bounds) b) depth = true ->
  eval_hyps hyps (var0 :: vars)
    (contains (I.convert b) (Xreal (eval_real' prog (var0 :: vars) consts))).
Proof.
intros prec depth var0 vars hyps prog consts b fi Hfi.
simpl.
intros H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply A.bisect_1d_correct' with (P := fun x => contains (I.convert b) (Xreal (eval_real' prog (x :: vars) consts))) (2 := H).
intros x xi Ix H''.
eapply subset_contains.
apply I.subset_correct, H''.
clear H''.
destruct hyps as [|hx hyps].
easy.
destruct H' as [H1 H2].
unfold eval_real'.
change (tl _) with (compute_inputs prec hyps consts).
simpl.
destruct (app_merge_hyps_eval_bnd _ _ _ consts H2) as [bp [<- <-]].
now apply Hfi.
unfold compute_inputs.
destruct R.merge_hyps as [|vi t].
easy.
simpl in H' |- *.
destruct H' as [H' H''].
rewrite I.lower_correct; [|now exists var0].
rewrite I.upper_correct; [|now exists var0].
revert H'; case vi => [|l u].
{ now simpl; rewrite F'.valid_lb_nan, F'.valid_ub_nan. }
now simpl; case (_ && _)%bool.
Qed.

Definition eval_bisect prec depth hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun b =>
    R.eval_goal_bnd prec g (nth 0 (A.BndValuator.eval prec prog (b :: bounds)) I.nai)
  ) depth.

Theorem eval_bisect_correct :
  forall prec depth var0 vars hyps prog consts g,
  eval_bisect prec depth hyps prog consts g = true ->
  eval_hyps hyps (var0 :: vars)
    (eval_goal g (eval_real' prog (var0 :: vars) consts)).
Proof.
intros prec depth var0 vars hyps prog consts g H.
apply (eval_bisect_aux prec depth) with (fi := fun b bounds => nth 0 (A.BndValuator.eval prec prog (b :: bounds)) I.nai) (2 := H).
intros bp xi x Ix.
apply (A.BndValuator.eval_correct' _ _ (A.Bproof _ _ Ix :: bp)).
Qed.

Definition eval_bisect_contains prec depth hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun xi =>
    I.subset (nth 0 (A.BndValuator.eval prec prog (xi :: bounds)) I.nai) b
  ) depth.

Theorem eval_bisect_contains_correct :
  forall prec depth var0 vars hyps prog consts b,
  eval_bisect_contains prec depth hyps prog consts b = true ->
  eval_hyps hyps (var0 :: vars)
    (contains (I.convert b) (Xreal (eval_real' prog (var0 :: vars) consts))).
Proof.
intros prec depth var0 vars hyps prog consts b H.
apply (eval_bisect_contains_aux prec depth) with (fi := fun b bounds => nth 0 (A.BndValuator.eval prec prog (b :: bounds)) I.nai) (2 := H).
intros bp xi x Ix.
apply (A.BndValuator.eval_correct' _ _ (A.Bproof _ _ Ix :: bp)).
Qed.

Definition eval_bisect_plain prec depth extend hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.lookup_1d (fun xi =>
    nth 0 (A.BndValuator.eval prec prog (xi :: bounds)) I.nai
  ) (I.lower xi) (I.upper xi) extend depth.

Definition eval_bisect_diff prec depth hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun b =>
    R.eval_goal_bnd prec g (A.DiffValuator.eval prec prog bounds 0 b)
  ) depth.

Theorem eval_bisect_diff_correct :
  forall prec depth var0 vars hyps prog consts g,
  eval_bisect_diff prec depth hyps prog consts g = true ->
  eval_hyps hyps (var0 :: vars)
    (eval_goal g (eval_real' prog (var0 :: vars) consts)).
Proof.
intros prec depth var0 vars hyps prog consts g H.
apply (eval_bisect_aux prec depth) with (fi := fun b bounds => A.DiffValuator.eval prec prog bounds 0 b) (2 := H).
intros bp xi x Ix.
apply A.DiffValuator.eval_correct with (1 := Ix).
Qed.

Definition eval_bisect_contains_diff prec depth hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun xi =>
    I.subset (A.DiffValuator.eval prec prog bounds 0 xi) b
  ) depth.

Theorem eval_bisect_contains_diff_correct :
  forall prec depth var0 vars hyps prog consts b,
  eval_bisect_contains_diff prec depth hyps prog consts b = true ->
  eval_hyps hyps (var0 :: vars)
    (contains (I.convert b) (Xreal (eval_real' prog (var0 :: vars) consts))).
Proof.
intros prec depth var0 vars hyps prog consts b H.
apply (eval_bisect_contains_aux prec depth) with (fi := fun b bounds => A.DiffValuator.eval prec prog bounds 0 b) (2 := H).
intros bp xi x Ix.
apply A.DiffValuator.eval_correct with (1 := Ix).
Qed.

Definition eval_bisect_diff_plain prec depth extend hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.lookup_1d (fun xi =>
    A.DiffValuator.eval prec prog bounds 0 xi
  ) (I.lower xi) (I.upper xi) extend depth.

Definition eval_bisect_taylor prec deg depth hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const (tail bounds) in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun b =>
    R.eval_goal_bnd prec g (A.TaylorValuator.TM.eval (prec, deg)
      (nth 0 (A.TaylorValuator.eval prec deg b prog bounds) A.TaylorValuator.TM.dummy) b b)
  ) depth.

Theorem eval_bisect_taylor_correct :
  forall prec deg depth var0 vars hyps prog consts g,
  eval_bisect_taylor prec deg depth hyps prog consts g = true ->
  eval_hyps hyps (var0 :: vars)
    (eval_goal g (eval_real' prog (var0 :: vars) consts)).
Proof.
intros prec deg depth var0 vars hyps prog consts g H.
apply (eval_bisect_aux prec depth) with (fi := fun b bounds =>
  A.TaylorValuator.TM.eval (prec, deg)
    (nth 0 (A.TaylorValuator.eval prec deg b prog (A.TaylorValuator.TM.var ::
      map A.TaylorValuator.TM.const bounds)) A.TaylorValuator.TM.dummy) b b) (2 := H).
intros bp xi x Ix.
rewrite map_map.
apply A.TaylorValuator.eval_correct with (1 := Ix).
Qed.

Definition eval_bisect_contains_taylor prec deg depth hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const (tail bounds) in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun xi =>
    I.subset (A.TaylorValuator.TM.eval (prec, deg)
      (nth 0 (A.TaylorValuator.eval prec deg xi prog bounds) A.TaylorValuator.TM.dummy) xi xi) b
  ) depth.

Theorem eval_bisect_contains_taylor_correct :
  forall prec deg depth var0 vars hyps prog consts b,
  eval_bisect_contains_taylor prec deg depth hyps prog consts b = true ->
  eval_hyps hyps (var0 :: vars)
    (contains (I.convert b) (Xreal (eval_real' prog (var0 :: vars) consts))).
Proof.
intros prec deg depth var0 vars hyps prog consts b H.
apply (eval_bisect_contains_aux prec depth) with (fi := fun b bounds =>
  A.TaylorValuator.TM.eval (prec, deg)
    (nth 0 (A.TaylorValuator.eval prec deg b prog (A.TaylorValuator.TM.var ::
      map A.TaylorValuator.TM.const bounds)) A.TaylorValuator.TM.dummy) b b) (2 := H).
intros bp xi x Ix.
rewrite map_map.
apply A.TaylorValuator.eval_correct with (1 := Ix).
Qed.

Definition eval_bisect_taylor_plain prec deg depth extend hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  let xi := nth 0 bounds I.nai in
  let bounds := A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const (tail bounds) in
  A.lookup_1d (fun xi =>
    A.TaylorValuator.TM.eval (prec, deg)
      (nth 0 (A.TaylorValuator.eval prec deg xi prog bounds) A.TaylorValuator.TM.dummy) xi xi
  ) (I.lower xi) (I.upper xi) extend depth.

Definition eval_RInt prec deg limit hyps pg pf pu pv cg cf cu cv g :=
  let hyps := R.merge_hyps prec hyps in
  let fi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai in
  let ui :=
    let bounds := hyps ++ map (T.eval_bnd prec) cu in
    nth 0 (A.BndValuator.eval prec pu bounds) I.nai in
  let vi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cv in
    nth 0 (A.BndValuator.eval prec pv bounds) I.nai in
  let cb := fun x =>
    match x with IR.IBu => ui | IR.IBv => vi | IR.IBp x => I.bnd x x end in
  let mid := fun u v =>
    let u := cb u in
    let v := cb v in
    I.midpoint (I.join u v) in
  let Fi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun u v =>
      let u := cb u in
      let v := cb v in
      let xi := I.join u v in
      let gi :=
        A.TaylorValuator.TM.get_tm (prec, deg) xi
          (nth 0 (A.TaylorValuator.eval prec deg xi pf (A.TaylorValuator.TM.var :: bounds))
            A.TaylorValuator.TM.dummy) in
      IT.taylor_integral_naive_intersection prec fi gi xi u v in
  let check :=
    let bounds := hyps ++ map (T.eval_bnd prec) cg in
    fun b =>
      let yi := nth 0 (A.BndValuator.eval prec pg (b :: bounds)) I.nai in
      R.eval_goal_bnd prec g yi in
  check (IR.bisect prec limit mid Fi check).

Theorem eval_RInt_correct :
  forall prec deg limit vars hyps pg pf pu pv cg cf cu cv g,
  no_floor_prog pf = true ->
  eval_RInt prec deg limit hyps pg pf pu pv cg cf cu cv g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt (fun t => Prog.eval_real' pf (t :: vars) cf)
        (Prog.eval_real' pu vars cu) (Prog.eval_real' pv vars cv)) :: vars) cg)).
Proof.
intros prec deg limit vars hyps pg pf pu pv cg cf cu cv g Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply (R.eval_goal_bnd_correct prec) with (2 := H).
unfold Prog.eval_real'.
simpl.
fold (compute_inputs prec hyps cg).
fold (compute_inputs prec hyps cu).
fold (compute_inputs prec hyps cv).
destruct (app_merge_hyps_eval_bnd prec _ _ cg H') as [bpg [<- <-]].
apply A.BndValuator.eval_correct_ext'.
destruct (app_merge_hyps_eval_bnd prec _ _ cu H') as [bpu [<- <-]].
destruct (app_merge_hyps_eval_bnd prec _ _ cv H') as [bpv [<- <-]].
generalize (A.BndValuator.eval_correct' prec pu bpu 0) (A.BndValuator.eval_correct' prec pv bpv 0).
generalize (nth 0 (A.BndValuator.eval prec pv (map A.interval_from_bp bpv)) I.nai).
generalize (nth 0 (A.BndValuator.eval prec pu (map A.interval_from_bp bpu)) I.nai).
generalize (nth 0 (Prog.eval_real pv (map A.real_from_bp bpv)) 0%R).
generalize (nth 0 (Prog.eval_real pu (map A.real_from_bp bpu)) 0%R).
clear -H' Hp.
intros u v ui vi Hu Hv.
apply IR.contains_RInt_valid.
apply IR.bisect_correct ; [ typeclasses eauto .. | idtac ].
intros u' v'.
set (cbu := match u' with IR.IBu => ui | IR.IBv => vi | IR.IBp x => I.bnd x x end).
set (cbv := match v' with IR.IBu => ui | IR.IBv => vi | IR.IBp x => I.bnd x x end).
fold (compute_inputs prec hyps cf).
destruct (app_merge_hyps_eval_bnd prec _ _ cf H') as [bpf [<- <-]].
match goal with
| |- IR.valid _ _ _ _ _ ?fi =>
  let fi' := eval pattern cbu, cbv in fi in
  change fi with fi'
end.
apply IR.valid_at_point ; try easy.
clear -Hp.
intros ui vi u v Hu Hv.
set (i := IT.taylor_integral_naive_intersection _ _ _ _ _ _).
apply RInt_helper.
intros Hi.
assert (ex_RInt (fun t => nth 0 (Prog.eval_real pf (t :: map A.real_from_bp bpf)) 0%R) u v) as [I HI].
  apply (A.BndValuator.ex_RInt_eval prec) with (i := I.join ui vi) (1 := Hp).
    apply contains_connected.
    apply Rmin_case ; apply I.join_correct.
    now left.
    now right.
    apply Rmax_case ; apply I.join_correct.
    now left.
    now right.
  contradict Hi.
  unfold i, IT.taylor_integral_naive_intersection. clear i.
  rewrite I.real_correct.
  destruct (I.convert (I.mul _ _ _)) as [|il iu] eqn:Hm.
    easy.
  exfalso.
  now rewrite I.mul_propagate_r in Hm.
exists I.
apply (conj HI).
rewrite <- is_RInt_unique with (1 := HI).
apply IT.taylor_integral_naive_intersection_correct ; cycle 2.
  now exists I.
  exact Hu.
  exact Hv.
  apply I.join_correct.
  now left.
  apply I.join_correct.
  now right.
  apply A.BndValuator.eval_correct_ext'.
apply A.TaylorValuator.TM.get_tm_correct ; cycle 1.
  exists u.
  apply I.join_correct.
  now left.
rewrite map_map.
apply A.TaylorValuator.eval_correct_aux'.
Qed.

Definition bertrand_prog alpha beta p :=
  let x := length p in
  app p (Prog.Unary (PowerInt alpha) x :: Prog.Unary Ln (S x) :: Prog.Unary (PowerInt (Z_of_nat beta)) 0 :: Prog.Binary Mul 2 0 :: Prog.Binary Mul 4 0 :: nil).

Lemma bertrand_prog_correct :
  forall alpha beta p c x,
  nth 0 (Prog.eval_real (bertrand_prog alpha beta p) (x :: c)) 0 =
  (nth 0 (Prog.eval_real p (x :: c)) 0 * (powerRZ x alpha * pow (ln x) beta)).
Proof.
intros alpha beta p c x.
unfold Prog.eval_real, bertrand_prog.
rewrite 2!Prog.rev_formula.
rewrite rev_app_distr.
simpl.
replace (nth (length p) _ _) with x.
now rewrite <- pow_powerRZ.
rewrite <- rev_length.
now induction (rev p) as [|h t].
Qed.

Definition bertrand_infty_interval alpha beta prec ui :=
  if F'.le' F.one (I.lower ui) then
    BI.f_int_fast prec ui alpha beta
  else I.nai.

Definition bertrand_zero_interval alpha beta prec vi :=
  if andb (F'.lt' F.zero (I.lower vi)) (F'.le' (I.upper vi) F.one) then
    BI.f0eps_int prec vi alpha beta
  else I.nai.

Definition invxln_prog beta p :=
  let x := length p in
  app p (Prog.Unary Ln x :: Prog.Unary (PowerInt (Z_of_nat (S (S beta)))) 0 :: Prog.Binary Mul (S (S x)) 0 :: Prog.Binary Div 3 0 :: nil).

Lemma invxln_prog_correct :
  forall beta p c x,
  nth 0 (Prog.eval_real (invxln_prog beta p) (x :: c)) 0 =
  (nth 0 (Prog.eval_real p (x :: c)) 0 / (x * pow (ln x) (S (S beta)))).
Proof.
intros beta p c x.
unfold Prog.eval_real, invxln_prog.
rewrite 2!Prog.rev_formula.
rewrite rev_app_distr.
simpl.
replace (nth (length p) _ _) with x.
now rewrite Pos2Nat.inj_succ, SuccNat2Pos.id_succ.
rewrite <- rev_length.
now induction (rev p) as [|h t].
Qed.

Definition invxln_interval beta prec ui :=
  if F'.lt' F.one (I.lower ui) then
    BI.f_neg_int prec ui (S beta)
  else I.nai.

(*Eval cbv -[ln exp powerRZ IZR] in Prog.eval_real (invxln_prog 2 (Prog.Unary Exp 0 :: nil)) (42%R :: nil).*)

Definition eval_RInt_gen_infty prec deg limit hyps mi pg pf pfm pu cg cf cfm cu g :=
  let hyps := R.merge_hyps prec hyps in
  let fi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai in
  let fmi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cfm in
    fun b => nth 0 (A.BndValuator.eval prec pfm (b :: bounds)) I.nai in
  let ui :=
    let bounds := hyps ++ map (T.eval_bnd prec) cu in
    nth 0 (A.BndValuator.eval prec pu bounds) I.nai in
  let mid u v :=
    match u, v with
    | IR.IBu, IR.IBv => I.midpoint (I.upper_extent ui)
    | IR.IBu, IR.IBp v => I.midpoint (I.join ui (I.bnd v v))
    | IR.IBp u, IR.IBv => I.midpoint (I.upper_extent (I.bnd u u))
    | IR.IBp u, IR.IBp v => I.midpoint (I.bnd u v)
    | _, _ => F.zero
    end in
  let Fi1 :=
    let bounds := hyps ++ map (T.eval_bnd prec) cfm in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun ui vi =>
      let xi := I.join ui vi in
      let gi :=
        A.TaylorValuator.TM.get_tm (prec, deg) xi
          (nth 0 (A.TaylorValuator.eval prec deg xi pfm (A.TaylorValuator.TM.var :: bounds))
            A.TaylorValuator.TM.dummy) in
      IT.taylor_integral_naive_intersection prec fmi gi xi ui vi in
  let Fi2 :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun ui =>
      let yi := fi (I.upper_extent ui) in
      if I.bounded yi then I.mul prec yi (mi prec ui) else I.nai in
  let Fi u v :=
    match u, v with
    | IR.IBu, IR.IBv => Fi2 ui
    | IR.IBu, IR.IBp v => Fi1 ui (I.bnd v v)
    | IR.IBp u, IR.IBv => Fi2 (I.bnd u u)
    | IR.IBp u, IR.IBp v => Fi1 (I.bnd u u) (I.bnd v v)
    | _, _ => I.nai
    end in
  let check :=
    let bounds := hyps ++ map (T.eval_bnd prec) cg in
    fun b =>
      let yi := nth 0 (A.BndValuator.eval prec pg (b :: bounds)) I.nai in
      R.eval_goal_bnd prec g yi in
  check (IR.bisect prec limit mid Fi check).

Theorem eval_RInt_gen_infty_correct :
  forall prec deg limit vars hyps mi mp mr pg pf pu cg cf cu g,
  (forall yi ui f u, contains (I.convert ui) (Xreal u) ->
    (forall t, (u <= t)%R -> continuous f t) ->
    (forall t, (u <= t)%R -> contains (I.convert yi) (Xreal (f t))) ->
    I.bounded yi = true ->
    I.convert (mi prec ui) <> Inan ->
    exists I : R,
    is_RInt_gen (fun t : R => f t * mr t) (at_point u) (Rbar_locally p_infty) I /\
    contains (I.convert (I.mul prec yi (mi prec ui))) (Xreal I)) ->
  (forall c t, nth 0 (Prog.eval_real mp (t :: c)) 0 = nth 0 (Prog.eval_real pf (t :: c)) 0 * mr t)%R ->
  no_floor_prog mp = true ->
  no_floor_prog pf = true ->
  eval_RInt_gen_infty prec deg limit hyps mi pg pf mp pu cg cf cf cu g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * mr t)
        (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty)) :: vars) cg)).
Proof.
intros prec deg limit vars hyps mi mp mr pg pf pu cg cf cu g Hf Hm1 Hm2 Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply (R.eval_goal_bnd_correct prec) with (2 := H).
unfold Prog.eval_real'.
simpl.
fold (compute_inputs prec hyps cg).
destruct (app_merge_hyps_eval_bnd prec _ _ cg H') as [bpg [<- <-]].
apply A.BndValuator.eval_correct_ext'.
fold (compute_inputs prec hyps cu).
destruct (app_merge_hyps_eval_bnd prec _ _ cu H') as [bpu [<- <-]].
generalize (A.BndValuator.eval_correct' prec pu bpu 0).
generalize (nth 0 (A.BndValuator.eval prec pu (map A.interval_from_bp bpu)) I.nai).
generalize (nth 0 (Prog.eval_real pu (map A.real_from_bp bpu)) 0%R).
clear -H' Hf Hm1 Hm2 Hp.
intros u ui Hu.
apply IR.bisect_correct with (uf := at_point u) (vf := Rbar_locally p_infty) ;
  [ typeclasses eauto .. | idtac ].
intros u' v'.
fold (compute_inputs prec hyps cf).
destruct (app_merge_hyps_eval_bnd prec _ _ cf H') as [bpf [<- <-]].
set (fi :=
  let bounds := map A.interval_from_bp bpf in
  fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai).
set (fmi :=
  let bounds := map A.interval_from_bp bpf in
  fun b => nth 0 (A.BndValuator.eval prec mp (b :: bounds)) I.nai).
set (Fi1 :=
  let bounds := map A.TaylorValuator.TM.const (map A.interval_from_bp bpf) in
  fun ui vi =>
    let xi := I.join ui vi in
    let gi :=
      A.TaylorValuator.TM.get_tm (prec, deg) xi
        (nth 0 (A.TaylorValuator.eval prec deg xi mp (A.TaylorValuator.TM.var :: bounds))
          A.TaylorValuator.TM.dummy) in
    IT.taylor_integral_naive_intersection prec fmi gi xi ui vi).
set (Fi2 :=
  let bounds := map A.interval_from_bp bpf in
  let bounds := map A.TaylorValuator.TM.const bounds in
  fun ui =>
    let yi := fi (I.upper_extent ui) in
    if I.bounded yi then I.mul prec yi (mi prec ui) else I.nai).
apply IR.valid_at_mixed with (u := u) (v := Rbar_locally p_infty)
    (fi1 := Fi1) (fi2 := Fi2) (ui := ui) (u' := u') (v' := v').
- typeclasses eauto.
- exact Hu.
- clear -Hf Hm1 Hm2 Hp.
  intros ui vi u v Hu Hv.
  apply RInt_helper.
  intros Hi.
  assert (ex_RInt (fun t => nth 0 (Prog.eval_real pf (t :: map A.real_from_bp bpf)) 0%R * mr t) u v) as [I HI].
    eapply ex_RInt_ext.
      intros x _.
      apply Hm1.
    apply (A.BndValuator.ex_RInt_eval prec) with (i := I.join ui vi).
      apply Hm2.
      apply contains_connected.
      apply Rmin_case ; apply I.join_correct.
      now left.
      now right.
      apply Rmax_case ; apply I.join_correct.
      now left.
      now right.
    contradict Hi.
    unfold Fi1, IT.taylor_integral_naive_intersection, fmi. clear -Hi.
    rewrite I.real_correct.
    destruct (I.convert (I.mul _ _ _)) as [|il iu] eqn:Hm.
      easy.
    exfalso.
    eapply I.mul_propagate_r in Hi.
    now rewrite Hm in Hi.
  exists I.
  apply (conj HI).
  rewrite <- is_RInt_unique with (1 := HI).
  apply IT.taylor_integral_naive_intersection_correct ; cycle 2.
    now exists I.
    exact Hu.
    exact Hv.
    apply I.join_correct.
    now left.
    apply I.join_correct.
    now right.
    intros xi x Hx.
    rewrite <- Hm1.
    now apply A.BndValuator.eval_correct_ext'.
  apply A.TaylorValuator.TM.get_tm_correct ; cycle 1.
    exists u.
    apply I.join_correct.
    now left.
  rewrite map_map.
  eapply A.TaylorValuator.TM.approximates_ext.
  intros x.
  rewrite <- Hm1.
  easy.
  apply A.TaylorValuator.eval_correct_aux'.
- clear -Hp Hf.
  intros ui u Hu.
  apply RInt_gen_helper ; [typeclasses eauto .. | idtac].
  unfold Fi2.
  destruct I.bounded eqn:Hb ; cycle 1.
    now rewrite I.nai_correct.
  intros Hi.
  apply Hf with (1 := Hu) (4 := Hb).
  + intros t Ht.
    apply A.BndValuator.continuous_eval with (prec := prec) (i := I.upper_extent ui) (1 := Hp).
    now apply I.upper_extent_correct with (1 := Hu).
    change (I.convert (fi (I.upper_extent ui)) <> Inan).
    clear -Hb.
Admitted.
(*     now destruct fi. *)
(*   + intros t Ht. *)
(*     apply A.BndValuator.eval_correct_ext'. *)
(*     now apply I.upper_extent_correct with (1 := Hu). *)
(*   + contradict Hi. *)
(*     now apply I.mul_propagate_r. *)
(* Qed. *)

Theorem eval_RInt_gen_infty_bertrand :
  forall prec deg limit vars hyps alpha beta pg pf pu cg cf cu g,
  (alpha < -1)%Z ->
  no_floor_prog pf = true ->
  eval_RInt_gen_infty prec deg limit hyps (bertrand_infty_interval alpha beta) pg pf (bertrand_prog alpha beta pf) pu cg cf cf cu g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * (powerRZ t alpha * pow (ln t) beta))
        (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty)) :: vars) cg)).
Proof.
intros prec deg limit vars hyps alpha beta pg pf pu cg cf cu g Halpha Hp.
apply eval_RInt_gen_infty_correct ; cycle 1.
- apply bertrand_prog_correct.
- unfold bertrand_prog, no_floor_prog in Hp |- *.
  rewrite <- fold_left_rev_right.
  rewrite rev_app_distr.
  simpl.
  rewrite fold_left_rev_right.
  now rewrite Hp.
- exact Hp.
- intros fi ui f u Hu Hc Hf Hb.
  unfold bertrand_infty_interval.
  destruct F'.le' eqn:Hul ; cycle 1.
    now rewrite I.nai_correct.
  intros _.
  assert (Hu': (1 <= u)%R).
    apply F'.le'_correct in Hul.
    rewrite F.one_correct in Hul.
    rewrite I.lower_correct in Hul; [|admit].
    destruct (I.convert ui) as [|[|ul] ur] ; try easy.
    now apply Rle_trans with (2 := proj1 Hu).
  eapply IU.integral_interval_mul_infty with (1 := Hu) (2 := Hf) (3 := Hb) (4 := Hc).
  + intros x Hx.
    assert (Hx': (0 < x)%R).
      apply Rlt_le_trans with (1 := Rlt_0_1).
      now apply Rle_trans with u.
    apply @continuous_mult.
    apply @ex_derive_continuous.
    apply ex_derive_powerRZ.
    right.
    now apply Rgt_not_eq.
    apply @ex_derive_continuous.
    apply ex_derive_pow.
    eexists.
    now apply is_derive_ln.
  + intros x Hx.
    apply Stdlib.Rmult_le_pos_pos.
    apply powerRZ_le.
    lra.
    apply pow_le.
    rewrite <- ln_1.
    apply ln_le.
    apply Rlt_0_1.
    now apply Rle_trans with u.
  + apply f_lim_correct with (2 := Halpha).
    now apply Rlt_le_trans with (1 := Rlt_0_1).
  + apply BI.f_int_fast_correct.
    exact Hu.
    now apply Rlt_le_trans with (1 := Rlt_0_1).
    now apply Zlt_not_eq.
Admitted.

Theorem eval_RInt_gen_infty_invxln :
  forall prec deg limit vars hyps beta pg pf pu cg cf cu g,
  no_floor_prog pf = true ->
  eval_RInt_gen_infty prec deg limit hyps (invxln_interval beta) pg pf (invxln_prog beta pf) pu cg cf cf cu g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf / (t * pow (ln t) (S (S beta))))
        (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty)) :: vars) cg)).
Proof.
intros prec deg limit vars hyps beta pg pf pu cg cf cu g Hp.
apply eval_RInt_gen_infty_correct ; cycle 1.
- apply invxln_prog_correct.
- unfold invxln_prog, no_floor_prog in Hp |- *.
  rewrite <- fold_left_rev_right.
  rewrite rev_app_distr.
  simpl.
  rewrite fold_left_rev_right.
  now rewrite Hp.
- exact Hp.
- intros fi ui f u Hu Hc Hf Hb.
  unfold invxln_interval.
  destruct F'.lt' eqn:Hul ; cycle 1.
    now rewrite I.nai_correct.
  intros _.
  assert (Hu': (1 < u)%R).
    apply F'.lt'_correct in Hul.
    rewrite F.one_correct in Hul.
    rewrite I.lower_correct in Hul; [|admit].
    destruct (I.convert ui) as [|[|ul] ur] ; try easy.
    now apply Rlt_le_trans with (2 := proj1 Hu).
  eapply IU.integral_interval_mul_infty with (1 := Hu) (2 := Hf) (3 := Hb) (4 := Hc).
  + intros x Hx.
    assert (Hx': (1 < x)%R).
      now apply Rlt_le_trans with u.
    apply (continuous_f_neg x (S (S beta))).
    now apply Rlt_trans with (1 := Rlt_0_1).
    now apply Rgt_not_eq.
  + intros x Hx.
    apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat.
    lra.
    apply (pow_lt (ln x) (S (S beta))).
    rewrite <- ln_1.
    apply ln_increasing.
    apply Rlt_0_1.
    now apply Rlt_le_trans with u.
  + now apply (f_neg_correct_RInt_gen_a_infty u (S beta)).
  + now apply BI.f_neg_int_correct.
Admitted.

Definition eval_RInt_gen_zero prec deg limit hyps mi pg pf pfm pv cg cf cfm cv g :=
  let hyps := R.merge_hyps prec hyps in
  let fi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai in
  let fmi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cfm in
    fun b => nth 0 (A.BndValuator.eval prec pfm (b :: bounds)) I.nai in
  let vi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cv in
    nth 0 (A.BndValuator.eval prec pv bounds) I.nai in
  let mid u v :=
    match u, v with
    | IR.IBu, IR.IBv => I.midpoint (I.join I.zero vi)
    | IR.IBu, IR.IBp v => I.midpoint (I.bnd F.zero v)
    | IR.IBp u, IR.IBv => I.midpoint (I.join (I.bnd u u) vi)
    | IR.IBp u, IR.IBp v => I.midpoint (I.bnd u v)
    | _, _ => F.zero
    end in
  let Fi1 :=
    let bounds := hyps ++ map (T.eval_bnd prec) cfm in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun ui vi =>
      let xi := I.join ui vi in
      let gi :=
        A.TaylorValuator.TM.get_tm (prec, deg) xi
          (nth 0 (A.TaylorValuator.eval prec deg xi pfm (A.TaylorValuator.TM.var :: bounds))
            A.TaylorValuator.TM.dummy) in
      IT.taylor_integral_naive_intersection prec fmi gi xi ui vi in
  let Fi2 :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun vi =>
      let yi := fi (I.join I.zero vi) in
      if I.bounded yi then I.mul prec yi (mi prec vi) else I.nai in
  let Fi u v :=
    match u, v with
    | IR.IBu, IR.IBv => Fi2 vi
    | IR.IBu, IR.IBp v => Fi2 (I.bnd v v)
    | IR.IBp u, IR.IBv => Fi1 (I.bnd u u) vi
    | IR.IBp u, IR.IBp v => Fi1 (I.bnd u u) (I.bnd v v)
    | _, _ => I.nai
    end in
  let check :=
    let bounds := hyps ++ map (T.eval_bnd prec) cg in
    fun b =>
      let yi := nth 0 (A.BndValuator.eval prec pg (b :: bounds)) I.nai in
      R.eval_goal_bnd prec g yi in
  check (IR.bisect prec limit mid Fi check).

Theorem eval_RInt_gen_zero_correct :
  forall prec deg limit vars hyps mi mp mr pg pf pv cg cf cv g,
  (forall yi vi f v, contains (I.convert vi) (Xreal v) ->
    (forall t, (0 <= t <= v)%R -> continuous f t) ->
    (forall t, (0 <= t <= v)%R -> contains (I.convert yi) (Xreal (f t))) ->
    I.bounded yi = true ->
    I.convert (mi prec vi) <> Inan ->
    exists I : R,
    is_RInt_gen (fun t : R => f t * mr t) (at_right 0) (at_point v) I /\
    contains (I.convert (I.mul prec yi (mi prec vi))) (Xreal I)) ->
  (forall c t, nth 0 (Prog.eval_real mp (t :: c)) 0 = nth 0 (Prog.eval_real pf (t :: c)) 0 * mr t)%R ->
  no_floor_prog mp = true ->
  no_floor_prog pf = true ->
  eval_RInt_gen_zero prec deg limit hyps mi pg pf mp pv cg cf cf cv g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * mr t)
        (at_right 0) (at_point (Prog.eval_real' pv vars cv))) :: vars) cg)).
Proof.
intros prec deg limit vars hyps mi mp mr pg pf pv cg cf cv g Hf Hm1 Hm2 Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply (R.eval_goal_bnd_correct prec) with (2 := H).
unfold Prog.eval_real'.
simpl.
fold (compute_inputs prec hyps cg).
destruct (app_merge_hyps_eval_bnd prec _ _ cg H') as [bpg [<- <-]].
apply A.BndValuator.eval_correct_ext'.
fold (compute_inputs prec hyps cv).
destruct (app_merge_hyps_eval_bnd prec _ _ cv H') as [bpv [<- <-]].
generalize (A.BndValuator.eval_correct' prec pv bpv 0).
generalize (nth 0 (A.BndValuator.eval prec pv (map A.interval_from_bp bpv)) I.nai).
generalize (nth 0 (Prog.eval_real pv (map A.real_from_bp bpv)) 0%R).
clear -H' Hf Hm1 Hm2 Hp.
intros v vi Hv.
apply IR.bisect_correct with (uf := at_right 0) (vf := at_point v) ;
  [ typeclasses eauto .. | idtac ].
intros u' v'.
fold (compute_inputs prec hyps cf).
destruct (app_merge_hyps_eval_bnd prec _ _ cf H') as [bpf [<- <-]].
set (fi :=
  let bounds := map A.interval_from_bp bpf in
  fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai).
set (fmi :=
  let bounds := map A.interval_from_bp bpf in
  fun b => nth 0 (A.BndValuator.eval prec mp (b :: bounds)) I.nai).
set (Fi1 :=
  let bounds := map A.TaylorValuator.TM.const (map A.interval_from_bp bpf) in
  fun ui vi =>
    let xi := I.join ui vi in
    let gi :=
      A.TaylorValuator.TM.get_tm (prec, deg) xi
        (nth 0 (A.TaylorValuator.eval prec deg xi mp (A.TaylorValuator.TM.var :: bounds))
          A.TaylorValuator.TM.dummy) in
    IT.taylor_integral_naive_intersection prec fmi gi xi ui vi).
set (Fi2 :=
  let bounds := map A.interval_from_bp bpf in
  let bounds := map A.TaylorValuator.TM.const bounds in
  fun vi =>
    let yi := fi (I.join I.zero vi) in
    if I.bounded yi then I.mul prec yi (mi prec vi) else I.nai).
apply IR.valid_at_mixed' with (u := at_right 0) (v := v)
    (fi1 := Fi1) (fi2 := Fi2) (vi := vi) (u' := u') (v' := v').
- typeclasses eauto.
- exact Hv.
- clear -Hf Hm1 Hm2 Hp.
  intros ui vi u v Hu Hv.
  apply RInt_helper.
  intros Hi.
  assert (ex_RInt (fun t => nth 0 (Prog.eval_real pf (t :: map A.real_from_bp bpf)) 0%R * mr t) u v) as [I HI].
    eapply ex_RInt_ext.
      intros x _.
      apply Hm1.
    apply (A.BndValuator.ex_RInt_eval prec) with (i := I.join ui vi).
      apply Hm2.
      apply contains_connected.
      apply Rmin_case ; apply I.join_correct.
      now left.
      now right.
      apply Rmax_case ; apply I.join_correct.
      now left.
      now right.
    contradict Hi.
    unfold Fi1, IT.taylor_integral_naive_intersection, fmi. clear -Hi.
    rewrite I.real_correct.
    destruct (I.convert (I.mul _ _ _)) as [|il iu] eqn:Hm.
      easy.
    exfalso.
    eapply I.mul_propagate_r in Hi.
    now rewrite Hm in Hi.
  exists I.
  apply (conj HI).
  rewrite <- is_RInt_unique with (1 := HI).
  apply IT.taylor_integral_naive_intersection_correct ; cycle 2.
    now exists I.
    exact Hu.
    exact Hv.
    apply I.join_correct.
    now left.
    apply I.join_correct.
    now right.
    intros xi x Hx.
    rewrite <- Hm1.
    now apply A.BndValuator.eval_correct_ext'.
  apply A.TaylorValuator.TM.get_tm_correct ; cycle 1.
    exists u.
    apply I.join_correct.
    now left.
  rewrite map_map.
  eapply A.TaylorValuator.TM.approximates_ext.
  intros x.
  rewrite <- Hm1.
  easy.
  apply A.TaylorValuator.eval_correct_aux'.
- clear -Hp Hf.
  intros vi v Hv.
  apply RInt_gen_helper ; [typeclasses eauto .. | idtac].
  unfold Fi2.
  destruct I.bounded eqn:Hb ; cycle 1.
    now rewrite I.nai_correct.
  assert (Ht': forall t, (0 <= t <= v)%R -> contains (I.convert (I.join I.zero vi)) (Xreal t)).
    apply contains_connected.
    apply I.join_correct.
    left.
    rewrite I.zero_correct.
    split ; apply Rle_refl.
    apply I.join_correct.
    now right.
  intros Hi.
  apply Hf with (1 := Hv) (4 := Hb).
  + intros t Ht.
    apply A.BndValuator.continuous_eval with (prec := prec) (i := I.join I.zero vi) (1 := Hp).
    now apply Ht'.
    change (I.convert (fi (I.join I.zero vi)) <> Inan).
    clear -Hb.
Admitted.
(*     now destruct fi. *)
(*   + intros t Ht. *)
(*     apply A.BndValuator.eval_correct_ext'. *)
(*     now apply Ht'. *)
(*   + contradict Hi. *)
(*     now apply I.mul_propagate_r. *)
(* Qed. *)

Theorem eval_RInt_gen_zero_bertrand :
  forall prec deg limit vars hyps alpha beta pg pf pv cg cf cv g,
  (-1 < alpha)%Z ->
  no_floor_prog pf = true ->
  eval_RInt_gen_zero prec deg limit hyps (bertrand_zero_interval alpha beta) pg pf (bertrand_prog alpha beta pf) pv cg cf cf cv g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * (powerRZ t alpha * pow (ln t) beta))
        (at_right 0) (at_point (Prog.eval_real' pv vars cv))) :: vars) cg)).
Proof.
intros prec deg limit vars hyps alpha beta pg pf pv cg cf cv g Halpha Hp.
apply eval_RInt_gen_zero_correct ; cycle 1.
- apply bertrand_prog_correct.
- unfold bertrand_prog, no_floor_prog in Hp |- *.
  rewrite <- fold_left_rev_right.
  rewrite rev_app_distr.
  simpl.
  rewrite fold_left_rev_right.
  now rewrite Hp.
- exact Hp.
- intros fi vi f v Hv Hc Hf Hb.
  unfold bertrand_zero_interval.
  destruct F'.lt' eqn:Hvl ; cycle 1.
    cbv [andb].
    now rewrite I.nai_correct.
  destruct F'.le' eqn:Hvu ; cycle 1.
    cbv [andb].
    now rewrite I.nai_correct.
  intros _.
  assert (Hv': (0 < v)%R).
    apply F'.lt'_correct in Hvl.
    rewrite F.zero_correct in Hvl.
    rewrite I.lower_correct in Hvl; [|admit].
    destruct (I.convert vi) as [|[|vl] vr] ; try easy.
    now apply Rlt_le_trans with (2 := proj1 Hv).
  eapply IU.integral_interval_mul_zero with (1 := Hv') (2 := Hv) (3 := Hf) (4 := Hb) (5 := Hc).
  + intros x Hx.
    apply @continuous_mult.
    apply @ex_derive_continuous.
    apply ex_derive_powerRZ.
    right.
    now apply Rgt_not_eq.
    apply @ex_derive_continuous.
    apply ex_derive_pow.
    eexists.
    now apply is_derive_ln.
  + destruct (Zeven_odd_dec (Z.of_nat beta)) as [Hbeta|Hbeta] ; [left|right] ; intros x Hx.
      apply Rmult_le_pos_pos.
      now apply powerRZ_le.
      apply IT.TM.TMI.ZEven_pow_le.
      now apply Zeven_equiv.
    apply Rmult_le_pos_neg.
    now apply powerRZ_le.
    apply IT.TM.TMI.ZOdd_pow_le.
    now apply Zodd_equiv.
    rewrite <- ln_1.
    apply ln_le.
    apply Hx.
    apply Rle_trans with (1 := proj2 Hx).
    apply F'.le'_correct in Hvu.
    rewrite F.one_correct in Hvu.
    rewrite I.upper_correct in Hvu; [|admit].
    destruct (I.convert vi) as [|vr [|vu]] ; try easy.
    now apply Rle_trans with (1 := proj2 Hv).
  + now apply f0eps_lim_correct with (1 := Halpha).
  + apply BI.f0eps_correct ; try easy.
    now apply Zgt_not_eq.
Admitted.

Ltac tuple_to_list params l :=
  match params with
  | pair ?a ?b => tuple_to_list a (b :: l)
  | pair _ ?b => fail 100 "Unknown tactic parameter" b
  | ?b => constr:(b :: l)
  | ?b => fail 100 "Unknown tactic parameter" b
  end.

Inductive interval_tac_method : Set :=
  | itm_eval
  | itm_bisect
  | itm_bisect_diff
  | itm_bisect_taylor.

Ltac do_interval_generalize :=
  match goal with
  | |- contains (I.convert ?b) (Xreal ?t) -> _ =>
    let H := fresh "H" in
    intro H ;
    lazymatch eval cbv -[IZR Rdiv] in (I.convert b) with
    | Ibnd ?l ?u =>
      lazymatch l with
      | Xreal ?l =>
        lazymatch u with
        | Xnan => change (l <= t /\ True)%R in H ; destruct H as [H _]
        | Xreal ?u => change (l <= t <= u)%R in H
        end
      | Xnan =>
        lazymatch u with
        | Xreal ?u => change (True /\ t <= u)%R in H ; destruct H as [_ H]
        | Xnan => fail "Xnan: Nothing known about" t
        end
      end
    | Inan => fail "Inan: Nothing known about" t
    end ;
    revert H
  end.

Ltac do_reduction nocheck native :=
  clear ;
  match nocheck with
  | true =>
    match native with
    | true => native_cast_no_check (eq_refl true)
    | false => vm_cast_no_check (eq_refl true)
    end
  | false =>
    (abstract
    match native with
    | true => native_cast_no_check (eq_refl true)
    | false => vm_cast_no_check (eq_refl true)
    end) ||
    fail "Numerical evaluation failed to conclude. You may want to adjust some parameters"
  end.

Ltac do_interval vars prec degree depth native nocheck eval_tac :=
  let prec := eval vm_compute in (F.PtoP prec) in
  massage_goal ;
  reify_full vars ;
  match eval_tac with
  | itm_eval => apply (eval_bnd_correct prec)
  | itm_bisect => apply (eval_bisect_correct prec depth)
  | itm_bisect_diff => apply (eval_bisect_diff_correct prec depth)
  | itm_bisect_taylor => apply (eval_bisect_taylor_correct prec degree depth)
  end ;
  do_reduction nocheck native.

Ltac do_interval_intro y extend vars prec degree depth native nocheck eval_tac :=
  let prec := eval vm_compute in (F.PtoP prec) in
  let i := fresh "__i" in
  evar (i : I.type) ;
  cut (contains (I.convert i) (Xreal y))%R ; cycle 1 ; [
    let vars := get_vars y vars in
    reify_partial y vars ;
    apply (eq_ind _ (fun z => contains (I.convert i) (Xreal z))) ;
    find_hyps vars ;
    match eval_tac with
    | itm_eval => apply (eval_bnd_contains_correct prec)
    | itm_bisect => apply (eval_bisect_contains_correct prec depth)
    | itm_bisect_diff => apply (eval_bisect_contains_diff_correct prec depth)
    | itm_bisect_taylor => apply (eval_bisect_contains_taylor_correct prec degree depth)
    end ;
    match goal with
    | |- _ ?hyps ?prog ?consts _ = true =>
      let yi :=
        match eval_tac with
        | itm_eval => constr:(eval_bnd_plain prec hyps prog consts)
        | itm_bisect => constr:(eval_bisect_plain prec depth extend hyps prog consts)
        | itm_bisect_diff => constr:(eval_bisect_diff_plain prec depth extend hyps prog consts)
        | itm_bisect_taylor => constr:(eval_bisect_taylor_plain prec degree depth extend hyps prog consts)
        end in
      let yi :=
        match native with
        | true => eval native_compute in (extend yi)
        | false => eval vm_compute in (extend yi)
        end in
      instantiate (i := yi)
    end ;
    do_reduction nocheck native
  | do_interval_generalize ; clear i ].

Ltac do_parse params depth :=
  let rec aux vars prec degree depth native nocheck itm params :=
    lazymatch params with
    | nil => constr:((vars, prec, degree, depth, native, nocheck, itm))
    | cons (i_prec ?p) ?t => aux vars p degree depth native nocheck itm t
    | cons (i_degree ?d) ?t => aux vars prec d depth native nocheck itm t
    | cons (i_bisect ?x) ?t => aux (cons x nil) prec degree depth native nocheck itm_bisect t
    | cons (i_bisect_diff ?x) ?t => aux (cons x nil) prec degree depth native nocheck itm_bisect_diff t
    | cons (i_bisect_taylor ?x) ?t => aux (cons x nil) prec degree depth native nocheck itm_bisect_taylor t
    | cons (i_depth ?d) ?t => aux vars prec degree d native nocheck itm t
    | cons i_native_compute ?t => aux vars prec degree depth true nocheck itm t
    | cons i_delay ?t => aux vars prec degree depth native true itm t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@nil R) 30%positive 10%nat depth false false itm_eval params.

Ltac do_interval_parse params :=
  match do_parse params 15%nat with
  | (?vars, ?prec, ?degree, ?depth, ?native, ?nocheck, ?itm) =>
    do_interval vars prec degree depth native nocheck itm
  end.

Ltac do_interval_intro_parse t extend params :=
  match do_parse params 5%nat with
  | (?vars, ?prec, ?degree, ?depth, ?native, ?nocheck, ?itm) =>
    do_interval_intro t extend vars prec degree depth native nocheck itm
  end.

Ltac do_integral prec degree fuel native nocheck :=
  let prec := eval vm_compute in (F.PtoP prec) in
  massage_goal ;
  lazymatch goal with
  | |- context [RInt _ _ _] =>
    reify_RInt ;
    apply (eval_RInt_correct prec degree fuel) with (1 := eq_refl true)
  | |- context [RInt_gen _ (at_point _) (Rbar_locally p_infty)] =>
    reify_RInt_gen_infty ;
    lazymatch goal with
    | |- context [RInt_gen (fun t => _ / (t * ln t ^ _))%R _ _] =>
      apply (eval_RInt_gen_infty_invxln prec degree fuel) with (1 := eq_refl true)
    | |- context [RInt_gen (fun t => _ * / (t * ln t ^ _))%R _ _] =>
      apply (eval_RInt_gen_infty_invxln prec degree fuel) with (1 := eq_refl true)
    | |- context [RInt_gen (fun t => _ * (powerRZ t _ * ln t ^ _))%R _ _] =>
      apply (eval_RInt_gen_infty_bertrand prec degree fuel) with (1 := eq_refl Lt) (2 := eq_refl true)
    end
  | |- context [RInt_gen _ (at_right 0) (at_point _)] =>
    reify_RInt_gen_zero ;
    lazymatch goal with
    | |- context [RInt_gen (fun t => _ * (powerRZ t _ * ln t ^ _))%R _ _] =>
      apply (eval_RInt_gen_zero_bertrand prec degree fuel) with (1 := eq_refl Lt) (2 := eq_refl true)
    end
  | _ => fail "No integral recognized"
  end ;
  do_reduction nocheck native.

Ltac do_parse' params :=
  let rec aux prec degree fuel native nocheck params :=
    lazymatch params with
    | nil => constr:((prec, degree, fuel, native, nocheck))
    | cons (i_prec ?p) ?t => aux p degree fuel native nocheck t
    | cons (i_degree ?d) ?t => aux prec d fuel native nocheck t
    | cons (i_fuel ?f) ?t => aux prec degree f native nocheck t
    | cons i_native_compute ?t => aux prec degree fuel true nocheck t
    | cons i_delay ?t => aux prec degree fuel native true t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux 30%positive 10%nat 100%positive false false params.

Ltac do_integral_parse params :=
  match do_parse' params with
  | (?prec, ?degree, ?fuel, ?native, ?nocheck) =>
    do_integral prec degree fuel native nocheck
  end.

End Private.

Import Private.

Tactic Notation "interval" :=
  do_interval_parse (@nil interval_tac_parameters).

Tactic Notation "interval" "with" constr(params) :=
  do_interval_parse ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "interval_intro" constr(t) :=
  do_interval_intro_parse t (fun v : I.type => v) (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" :=
  do_interval_intro_parse t I.upper_extent (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "upper"  :=
  do_interval_intro_parse t I.lower_extent (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "with" constr(params) :=
  do_interval_intro_parse t (fun v : I.type => v) ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) :=
  do_interval_intro_parse t I.upper_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) :=
  do_interval_intro_parse t I.lower_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "as" simple_intropattern(H) :=
  do_interval_intro_parse t (fun v : I.type => v) (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.upper_extent (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "as" simple_intropattern(H)  :=
  do_interval_intro_parse t I.lower_extent (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t (fun v : I.type => v) ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.upper_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.lower_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "integral" :=
  do_integral_parse (@nil interval_tac_parameters).

Tactic Notation "integral" "with" constr(params) :=
  do_integral_parse ltac:(tuple_to_list params (@nil interval_tac_parameters)).

End IntervalTactic.

(* Require Import Specific_stdz. *)
(* Require Import Specific_bigint. *)
(* Require Import Specific_ops. *)
(* Module SFBI2 := SpecificFloat BigIntRadix2. *)
(* Module ITSFBI2 := IntervalTactic SFBI2. *)
(* Export ITSFBI2. *)

Require Import Primitive_ops.
Module ITSFPBI2 := IntervalTactic PrimitiveFloat.
Export ITSFPBI2.

Import Private.

(* From testsuite/example-20171018.v *)

(* foire: nearbyint non implémenté *)
(* Lemma h_54_ln_2  h : *)
(*   -53 <= h <= 0 -> *)
(*   -  Rnearbyint rnd_DN (h * ln 2 / ln 5) * ln 5 <= 54 * ln 2. *)
(* Proof. *)
(* intros. *)
(* interval. *)
(* Qed. *)

(* From testsuite/example-20160218.v *)

(* foire: pas de marge *)
(* Lemma constant : *)
(*   3 <= RInt (fun x => 1) 0 3 <= 3. *)
(* Proof. *)
(* integral. *)
(* Qed. *)

(* From testsuite/example-20120205.v *)

(* foire: pas de marge *)
(* Goal forall x, (1 <= x)%R -> (x <= x * x)%R. *)
(* Proof. *)
(* intros. *)
(* apply Rminus_le. *)
(* interval with (i_bisect_diff x). *)
(* Qed. *)

(* From testsuite/example-20071016.v *)

Require Import Coquelicot.Coquelicot.

(* foire: pas de marge *)
(* Goal *)
(*   RInt_gen (fun x => 1 * (powerRZ x 3 * ln x^2)) *)
(*            (at_right 0) (at_point 1) = 1/32. *)
(* Proof. *)
(*   refine ((fun H => Rle_antisym _ _ (proj2 H) (proj1 H)) _). *)
(*   integral. *)
(* Qed. *)

(* From testsuite/bug-20150924.v *)

(* foire: pas de marge *)
(* Goal forall x : R, *)
(*   (Rabs (x - x) <= 1/5)%R. *)
(* Proof. *)
(* intros x. *)
(* interval with (i_bisect_diff x). *)
(* Qed. *)

(* From testsuite/bug-20150925.v *)

(* foire: pas de marge *)
(* Goal forall x, (-1 / 3 <= x - x <= 1 / 7)%R. *)
(* Proof. *)
(* intros x. *)
(* interval with (i_bisect_diff x). *)
(* Qed. *)



(*

(* From bench-ineqs/benchmarks/coq/multi_poly.v *)

Lemma RD : forall x1 x2 x3 : R, -5 <= x1 <= 5 -> -5 <= x2 <= 5 -> -5 <= x3 <= 5 -> -367126907/10000000 <= -x1 + 2*x2 - x3 - 835634534/1000000000 * x2 * (1 + x2).
Time intros x1 x2 x3 H1 H2 H3; interval with (i_bisect_diff x2, i_prec 50).
Qed.

Lemma adaptiveLV : forall x1 x2 x3 x4 : R,
    -2 <= x1 <= 2 -> -2 <= x2 <= 2 -> -2 <= x3 <= 2 -> -2 <= x4 <= 2 ->
    -20801/1000 <= x1*x2^2 + x1 * x3^2 + x1*x4^2 - 11/10 * x1 + 1.
Time intros x1 x2 x3 x4 H1 H2 H3 H4; interval with (i_bisect_diff x1).
Qed.

Lemma butcher : forall x1 x2 x3 x4 x5 x6 : R,
    -1 <= x1 <= 0 -> -1/10 <= x2 <= 9/10 -> -1/10 <= x3 <= 1/2 ->
    -1 <= x4 <= -1/10 -> -1/10 <= x5 <= -5/100 -> -1/10 <= x6 <= -3/100 ->
    -144/100 <= x6 * x2^2 + x5 * x3 ^2 - x1 * x4^2 + x4^3 + x4^2 - x1/3 + 4*x4/3.
Time intros x1 x2 x3 x4 x5 x6 H1 H2 H3 H4 H5 H6;
  interval with (i_bisect_diff x4).
Qed.

Lemma magnetism : forall x1 x2 x3 x4 x5 x6 x7 : R,
    -1 <= x1 <= 1 -> -1 <= x2 <= 1 -> -1 <= x3 <= 1 -> -1 <= x4 <= 1 ->
    -1 <= x5 <= 1 -> -1 <= x6 <= 1 -> -1 <= x7 <= 1 ->
    -25001/100000 <= x1^2 + 2*x2^2 + 2*x3^2 + 2*x4^2 + 2*x5^2 + 2*x6^2 + 2*x7^2 - x1.
Time intros x1 x2 x3 x4 x5 x6 x7 H1 H2 H3 H4 H5 H6 H7;
  interval with (i_bisect_diff x1).
Qed.

(* From bench-ineqs/benchmarks/coq/univ_metitarski.v *)

Notation eps := (1/1024)%R (only parsing).
Notation meps := (-1/1024)%R (only parsing).

(** MetiTarski_JAR2010 paper *)

(* plot(2 * abs(x) / (2 + x) - abs(log(1+x)), [-1, 10]); *)
Lemma MT1 :
  forall x : R, -1 + eps <= x <= 10 ->
           2 * Rabs x / (2 + x) <= Rabs (ln (1 + x)) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x).
Qed.

(* plot(abs(log(1+x)) + log(1 - abs(x)), [-1, 1]); *)
Lemma MT2 :
  forall x : R, -1 + eps <= x <= 1 - eps ->
           Rabs (ln (1 + x)) <= - ln (1 - Rabs x) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x).
Qed.

(* plot(abs(x)/(1 + abs(x)) - abs(log(1+x)), [-1, 1]); *)
Lemma MT3 :
  forall x : R, -1 + eps <= x <= 1 ->
           Rabs x / (1 + Rabs x) <= Rabs (ln (1 + x)) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(abs(log(1+x)) - abs(x)*(1+abs(x))/abs(1+x), [-1, 10]); *)
Lemma MT4 :
  forall x : R, -1 + eps <= x <= 1 ->
                Rabs (ln (1 + x)) <= (Rabs x) * (1 + Rabs x) / Rabs (1 + x) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(abs(x) / 4 - abs(exp(x) - 1), [-1, 1]); *)
Lemma MT5 :
  forall x : R, (-1 <= x <= meps \/ eps <= x <= 1) ->
           Rabs x / 4 < Rabs (exp x - 1).
Proof.
Time intros x [H|H]; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(abs(exp(x) - 1) - 7 * abs(x)/4, [0, 1]); *)
Lemma MT6 :
  forall x : R, (-1 <= x <= meps \/ eps <= x <= 1) ->
                Rabs (exp x - 1) < 7 * (Rabs x) / 4.
Proof.
Time intros x [H|H]; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(abs(exp(x) - 1) - (exp(abs(x)) - 1), [-10, 10]); *)
Lemma MT7 : forall x : R, -10 <= x <= meps -> Rabs (exp x - 1) <= exp (Rabs x) - 1.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(abs(exp(x)-(1+x)) - abs(exp(abs(x))-(1+abs(x))), [-10, 10]); *)
Lemma MT8 :
  forall x : R, -10 <= x <= meps ->
  Rabs (exp x - (1 + x)) <= Rabs (exp (Rabs x) - (1 + Rabs x)).
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x, i_prec 40).
Qed.

(* plot(abs(exp(x)-(1+x/2)^2) - abs(exp(abs(x))-(1+abs(x)/2)^2), [-10, 10]); *)
Lemma MT9 :
  forall x : R, -10 <= x <= meps ->
  Rabs (exp x - (1 + x / 2) ^ 2) <= Rabs (exp (Rabs x) - (1 + (Rabs x) / 2) ^ 2).
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x, i_prec 40).
Qed.

(* plot(2*x/(2+x) - log(1+x), [0, 10]); *)
Lemma MT10 :
  forall x : R, 0 <= x <= 10 -> 2 * x / (2 + x) <= ln (1 + x) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x).
Qed.

(* plot(x/sqrt(1+x) - log(1+x), [-1/3,0]); *)
Lemma MT11 :
  forall x : R, -1/3 <= x <= 0 -> x / sqrt (1 + x) <= ln (1 + x) + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x, i_prec 40).
Qed.

(* plot(log((1+x)/x)-(12*x^2 + 12*x + 1)/(12*x^3 + 18*x^2 + 6*x), [1/3, 10]); *)
Lemma MT12 :
  forall x : R, 1/3 <= x <= 10 ->
  ln ((1 + x) / x) <= (12*x^2 + 12*x + 1) / (12*x^3 + 18*x^2 + 6*x).
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x).
Qed.

(* plot(log((1+x)/x)-1/sqrt(x^2 + x), [1/3, 10]); *)
Lemma MT13 :
  forall x : R, 1/3 <= x <= 10 ->
  ln ((1 + x) / x) <= 1 / sqrt (x ^ 2 + x).
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x, i_prec 40).
Qed.

(* plot(exp(x - x^2) - 1 - x, [0, 1]); *)
Lemma MT14 : forall x : R, 0 <= x <= 1 -> exp (x - x^2) <= 1 + x + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(exp(-x/(1-x))-(1-x), [-10,1/2]); *)
Lemma MT15 : forall x : R, -10 <= x <= 1/2 -> exp(-x/(1 - x)) <= 1 - x + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(abs(sin(x)) - 6/5 * abs(x), [-1, 1]); *)
Lemma MT16 : forall x : R, -1 <= x <= 1 -> Rabs (sin x) <= 6/5 * Rabs x + eps.
Proof.
Time intros x H; apply Rminus_le; interval with (i_bisect_diff x).
Qed.

(* plot(1 - 2 * x - cos(pi * x), [0, 1/2]); *)
Lemma MT17 : forall x : R, eps <= x <= 100/201 -> cos (PI * x) > 1 - 2 * x.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(cos(x) - 1 + x^2/2, [-10,10]); *)
Lemma MT18 : forall x : R, -10 <= x <= 10 -> cos x - 1 + x^2 / 2 + eps >= 0.
Proof.
Time intros x H; apply Rminus_ge; interval with (i_bisect_taylor x).
Qed.

(* plot(8 * sqrt(3) * x / (3 * sqrt(3) + sqrt(75 + 80 * x^2)) - atan(x), [0, 10]); *)
Lemma MT19 :
  forall x : R, 0 <= x <= 10 ->
  eps + atan x >= 8 * sqrt 3 * x / (3 * sqrt 3 + sqrt (75 + 80 * x^2)).
Proof.
Time intros x H; apply Rminus_ge; interval with (i_bisect_diff x).
Qed.

(* plot((x + 1/x) * arctan(x) - 1, [0,5]); *)
Lemma MT20 : forall x : R, eps <= x <= 10 -> (x + 1 / x) * atan x > 1.
Proof.
Time intros x H; interval with (i_bisect_diff x, i_depth 25).
Qed.

(* plot(3 * x / (1 + 2 * sqrt(1 + x^2)) - atan(x), [0, 10]); *)
Lemma MT21 :
  forall x : R, 0 <= x <= 10 -> eps + atan x > 3 * x / (1 + 2 * sqrt (1 + x^2)).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* foire en flottant primitifs *)
(* plot(cos(x)-sin(x)/x, [0, pi]); *)
(* Lemma MT22 : forall x : R, eps <= x <= PI -> cos x <= sin x / x. *)
(* Proof. *)
(* Time intros x H; apply Rminus_le; interval with (i_bisect_taylor x, i_depth 16). *)
(* Qed. *)

(* plot(cos(x) - (sin(x)/x)^2, [0, pi/2]); *)
Lemma MT23 : forall x : R, eps <= x <= PI / 2 -> cos x < (sin x / x) ^ 2.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_taylor x).
Qed.

(* plot(sin(x)/3 + sin(3*x)/6, [pi/3-1, 2*pi/3+1]); *)
Lemma MT24 :
  forall x : R, PI/3 <= x <= 2*PI/3 - eps -> (sin x) / 3 + (sin (3*x)) / 6 > 0.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* plot(12-14.2*exp(-.318*x)+(3.25*cos(1.16*x)-.155*sin(1.16*x))*exp(-1.34*x),[-1/2,2]); *)
Lemma MT25 :
  forall x : R, 0 <= x <= 2 ->
  12 - 142/10 * exp(-318/1000*x) + (325/100*cos(116/100*x) - 155/1000*sin(116/100*x)) * exp(-134/100*x) > 0.
Proof.
Time intros x H; interval with (i_bisect x).
Qed.

(* From bench-ineqs/benchmarks/coq/univ_transcend.v *)

(** http://lipforge.ens-lyon.fr/www/crlibm/ *)
(** http://lipforge.ens-lyon.fr/frs/download.php/162/crlibm-1.0beta4.tar.gz *)

Section CRlibm_exp.
Let p_2_55 : R := 36028797018963968.
Let c3 := 6004799504235417 / p_2_55.
Let c4 := 1501199876148417 / p_2_55.
Notation p x := (x + 1/2 * x^2 + c3 * x^3 + c4 * x^4)%R (only parsing).
Notation eps' := (1/1048576)%R (only parsing).
Notation meps' := (-1/1048576)%R (only parsing).

(* foire : normal vu la précision *)
(* Lemma crlibm_exp : *)
(*   forall x : R, *)
(*   (-355/4194304 <= x <= meps') \/ (eps' <= x <= 355/4194304) -> *)
(*   Rabs ((p x - exp x + 1) / (exp x - 1)) <= 1/4611686018427387904. *)
(* Time intros x [H|H]; unfold c3, c4, p_2_55; *)
(*   interval with (i_bisect_taylor x, i_prec 90). *)
(* Qed. *)
End CRlibm_exp.

(** Melquiond_IJCAR2008 paper *)

(* plot(abs(sqrt(x) - (((((122 / 7397 * x + (-1733) / 13547) * x
  + 529 / 1274) * x + (-767) / 999) * x
  + 407 / 334) * x + 227 / 925)) - 5/65536, [1/2, 2]); *)
Lemma remez_sqrt :
  forall x, 1/2 <= x <= 2 ->
  Rabs (sqrt x - (((((122 / 7397 * x + (-1733) / 13547) * x
                   + 529 / 1274) * x + (-767) / 999) * x
                   + 407 / 334) * x + 227 / 925))
    <= 5/65536.
Time intros x H;
  (* interval with (i_bisect_diff x). *)
  interval with (i_bisect_taylor x).
Qed.

(** Daumas_Lester_Munoz_TC2009 paper with a tighter bound *)

(* plot(abs(atan(x)-(x-(11184811/33554432)*x^3-(13421773/67108864)*x^5))-5/2^28, [-1/30, 1/30]); *)
Lemma abs_err_atan :
  forall x : R, -1/30 <= x <= 1/30 ->
  Rabs (atan x - (x - (11184811/33554432) * x^3 - (13421773/67108864) * x^5))
  <= 5/268435456.
Time intros x H;
  interval with (i_bisect_diff x).
Qed.

(** Daumas_Melquiond_Munoz_ARITH2005 paper *)

Section Rel_err_geodesic.
Let a := 6378137.
Let f := 1000000000/298257223563.
Let umf2 := (1 - f) ^ 2.
Let max := 715/512.
Notation rp phi := (a / sqrt (1 + umf2 * (tan phi) ^ 2)) (only parsing).
Notation arp phi :=
  (let: x := max ^ 2 - phi ^ 2 in
  4439091/4 + x * (9023647/4 + x * (
    13868737/64 + x * (13233647/2048 + x * (
      -1898597/16384 + x * (-6661427/131072)))))) (only parsing).

Lemma rel_err_geodesic :
  forall phi, 0 <= phi <= max ->
  Rabs ((rp phi - arp phi) / rp phi) <= 23/16777216.
Proof.
Time unfold (*rp, arp,*) a, umf2, f, max; intros phi Hphi;
(* interval with (i_bisect_diff phi). *)
  interval with (i_bisect_taylor phi).
Qed.
End Rel_err_geodesic.

(** Harrison_TPHOLs1997 paper *)

(* plot(abs((exp(x)-1)-(x+(8388676/2^24)*x^2+(11184876/2^26)*x^3))-((23/27)/(2^33)), [-10831/1000000, 10831/1000000]); *)
Lemma harrison97 :
  forall x : R,
  (-10831/1000000 <= x <= 10831/1000000) ->
  Rabs ((exp x - 1) - (x + (8388676/2^24) * x^2 + (11184876/2^26) * x^3))
  <= ((23/27) / (2^33)).
Time intros x H;
  interval with (i_bisect_taylor x, i_prec 50).
Qed.

(* From bench-ineqs/benchmarks/coq/univ_metitarski_Rlt.v *)

(** MetiTarski_JAR2010 paper *)

(* plot(abs(sin(x)) - 6/5 * abs(x), [-1, 1]); *)
Lemma MT16__1 : forall x : R, (-1 <= x <= 0) -> (sin x) > - (6/5 * - x + eps).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

Lemma MT16__2 : forall x : R, (-1 <= x <= 0) -> (sin x) < 6/5 * - x + eps.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

Lemma MT16__3 : forall x : R, (0 <= x <= 1) -> (sin x) > - (6/5 * x + eps).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

Lemma MT16__4 : forall x : R, (0 <= x <= 1) -> (sin x) < 6/5 * x + eps.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(1 - 2 * x - cos(pi * x), [0, 1/2]); *)
Lemma MT17' : forall x : R, eps <= x <= 100/201 -> cos (PI * x) > 1 - 2 * x.
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot(cos(x) - 1 + x^2/2, [-10,10]); *)
Lemma MT18' : forall x : R, -10 <= x <= 10 -> cos x - 1 + x^2 / 2 + eps > 0.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

(* plot(8 * sqrt(3) * x / (3 * sqrt(3) + sqrt(75 + 80 * x^2)) - atan(x), [0, 10]); *)
Lemma MT19' :
  forall x : R, 0 <= x <= 10 ->
  eps + atan x > 8 * sqrt 3 * x / (3 * sqrt 3 + sqrt (75 + 80 * x^2)).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* plot((x + 1/x) * arctan(x) - 1, [0,5]); *)
Lemma MT20' : forall x : R, eps <= x <= 10 -> (x + 1 / x) * atan x > 1.
Proof.
Time intros x H; interval with (i_bisect_diff x, i_depth 25).
Qed.

(* plot(3 * x / (1 + 2 * sqrt(1 + x^2)) - atan(x), [0, 10]); *)
Lemma MT21' :
  forall x : R, 0 <= x <= 10 -> eps + atan x > 3 * x / (1 + 2 * sqrt (1 + x^2)).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_diff x).
Qed.

(* foire en flottants primitifs *)
(* plot(cos(x)-sin(x)/x, [0, pi]); *)
(* Lemma MT22' : forall x : R, eps <= x <= PI -> cos x < sin x / x. *)
(* Time intros x H; apply Rminus_lt; interval with (i_bisect_taylor x, i_depth 16). *)
(* Qed. *)

(* plot(cos(x) - (sin(x)/x)^2, [0, pi/2]); *)
Lemma MT23' : forall x : R, eps <= x <= PI / 2 ->
  cos x < (sin x / x) * (sin x / x).
Proof.
Time intros x H; apply Rminus_lt; interval with (i_bisect_taylor x).
Qed.

(* plot(sin(x)/3 + sin(3*x)/6, [pi/3-1, 2*pi/3+1]); *)
Lemma MT24' :
  forall x : R, PI/3 <= x <= 2*PI/3 - eps -> (sin x) / 3 + (sin (3*x)) / 6 > 0.
Proof.
Time intros x H; interval with (i_bisect_diff x).
Qed.

(* From bench-ineqs/benchmarks/coq/fpminmax.v *)

(** Facilities to parse negative powers and pre-compute powers of 2 *)
Notation "a * b ^(- n )" := (a / b ^ n)%R
  (at level 40, b at next level, only parsing) : R_scope.

(** FP minimax polynomials for cos(3/2 * cos(x)), generated using Sollya *)
Notation f x := (cos (3/2 * cos x)) (only parsing).
Notation D x := (-1 <= x <= 1/2) (only parsing).

(** Degree-2 *)
Notation p2 x := (5009597 * 2^(-26) + x * (-3452481 * 2^(-36) + x * (10948483 * 2^(-24)))) (only parsing).
Notation eps2 := (57 * 2^(-10)) (only parsing).

Lemma cos_cos_d2 :
  forall x, D x -> Rabs ((p2 x - f x) / f x) <= eps2.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

(** Degree-3 *)
Notation p3 x := (9578005 * 2^(-27) + x * (-8411879 * 2^(-29) + x * (6079307 * 2^(-23) + x * (14167647 * 2^(-27))))) (only parsing).
Notation eps3 := (51 * 2^(-11)) (only parsing).

Lemma cos_cos_d3 :
  forall x, D x -> Rabs ((p3 x - f x) / f x) <= eps3.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

(** Degree-4 *)
Notation p4 x := (2366509 * 2^(-25) + x * (10537089 * 2^(-34) + x * (1593929 * 2^(-21) + x * (-3609977 * 2^(-29) + x * (-609875 * 2^(-22)))))) (only parsing).
Notation eps4 := (51 * 2^(-14)) (only parsing).

Lemma cos_cos_d4 :
  forall x, D x -> Rabs ((p4 x - f x) / f x) <= eps4.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

(** Degree-5 *)
Notation p5 x := (9491875 * 2^(-27) + x * (1388077 * 2^(-31) + x * (12575645 * 2^(-24) + x * (-3473267 * 2^(-28) + x * (-13477879 * 2^(-27) + x * (11406127 * 2^(-28))))))) (only parsing).
Notation eps5 := (3 * 2^(-12)) (only parsing).

Lemma cos_cos_d5 :
  forall x, D x -> Rabs ((p5 x - f x) / f x) <= eps5.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

(** Degree-6 *)
Notation p6 x := (9492545 * 2^(-27) + x * (12716483 * 2^(-36) + x * (3142515 * 2^(-22) + x * (-8980587 * 2^(-31) + x * (-12736139 * 2^(-27) + x * (8061261 * 2^(-29) + x * (-13450525 * 2^(-29)))))))) (only parsing).
Notation eps6 := (17 * 2^(-16)) (only parsing).

Lemma cos_cos_d6 :
  forall x, D x -> Rabs ((p6 x - f x) / f x) <= eps6.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

(** Degree-7 *)
Notation p7 x := (4747227 * 2^(-26) + x * (5795109 * 2^(-37) + x * (784233 * 2^(-20) + x * (-6099871 * 2^(-32) + x * (-10729417 * 2^(-27) + x * (12242037 * 2^(-30) + x * (-8892053 * 2^(-27) + x * (-14339757 * 2^(-29))))))))) (only parsing).
Notation eps7 := (25 * 2^(-19)) (only parsing).

Lemma cos_cos_d7 :
  forall x, D x -> Rabs ((p7 x - f x) / f x) <= eps7.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

(** Degree-8 *)
Notation p8 x := (9494185 * 2^(-27) + x * (12149587 * 2^(-41) + x * (6275713 * 2^(-23) + x * (-14107149 * 2^(-36) + x * (-2763427 * 2^(-25) + x * (14503039 * 2^(-33) + x * (-530509 * 2^(-23) + x * (-8256955 * 2^(-31) + x * (3638503 * 2^(-28)))))))))) (only parsing).
Notation eps8 := (5 * 2^(-20)) (only parsing).

Lemma cos_cos_d8 :
  forall x, D x -> Rabs ((p8 x - f x) / f x) <= eps8.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

(* From bench-ineqs/benchmarks/coq/fpminmax.v *)

(** Facilities to parse negative powers and pre-compute powers of 2 *)
Notation "a * b ^(- n )" := (a / b ^ n)%R
  (at level 40, b at next level, only parsing) : R_scope.

Lemma cos_cos_d2__1 :
  forall x, D x -> (p2 x - f x) / f x > - eps2.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d2__2 :
  forall x, D x -> (p2 x - f x) / f x < eps2.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d3__1 :
  forall x, D x -> (p3 x - f x) / f x > - eps3.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d3__2 :
  forall x, D x -> (p3 x - f x) / f x < eps3.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d4__1 :
  forall x, D x -> (p4 x - f x) / f x > - eps4.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d4__2 :
  forall x, D x -> (p4 x - f x) / f x < eps4.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d5__1 :
  forall x, D x -> (p5 x - f x) / f x > - eps5.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d5__2 :
  forall x, D x -> (p5 x - f x) / f x < eps5.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d6__1 :
  forall x, D x -> (p6 x - f x) / f x > - eps6.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d6__2 :
  forall x, D x -> (p6 x - f x) / f x < eps6.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d7__1 :
  forall x, D x -> (p7 x - f x) / f x > - eps7.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d7__2 :
  forall x, D x -> (p7 x - f x) / f x < eps7.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d8__1 :
  forall x, D x -> (p8 x - f x) / f x > - eps8.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

Lemma cos_cos_d8__2 :
  forall x, D x -> (p8 x - f x) / f x < eps8.
Proof.
Time intros x H; interval with (i_bisect_taylor x).
Qed.

*)








(*

Require Import Generic_ops.
Module GFSZ2 := GenericFloat Radix2.
Module ITGFSZ2 := IntervalTactic GFSZ2.
Export ITGFSZ2.

Goal True.
interval_intro
  (RInt_gen
     (fun x => (1 * (/ (x * (pow (ln x) 2)))))
     (at_right 0)
     (at_point (1/3))) with (i_integral_deg 2).
done.


Goal True.
interval_intro
  (RInt_gen
     (fun x => (1 / x * (/ (x * (ln x)^3))))
     (at_point 10)
     (Rbar_locally p_infty)) with (i_integral_deg 0).
done.


Goal True.
interval_intro
  (RInt_gen
     (fun x => (1 / ((x^2 - 1)*(x^4 + 1)) * (powerRZ x 2 * (ln x)^1)))
     (at_right 0)
     (at_point (1/2))).
done.

Lemma blo0 :
   1 <= RInt (fun x => exp x) 0 1 <= 2.
Proof.
integral.
Qed.

Lemma blo2 :
  (2/3 <= 5/7)%R.
Proof.
intros.
interval_intro (5/7)%R lower with (i_prec 4%nat).
apply Rle_trans with (2 := H).
interval.
Qed.

Lemma blo3 :
  forall x, (x <= 0)%R ->
  (0 <= x - x <= 0)%R.
Proof.
intros.
Time interval with (i_bisect_diff x).
Qed.

Lemma blo4 :
  forall x, (3/2 <= x <= 2)%R ->
  forall y, (1 <= y <= 33/32)%R ->
  (Rabs (sqrt(1 + x/sqrt(x+y)) - 144/1000*x - 118/100) <= 71/32768)%R.
Proof.
intros.
interval with (i_bisect x).
Qed.

Lemma blo5 :
  forall x, (-1 <= x <= 1)%R ->
  (0 <= exp x - (1 + x) <= 3/4)%R.
Proof.
intros.
split; try interval with (i_bisect_taylor x, i_degree 2).
interval with (i_bisect_diff x).
Qed.

Lemma blo6 : 51/1000 <= RInt_gen (fun x => sin x * (powerRZ x (-5)%Z * pow (ln x) 1%nat)) (at_point 1) (Rbar_locally p_infty) <= 52/1000.
Proof.
integral.
Qed.

Lemma blo7 :  -962587772 * / 8589934592 <=
      RInt_gen (fun x : R => x * (powerRZ x 1 * ln x ^ 1))
        (at_right 0) (at_point 1) <= -940939775 * / 8589934592.
Proof.
integral.
Qed.

Lemma blo8 : 876496966 * / 4398046511104 <=
      RInt_gen (fun x : R => 1 / x ^ 2 * exp (- x))
        (at_point 5) (Rbar_locally p_infty) <= 876509397 * / 4398046511104.
Proof.
integral.
Qed.

Lemma pi10 : (31415926535/10000000000 < PI < 31415926536/10000000000)%R.
Proof.
split; interval with (i_prec 40).
Qed.

*)
