Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import over_instrumented_values.
Require Import oitval_instantiation.
Require Import oitval_val_conversion.
Require Import oitval_val_conversion_facts.
Require Import is_instantiable_oitval.
Require Import over_instrumented_semantics.

Require Import injection_operational_semantics.
Require Import ldna_in.
Require Import ldna_in_facts.
Require Import proof_injection_op_sem.

Require Import instrumented_values.
Require Import instrumented_semantics.
Require Import itval_val_conversion.
Require Import oival_ival_conversion.
Require Import oival_ival_conversion_facts.




Definition dummy_val := V_Num 0.
Definition dummy_oival := OIV_Num 0.

(* SIMPLE VALUES *)

Inductive partially_approximated_val : val -> val -> Prop :=
| PApprox_val_approx :
    forall (v:val),
      partially_approximated_val v dummy_val
| PApprox_val_Num :
    forall (n:Z),
      partially_approximated_val (V_Num n) (V_Num n)
| PApprox_val_Bool :
    forall (b:bool),
      partially_approximated_val (V_Bool b) (V_Bool b)
| PApprox_val_Constr0 :
    forall (n:constr),
      partially_approximated_val (V_Constr0 n) (V_Constr0 n)
| PApprox_val_Constr1 :
    forall (n:constr) (v v':val),
      partially_approximated_val v v'
      -> partially_approximated_val (V_Constr1 n v) (V_Constr1 n v')
| PApprox_val_Couple :
    forall (v1 v1' v2 v2':val),
    partially_approximated_val v1 v1'
    -> partially_approximated_val v2 v2'
    -> partially_approximated_val (V_Couple v1 v2) (V_Couple v1' v2')
| PApprox_val_Closure :
    forall (x:identifier) (e:expr) (c c':env),
      partially_approximated_env c c'
      -> partially_approximated_val (V_Closure x e c) (V_Closure x e c')
| PApprox_val_Rec_Closure :
    forall (f x:identifier) (e:expr) (c c':env),
      partially_approximated_env c c'
      -> partially_approximated_val (V_Rec_Closure f x e c) (V_Rec_Closure f x e c')

with partially_approximated_env : env -> env -> Prop :=
| PApprox_env_empty :
    partially_approximated_env Env_empty Env_empty
| PApprox_env_cons :
    forall (x:identifier) (v v':val) (c c':env),
    partially_approximated_val v v'
    -> partially_approximated_env c c'
    -> partially_approximated_env (Env_cons x v c) (Env_cons x v' c').

(* OVER-INSTRUMENTED VALUES *)

Inductive partially_approximated_oitdeps_fun : (val->bool) -> (val->bool) -> Prop :=
| PApprox_oitdeps_fun :
    forall (tf tf':val->bool),
      (forall (vl:val), tf' vl = true \/ tf' vl = tf vl)
      -> partially_approximated_oitdeps_fun tf tf'.

Inductive partially_approximated_oitdeps : oitdeps -> oitdeps -> Prop :=
| PApprox_oitdeps_empty :
    partially_approximated_oitdeps nil nil
| PApprox_oitdeps_cons :
    forall (oitd oitd':oitdeps) (l:label) (tf tf':val->bool),
      partially_approximated_oitdeps oitd oitd'
      -> partially_approximated_oitdeps_fun tf tf'
      -> partially_approximated_oitdeps (cons (l,tf) oitd) (cons (l,tf') oitd').

Inductive partially_approximated_oideps_fun : (val->val) -> (val->val) -> Prop :=
| PApprox_oideps_fun :
    forall (f f':val->val),
      (forall (vl:val), partially_approximated_val (f vl) (f' vl))
      -> partially_approximated_oideps_fun f f'.

Inductive partially_approximated_oideps : oideps -> oideps -> Prop :=
| PApprox_oideps_empty :
    partially_approximated_oideps nil nil
| PApprox_oideps_cons :
    forall (oid oid':oideps) (l:label) (f f':val->val),
      partially_approximated_oideps oid oid'
      -> partially_approximated_oideps_fun f f'
      -> partially_approximated_oideps (cons (l,f) oid) (cons (l,f') oid').


(* express that oiu2 is a partial approximation of oiu1 *)
Inductive partially_approximated_oival0 : oival0 -> oival0 -> Prop :=
| PApprox_oival0_approx :
    forall (v:oival0),
      partially_approximated_oival0 v (OIV_Num 0)
| PApprox_oival0_Num :
    forall (n:Z),
    partially_approximated_oival0 (OIV_Num n) (OIV_Num n)
| PApprox_oival0_Bool :
    forall (b:bool),
    partially_approximated_oival0 (OIV_Bool b) (OIV_Bool b)
| PApprox_oival0_Constr0 :
    forall (n:constr),
    partially_approximated_oival0 (OIV_Constr0 n) (OIV_Constr0 n)
| PApprox_oival0_Constr1 :
    forall (oiu oiu':oival) (n:constr),
    partially_approximated_oival oiu oiu'
    -> partially_approximated_oival0 (OIV_Constr1 n oiu) (OIV_Constr1 n oiu')
| PApprox_oival0_Couple :
    forall (oiu1 oiu2 oiu1' oiu2':oival),
    partially_approximated_oival oiu1 oiu1'
    -> partially_approximated_oival oiu2 oiu2'
    -> partially_approximated_oival0 (OIV_Couple oiu1 oiu2) (OIV_Couple oiu1' oiu2')
| PApprox_oival0_Closure :
    forall (oic oic':oienv) (x:identifier) (e:expr),
    partially_approximated_oienv oic oic'
    -> partially_approximated_oival0 (OIV_Closure x e oic) (OIV_Closure x e oic')
| PApprox_oival0_Rec_Closure :
    forall (oic oic':oienv) (f x:identifier) (e:expr),
    partially_approximated_oienv oic oic'
    -> partially_approximated_oival0 (OIV_Rec_Closure f x e oic) (OIV_Rec_Closure f x e oic')


with partially_approximated_oival : oival -> oival -> Prop :=
| PApprox_oival :
    forall (oid oid':oideps) (oiv oiv':oival0),
    partially_approximated_oideps oid oid'
    -> partially_approximated_oival0 oiv oiv'
    -> partially_approximated_oival (OIV_ oid oiv) (OIV_ oid' oiv')

with partially_approximated_oienv : oienv -> oienv -> Prop :=
| PApprox_oienv_empty :
    partially_approximated_oienv OIEnv_empty OIEnv_empty
| PApprox_oienv_cons :
    forall (x:identifier) (oiu oiu':oival) (oic oic':oienv),
    partially_approximated_oival oiu oiu'
    -> partially_approximated_oienv oic oic'
    -> partially_approximated_oienv (OIEnv_cons x oiu oic) (OIEnv_cons x oiu' oic').


Inductive partially_approximated_oitval : oitval -> oitval -> Prop :=
| PApprox_oitval :
    forall (oitd oitd':oitdeps) (oiu oiu':oival),
    partially_approximated_oitdeps oitd oitd'
    -> partially_approximated_oival oiu oiu'
    -> partially_approximated_oitval (OIV oitd oiu) (OIV oitd' oiu').

Inductive partially_approximated_oitenv : oitenv -> oitenv -> Prop :=
| PApprox_oitenv_empty :
    partially_approximated_oitenv OITEnv_empty OITEnv_empty
| PApprox_oitenv_cons :
    forall (x:identifier) (oitu oitu':oitval) (oitc oitc':oitenv),
    partially_approximated_oitval oitu oitu'
    -> partially_approximated_oitenv oitc oitc'
    -> partially_approximated_oitenv (OITEnv_cons x oitu oitc) (OITEnv_cons x oitu' oitc').

(*
TODO: déplacer l'explication hors du code source Coq

explications:
- pa_oid possède 2 cas à cause de la règle Annot (qui ajoute un f non approximé dans d)
- pa_oitd possède 2 cas à cause des 3 deps_spec_... qui propagent l'approx
- 
à part ça, le reste est équivalent à oitval_to_itval_to_oitval

pa_oitd_fun =
| forall vl, tf' vl = true OR tf' vl = tf vl
pa_oitd =
| nil
| cons: tf = pa_oitd_fun, oitd = pa_oitd

pa_oid_fun =
| forall vl, f' vl = dummy_val OR f' vl = f vl
pa_oid =
| nil
| cons: f = pa_oid_fun, oid = pa_oid

pa_oienv =
| empty
| cons: oiu = pa_oival, oic = pa_oienv

pa_oival0 =
| same (num, bool, constr0)
| constr1: u = pa_oival
| closure: c = pa_oienv
| rec: c = pa_oienv
| couple: u1 = pa_oival, u2 = pa_oival

pa_oival =
|d' = pa_oid, v = pa_oival0

pa_oitval =
|td' = pa_oitd, u = pa_oival


à l'endroit où on utilisait le lemme oival_of_in_approximated_oitenv_via_itenv, on avait une évaluation dans un environnement complètement approximé (oitenv_to_itenv_to_oitenv, donc le lemme suivant nous suffirait:
si éval dans env approx donne oitu
alors on a éval dans env qui donne oitu'
      et oitu = partial_approx oitu'
mais la preuve par induction nécessite une hypothèse moins forte:
si éval dans env partial_approx donne oitu
alors on a éval dans env qui donne oitu'
      et oitu = partial_approx oitu'

 *)


(* STRICT FOR OVER-INSTRUMENTED VALUES *)

(* express that oiu2 is a partial approximation of oiu1 *)
Inductive strictly_partially_approximated_oival0 : oival0 -> oival0 -> Prop :=
| SPApprox_oival0_Num :
    forall (n:Z),
    strictly_partially_approximated_oival0 (OIV_Num n) (OIV_Num n)
| SPApprox_oival0_Bool :
    forall (b:bool),
    strictly_partially_approximated_oival0 (OIV_Bool b) (OIV_Bool b)
| SPApprox_oival0_Constr0 :
    forall (n:constr),
    strictly_partially_approximated_oival0 (OIV_Constr0 n) (OIV_Constr0 n)
| SPApprox_oival0_Constr1 :
    forall (oiu oiu':oival) (n:constr),
    strictly_partially_approximated_oival oiu oiu'
    -> strictly_partially_approximated_oival0 (OIV_Constr1 n oiu) (OIV_Constr1 n oiu')
| SPApprox_oival0_Couple :
    forall (oiu1 oiu2 oiu1' oiu2':oival),
    strictly_partially_approximated_oival oiu1 oiu1'
    -> strictly_partially_approximated_oival oiu2 oiu2'
    -> strictly_partially_approximated_oival0 (OIV_Couple oiu1 oiu2) (OIV_Couple oiu1' oiu2')
| SPApprox_oival0_Closure :
    forall (oic oic':oienv) (x:identifier) (e:expr),
    strictly_partially_approximated_oienv oic oic'
    -> strictly_partially_approximated_oival0 (OIV_Closure x e oic) (OIV_Closure x e oic')
| SPApprox_oival0_Rec_Closure :
    forall (oic oic':oienv) (f x:identifier) (e:expr),
    strictly_partially_approximated_oienv oic oic'
    -> strictly_partially_approximated_oival0 (OIV_Rec_Closure f x e oic) (OIV_Rec_Closure f x e oic')


with strictly_partially_approximated_oival : oival -> oival -> Prop :=
| SPApprox_oival :
    forall (oid oid':oideps) (oiv oiv':oival0),
    partially_approximated_oideps oid oid'
    -> strictly_partially_approximated_oival0 oiv oiv'
    -> strictly_partially_approximated_oival (OIV_ oid oiv) (OIV_ oid' oiv')

with strictly_partially_approximated_oienv : oienv -> oienv -> Prop :=
| SPApprox_oienv_empty :
    strictly_partially_approximated_oienv OIEnv_empty OIEnv_empty
| SPApprox_oienv_cons :
    forall (x:identifier) (oiu oiu':oival) (oic oic':oienv),
    strictly_partially_approximated_oival oiu oiu'
    -> strictly_partially_approximated_oienv oic oic'
    -> strictly_partially_approximated_oienv (OIEnv_cons x oiu oic) (OIEnv_cons x oiu' oic').


Inductive strictly_partially_approximated_oitval : oitval -> oitval -> Prop :=
| SPApprox_oitval :
    forall (oitd oitd':oitdeps) (oiu oiu':oival),
    partially_approximated_oitdeps oitd oitd'
    -> strictly_partially_approximated_oival oiu oiu'
    -> strictly_partially_approximated_oitval (OIV oitd oiu) (OIV oitd' oiu').

Inductive strictly_partially_approximated_oitenv : oitenv -> oitenv -> Prop :=
| SPApprox_oitenv_empty :
    strictly_partially_approximated_oitenv OITEnv_empty OITEnv_empty
| SPApprox_oitenv_cons :
    forall (x:identifier) (oitu oitu':oitval) (oitc oitc':oitenv),
    strictly_partially_approximated_oitval oitu oitu'
    -> strictly_partially_approximated_oitenv oitc oitc'
    -> strictly_partially_approximated_oitenv (OITEnv_cons x oitu oitc) (OITEnv_cons x oitu' oitc').


(*** TACTIC ***)

Ltac auto_papprox :=
  match goal with
    | |- partially_approximated_val _ dummy_val => apply PApprox_val_approx; auto_papprox
    | |- partially_approximated_val _ (V_Num 0) => apply PApprox_val_approx; auto_papprox
    | |- partially_approximated_val (V_Num _) _ => apply PApprox_val_Num; auto_papprox
    | |- partially_approximated_val (V_Bool _) _ => apply PApprox_val_Bool; auto_papprox
    | |- partially_approximated_val (V_Constr0 _) _ => apply PApprox_val_Constr0; auto_papprox
    | |- partially_approximated_val (V_Constr1 _ _) _ => apply PApprox_val_Constr1; auto_papprox
    | |- partially_approximated_val (V_Couple _ _) _ => apply PApprox_val_Couple; auto_papprox
    | |- partially_approximated_val (V_Closure _ _ _) _ => apply PApprox_val_Closure; auto_papprox
    | |- partially_approximated_val (V_Rec_Closure _ _ _ _) _ => apply PApprox_val_Rec_Closure; auto_papprox
    | |- partially_approximated_env (Env_empty) _ => apply PApprox_env_empty; auto_papprox
    | |- partially_approximated_env (Env_cons _ _ _) _ => apply PApprox_env_cons; auto_papprox
    | |- partially_approximated_oitdeps nil nil => apply PApprox_oitdeps_empty; auto_papprox
    | |- partially_approximated_oitdeps (cons _ _) _ => apply PApprox_oitdeps_cons; auto_papprox
    | |- partially_approximated_oideps nil nil => apply PApprox_oideps_empty; auto_papprox
    | |- partially_approximated_oideps (cons _ _) _ => apply PApprox_oideps_cons; auto_papprox
    | |- partially_approximated_oitval _ _ => apply PApprox_oitval; auto_papprox
    | |- partially_approximated_oival _ _ => apply PApprox_oival; auto_papprox
    | |- partially_approximated_oival0 _ (OIV_Num 0) => apply PApprox_oival0_approx; auto_papprox
    | |- partially_approximated_oival0 (OIV_Num _) _ => apply PApprox_oival0_Num; auto_papprox
    | |- partially_approximated_oival0 (OIV_Bool _) _ => apply PApprox_oival0_Bool; auto_papprox
    | |- partially_approximated_oival0 (OIV_Constr0 _) _ => apply PApprox_oival0_Constr0; auto_papprox
    | |- partially_approximated_oival0 (OIV_Constr1 _ _) _ => apply PApprox_oival0_Constr1; auto_papprox
    | |- partially_approximated_oival0 (OIV_Couple _ _) _ => apply PApprox_oival0_Couple; auto_papprox
    | |- partially_approximated_oival0 (OIV_Closure _ _ _) _ => apply PApprox_oival0_Closure; auto_papprox
    | |- partially_approximated_oival0 (OIV_Rec_Closure _ _ _ _) _ => apply PApprox_oival0_Rec_Closure; auto_papprox
    | |- partially_approximated_oienv OIEnv_empty OIEnv_empty => apply PApprox_oienv_empty; auto_papprox
    | |- partially_approximated_oienv (OIEnv_cons _ _ _) (OIEnv_cons _ _ _) =>
      apply PApprox_oienv_cons; auto_papprox
    | |- partially_approximated_oitenv OITEnv_empty OITEnv_empty => apply PApprox_oitenv_empty; auto_papprox
    | |- partially_approximated_oitenv (OITEnv_cons _ _ _) (OITEnv_cons _ _ _) =>
      apply PApprox_oitenv_cons; auto_papprox

    | |- strictly_partially_approximated_oitval _ _ => apply SPApprox_oitval; auto_papprox
    | |- strictly_partially_approximated_oival _ _ => apply SPApprox_oival; auto_papprox
    | |- strictly_partially_approximated_oival0 (OIV_Num _) _ => apply SPApprox_oival0_Num; auto_papprox
    | |- strictly_partially_approximated_oival0 (OIV_Bool _) _ => apply SPApprox_oival0_Bool; auto_papprox
    | |- strictly_partially_approximated_oival0 (OIV_Constr0 _) _ => apply SPApprox_oival0_Constr0; auto_papprox
    | |- strictly_partially_approximated_oival0 (OIV_Constr1 _ _) _ => apply SPApprox_oival0_Constr1; auto_papprox
    | |- strictly_partially_approximated_oival0 (OIV_Couple _ _) _ => apply SPApprox_oival0_Couple; auto_papprox
    | |- strictly_partially_approximated_oival0 (OIV_Closure _ _ _) _ => apply SPApprox_oival0_Closure; auto_papprox
    | |- strictly_partially_approximated_oival0 (OIV_Rec_Closure _ _ _ _) _ => apply SPApprox_oival0_Rec_Closure; auto_papprox
    | |- strictly_partially_approximated_oienv OIEnv_empty OIEnv_empty => apply SPApprox_oienv_empty; auto_papprox
    | |- strictly_partially_approximated_oienv (OIEnv_cons _ _ _) (OIEnv_cons _ _ _) =>
      apply SPApprox_oienv_cons; auto_papprox
    | |- strictly_partially_approximated_oitenv OITEnv_empty OITEnv_empty => apply SPApprox_oitenv_empty; auto_papprox
    | |- strictly_partially_approximated_oitenv (OITEnv_cons _ _ _) (OITEnv_cons _ _ _) =>
      apply SPApprox_oitenv_cons; auto_papprox
    | |- _ => auto
  end.






(*** FACTS  ***)

Lemma partially_approximated_val_refl :
  forall v : val, partially_approximated_val v v.
Proof.
  apply (val_ind2
           (fun v => partially_approximated_val v v)
           (fun c => partially_approximated_env c c));
  intros; auto_papprox.
Qed.

Lemma partially_approximated_env_refl :
  forall c : env, partially_approximated_env c c.
Proof.
  apply (env_ind2
           (fun v => partially_approximated_val v v)
           (fun c => partially_approximated_env c c));
  intros; auto_papprox.
Qed.



Lemma partially_approximated_oitdeps_fun_refl :
  forall tf : val->bool, partially_approximated_oitdeps_fun tf tf.
Proof.
  intros tf.
  apply PApprox_oitdeps_fun.
  intros vl.
  right; auto.
Qed.

Lemma partially_approximated_oitdeps_refl :
  forall oitd : oitdeps, partially_approximated_oitdeps oitd oitd.
Proof.
  induction oitd; auto_papprox.
  destruct a as [l f].
  auto_papprox.
  apply partially_approximated_oitdeps_fun_refl.
Qed.

Lemma partially_approximated_oideps_fun_refl :
  forall f : val->val, partially_approximated_oideps_fun f f.
Proof.
  intros f.
  apply PApprox_oideps_fun.
  intros vl.
  apply partially_approximated_val_refl.
Qed.

Lemma partially_approximated_oideps_refl :
  forall oid : oideps, partially_approximated_oideps oid oid.
Proof.
  induction oid; auto_papprox.
  destruct a as [l f].
  auto_papprox.
  apply partially_approximated_oideps_fun_refl.
Qed.

Lemma strictly_partially_approximated_oival_refl :
  forall oiu : oival, strictly_partially_approximated_oival oiu oiu.
Proof.
  apply (oival_ind2
           (fun oiu => strictly_partially_approximated_oival oiu oiu)
           (fun oiv => strictly_partially_approximated_oival0 oiv oiv)
           (fun oic => strictly_partially_approximated_oienv oic oic));
  intros;  auto_papprox.
  apply partially_approximated_oideps_refl.
Qed.

Lemma strictly_partially_approximated_oitenv_refl :
  forall oitc : oitenv, strictly_partially_approximated_oitenv oitc oitc.
Proof.
  apply (oitenv_ind2
           (fun oitu => strictly_partially_approximated_oitval oitu oitu)
           (fun oitc => strictly_partially_approximated_oitenv oitc oitc));
  intros;  auto_papprox.
  apply partially_approximated_oitdeps_refl.
  apply strictly_partially_approximated_oival_refl.
Qed.

(*** FACTS ABOUT INSTANTIATION ***)

Lemma aif_in_partially_approximated_oideps_some :
  forall (oid oid':oideps) (l:label) (vl v':val),
  partially_approximated_oideps oid oid'
  -> apply_impact_fun l vl oid' = Some v'
  -> exists (v:val), apply_impact_fun l vl oid = Some v
    /\ partially_approximated_val v v'.
Proof.
  intros oid oid' l vl v' H H0.
  induction H.

  inversion H0.

  simpl in H0.
  destruct (eq_label_dec l l0) eqn:H_l_l0.

  (* l = l0 *)
  induction H1.
  specialize (H1 vl).
  inversion H1; inversion H0.

  exists (f vl); simpl; rewrite H_l_l0; split; auto_papprox.

  exists (V_Num n); simpl; rewrite H_l_l0, <-H3, <-H4; split; auto_papprox.
  exists (V_Bool b); simpl; rewrite H_l_l0, <-H3, <-H4; split; auto_papprox.
  exists (V_Constr0 n); simpl; rewrite H_l_l0, <-H3, <-H4; split; auto_papprox.
  exists (V_Constr1 n v); simpl; rewrite H_l_l0, <-H2, <-H3; split; auto_papprox.
  exists (V_Couple v1 v2); simpl; rewrite H_l_l0, <-H2, <-H3; split; auto_papprox.
  exists (V_Closure x e0 c); simpl; rewrite H_l_l0, <-H2, <-H3; split; auto_papprox.
  exists (V_Rec_Closure f0 x e0 c); simpl; rewrite H_l_l0, <-H2, <-H3; split; auto_papprox.

  (* l <> l0 *)
  specialize (IHpartially_approximated_oideps H0).
  inversion IHpartially_approximated_oideps as [v HH].
  inversion HH as [H_aif_oid H_papprox_v].
  exists v.
  simpl.
  rewrite H_l_l0.
  split; auto.
Qed.

Lemma aif_in_partially_approximated_oideps_none :
  forall (oid oid':oideps) (l:label) (vl:val),
  partially_approximated_oideps oid oid'
  -> apply_impact_fun l vl oid' = None
  -> apply_impact_fun l vl oid = None.
Proof.
  intros oid oid' l vl H H0.
  induction H; auto.

  simpl; simpl in H0.
  destruct (eq_label_dec l l0).
  inversion H0.
  auto.
Qed.

Lemma atif_in_partially_approximated_oitdeps_some_true :
  forall (oitd oitd':oitdeps) (l:label) (vl:val),
  partially_approximated_oitdeps oitd oitd'
  -> apply_timpact_fun l vl oitd' <> Some true
  -> apply_timpact_fun l vl oitd <> Some true.
Proof.
  intros oitd oitd' l vl H H0.
  induction H; auto.

  simpl; simpl in H0.
  destruct (eq_label_dec l l0).

  inversion H1.
  specialize (H2 vl).
  inversion_clear H2.
  rewrite H5 in H0.
  simpl in H0.
  destruct (apply_timpact_fun l vl oitd'); elim (H0 eq_refl).
  rewrite <-H5.

  assert(HH: apply_timpact_fun l vl oitd' <> Some true).
  intro HH; rewrite HH in H0; simpl in H0; rewrite Bool.orb_true_intro in H0; auto.
  rewrite utils.match_option_bool_not_true2 in H0; auto.
  apply IHpartially_approximated_oitdeps in HH.
  rewrite utils.match_option_bool_not_true2; auto.
  auto.
Qed.

Lemma instantiate_partially_approximated_oival :
  forall (oiu oiu':oival) (l:label) (vl v':val),
  partially_approximated_oival oiu oiu'
  -> instantiate_oival l vl oiu' = Some v'
  -> exists (v:val), instantiate_oival l vl oiu = Some v
                     /\ partially_approximated_val v v'.
Proof.
  apply (oival_ind2
    (fun oiu => forall (oiu':oival) (l:label) (vl v':val),
      partially_approximated_oival oiu oiu'
      -> instantiate_oival l vl oiu' = Some v'
      -> exists (v:val), instantiate_oival l vl oiu = Some v
        /\ partially_approximated_val v v')
    (fun oiv => forall (oiv':oival0) (l:label) (vl v':val),
      partially_approximated_oival0 oiv oiv'
      -> instantiate_oival0 l vl oiv' = Some v'
      -> exists (v:val), instantiate_oival0 l vl oiv = Some v
        /\ partially_approximated_val v v')
    (fun oic => forall (oic':oienv) (l:label) (vl:val) (c':env),
      partially_approximated_oienv oic oic'
      -> instantiate_oienv l vl oic' = Some c'
      -> exists (c:env), instantiate_oienv l vl oic = Some c
        /\ partially_approximated_env c c')).

  (* case oival *)
  intros d vv H oiu' l vl v' H0 H1.
  inversion H0.
  rewrite <-H5 in H1.
  simpl in H1.

  destruct (apply_impact_fun l vl oid') eqn:H_aif_oid'.
  
  (** l is in oid *)
  rewrite H1 in H_aif_oid'; clear H1 v.
  apply aif_in_partially_approximated_oideps_some with (oid:=d) in H_aif_oid'; auto.
  inversion_clear H_aif_oid' as [v HH].
  inversion_clear HH as [H_aif_oid H_papprox_v].
  exists v.
  simpl.
  rewrite H_aif_oid.
  auto.

  (** l is not in oid *)
  apply aif_in_partially_approximated_oideps_none with (oid:=d) in H_aif_oid'; auto.
  rename H_aif_oid' into H_aif_oid.
  specialize(H oiv' l vl v' H6 H1).
  inversion_clear H as [v HH].
  inversion_clear HH as [H_inst_vv H_papprox_v].
  exists v.
  simpl.
  rewrite H_aif_oid.
  auto.

  (* case oival0 Num *)
  intros n oiv' l vl v' H H0.
  inversion H;
    [rewrite <-H2 in H0|rewrite <-H1 in H0];
    inversion H0;
    exists (V_Num n);
    split; auto_papprox.

  (* case oival0 Bool *)
  intros b oiv' l vl v' H H0.
  inversion H;
  [rewrite <-H2 in H0|rewrite <-H1 in H0];
    inversion H0;
    exists (V_Bool b);
    split; auto_papprox.

  (* case oival0 Constr0 *)
  intros n oiv' l vl v' H H0.
  inversion H;
  [rewrite <-H2 in H0|rewrite <-H1 in H0];
    inversion H0;
    exists (V_Constr0 n);
    split; auto_papprox.

  (* case oival0 Constr1 *)
  intros n u H oiv' l vl v' H0 H1.
  inversion H0;
  rewrite <-H3 in H1; simpl in H1.

  destruct (is_instantiable_oival u l vl) as [v0 H_inst_u];
  exists(V_Constr1 n v0);
  simpl; rewrite H_inst_u.
  inversion H1.
  split; simpl; auto_papprox.

  destruct(instantiate_oival l vl oiu') as [v'0|] eqn:H_inst_oiu'; try solve [inversion H1].
  simpl in H1.
  inversion H1.
  specialize(H oiu' l vl v'0 H5 H_inst_oiu').
  inversion_clear H as [v HH].
  inversion_clear HH as [H_inst_u H_papprox_v].
  exists (V_Constr1 n v).
  split; auto_papprox.
  simpl.
  rewrite H_inst_u; auto.

  (* case oival0 Closure *)
  intros x e oic H oiv' l vl v' H0 H1.
  inversion H0;
    rewrite <-H3 in H1; inversion H1.

  destruct (is_instantiable_oienv oic l vl) as [c H_inst_oic];
  exists(V_Closure x e c);
  simpl; rewrite H_inst_oic.
  inversion H1.
  split; simpl; auto_papprox.

  destruct(instantiate_oienv l vl oic') as [c'|] eqn:H_inst_oic'; try solve [inversion H8]; inversion H8.
  specialize(H oic' l vl c' H6 H_inst_oic').
  inversion_clear H as [c HH].
  inversion_clear HH as [H_inst_oic H_papprox_c].
  exists (V_Closure x e c).
  split; auto_papprox.
  simpl.
  rewrite H_inst_oic; auto.

  (* case oival0 Couple *)
  intros u1 H u2 H0 oiv' l vl v' H1 H2.
  inversion H1.

  rewrite <-H4 in H2; simpl in H2.
  destruct (is_instantiable_oival u1 l vl) as [v1 H_inst_u1];
  destruct (is_instantiable_oival u2 l vl) as [v2 H_inst_u2];
  exists(V_Couple v1 v2);
  simpl; rewrite H_inst_u1; rewrite H_inst_u2.
  inversion H2.
  split; simpl; auto_papprox.

  rewrite <-H6 in H2; simpl in H2.
  destruct(instantiate_oival l vl oiu1') as [v'1|] eqn:H_inst_oiu1'; try solve [inversion H2].
  destruct(instantiate_oival l vl oiu2') as [v'2|] eqn:H_inst_oiu2'; try solve [inversion H2].
  inversion_clear H2.
  specialize(H oiu1' l vl v'1 H5 H_inst_oiu1').
  inversion_clear H as [v1 HH].
  inversion_clear HH as [H_inst_u1 H_papprox_v1].
  specialize(H0 oiu2' l vl v'2 H7 H_inst_oiu2').
  inversion_clear H0 as [v2 HH].
  inversion_clear HH as [H_inst_u2 H_papprox_v2].
  exists(V_Couple v1 v2).
  split; auto_papprox.
  simpl; rewrite H_inst_u1, H_inst_u2; auto.

  (* case oival0 Rec_Closure *)
  intros f x e oic H oiv' l vl v' H0 H1.
  inversion H0;
    rewrite <-H3 in H1; inversion H1.

  destruct (is_instantiable_oienv oic l vl) as [c H_inst_oic];
  exists(V_Rec_Closure f x e c);
  simpl; rewrite H_inst_oic.
  inversion H1.
  split; simpl; auto_papprox.

  destruct(instantiate_oienv l vl oic') as [c'|] eqn:H_inst_oic'; try solve [inversion H9]; inversion H9.
  specialize(H oic' l vl c' H7 H_inst_oic').
  inversion_clear H as [c HH].
  inversion_clear HH as [H_inst_oic H_papprox_c].
  exists (V_Rec_Closure f x e c).
  split; auto_papprox.
  simpl.
  rewrite H_inst_oic; auto.

  (* case env empty *)
  intros oic' l vl c' H H0.
  inversion H.
  rewrite <-H2 in H0; inversion H0.
  exists Env_empty; split; auto_papprox.

  (* case env cons *)
  intros x u H oic'0 H0 oic' l vl c'0 H1 H2.
  inversion H1.
  rewrite <-H5 in H2; simpl in H2.
  destruct(instantiate_oival l vl oiu') as [v'|] eqn:H_inst_oiu'; try solve [inversion H2].
  destruct(instantiate_oienv l vl oic'1) as [c'1|] eqn:H_inst_oic'1; try solve [inversion H2]; inversion H2.
  inversion_clear H2.
  specialize(H oiu' l vl v' H7 H_inst_oiu').
  inversion_clear H as [v HH].
  inversion_clear HH as [H_inst_u H_papprox_v].
  specialize(H0 oic'1 l vl c'1 H8 H_inst_oic'1).
  inversion_clear H0 as [c HH].
  inversion_clear HH as [H_inst_oic' H_papprox_c].
  exists (Env_cons x v c).
  split; auto_papprox.
  simpl.
  rewrite H_inst_u, H_inst_oic'; auto.
Qed.


Lemma instantiate_partially_approximated_oitval :
  forall (oitu oitu':oitval) (l:label) (vl v':val),
  partially_approximated_oitval oitu oitu'
  -> instantiate_oitval l vl oitu' = Some v'
  -> exists (v:val), instantiate_oitval l vl oitu = Some v
                     /\ partially_approximated_val v v'.
Proof.
  intros oitu oitu' l vl v' H H0.
  inversion H.
  rewrite <-H4 in H0; simpl in H0.
  assert(HH: apply_timpact_fun l vl oitd' <> Some true); try solve [intro HH; rewrite HH in H0; inversion H0].
  rewrite utils.match_option_bool_not_true in H0; auto.
  destruct(instantiate_partially_approximated_oival oiu oiu' l vl v' H2 H0) as [v].
  inversion H5 as [H_inst_oiu H_papprox_v].
  exists (v).
  split; auto.
  simpl.
  rewrite utils.match_option_bool_not_true; auto.
  apply atif_in_partially_approximated_oitdeps_some_true with (oitd':=oitd'); auto.
Qed.

Lemma instantiate_partially_approximated_oitenv :
  forall (oitc oitc_:oitenv) (l:label) (vl:val) (c_:env),
  partially_approximated_oitenv oitc oitc_
  -> instantiate_oitenv l vl oitc_ = Some c_
  -> exists (c:env), instantiate_oitenv l vl oitc = Some c
                     /\ partially_approximated_env c c_.
Proof.
  intros oitc oitc_ l vl c_ H.
  revert c_.
  induction H; intros c_ H_inst_oitc_.
  exists c_; split; auto.
  apply partially_approximated_env_refl.

  simpl in H_inst_oitc_.
  destruct(instantiate_oitval l vl oitu') as [v'|] eqn:H_inst_oitu'; try solve [inversion H_inst_oitc_].
  destruct(instantiate_oitenv l vl oitc') as [c'|] eqn:H_inst_oitc'; try solve [inversion H_inst_oitc_].
  inversion_clear H_inst_oitc_.
  specialize (IHpartially_approximated_oitenv c' eq_refl).
  inversion_clear IHpartially_approximated_oitenv as [c HH].
  inversion_clear HH as [H_inst_oitc H_papprox_c].
  destruct(instantiate_partially_approximated_oitval _ _ _ _ _ H H_inst_oitu') as [v HH].
  inversion_clear HH as [H_inst_oitu H_papprox_v].  
  exists (Env_cons x v c).
  simpl.
  rewrite H_inst_oitu, H_inst_oitc; simpl.
  split; auto_papprox.
Qed.


(*** FACTS ABOUT CONVERSION ***)

Lemma partially_approximated_val_to_oival :
  forall (v v_:val),
    partially_approximated_val v v_
    -> partially_approximated_oival (val_to_oival v) (val_to_oival v_).
Proof.
  intros v v_ H.

  apply (val_ind2
           (fun v => forall (v_:val), partially_approximated_val v v_
                     -> partially_approximated_oival (val_to_oival v) (val_to_oival v_))
           (fun c => forall (c_:env), partially_approximated_env c c_
                     -> partially_approximated_oienv (env_to_oienv c) (env_to_oienv c_)));
    intros; try inversion H2; try inversion H1; try inversion H0; simpl; auto_papprox.
Qed.

Lemma partially_approximated_val_to_oitval :
  forall (v v_:val),
    partially_approximated_val v v_
    -> partially_approximated_oitval (val_to_oitval v) (val_to_oitval v_).
Proof.
  intros v v_ H.

  unfold val_to_oitval; simpl; auto_papprox.
  apply partially_approximated_val_to_oival; auto.
Qed.

Lemma partially_approximated_env_to_oitenv :
  forall (c c_:env),
    partially_approximated_env c c_
    -> partially_approximated_oitenv (env_to_oitenv c) (env_to_oitenv c_).
Proof.
  intros c c_ H.

  induction H; simpl; auto_papprox.

  apply partially_approximated_val_to_oival; auto.
Qed.

(*** FACTS ABOUT TOTALLY-APPROXIMATED ***)

Lemma approximated_oitval_implies_strictly_partially_approximated :
  forall (oitu oitu':oitval),
    oitu' = itval_to_oitval (oitval_to_itval oitu)
    -> strictly_partially_approximated_oitval oitu oitu'.
Proof.
  intros oitu oitu' H.
  destruct oitu as [oitd oiu].
  destruct oitu' as [oitd' oiu'].
  inversion H.
  apply SPApprox_oitval with (oitd:=oitd) (oitd':=itdeps_to_oitdeps (oitdeps_to_itdeps oitd)) (oiu:=oiu) (oiu':=ival_to_oival (oival_to_ival oiu)); auto.
  
  (* oitdeps *)
  clear dependent oiu'.
  clear dependent oitd'.
  induction oitd.
  apply PApprox_oitdeps_empty.
  destruct a as [l f].
  simpl.
  apply PApprox_oitdeps_cons; auto.
  apply PApprox_oitdeps_fun; auto.

  (* oival *)
  clear dependent oiu'.
  clear dependent oitd'.
  apply (oival_ind2
           (fun oiu => strictly_partially_approximated_oival oiu (ival_to_oival (oival_to_ival oiu)))
           (fun oiv => strictly_partially_approximated_oival0 oiv (ival0_to_oival0 (oival0_to_ival0 oiv)))
           (fun oic => strictly_partially_approximated_oienv oic (ienv_to_oienv (oienv_to_ienv oic))));
    intros; simpl; auto_papprox.

  (* oideps *)
  induction d.
  apply PApprox_oideps_empty.
  destruct a as [l f].
  simpl.
  apply PApprox_oideps_cons; auto.
  apply PApprox_oideps_fun; auto.
  intros vl.
  auto_papprox.
Qed.

Lemma approximated_oitenv_implies_strictly_partially_approximated :
  forall (oitc oitc_:oitenv),
    oitc_ = itenv_to_oitenv (oitenv_to_itenv oitc)
    -> strictly_partially_approximated_oitenv oitc oitc_.
Proof.
  induction oitc; intros oitc_ H.

  inversion H; simpl; auto_papprox.

  simpl in H.
  rewrite H; auto_papprox.
  apply approximated_oitval_implies_strictly_partially_approximated; auto.
Qed.


(*** FACTS ABOUT TOTALLY-APPROXIMATED ***)

Lemma strictly_partially_approximated_oitval_implies_partially_approximated :
  forall (oitu oitu':oitval),
    strictly_partially_approximated_oitval oitu oitu'
    -> partially_approximated_oitval oitu oitu'.
Proof.
  intros oitu oitu' H.

  inversion H; simpl; auto_papprox.

  (* oitval *)
  clear H H0 H2 H3 oitd oitd' oitu oitu'.
  revert oiu' H1.
  apply (oival_ind2
           (fun oiu => forall oiu' : oival, strictly_partially_approximated_oival oiu oiu' ->
                                            partially_approximated_oival oiu oiu')
           (fun oiv => forall oiv' : oival0, strictly_partially_approximated_oival0 oiv oiv' ->
                                            partially_approximated_oival0 oiv oiv')
           (fun oic => forall oic' : oienv, strictly_partially_approximated_oienv oic oic' ->
                                            partially_approximated_oienv oic oic')
        );
    intros;
    try solve [inversion H; auto_papprox];
    try solve [inversion H0; auto_papprox];
    try solve [inversion H1; auto_papprox].
Qed.

Lemma strictly_partially_approximated_oitenv_implies_partially_approximated :
  forall (oitc oitc':oitenv),
    strictly_partially_approximated_oitenv oitc oitc'
    -> partially_approximated_oitenv oitc oitc'.
Proof.
  intros oitc oitc' H.
  induction H; auto_papprox.

  apply strictly_partially_approximated_oitval_implies_partially_approximated; auto.
Qed.

(*** FACTS ABOUT CONCATENATION ***)

Lemma partially_approximated_conc_oitenv :
  forall (oitc1 oitc1_ oitc2 oitc2_:oitenv),
    partially_approximated_oitenv oitc1 oitc1_
    -> partially_approximated_oitenv oitc2 oitc2_
    -> partially_approximated_oitenv (conc_oitenv oitc1 oitc2) (conc_oitenv oitc1_ oitc2_).
Proof.
  induction oitc1; intros oitc1_ oitc2 oitc2_ H H0; simpl.

  inversion H; simpl; auto.

  inversion H; simpl.
  auto_papprox.
Qed.

Lemma strictly_partially_approximated_conc_oitenv :
  forall (oitc1 oitc1_ oitc2 oitc2_:oitenv),
    strictly_partially_approximated_oitenv oitc1 oitc1_
    -> strictly_partially_approximated_oitenv oitc2 oitc2_
    -> strictly_partially_approximated_oitenv (conc_oitenv oitc1 oitc2) (conc_oitenv oitc1_ oitc2_).
Proof.
  induction oitc1; intros oitc1_ oitc2 oitc2_ H H0; simpl.

  inversion H; simpl; auto.

  inversion H; simpl.
  auto_papprox.
Qed.

(*** FACTS ABOUT IS_FILTERED_VAL ***)

Lemma is_filtered_partially_approximated_val :
  forall (c_p_:env) (v v_:val) (p:pattern),
    partially_approximated_val v v_
    -> is_filtered v_ p = Filtered_result_Match c_p_
    -> exists (c_p:env), is_filtered v p = Filtered_result_Match c_p
                              /\ partially_approximated_env c_p c_p_.
Proof.
  intros c_p_ v v_ p H H0.
  destruct v_; destruct p; inversion H0.

  (* case Constr0 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H2.
  inversion H.
  exists Env_empty.
  simpl; rewrite H_n_c.
  split; auto_papprox.

  (* case Constr1 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H2.
  inversion H.
  exists (Env_cons i v0 Env_empty).
  simpl; rewrite H_n_c.
  split; auto_papprox.

  (* case Couple *)
  inversion H.
  exists (Env_cons i v1 (Env_cons i0 v2 Env_empty)); simpl; split; auto_papprox.
Qed.

Lemma is_not_filtered_partially_approximated_val :
  forall (v v_:val) (p:pattern),
    partially_approximated_val v v_
    -> is_filtered v_ p = Filtered_result_Match_var
    -> is_filtered v p = Filtered_result_Match_var.
Proof.
  intros v v_ p H H0.
  destruct v_; destruct p; inversion H0; inversion H; auto.

  (* case Constr0 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H2.
  simpl; rewrite H_n_c; auto.
Qed.

(*** FACTS ABOUT IS_FILTERED_OITVAL ***)

Lemma is_filtered_strictly_partially_approximated_oitval :
  forall (c_p_:oitenv) (oitu oitu_:oitval) (p:pattern),
    strictly_partially_approximated_oitval oitu oitu_
    -> is_filtered_oitval oitu_ p = Filtered_oitval_result_Match c_p_
    -> exists (c_p:oitenv), is_filtered_oitval oitu p = Filtered_oitval_result_Match c_p
                              /\ strictly_partially_approximated_oitenv c_p c_p_.
Proof.
  intros c_p_ oitu oitu_ p H H0.
  inversion H.
  inversion H2.
  destruct oiv'; destruct p;
  rewrite <-H4, <-H8 in H0; inversion H0.

  (* case Constr0 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H10.
  inversion H6.
  exists OITEnv_empty.
  simpl; rewrite H_n_c.
  split; auto_papprox.

  (* case Constr1 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H10.
  inversion H6.
  exists (OITEnv_cons i (OIV nil oiu0) OITEnv_empty).
  simpl; rewrite H_n_c.
  split; auto_papprox.

  (* case Couple *)
  inversion H6.
  exists (OITEnv_cons i (OIV nil oiu1) (OITEnv_cons i0 (OIV nil oiu2) OITEnv_empty)); simpl; split; auto_papprox.
Qed.

Lemma is_not_filtered_strictly_partially_approximated_oitval :
  forall (oitu oitu_:oitval) (p:pattern),
    strictly_partially_approximated_oitval oitu oitu_
    -> is_filtered_oitval oitu_ p = Filtered_oitval_result_Match_var
    -> is_filtered_oitval oitu p = Filtered_oitval_result_Match_var.
Proof.
  intros oitu oitu_ p H H0.
  inversion H.
  inversion H2.
  destruct oiv'; destruct p;
  rewrite <-H4, <-H8 in H0; inversion H0;
  inversion H6; auto.

  (* case Constr0 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H10.
  simpl; rewrite H_n_c; auto.
Qed.

(*** FACTS ABOUT ASSOC_IN_OITENV ***)

Lemma assoc_in_partially_approximated_oitenv :
  forall (oitc oitc_:oitenv) (oitu_:oitval) (x:identifier),
    partially_approximated_oitenv oitc oitc_
    -> assoc_ident_in_oitenv x oitc_ = Ident_in_oitenv oitu_
    -> exists (oitu:oitval), assoc_ident_in_oitenv x oitc = Ident_in_oitenv oitu
                             /\ partially_approximated_oitval oitu oitu_.
Proof.
  intros oitc oitc_ oitu_ x H.
  induction H; intros H_assoc_in_oitc_; inversion H_assoc_in_oitc_.

  destruct (beq_identifier x x0) eqn:H_x_x0; inversion H2.

  exists oitu.
  simpl.
  rewrite H_x_x0, <-H3; auto.

  specialize (IHpartially_approximated_oitenv H2).
  inversion_clear IHpartially_approximated_oitenv as [oitu0 HH].
  inversion_clear HH.
  exists oitu0.
  simpl.
  rewrite H_x_x0; auto.
Qed.
