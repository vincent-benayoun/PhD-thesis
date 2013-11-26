Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Require Import over_instrumented_values.
Require Import oitval_instantiation.
Require Import oitval_val_conversion.
Require Import oitval_val_conversion_facts.


Require Import ldna_in.

(*----- IMPACT FUNCTIONS (oitdeps and oideps) -----*)

Lemma ldna_in_oitdeps_apply_timpact_fun :
  forall (l:label) (td:oitdeps),
  label_does_not_appear_in_oitdeps l td
  -> forall (vl:val), apply_timpact_fun l vl td = None.
Proof.
  intros l td H vl.
  induction H.
  auto.
  simpl.
  induction eq_label_dec.
  absurd(l = l'); assumption.
  assumption.
Qed.

Lemma ldna_in_oideps_apply_impact_fun :
  forall (l:label) (d:oideps),
  label_does_not_appear_in_oideps l d
  -> forall (vl:val), apply_impact_fun l vl d = None.
Proof.
  intros l d H vl.
  induction H.
  auto.
  simpl.
  induction eq_label_dec.
  absurd(l = l'); assumption.
  assumption.
Qed.

(*----- INSTANTIATION -----*)

Lemma instantiate_oitval_when_ldna_in_oitval :
  forall (vl:val) (l:label) (uu:oitval),
  label_does_not_appear_in_oitval l uu
  -> instantiate_oitval l vl uu = Some (oitval_to_val uu).
Proof.
  intro vl.
  apply (ldna_in_oitval_ind2
    (fun l uu P => instantiate_oitval l vl uu = Some (oitval_to_val uu))
    (fun l u P => instantiate_oival l vl u = Some (oival_to_val u))
    (fun l v P => instantiate_oival0 l vl v = Some (oival0_to_val v))
    (fun l c P => instantiate_oienv l vl c = Some (oienv_to_env c))
    (fun l c P => True)
    (fun l c u P => True)); intros; simpl;
  auto; try (f_equal; assumption).

  assert(HH : apply_timpact_fun l vl td = None);
    [apply ldna_in_oitdeps_apply_timpact_fun; assumption
      | rewrite HH]; assumption.

  assert(HH : apply_impact_fun l vl d = None);
    [apply ldna_in_oideps_apply_impact_fun; assumption
      | rewrite HH]; assumption.

  unfold option_map; rewrite H; reflexivity.
  unfold option_map; rewrite H; reflexivity.
  unfold option_map; rewrite H; reflexivity.
  unfold option_map2; rewrite H; rewrite H0; reflexivity.
  unfold option_map2; rewrite H; rewrite H0; reflexivity.
Qed.


Lemma instantiate_oitenv_when_ldna_in_oitenv :
  forall (vl:val) (l:label) (c:oitenv),
  label_does_not_appear_in_oitenv l c
  -> instantiate_oitenv l vl c = Some (oitenv_to_env c).
Proof.
  intro vl.
  apply (ldna_in_oitenv_ind2
    (fun l uu P => instantiate_oitval l vl uu = Some (oitval_to_val uu))
    (fun l u P => instantiate_oival l vl u = Some (oival_to_val u))
    (fun l v P => instantiate_oival0 l vl v = Some (oival0_to_val v))
    (fun l c P => instantiate_oienv l vl c = Some (oienv_to_env c))
    (fun l c P => instantiate_oitenv l vl c = Some (oitenv_to_env c))
    (fun l c u P => True)); intros; simpl;
  auto; try (f_equal; assumption).

  assert(HH : apply_timpact_fun l vl td = None);
    [apply ldna_in_oitdeps_apply_timpact_fun; assumption
      | rewrite HH]; assumption.

  assert(HH : apply_impact_fun l vl d = None);
    [apply ldna_in_oideps_apply_impact_fun; assumption
      | rewrite HH]; assumption.

  unfold option_map; rewrite H; reflexivity.
  unfold option_map; rewrite H; reflexivity.
  unfold option_map; rewrite H; reflexivity.
  unfold option_map2; rewrite H; rewrite H0; reflexivity.
  unfold option_map2; rewrite H; rewrite H0; reflexivity.
  unfold option_map2; rewrite H; rewrite H0; reflexivity.
Qed.


(*----- CONVERSION -----*)

Lemma ldna_in_oitenv_implies_ldna_in_oienv :
  forall (c:env) (l:label),
    label_does_not_appear_in_oitenv l (env_to_oitenv c)
    -> label_does_not_appear_in_oienv l (env_to_oienv c).
Proof.
  intros c l.
  apply (env_ind2
    (fun v => label_does_not_appear_in_oitval l (val_to_oitval v)
      -> label_does_not_appear_in_oival l (val_to_oival v))
    (fun c => label_does_not_appear_in_oitenv l (env_to_oitenv c)
      -> label_does_not_appear_in_oienv l (env_to_oienv c)));
  try solve [intros n H; inversion H;
    simpl; auto with ldna_oival].

  intros n v IH1 H.
  simpl; inversion H; assumption.

  intros v1 IH1 v2 IH2 H.
  simpl; inversion H; assumption.

  intros x e c0 IH H.
  simpl; inversion H; assumption.

  intros f x e c0 IH H.
  simpl; inversion H; assumption.

  auto with ldna_oienv.

  intros x v IH1 c' IH2 H.
  simpl; inversion H.
  apply IH1 in H5.
  apply IH2 in H3.
  apply Ldna_in_oienv_cons; assumption.
Qed.
  

Lemma ldna_in_val_to_oival :
  forall (l:label) (v:val),
  label_does_not_appear_in_val l v
  -> label_does_not_appear_in_oival l (val_to_oival v).
Proof.
  apply (ldna_in_val_ind2
    (fun l v P => label_does_not_appear_in_oival l (val_to_oival v))
    (fun l c P => label_does_not_appear_in_oienv l (env_to_oienv c)))
  ; intros; simpl;
    (apply Ldna_in_oival; try apply Ldna_in_oideps_empty; auto with ldna_oival0)
    || auto with ldna_oienv.

  apply Ldna_in_oival0_Closure.
  assumption.
  rewrite oienv_to_oitenv_env_to_oienv; assumption.
  apply Ldna_in_oival0_Rec_Closure.
  assumption.
  rewrite oienv_to_oitenv_env_to_oienv; assumption.
Qed.


Lemma ldna_in_val_to_oitval :
  forall (l:label) (v:val),
  label_does_not_appear_in_val l v
  -> label_does_not_appear_in_oitval l (val_to_oitval v).
Proof.
  intros l v H.
  unfold val_to_oitval.
  apply Ldna_in_oitval.
  auto with ldna_oitdeps.
  apply ldna_in_val_to_oival.
  assumption.
Qed.


Lemma reverse_ldna_in_val_to_oival :
  forall (l:label) (v:val),
  label_does_not_appear_in_oival l (val_to_oival v)
  -> label_does_not_appear_in_val l v.
Proof.
  intros l.
  apply (val_ind2
    (fun v => label_does_not_appear_in_oival l (val_to_oival v)
      -> label_does_not_appear_in_val l v)
    (fun c => label_does_not_appear_in_oienv l (env_to_oienv c)
      -> label_does_not_appear_in_env l c)).

  auto with ldna_val.
  auto with ldna_val.
  auto with ldna_val.

  intros n v H H0.
  apply Ldna_in_val_Constr1.
  apply H.
  inversion H0.
  inversion H5.
  assumption.

  intros v1 H v2 H0 H1.
  inversion H1; inversion H6.
  apply Ldna_in_val_Couple.
  apply H; assumption.
  apply H0; assumption.
  
  intros x e c H H0.
  inversion H0; inversion H5.
  apply Ldna_in_val_Closure.
  apply H.
  assumption.
  rewrite <- oienv_to_oitenv_env_to_oienv.
  assumption.

  intros f x e c H H0.
  inversion H0; inversion H5.
  apply Ldna_in_val_Rec_Closure.
  apply H.
  assumption.
  rewrite <- oienv_to_oitenv_env_to_oienv.
  assumption.

  auto with ldna_env.

  intros x v H c' H0 H1.
  inversion H1.
  apply H0 in H5.
  apply H in H7.
  apply Ldna_in_env_cons; assumption.
Qed.

  

Lemma ldna_in_env_to_oitenv :
  forall (l:label) (c:env),
  label_does_not_appear_in_env l c
  -> label_does_not_appear_in_oitenv l (env_to_oitenv c).
Proof.
  apply (ldna_in_env_ind2
    (fun l v P => label_does_not_appear_in_oival l (val_to_oival v))
    (fun l c P => label_does_not_appear_in_oitenv l (env_to_oitenv c)))
  ; intros; simpl;
    try (apply Ldna_in_oival; try apply Ldna_in_oideps_empty; auto with ldna_oival0).

  apply Ldna_in_oival0_Closure.
  induction c.
  auto with ldna_oienv.
  apply ldna_in_oitenv_implies_ldna_in_oienv; assumption.
  rewrite oienv_to_oitenv_env_to_oienv.
  assumption.

  apply Ldna_in_oival0_Rec_Closure.
  induction c.
  auto with ldna_oienv.
  apply ldna_in_oitenv_implies_ldna_in_oienv; assumption.
  rewrite oienv_to_oitenv_env_to_oienv.
  assumption.

  auto with ldna_oitenv.

  apply Ldna_in_oitenv_cons. assumption.
  apply ldna_in_val_to_oitval.
  assumption.
Qed.

Lemma ldna_in_env_to_oienv :
  forall (l:label) (c:env),
  label_does_not_appear_in_env l c
  -> label_does_not_appear_in_oienv l (env_to_oienv c).
Proof.
  apply (ldna_in_env_ind2
    (fun l v P => label_does_not_appear_in_oival l (val_to_oival v))
    (fun l c P => label_does_not_appear_in_oienv l (env_to_oienv c)))
  ; intros; simpl;
    try (apply Ldna_in_oival; try apply Ldna_in_oideps_empty; auto with ldna_oival0).

  apply Ldna_in_oival0_Closure.
  induction c.
  auto with ldna_oienv.
  simpl.
  inversion H.
  apply Ldna_in_oienv_cons; assumption.
  rewrite oienv_to_oitenv_env_to_oienv.
  assumption.

  apply Ldna_in_oival0_Rec_Closure.
  induction c.
  auto with ldna_oienv.
  simpl.
  inversion H.
  apply Ldna_in_oienv_cons; assumption.
  rewrite oienv_to_oitenv_env_to_oienv.
  assumption.

  auto with ldna_oienv.

  apply Ldna_in_oienv_cons. assumption.
  apply ldna_in_val_to_oival.
  assumption.
Qed.

(*----- ENVIRONMENT (cons and conc) -----*)


Lemma ldna_in_expr_env_cons :
  forall (l:label) (c:oitenv) (e:expr) (uu:oitval) (x:identifier),
  label_does_not_appear_in_expr l c e
  -> label_does_not_appear_in_oitval l uu
  -> label_does_not_appear_in_expr l (OITEnv_cons x uu c) e.
Proof.
  induction 1; intros; auto with ldna_expr.
  
  assert(beq_identifier x0 x = true \/ beq_identifier x0 x = false).
  induction beq_identifier; auto.
  inversion H2.
  apply Ldna_in_expr_Var with (uu:=uu).
  simpl.
  rewrite H3; auto.
  assumption.
  apply Ldna_in_expr_Var with (uu:=uu0).
  simpl.
  rewrite H3; auto.
  assumption.

  assert(beq_identifier x0 x = true \/ beq_identifier x0 x = false).
  induction beq_identifier; auto.
  inversion H1.
  apply Ldna_in_expr_Var with (uu:=uu).
  simpl.
  rewrite H2; auto.
  assumption.
  apply Ldna_in_expr_Var2.
  simpl.
  rewrite H2; auto.

  apply Ldna_in_expr_Lambda.
  apply Ldna_in_oitenv_cons; assumption.
  apply IHlabel_does_not_appear_in_expr; assumption.

  apply Ldna_in_expr_Rec.
  apply Ldna_in_oitenv_cons; assumption.
  apply IHlabel_does_not_appear_in_expr; assumption.
Qed.

Lemma ldna_in_expr_env_conc :
  forall (l:label) (c:env) (c':oitenv) (e:expr),
  label_does_not_appear_in_expr l c' e
  -> label_does_not_appear_in_env l c
  -> label_does_not_appear_in_expr l (conc_oitenv (env_to_oitenv c) c') e.
Proof.
  induction c.
  auto.
  simpl.
  intros c' e H H0.
  apply ldna_in_expr_env_cons.
  apply IHc.
  assumption.
  inversion H0.
  assumption.
  inversion H0.
  apply ldna_in_val_to_oitval.
  assumption.
Qed.
