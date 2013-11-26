Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Require Import over_instrumented_values.
Require Import oitval_instantiation.
Require Import oitval_val_conversion.
Require Import oitval_val_conversion_facts.

Require Import ldna_in.
Require Import ldna_in_facts.


Lemma ldna_in_instantiate_oitval :
  forall (vl:val) (l:label) (uu:oitval),
    label_does_not_appear_in_oitval l uu
    -> forall (v:val), Some v = instantiate_oitval l vl uu
      -> label_does_not_appear_in_val l v.
Proof.
  intro vl.
  apply (ldna_in_oitval_ind2
    (fun l uu P =>
      forall (v:val), Some v = instantiate_oitval l vl uu
        -> label_does_not_appear_in_val l v)
    (fun l u P =>
      forall (v:val), Some v = instantiate_oival l vl u
        -> label_does_not_appear_in_val l v)
    (fun l v_u P =>
      forall (v:val), Some v = instantiate_oival0 l vl v_u
        -> label_does_not_appear_in_val l v)
    (fun l c P =>
      forall (c':env), Some c' = instantiate_oienv l vl c
        -> label_does_not_appear_in_env l c')
    (fun l c P =>
      forall (c':env), Some c' = instantiate_oitenv l vl c
        -> label_does_not_appear_in_env l c')
    (fun l c e P =>
      forall (c':env), Some c' = instantiate_oitenv l vl c
        -> label_does_not_appear_in_expr l (env_to_oitenv c') e))
  ; intros; simpl; try inversion H; try repeat (auto with ldna_val ldna_env ldna_expr).

  simpl in H0.
  assert(H_apply_timpact_fun := ldna_in_oitdeps_apply_timpact_fun _ _ l0 vl).
  rewrite H_apply_timpact_fun in H0.
  apply H; assumption.

  simpl in H0.
  assert(H_apply_impact_fun := ldna_in_oideps_apply_impact_fun _ _ l0 vl).
  rewrite H_apply_impact_fun in H0.
  apply H; assumption.

  simpl in H0.
  unfold option_map in H0.
  induction (instantiate_oival l vl u); inversion H0.
  auto with ldna_val.

  simpl in H1.
  unfold option_map in H1.
  induction (instantiate_oienv l vl c) eqn:HH; inversion H1.
  apply Ldna_in_val_Closure.
  apply H; reflexivity.
  apply H0.
  rewrite <- HH.
  apply instantiate_oienv_to_oitenv.
  
  simpl in H1.
  unfold option_map in H1.
  induction (instantiate_oienv l vl c) eqn:HH; inversion H1.
  apply Ldna_in_val_Rec_Closure.
  apply H; reflexivity.
  apply H0.
  rewrite <- HH.
  apply instantiate_oienv_to_oitenv.

  simpl in H1.
  unfold option_map2 in H1.
  induction (instantiate_oival l vl u1); inversion H1.
  induction (instantiate_oival l vl u2); inversion H1.
  auto with ldna_val.

  simpl in H1.
  unfold option_map2 in H1.
  induction (instantiate_oival l vl u); inversion H1.
  induction (instantiate_oienv l vl c); inversion H1.
  auto with ldna_env.

  simpl in H1.
  unfold option_map2 in H1.
  induction (instantiate_oitval l vl uu); inversion H1.
  induction (instantiate_oitenv l vl c); inversion H1.
  auto with ldna_env.

  assert (HH:=assoc_ident_in_oitenv_env_to_oitenv_instantiate_oitenv _ _ _ _ e _ _ H0).
  inversion HH.
  inversion H1.
  apply Ldna_in_expr_Var with (uu:=(val_to_oitval x0)).
  assumption.
  apply ldna_in_val_to_oitval.
  apply H; assumption.

  apply Ldna_in_expr_Var2.
  apply assoc_ident_not_in_oitenv_env_to_oitenv_instantiate_oitenv with (c:=c) (l:=l) (vl:=vl); assumption.

  apply Ldna_in_expr_Lambda.
  apply ldna_in_env_to_oitenv; auto.
  auto.

  apply Ldna_in_expr_Rec.
  apply ldna_in_env_to_oitenv; auto.
  auto.
Qed.

Lemma ldna_in_instantiate_oitenv :
  forall (vl:val) (l:label) (c:oitenv),
    label_does_not_appear_in_oitenv l c
    -> forall (c':env), Some c' = instantiate_oitenv l vl c
      -> label_does_not_appear_in_env l c'.
Proof.
  intro vl.
  apply (ldna_in_oitenv_ind2
    (fun l uu P =>
      forall (v:val), Some v = instantiate_oitval l vl uu
        -> label_does_not_appear_in_val l v)
    (fun l u P =>
      forall (v:val), Some v = instantiate_oival l vl u
        -> label_does_not_appear_in_val l v)
    (fun l v_u P =>
      forall (v:val), Some v = instantiate_oival0 l vl v_u
        -> label_does_not_appear_in_val l v)
    (fun l c P =>
      forall (c':env), Some c' = instantiate_oienv l vl c
        -> label_does_not_appear_in_env l c')
    (fun l c P =>
      forall (c':env), Some c' = instantiate_oitenv l vl c
        -> label_does_not_appear_in_env l c')
    (fun l c e P =>
      forall (c':env), Some c' = instantiate_oitenv l vl c
        -> label_does_not_appear_in_expr l (env_to_oitenv c') e))
  ; intros; simpl; try inversion H; try repeat (auto with ldna_val ldna_env ldna_expr).

  simpl in H0.
  assert(H_apply_timpact_fun := ldna_in_oitdeps_apply_timpact_fun _ _ l0 vl).
  rewrite H_apply_timpact_fun in H0.
  apply H; assumption.

  simpl in H0.
  assert(H_apply_impact_fun := ldna_in_oideps_apply_impact_fun _ _ l0 vl).
  rewrite H_apply_impact_fun in H0.
  apply H; assumption.

  simpl in H0.
  unfold option_map in H0.
  induction (instantiate_oival l vl u); inversion H0.
  auto with ldna_val.

  simpl in H1.
  unfold option_map in H1.
  induction (instantiate_oienv l vl c) eqn:HH; inversion H1.
  apply Ldna_in_val_Closure.
  apply H; reflexivity.
  apply H0.
  rewrite <- HH.
  apply instantiate_oienv_to_oitenv.
  
  simpl in H1.
  unfold option_map in H1.
  induction (instantiate_oienv l vl c) eqn:HH; inversion H1.
  apply Ldna_in_val_Rec_Closure.
  apply H; reflexivity.
  apply H0.
  rewrite <- HH.
  apply instantiate_oienv_to_oitenv.

  simpl in H1.
  unfold option_map2 in H1.
  induction (instantiate_oival l vl u1); inversion H1.
  induction (instantiate_oival l vl u2); inversion H1.
  auto with ldna_val.

  simpl in H1.
  unfold option_map2 in H1.
  induction (instantiate_oival l vl u); inversion H1.
  induction (instantiate_oienv l vl c); inversion H1.
  auto with ldna_env.

  simpl in H1.
  unfold option_map2 in H1.
  induction (instantiate_oitval l vl uu); inversion H1.
  induction (instantiate_oitenv l vl c); inversion H1.
  auto with ldna_env.

  assert (HH:=assoc_ident_in_oitenv_env_to_oitenv_instantiate_oitenv _ _ _ _ e _ _ H0).
  inversion HH.
  inversion H1.
  apply Ldna_in_expr_Var with (uu:=(val_to_oitval x0)).
  assumption.
  apply ldna_in_val_to_oitval.
  apply H; assumption.

  apply Ldna_in_expr_Var2.
  apply assoc_ident_not_in_oitenv_env_to_oitenv_instantiate_oitenv with (c:=c) (l:=l) (vl:=vl); assumption.

  apply Ldna_in_expr_Lambda.
  apply ldna_in_env_to_oitenv; auto.
  auto.

  apply Ldna_in_expr_Rec.
  apply ldna_in_env_to_oitenv; auto.
  auto.
Qed.

Lemma ldna_in_expr_env_to_oitenv_instantiate :
  forall (vl:val) (l:label) (c:oitenv) (e:expr),
    label_does_not_appear_in_expr l c e
    -> forall (c':env), Some c' = instantiate_oitenv l vl c
      -> label_does_not_appear_in_expr l (env_to_oitenv c') e.
Proof.
  intro vl.
  apply (ldna_in_expr_ind2
    (fun l uu P =>
      forall (v:val), Some v = instantiate_oitval l vl uu
        -> label_does_not_appear_in_val l v)
    (fun l u P =>
      forall (v:val), Some v = instantiate_oival l vl u
        -> label_does_not_appear_in_val l v)
    (fun l v_u P =>
      forall (v:val), Some v = instantiate_oival0 l vl v_u
        -> label_does_not_appear_in_val l v)
    (fun l c P =>
      forall (c':env), Some c' = instantiate_oienv l vl c
        -> label_does_not_appear_in_env l c')
    (fun l c P =>
      forall (c':env), Some c' = instantiate_oitenv l vl c
        -> label_does_not_appear_in_env l c')
    (fun l c e P =>
      forall (c':env), Some c' = instantiate_oitenv l vl c
        -> label_does_not_appear_in_expr l (env_to_oitenv c') e))
  ; intros; simpl; try inversion H; try repeat (auto with ldna_val ldna_env ldna_expr).

  simpl in H0.
  assert(H_apply_timpact_fun := ldna_in_oitdeps_apply_timpact_fun _ _ l0 vl).
  rewrite H_apply_timpact_fun in H0.
  apply H; assumption.

  simpl in H0.
  assert(H_apply_impact_fun := ldna_in_oideps_apply_impact_fun _ _ l0 vl).
  rewrite H_apply_impact_fun in H0.
  apply H; assumption.

  simpl in H0.
  unfold option_map in H0.
  induction (instantiate_oival l vl u); inversion H0.
  auto with ldna_val.

  simpl in H1.
  unfold option_map in H1.
  induction (instantiate_oienv l vl c) eqn:HH; inversion H1.
  apply Ldna_in_val_Closure.
  apply H; reflexivity.
  apply H0.
  rewrite <- HH.
  apply instantiate_oienv_to_oitenv.
  
  simpl in H1.
  unfold option_map in H1.
  induction (instantiate_oienv l vl c) eqn:HH; inversion H1.
  apply Ldna_in_val_Rec_Closure.
  apply H; reflexivity.
  apply H0.
  rewrite <- HH.
  apply instantiate_oienv_to_oitenv.

  simpl in H1.
  unfold option_map2 in H1.
  induction (instantiate_oival l vl u1); inversion H1.
  induction (instantiate_oival l vl u2); inversion H1.
  auto with ldna_val.

  simpl in H1.
  unfold option_map2 in H1.
  induction (instantiate_oival l vl u); inversion H1.
  induction (instantiate_oienv l vl c); inversion H1.
  auto with ldna_env.

  simpl in H1.
  unfold option_map2 in H1.
  induction (instantiate_oitval l vl uu); inversion H1.
  induction (instantiate_oitenv l vl c); inversion H1.
  auto with ldna_env.

  assert (HH:=assoc_ident_in_oitenv_env_to_oitenv_instantiate_oitenv _ _ _ _ e _ _ H0).
  inversion HH.
  inversion H1.
  apply Ldna_in_expr_Var with (uu:=(val_to_oitval x0)).
  assumption.
  apply ldna_in_val_to_oitval.
  apply H; assumption.

  apply Ldna_in_expr_Var2.
  apply assoc_ident_not_in_oitenv_env_to_oitenv_instantiate_oitenv with (c:=c) (l:=l) (vl:=vl); assumption.

  apply Ldna_in_expr_Lambda.
  apply ldna_in_env_to_oitenv; auto.
  auto.

  apply Ldna_in_expr_Rec.
  apply ldna_in_env_to_oitenv; auto.
  auto.
Qed.
