Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Require Import over_instrumented_values.
Require Import oitval_instantiation.


Lemma is_instantiable_oival :
  forall (u:oival) (l:label) (vl:val),
    exists (v':val), instantiate_oival l vl u = Some v'.
Proof.
  intros u l vl.
  apply (oival_ind2
    (fun u => exists (v':val), instantiate_oival l vl u = Some v')
    (fun v => exists (v':val), instantiate_oival0 l vl v = Some v')
    (fun c => exists (c':env), instantiate_oienv l vl c = Some c'));
  intros; simpl; eauto.

  induction (apply_impact_fun l vl d).
  exists a; reflexivity.
  assumption.

  unfold option_map.
  inversion H.
  rewrite H0.
  eauto.

  unfold option_map.
  inversion H.
  rewrite H0.
  eauto.

  unfold option_map2.
  inversion H.
  inversion H0.
  rewrite H1.
  rewrite H2.
  eauto.

  unfold option_map.
  inversion H.
  rewrite H0.
  eauto.

  unfold option_map2.
  inversion H.
  inversion H0.
  rewrite H1.
  rewrite H2.
  eauto.
Qed.

Lemma is_instantiable_oitval :
  forall (uu:oitval) (td:oitdeps) (u:oival) (l:label) (vl:val),
    uu = OIV td u
    -> apply_timpact_fun l vl td <> Some true
    -> exists (v':val), instantiate_oitval l vl uu = Some v'.
Proof.
  intros uu td u l vl H H0.
  rewrite H; simpl.
  
  induction (apply_timpact_fun l vl td).
  induction a.
  elim (H0 eq_refl).
  apply is_instantiable_oival.
  apply is_instantiable_oival.
Qed.

Lemma is_instantiable_oienv :
  forall (c:oienv) (l:label) (vl:val),
    exists (c':env), instantiate_oienv l vl c = Some c'.
Proof.
  intros u l vl.
  apply (oienv_ind2
    (fun u => exists (v':val), instantiate_oival l vl u = Some v')
    (fun v => exists (v':val), instantiate_oival0 l vl v = Some v')
    (fun c => exists (c':env), instantiate_oienv l vl c = Some c'));
  intros; simpl; eauto.

  induction (apply_impact_fun l vl d).
  exists a; reflexivity.
  assumption.

  unfold option_map.
  inversion H.
  rewrite H0.
  eauto.

  unfold option_map.
  inversion H.
  rewrite H0.
  eauto.

  unfold option_map2.
  inversion H.
  inversion H0.
  rewrite H1.
  rewrite H2.
  eauto.

  unfold option_map.
  inversion H.
  rewrite H0.
  eauto.

  unfold option_map2.
  inversion H.
  inversion H0.
  rewrite H1.
  rewrite H2.
  eauto.
Qed.