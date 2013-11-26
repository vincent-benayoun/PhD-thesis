Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import over_instrumented_values.
Require Import oitval_instantiation.
Require Import oitval_val_conversion.
Require Import oitval_val_conversion_facts.
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

(* pour Lemma exists_deps_spec_Apply *)
Require Import oival_of_correctness.

Require Import partially_approximated.
Require Import oival_of_in_partially_approximated_oitenv.

Require Import ldna_in_itval.
      


Lemma oienv_to_itenv_via_ienv_or_via_oitenv :
  forall (oic:oienv),
    ienv_to_itenv (oienv_to_ienv oic) = oitenv_to_itenv (oienv_to_oitenv oic).
Proof.
  intros oic.
  induction oic.
  auto.
  simpl.
  f_equal.
  assumption.
Qed.  

Lemma itdeps_to_oitdeps_to_itdeps :
  forall (itd:itdeps), oitdeps_to_itdeps (itdeps_to_oitdeps itd) = itd.
Proof.
  intros itd.
  induction itd.
  auto.
  simpl.
  f_equal.
  assumption.
Qed.
  
Lemma ideps_to_oideps_to_ideps :
  forall (id:ideps), oideps_to_ideps (ideps_to_oideps id) = id.
Proof.
  intros id.
  induction id.
  auto.
  simpl.
  f_equal.
  assumption.
Qed.

Lemma partially_approximated_oitdeps_to_itdeps :
  forall (oitd oitd_:oitdeps),
    partially_approximated_oitdeps oitd oitd_
    -> oitdeps_to_itdeps oitd = oitdeps_to_itdeps oitd_.
Proof.
  intros oitd oitd_ H.
  induction H; auto.

  simpl; f_equal; auto.
Qed.

Lemma partially_approximated_oideps_to_ideps :
  forall (oid oid_:oideps),
    partially_approximated_oideps oid oid_
    -> oideps_to_ideps oid = oideps_to_ideps oid_.
Proof.
  intros oid oid_ H.
  induction H; auto.

  simpl; f_equal; auto.
Qed.

  

Lemma assoc_ident_not_in_approximated_oitenv_via_itenv :
  forall (x:identifier) (oitc:oitenv),
  assoc_ident_in_oitenv x (itenv_to_oitenv (oitenv_to_itenv oitc)) = Ident_not_in_oitenv
  -> assoc_ident_in_oitenv x oitc = Ident_not_in_oitenv.
Proof.
  intros x oitc H.
  induction oitc; auto.
  simpl.
  simpl in H.
  destruct (beq_identifier x x0).
  inversion H.
  auto.
Qed.

Lemma assoc_ident_in_approximated_oitenv_via_itenv :
  forall (x:identifier) (oitc:oitenv) (oitu:oitval),
  assoc_ident_in_oitenv x (itenv_to_oitenv (oitenv_to_itenv oitc)) = Ident_in_oitenv oitu
  -> exists (oitu':oitval),
       assoc_ident_in_oitenv x oitc = Ident_in_oitenv oitu'
       /\ oitu = itval_to_oitval (oitval_to_itval oitu').
Proof.
  intros x oitc oitu H.
  induction oitc.
  inversion H.
  
  simpl; simpl in H.
  destruct (beq_identifier x x0).
  (* case x = x0 *)
  exists uu.
  split; auto.
  inversion H.
  reflexivity.

  (* case x <> x0 *)
  auto.
Qed.


Lemma oienv_to_oitenv_via_ienv_to_oienv_or_via_oitenv_to_itenv :
  forall (oic:oienv),
    (oienv_to_oitenv (ienv_to_oienv (oienv_to_ienv oic)))
    = itenv_to_oitenv (oitenv_to_itenv (oienv_to_oitenv oic)).
Proof.
  intros oic.
  induction oic; auto.
  simpl.
  f_equal.
  assumption.
Qed.

Lemma commute_approximate_oitdeps_conc :
  forall (oitd oitd':oitdeps),
    itdeps_to_oitdeps (oitdeps_to_itdeps (conc_oitdeps oitd oitd'))
    = conc_oitdeps (itdeps_to_oitdeps (oitdeps_to_itdeps oitd)) (itdeps_to_oitdeps (oitdeps_to_itdeps oitd')).
Proof.
  induction oitd; auto.

  destruct a as [l tf].
  intros oitd'.
  simpl.
  f_equal.
  auto.
Qed.

Lemma commute_approximate_oideps_conc :
  forall (oid oid':oideps),
    ideps_to_oideps (oideps_to_ideps (conc_oideps oid oid'))
    = conc_oideps (ideps_to_oideps (oideps_to_ideps oid)) (ideps_to_oideps (oideps_to_ideps oid')).
Proof.
  induction oid; auto.

  destruct a as [l tf].
  intros oid'.
  simpl.
  f_equal.
  auto.
Qed.

Lemma commute_approximate_oitenv_conc :
  forall (oitc1 oitc2:oitenv),
    itenv_to_oitenv (oitenv_to_itenv (conc_oitenv oitc1 oitc2))
    = conc_oitenv (itenv_to_oitenv (oitenv_to_itenv oitc1)) (itenv_to_oitenv (oitenv_to_itenv oitc2)).
Proof.
  intros oitc1 oitc2.
  induction oitc1; auto.

  simpl.
  f_equal; auto.
Qed.

Lemma is_filtered_oitval_in_approximated_oitval_via_itval :
  forall (c_p:oitenv) (oitu:oitval) (p:pattern),
    is_filtered_oitval (itval_to_oitval (oitval_to_itval oitu)) p = Filtered_oitval_result_Match c_p
    -> exists (c_p':oitenv), is_filtered_oitval oitu p = Filtered_oitval_result_Match c_p'
                              /\ c_p = (itenv_to_oitenv (oitenv_to_itenv c_p')).
Proof.
  intros c_p oitu p H.
  destruct oitu.
  destruct u.
  destruct v; destruct p; inversion H; simpl.

  destruct (eq_nat_dec n c); inversion H1.
  exists OITEnv_empty; auto.

  destruct (eq_nat_dec n c); inversion H1.
  exists (OITEnv_cons i (OIV nil u) OITEnv_empty); auto.

  exists (OITEnv_cons i (OIV nil u1) (OITEnv_cons i0 (OIV nil u2) OITEnv_empty)); auto.
Qed.

Lemma is_not_filtered_oitval_in_approximated_oitval_via_itval :
  forall (oitu:oitval) (p:pattern),
    is_filtered_oitval (itval_to_oitval (oitval_to_itval oitu)) p = Filtered_oitval_result_Match_var
    -> is_filtered_oitval oitu p = Filtered_oitval_result_Match_var.
Proof.
  intros oitu p H.
  destruct oitu.
  destruct u.
  destruct v; destruct p; inversion H; simpl; auto.

  destruct (eq_nat_dec n c); inversion H1; auto.
Qed.


Lemma is_filtered_itval_implies_is_filtered_oitval :
  forall (itc_p:itenv) (itu:itval) (oitu:oitval) (p:pattern),
    is_filtered_itval itu p = Filtered_itval_result_Match itc_p
    -> oitval_to_itval oitu = itu
    -> exists (oitc_p:oitenv), is_filtered_oitval oitu p = Filtered_oitval_result_Match oitc_p
                               /\ oitenv_to_itenv oitc_p = itc_p.
Proof.
  intros itc_p itu oitu p H H0.
  destruct itu as [itd iu].
  destruct iu as [id iv].
  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].
  inversion H0.
  destruct iv; destruct p; inversion H.

  (* case Constr0 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H5.
  destruct oiv; inversion H4.
  exists OITEnv_empty.
  simpl; rewrite H_n_c.
  split; auto.

  (* case Constr1 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H5.
  destruct oiv; inversion H4.
  exists (OITEnv_cons i (oival_to_oitval u0) OITEnv_empty).
  simpl; rewrite H_n_c.
  split; auto.

  (* case Couple *)
  destruct oiv; inversion H4.
  exists (OITEnv_cons i (oival_to_oitval u0) (OITEnv_cons i0 (oival_to_oitval u3) OITEnv_empty)); auto.
Qed.

Lemma is_not_filtered_itval_implies_is_not_filtered_oitval :
  forall (itu:itval) (oitu:oitval) (p:pattern),
    is_filtered_itval itu p = Filtered_itval_result_Match_var
    -> oitval_to_itval oitu = itu
    -> is_filtered_oitval oitu p = Filtered_oitval_result_Match_var.
Proof.
  intros itu oitu p H H0.
  destruct itu as [itd iu].
  destruct iu as [id iv].
  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].
  inversion H0.
  destruct iv; destruct p; inversion H;
  destruct oiv; inversion H4; auto.

  (* case Constr0 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H5.
  simpl; rewrite H_n_c; auto.

  (* case Constr1 *)
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H5.
  simpl; rewrite H_n_c; auto.
Qed.






Lemma oideps_to_ideps_of_partially_approximated :
  forall (oid oid_:oideps),
    partially_approximated_oideps oid oid_
    -> oideps_to_ideps oid = oideps_to_ideps oid_.
Proof.
  intros oid oid_ H.
  induction H; auto.
  simpl.
  f_equal; auto.
Qed.

Lemma oitval_to_itval_of_strictly_partially_approximated :
  forall (oitu oitu':oitval),
    strictly_partially_approximated_oitval oitu oitu'
    -> oitval_to_itval oitu = oitval_to_itval oitu'.
Proof.
  intros oitu oitu' H.
  
  induction H.
  simpl.
  f_equal.

  (* oitdeps *)
  clear H0.
  induction H; auto.
  simpl.
  f_equal; auto.

  (* oival *)
  clear H.
  revert oiu' H0.
  apply (oival_ind2
           (fun oiu => forall oiu' : oival,
                         strictly_partially_approximated_oival oiu oiu' -> oival_to_ival oiu = oival_to_ival oiu')
           (fun oiv => forall oiv' : oival0,
                         strictly_partially_approximated_oival0 oiv oiv' -> oival0_to_ival0 oiv = oival0_to_ival0 oiv')
           (fun oic => forall oic' : oienv,
                         strictly_partially_approximated_oienv oic oic' -> oienv_to_ienv oic = oienv_to_ienv oic'));
  intros; try solve[inversion H; auto].

  inversion H0.
  simpl; f_equal; auto.
  apply oideps_to_ideps_of_partially_approximated; auto.

  inversion H0; auto.
  simpl.
  f_equal; auto.

  inversion H0; auto.
  simpl.
  f_equal; auto.

  inversion H1; auto.
  simpl.
  f_equal; auto.

  inversion H0; auto.
  simpl.
  f_equal; auto.

  inversion H1; auto.
  simpl.
  f_equal; auto.
Qed.

Lemma strictly_partially_approximated_oival0_to_ival0 :
  forall (oiv oiv_:oival0),
    strictly_partially_approximated_oival0 oiv oiv_
    -> oival0_to_ival0 oiv = oival0_to_ival0 oiv_.
Proof.
  apply (oival0_ind2
           (fun oiu => forall oiu' : oival,
                         strictly_partially_approximated_oival oiu oiu' -> oival_to_ival oiu = oival_to_ival oiu')
           (fun oiv => forall oiv' : oival0,
                         strictly_partially_approximated_oival0 oiv oiv' -> oival0_to_ival0 oiv = oival0_to_ival0 oiv')
           (fun oic => forall oic' : oienv,
                         strictly_partially_approximated_oienv oic oic' -> oienv_to_ienv oic = oienv_to_ienv oic'));
  intros; try solve[inversion H; auto].

  inversion H0.
  simpl; f_equal; auto.
  apply oideps_to_ideps_of_partially_approximated; auto.

  inversion H0; auto.
  simpl.
  f_equal; auto.

  inversion H0; auto.
  simpl.
  f_equal; auto.

  inversion H1; auto.
  simpl.
  f_equal; auto.

  inversion H0; auto.
  simpl.
  f_equal; auto.

  inversion H1; auto.
  simpl.
  f_equal; auto.
Qed.


Lemma oienv_to_oitenv_via_ienv_to_itenv_or_via_oitenv_to_itenv :
  forall (oic:oienv),
    (itenv_to_oitenv (ienv_to_itenv (oienv_to_ienv oic)))
    = (itenv_to_oitenv (oitenv_to_itenv (oienv_to_oitenv oic))).
Proof.
  intros oic.
  induction oic; auto; simpl.
  f_equal.
  assumption.
Qed.


Lemma commute_oitdeps_to_itdeps_conc :
  forall (oitd1 oitd2:oitdeps),
    oitdeps_to_itdeps (conc_oitdeps oitd1 oitd2)
    = conc_itdeps (oitdeps_to_itdeps oitd1) (oitdeps_to_itdeps oitd2).
Proof.
  induction oitd1.
  auto.

  intros oitd2.
  destruct a as [l f].
  simpl.
  f_equal.
  auto.
Qed.

Lemma commute_oideps_to_ideps_conc :
  forall (oid1 oid2:oideps),
    oideps_to_ideps (conc_oideps oid1 oid2)
    = conc_ideps (oideps_to_ideps oid1) (oideps_to_ideps oid2).
Proof.
  induction oid1.
  auto.

  intros oid2.
  destruct a as [l f].
  simpl.
  f_equal.
  auto.
Qed.

Lemma commute_oitenv_to_itenv_conc :
  forall (oitc1 oitc2:oitenv),
    oitenv_to_itenv (conc_oitenv oitc1 oitc2)
    = conc_itenv (oitenv_to_itenv oitc1) (oitenv_to_itenv oitc2).
Proof.
  induction oitc1; auto.

  intros oitc2.
  simpl.
  f_equal.
  auto.
Qed.

Lemma deps_spec_Apply_oitdeps_to_itdeps :
  forall (oitd':oitdeps) (oid1 oid':oideps) (oitu2:oitval) (d1:ideps),
    deps_spec_Apply oitu2 oid1 oitd' oid'
    -> oideps_to_ideps oid1 = d1
    -> oitdeps_to_itdeps oitd' = d1.
Proof.
  intros oitd' oid1 oid' oitu2 d1 H_deps_spec_Apply.
  revert d1.
  induction H_deps_spec_Apply; auto.
  intros d1 H_oid1.
  simpl; simpl in H_oid1.
  destruct d1; inversion H_oid1.
  apply IHH_deps_spec_Apply in H2.
  inversion H_oid1.
  rewrite H2.
  rewrite H4.
  reflexivity.
Qed.

Lemma deps_spec_Apply_oideps_to_ideps :
  forall (oitd':oitdeps) (oid1 oid':oideps) (oitu2:oitval) (d1:ideps),
    deps_spec_Apply oitu2 oid1 oitd' oid'
    -> oideps_to_ideps oid1 = d1
    -> oideps_to_ideps oid' = d1.
Proof.
  intros oitd' oid1 oid' oitu2 d1 H_deps_spec_Apply.
  revert d1.
  induction H_deps_spec_Apply; auto.
  intros d1 H_oid1.
  simpl; simpl in H_oid1.
  destruct d1; inversion H_oid1.
  apply IHH_deps_spec_Apply in H2.
  inversion H_oid1.
  rewrite H2.
  rewrite H4.
  reflexivity.
Qed.

Lemma deps_spec_If_oitdeps_to_itdeps :
  forall (oitc:oitenv) (e1 e2:expr) (oitd':oitdeps) (oid oid':oideps) (d1:ideps),
    deps_spec_If oitc e1 e2 oid oitd' oid'
    -> oideps_to_ideps oid = d1
    -> oitdeps_to_itdeps oitd' = d1.
Proof.
  intros oitc e1 e2 oitd' oid oid' d1 H_deps_spec.
  revert d1.
  induction H_deps_spec; auto.
  intros d1 H_oid.
  simpl; simpl in H_oid.
  destruct d1; inversion H_oid.
  apply IHH_deps_spec in H2.
  inversion H_oid.
  rewrite H2.
  rewrite H4.
  reflexivity.
Qed.

Lemma deps_spec_If_oideps_to_ideps :
  forall (oitc:oitenv) (e1 e2:expr) (oitd':oitdeps) (oid oid':oideps) (d1:ideps),
    deps_spec_If oitc e1 e2 oid oitd' oid'
    -> oideps_to_ideps oid = d1
    -> oideps_to_ideps oid' = d1.
Proof.
  intros oitc e1 e2 oitd' oid oid' d1 H_deps_spec.
  revert d1.
  induction H_deps_spec; auto.
  intros d1 H_oid.
  simpl; simpl in H_oid.
  destruct d1; inversion H_oid.
  apply IHH_deps_spec in H2.
  inversion H_oid.
  rewrite H2.
  rewrite H4.
  reflexivity.
Qed.

Lemma deps_spec_Match_oitdeps_to_itdeps :
  forall (oitc:oitenv) (p:pattern) (x:identifier) (e1 e2:expr) (oitd':oitdeps) (oid oid':oideps) (d1:ideps),
    deps_spec_Match oitc p x e1 e2 oid oitd' oid'
    -> oideps_to_ideps oid = d1
    -> oitdeps_to_itdeps oitd' = d1.
Proof.
  intros oitc p x e1 e2 oitd' oid oid' d1 H_deps_spec.
  revert d1.
  induction H_deps_spec; auto.
  intros d1 H_oid.
  simpl; simpl in H_oid.
  destruct d1; inversion H_oid.
  apply IHH_deps_spec in H2.
  inversion H_oid.
  rewrite H2.
  rewrite H4.
  reflexivity.
Qed.

Lemma deps_spec_Match_oideps_to_ideps :
  forall (oitc:oitenv) (p:pattern) (x:identifier) (e1 e2:expr) (oitd':oitdeps) (oid oid':oideps) (d1:ideps),
    deps_spec_Match oitc p x e1 e2 oid oitd' oid'
    -> oideps_to_ideps oid = d1
    -> oideps_to_ideps oid' = d1.
Proof.
  intros oitc p x e1 e2 oitd' oid oid' d1 H_deps_spec.
  revert d1.
  induction H_deps_spec; auto.
  intros d1 H_oid.
  simpl; simpl in H_oid.
  destruct d1; inversion H_oid.
  apply IHH_deps_spec in H2.
  inversion H_oid.
  rewrite H2.
  rewrite H4.
  reflexivity.
Qed.



(*
TODO:
il me semble qu'il y a une erreur dans la sémantique pour la règle Apply
on a (conc_oitdeps td1 (conc_oitdeps td2 (conc_oitdeps td td')))
mais si une injection sur le label l modifie la valeur de e1
alors la fonction appliquée est différente
donc les labels qui peuvent faire boucler le corps de la fonction [td] n'ont pas de sens
on devrait donc mettre (conc_oitdeps td1 (conc_oitdeps td2 (merge_oitdeps td td')))
avec la propriété suivante :
apply_timpact_fun l vl td' <> Some true
-> apply_timpact_fun l vl (merge_oitdeps td td') <> Some true
et éventuellement
apply_timpact_fun l vl td' = Some false
-> apply_timpact_fun l vl (merge_oitdeps td td') = Some false


La preuve est terminée,
 il me reste à savoir pourquoi il me semblait y avoir une erreur dans la sémantique sur-instrumentée !
*)
Theorem ival_of_correctness :
  forall (itc:itenv) (e:expr) (itu:itval),
  ival_of itc e itu
  -> exists (oitu:oitval),
       (oival_of (itenv_to_oitenv itc) e oitu
        /\ oitval_to_itval oitu = itu).
Proof.

  intros itc e itu H_ival_of_e.
  induction H_ival_of_e;
    eauto with oival_of.

  (* case Ident *)
  exists(itval_to_oitval uu).
  split.
  apply OIVal_of_Ident.
  induction c.
  inversion H.
  simpl; simpl in H.
  induction (beq_identifier x x0); try inversion H; auto.
  apply itval_to_oitval_to_itval.

  (* case Lambda *)
  exists(itval_to_oitval uu).
  rewrite H; simpl.
  split.
  apply OIVal_of_Lambda.
  repeat f_equal.
  simpl.
  Locate itenv_to_ienv.
  apply itenv_to_oienv_via_ienv_or_via_oitenv.
  repeat f_equal.
  rewrite ienv_to_oienv_to_ienv; reflexivity.
  
  (* case Rec *)
  exists(itval_to_oitval uu).
  rewrite H; simpl.
  split.
  apply OIVal_of_Rec.
  repeat f_equal.
  simpl.
  Locate itenv_to_ienv.
  apply itenv_to_oienv_via_ienv_or_via_oitenv.
  repeat f_equal.
  rewrite ienv_to_oienv_to_ienv; reflexivity.

  (* case Apply *)
  inversion_clear IHH_ival_of_e1 as [oitu1 IHH_oival_of_e1].
  inversion_clear IHH_ival_of_e2 as [oitu2 IHH_oival_of_e2].
  inversion_clear IHH_ival_of_e3 as [oitu IHH_oival_of_e].

  inversion_clear IHH_oival_of_e1 as [IH_oival_of_e1 IH_oival_of_e1_rel].
  inversion_clear IHH_oival_of_e2 as [IH_oival_of_e2 IH_oival_of_e2_rel].
  inversion_clear IHH_oival_of_e as [IH_oival_of_e IH_oival_of_e_rel].
  
  destruct oitu1 as [oitd1 oiu1].
  destruct oiu1 as [oid1 oiv1].
  destruct oitu2 as [oitd2 oiu2] eqn:H_oitu2.
  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].

  assert(H_td'_d' := exists_deps_spec_Apply oid1 oitu2).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_Apply].

  (** oiv1 is a Closure *)
  induction oiv1; try solve [simpl in IH_oival_of_e1_rel; inversion IH_oival_of_e1_rel].

  (** change the environment in IH_oival_of_e *)
  rewrite <- H_oitu2 in IH_oival_of_e2.
  simpl in IH_oival_of_e1_rel.
  inversion IH_oival_of_e1_rel as [[H_td1 H_d1 H_x H_e H_c1]].
  rewrite <-H_x, <-H_c1, <-H_e, <-IH_oival_of_e2_rel in IH_oival_of_e.
  unfold itenv_to_oitenv in IH_oival_of_e.
  fold itenv_to_oitenv in IH_oival_of_e.
  rewrite oienv_to_oitenv_via_ienv_to_itenv_or_via_oitenv_to_itenv in IH_oival_of_e.
  change (OITEnv_cons x0
                      (itval_to_oitval (oitval_to_itval (OIV oitd2 oiu2)))
                      (itenv_to_oitenv
                         (oitenv_to_itenv (oienv_to_oitenv c0))))
  with (itenv_to_oitenv (oitenv_to_itenv (OITEnv_cons x0
                                                      (OIV oitd2 oiu2)
                                                      (oienv_to_oitenv c0))))
    in IH_oival_of_e.         

  apply oival_of_in_approximated_oitenv_via_itenv in IH_oival_of_e.
  rewrite <-H_oitu2  in IH_oival_of_e.
  inversion_clear IH_oival_of_e as [oitu'' IHH_oival_of_e].
  destruct oitu'' as [oitd'' oiu''].
  destruct oiu'' as [oid'' oiv''].
  inversion_clear IHH_oival_of_e as [IH_oival_of_e H_oitu''].
  apply oitval_to_itval_of_strictly_partially_approximated in H_oitu''.
  inversion H_oitu''.

  (** here is the instrumented value of (Apply e1 e2) *)
  exists (OIV (conc_oitdeps oitd1 (conc_oitdeps oitd2 (conc_oitdeps oitd'' oitd'))) (OIV_ (conc_oideps oid' oid'') oiv'')).
  split.

  apply (OIVal_of_Apply (itenv_to_oitenv c) c0 e1 e2 e0 x0 oitu2 _ oiu2 oid'' oid' oid1 oitd1 oitd2 oitd'' oitd' oiv''); auto.

  (** the given value is uu when we clear impact functions (oitval_to_itval) *)
  rewrite H0; simpl.
  f_equal.
  repeat rewrite commute_oitdeps_to_itdeps_conc.
  repeat f_equal.
  assumption.
  rewrite H in IH_oival_of_e2_rel.
  inversion IH_oival_of_e2_rel.
  reflexivity.
  inversion IH_oival_of_e_rel; auto.
  apply (deps_spec_Apply_oitdeps_to_itdeps _ oid1 oid' oitu2); auto.
  simpl in H_oitu''.
  f_equal.
  inversion IH_oival_of_e_rel.
  rewrite commute_oideps_to_ideps_conc.
  f_equal; auto.
  apply (deps_spec_Apply_oideps_to_ideps oitd' oid1 oid' oitu2); auto.
  inversion IH_oival_of_e_rel; auto.
  
  (* case Apply_rec *)
  inversion_clear IHH_ival_of_e1 as [oitu1 IHH_oival_of_e1].
  inversion_clear IHH_ival_of_e2 as [oitu2 IHH_oival_of_e2].
  inversion_clear IHH_ival_of_e3 as [oitu IHH_oival_of_e].

  inversion_clear IHH_oival_of_e1 as [IH_oival_of_e1 IH_oival_of_e1_rel].
  inversion_clear IHH_oival_of_e2 as [IH_oival_of_e2 IH_oival_of_e2_rel].
  inversion_clear IHH_oival_of_e as [IH_oival_of_e IH_oival_of_e_rel].
  
  destruct oitu1 as [oitd1 oiu1].
  destruct oiu1 as [oid1 oiv1].
  destruct oitu2 as [oitd2 oiu2] eqn:H_oitu2.
  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].

  assert(H_td'_d' := exists_deps_spec_Apply oid1 oitu2).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_Apply].

  (** oiv1 is a Rec_Closure *)
  rewrite H in IH_oival_of_e1_rel.
  induction oiv1; try solve [simpl in IH_oival_of_e1_rel; inversion IH_oival_of_e1_rel].

  (** change the environment in IH_oival_of_e *)
  rewrite <- H_oitu2 in IH_oival_of_e2.
  inversion IH_oival_of_e1_rel as [[H_td1 H_d1 H_f H_x H_e H_c1]].
  rewrite H_f, H_x, H_e, <-H_c1 in *; clear H_f H_x H_e f0 x0 e0.
  rewrite H, <-IH_oival_of_e2_rel in IH_oival_of_e.
  unfold itenv_to_oitenv in IH_oival_of_e.
  fold itenv_to_oitenv in IH_oival_of_e.
  rewrite <-IH_oival_of_e1_rel in IH_oival_of_e.
  rewrite oienv_to_oitenv_via_ienv_to_itenv_or_via_oitenv_to_itenv in IH_oival_of_e.
  remember (OIV oitd1 (OIV_ oid1 (OIV_Rec_Closure f x e c0))) as oitu1.
  change (OITEnv_cons f (itval_to_oitval (oitval_to_itval oitu1))
                      (OITEnv_cons x (itval_to_oitval (oitval_to_itval (OIV oitd2 oiu2)))
                                   (itenv_to_oitenv (oitenv_to_itenv (oienv_to_oitenv c0)))))
  with (itenv_to_oitenv (oitenv_to_itenv (OITEnv_cons f oitu1
                                                      (OITEnv_cons x (OIV oitd2 oiu2)
                                                                   (oienv_to_oitenv c0)))))
    in IH_oival_of_e.
  apply oival_of_in_approximated_oitenv_via_itenv in IH_oival_of_e.
  rewrite <-H_oitu2  in IH_oival_of_e.
  inversion_clear IH_oival_of_e as [oitu'' IHH_oival_of_e].
  destruct oitu'' as [oitd'' oiu''].
  destruct oiu'' as [oid'' oiv''].
  inversion_clear IHH_oival_of_e as [IH_oival_of_e H_oitu''].
  apply oitval_to_itval_of_strictly_partially_approximated in H_oitu''.
  inversion H_oitu''.

  (** here is the instrumented value of (Apply e1 e2) *)
  exists (OIV (conc_oitdeps oitd1 (conc_oitdeps oitd2 (conc_oitdeps oitd'' oitd'))) (OIV_ (conc_oideps oid' oid'') oiv'')).
  split.

  apply (OIVal_of_Apply_Rec (itenv_to_oitenv c) c0 e1 e2 e f x oitu1 oitu2 _ oiu2 oid'' oid' oid1 oitd1 oitd2 oitd'' oitd' oiv''); auto.

  (** the given value is uu when we clear impact functions (oitval_to_itval) *)
  rewrite H1; simpl.
  f_equal.
  repeat rewrite commute_oitdeps_to_itdeps_conc.
  repeat f_equal; auto.
  rewrite H0 in IH_oival_of_e2_rel.
  inversion IH_oival_of_e2_rel; auto.
  inversion IH_oival_of_e_rel; auto.
  apply (deps_spec_Apply_oitdeps_to_itdeps _ oid1 oid' oitu2); auto.
  simpl in H_oitu''.
  f_equal.
  inversion IH_oival_of_e_rel.
  rewrite commute_oideps_to_ideps_conc.
  f_equal; auto.
  apply (deps_spec_Apply_oideps_to_ideps oitd' oid1 oid' oitu2); auto.
  inversion IH_oival_of_e_rel; auto.

  (* case Let_in *)
  
  (** oival_of e1 and e2 *)
  inversion_clear IHH_ival_of_e1 as [oitu1 HH].
  inversion_clear HH as [H_oival_of_e1 H_oitu1_uu1].
  inversion_clear IHH_ival_of_e2 as [oitu2 HH].
  inversion_clear HH as [H_oival_of_e2 H_oitu2_uu2].
  destruct oitu1 as [oitd1 oiu1].
  destruct oitu2 as [oitd2 oiu2].
  
  (** change environment in H_oival_of_e2 *)
  apply oival_of_in_strictly_partially_approximated_oitenv
  with (oitc:=(OITEnv_cons x (OIV oitd1 oiu1) (itenv_to_oitenv c)))
    in H_oival_of_e2;
    [|simpl; apply SPApprox_oitenv_cons;
      [apply approximated_oitval_implies_strictly_partially_approximated; rewrite H_oitu1_uu1; auto
      |apply strictly_partially_approximated_oitenv_refl]].

  inversion_clear H_oival_of_e2 as [oitu2' HH].
  inversion_clear HH as [H_oival_of_e2' H_oitu2'_oitu2].
  destruct oitu2' as [oitd2' oiu2'].

  (** application of the rule *)
  exists (OIV (conc_oitdeps oitd1 oitd2') oiu2').
  split; eauto with oival_of.

  rewrite H in H_oitu1_uu1.
  inversion H_oitu1_uu1; clear H_oitu1_uu1.
  rewrite H0 in H_oitu2_uu2.
  inversion H_oitu2_uu2; clear H_oitu2_uu2.
  apply oitval_to_itval_of_strictly_partially_approximated in H_oitu2'_oitu2.
  inversion H_oitu2'_oitu2; clear H_oitu2'_oitu2.

  simpl; f_equal.
  rewrite commute_oitdeps_to_itdeps_conc; f_equal.

  (* case If_true *)
  
  (** oival_of e and e1 *)
  inversion_clear IHH_ival_of_e1 as [oitu HH].
  inversion_clear HH as [H_oival_of_e H_oitu_uu].
  inversion_clear IHH_ival_of_e2 as [oitu1 HH].
  inversion_clear HH as [H_oival_of_e1 H_oitu1_uu1].
  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].
  destruct oitu1 as [oitd1 oiu1].
  destruct oiu1 as [oid1 oiv1].
  inversion H_oitu_uu.
  destruct oiv; try solve [inversion H3].
  destruct b; try solve [inversion H3].  

  (** oitd' and oid' *)
  assert(H_td'_d' := exists_deps_spec_If (itenv_to_oitenv c) e1 e2 oid).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_If].
  
  (** application of the rule *)
  exists (OIV (conc_oitdeps oitd' (conc_oitdeps oitd oitd1)) (OIV_ (conc_oideps oid' oid1) oiv1)).
  split; eauto with oival_of.

  rewrite H in H_oitu1_uu1.
  inversion H_oitu1_uu1; clear H_oitu1_uu1.

  simpl; repeat f_equal.
  repeat rewrite commute_oitdeps_to_itdeps_conc.
  repeat f_equal.

  apply deps_spec_If_oitdeps_to_itdeps with (d1:=d) in H_deps_spec_If; auto.
  rewrite H2; auto.

  repeat rewrite commute_oideps_to_ideps_conc; f_equal.
  apply deps_spec_If_oideps_to_ideps with (d1:=d) in H_deps_spec_If; auto.
  rewrite H2; auto.

  (* case If_false *)

  (** oival_of e and e1 *)
  inversion_clear IHH_ival_of_e1 as [oitu HH].
  inversion_clear HH as [H_oival_of_e H_oitu_uu].
  inversion_clear IHH_ival_of_e2 as [oitu2 HH].
  inversion_clear HH as [H_oival_of_e2 H_oitu2_uu2].
  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].
  destruct oitu2 as [oitd2 oiu2].
  destruct oiu2 as [oid2 oiv2].
  inversion H_oitu_uu.
  destruct oiv; try solve [inversion H3].
  destruct b; try solve [inversion H3].  

  (** oitd' and oid' *)
  assert(H_td'_d' := exists_deps_spec_If (itenv_to_oitenv c) e1 e2 oid).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_If].
  
  (** application of the rule *)
  exists (OIV (conc_oitdeps oitd' (conc_oitdeps oitd oitd2)) (OIV_ (conc_oideps oid' oid2) oiv2)).
  split; eauto with oival_of.

  rewrite H in H_oitu2_uu2.
  inversion H_oitu2_uu2; clear H_oitu2_uu2.

  simpl; repeat f_equal.
  repeat rewrite commute_oitdeps_to_itdeps_conc.
  repeat f_equal.

  apply deps_spec_If_oitdeps_to_itdeps with (d1:=d) in H_deps_spec_If; auto.
  rewrite H2; auto.

  repeat rewrite commute_oideps_to_ideps_conc; f_equal.
  apply deps_spec_If_oideps_to_ideps with (d1:=d) in H_deps_spec_If; auto.
  rewrite H2; auto.

  (* case Match *)
  
  (** oival_of e and e1 *)
  inversion_clear IHH_ival_of_e1 as [oitu HH].
  inversion_clear HH as [H_oival_of_e H_oitu_uu].
  inversion_clear IHH_ival_of_e2 as [oitu1' HH].
  inversion_clear HH as [H_oival_of_e1 H_oitu1'_uu1].

  apply is_filtered_itval_implies_is_filtered_oitval with (oitu:=oitu) in H0; auto.
  inversion_clear H0 as [oitc_p HH].
  inversion_clear HH as [H_is_filtered_oitval H_oitc_p].  

  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].
  inversion H_oitu_uu.

  (** oitd' and oid' *)
  assert(H_td'_d' := exists_deps_spec_Match (itenv_to_oitenv c) p x e1 e2 oid).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_If].
  
  (** change environment in H_oival_of_e1 *)
  rewrite <-H_oitc_p in H_oival_of_e1.
  rewrite <-(itenv_to_oitenv_to_itenv c) in H_oival_of_e1.
  rewrite <-commute_oitenv_to_itenv_conc in H_oival_of_e1.
  apply oival_of_in_approximated_oitenv_via_itenv in H_oival_of_e1.
  inversion_clear H_oival_of_e1 as [oitu1 HH].
  inversion_clear HH as [H_oival_of_e1 H_oitu1_uu1].
  destruct oitu1 as [oitd1 oiu1].
  destruct oiu1 as [oid1 oiv1].

  (** application of the rule *)
  exists (OIV (conc_oitdeps oitd' (conc_oitdeps oitd oitd1)) (OIV_ (conc_oideps oid' oid1) oiv1)).
  split; eauto with oival_of.

  rewrite H in H0; inversion H0.

  inversion H_oitu1_uu1.
  inversion H9.
  rewrite H1, <-H8, <-H13 in H_oitu1'_uu1; inversion H_oitu1'_uu1.
  simpl; f_equal.
  rewrite commute_oitdeps_to_itdeps_conc; f_equal.
  apply deps_spec_Match_oitdeps_to_itdeps with (d1:=d) in H_deps_spec_If; auto.
  rewrite H4; auto.
  rewrite commute_oitdeps_to_itdeps_conc; f_equal.
  apply partially_approximated_oitdeps_to_itdeps; auto.
  rewrite commute_oideps_to_ideps_conc.
  f_equal; auto.
  f_equal; auto.
  apply deps_spec_Match_oideps_to_ideps with (d1:=d) in H_deps_spec_If; auto.
  rewrite H4; auto.
  apply partially_approximated_oideps_to_ideps; auto.
  apply strictly_partially_approximated_oival0_to_ival0; auto.

  (* case Match_var *)

  (** oival_of e and e2 *)
  inversion_clear IHH_ival_of_e1 as [oitu HH].
  inversion_clear HH as [H_oival_of_e H_oitu_uu].
  inversion_clear IHH_ival_of_e2 as [oitu2 HH].
  inversion_clear HH as [H_oival_of_e2 H_oitu2_uu2].
  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].
  destruct oitu2 as [oitd2 oiu2].
  destruct oiu2 as [oid2 oiv2].

  apply is_not_filtered_itval_implies_is_not_filtered_oitval with (oitu:=(OIV oitd (OIV_ oid oiv))) in H0; auto.
  
  (** oitd' and oid' *)
  assert(H_td'_d' := exists_deps_spec_Match (itenv_to_oitenv c) p x e1 e2 oid).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_Match].
  
  (** change environment in H_oival_of_e2 *)
  apply oival_of_in_strictly_partially_approximated_oitenv
  with (oitc:=(OITEnv_cons x (OIV oitd (OIV_ oid oiv)) (itenv_to_oitenv c)))
    in H_oival_of_e2;
    [|simpl; apply SPApprox_oitenv_cons;
      [apply approximated_oitval_implies_strictly_partially_approximated; rewrite H_oitu_uu; auto
      |apply strictly_partially_approximated_oitenv_refl]].

  inversion_clear H_oival_of_e2 as [oitu2' HH].
  inversion_clear HH as [H_oival_of_e2' H_oitu2'_oitu2].
  destruct oitu2' as [oitd2' oiu2'].
  destruct oiu2' as [oid2' oiv2'].

  (** application of the rule *)
  exists (OIV (conc_oitdeps oitd' (conc_oitdeps oitd oitd2')) (OIV_ (conc_oideps oid' oid2') oiv2')).
  split; eauto with oival_of.

  rewrite H in H_oitu_uu.
  inversion H_oitu_uu; clear H_oitu_uu.
  rewrite H1 in H_oitu2_uu2.
  inversion H_oitu2_uu2; clear H_oitu2_uu2.
  apply oitval_to_itval_of_strictly_partially_approximated in H_oitu2'_oitu2.
  inversion H_oitu2'_oitu2; clear H_oitu2'_oitu2.
  assert(H_oitd'_d:=deps_spec_Match_oitdeps_to_itdeps _ _ _ _ _ _ _ _ d H_deps_spec_Match H4).
  assert(H_oid'_d:=deps_spec_Match_oideps_to_ideps _ _ _ _ _ _ _ _ d H_deps_spec_Match H4).

  simpl.
  repeat rewrite commute_oitdeps_to_itdeps_conc.
  rewrite commute_oideps_to_ideps_conc.
  rewrite H4.
  repeat f_equal; auto.

  (* case Constr1 *)
  
  (** oival_of e *)
  inversion_clear IHH_ival_of_e as [oitu HH].
  inversion_clear HH as [H_oival_of_e H_oitu_uu].
  destruct oitu as [oitd oiu].

  (** application of the rule *)
  exists (OIV oitd (OIV_ nil (OIV_Constr1 n oiu))).
  split; auto with oival_of.

  simpl.
  inversion H_oitu_uu; clear H_oitu_uu; auto.

  (* case Couple *)

  (** oival_of e and e1 *)
  inversion_clear IHH_ival_of_e1 as [oitu1 HH].
  inversion_clear HH as [H_oival_of_e1 H_oitu1_uu1].
  inversion_clear IHH_ival_of_e2 as [oitu2 HH].
  inversion_clear HH as [H_oival_of_e2 H_oitu2_uu2].
  destruct oitu1 as [oitd1 oiu1].
  destruct oitu2 as [oitd2 oiu2].

  (** application of the rule *)
  exists (OIV (conc_oitdeps oitd1 oitd2) (OIV_ nil (OIV_Couple oiu1 oiu2))).
  split; auto with oival_of.

  simpl.
  inversion H_oitu1_uu1; clear H_oitu1_uu1.
  inversion H_oitu2_uu2; clear H_oitu2_uu2.
  rewrite commute_oitdeps_to_itdeps_conc; auto.

  (* case Annot *)

  (** oival_of e *)
  inversion_clear IHH_ival_of_e as [oitu HH].
  inversion_clear HH as [H_oival_of_e H_oitu_uu].
  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].

  (** application of the rule *)
  exists (OIV oitd (OIV_ (cons (l, fun x=>x) oid) oiv)).
  split; auto with oival_of.

  simpl.
  inversion H_oitu_uu; clear H_oitu_uu; auto.
Qed.


Lemma oitval_to_itval_to_val :
  forall (oitu:oitval),
    itval_to_val (oitval_to_itval oitu) = oitval_to_val oitu.
Proof.
  intros oitu.  
  induction oitu.
  simpl.

  apply (oival_ind2
           (fun oiu => ival_to_val (oival_to_ival oiu) = oival_to_val oiu)
           (fun oiv => ival0_to_val (oival0_to_ival0 oiv) = oival0_to_val oiv)
           (fun oic => ienv_to_env (oienv_to_ienv oic) = oienv_to_env oic));
    intros; auto;
    simpl; f_equal; auto.
Qed.

Lemma ldna_in_oitdeps_to_itdeps_to_oitdeps :
  forall (l:label) (oitd_:oitdeps),
    label_does_not_appear_in_oitdeps l oitd_
    -> forall (oitd:oitdeps),
         oitd_ = itdeps_to_oitdeps (oitdeps_to_itdeps oitd)
         -> label_does_not_appear_in_oitdeps l oitd.
Proof.
  intros l oitd_ H.
  induction H; intros oitd HH.
  
  destruct oitd.
  apply Ldna_in_oitdeps_empty.
  destruct p; inversion HH.

  destruct oitd.
  inversion HH.
  destruct p as [l'' tf].
  inversion HH.
  apply Ldna_in_oitdeps_cons; auto.
  rewrite <-H2; auto.
Qed.

Lemma ldna_in_oideps_to_ideps_to_oideps :
  forall (l:label) (oid_:oideps),
    label_does_not_appear_in_oideps l oid_
    -> forall (oid:oideps),
         oid_ = ideps_to_oideps (oideps_to_ideps oid)
         -> label_does_not_appear_in_oideps l oid.
Proof.
  intros l oid_ H.
  induction H; intros oid HH.
  
  destruct oid.
  apply Ldna_in_oideps_empty.
  destruct p; inversion HH.

  destruct oid.
  inversion HH.
  destruct p as [l'' tf].
  inversion HH.
  apply Ldna_in_oideps_cons; auto.
  rewrite <-H2; auto.
Qed.


Lemma ldna_in_oitval_to_itval_to_oitval :
  forall (l:label) (oitu_:oitval),
    label_does_not_appear_in_oitval l oitu_
    -> forall (oitu:oitval),
         oitu_ = itval_to_oitval (oitval_to_itval oitu)
         -> label_does_not_appear_in_oitval l oitu.
Proof.
  intros l.

  apply (ldna_in_oitval_ind2
           (fun l oitu_ P => forall (oitu:oitval),
                               oitu_ = itval_to_oitval (oitval_to_itval oitu)
                               -> label_does_not_appear_in_oitval l oitu)
           (fun l oiu_ P => forall (oiu:oival),
                              oiu_ = ival_to_oival (oival_to_ival oiu)
                              -> label_does_not_appear_in_oival l oiu)
           (fun l oiv_ P => forall (oiv:oival0),
                              oiv_ = ival0_to_oival0 (oival0_to_ival0 oiv)
                              -> label_does_not_appear_in_oival0 l oiv)
           (fun l oic_ P => forall (oic:oienv),
                              oic_ = ienv_to_oienv (oienv_to_ienv oic)
                              -> label_does_not_appear_in_oienv l oic)
           (fun l oitc_ P => forall (oitc:oitenv),
                              oitc_ = itenv_to_oitenv (oitenv_to_itenv oitc)
                              -> label_does_not_appear_in_oitenv l oitc)
           (fun l oitc_ e P => forall (oitc:oitenv),
                                 oitc_ = itenv_to_oitenv (oitenv_to_itenv oitc)
                                 -> label_does_not_appear_in_expr l oitc e));
    intros; auto.

  destruct oitu.
  inversion H0.
  apply Ldna_in_oitval; auto.
  apply ldna_in_oitdeps_to_itdeps_to_oitdeps with (oitd_:=td); auto.

  destruct oiu; inversion H0.
  apply Ldna_in_oival; auto.
  apply ldna_in_oideps_to_ideps_to_oideps with (oid_:=d); auto.

  destruct oiv; inversion H.
  apply Ldna_in_oival0_Num.

  destruct oiv; inversion H.
  apply Ldna_in_oival0_Bool.

  destruct oiv; inversion H.
  apply Ldna_in_oival0_Constr0.

  destruct oiv; inversion H0.
  apply Ldna_in_oival0_Constr1; auto.

  destruct oiv; inversion H1.
  rewrite <-H3, <-H4 in *; clear H3 H4.
  apply Ldna_in_oival0_Closure; auto.
  apply H0.
  rewrite H5.
  rewrite oienv_to_oitenv_via_ienv_to_oienv_or_via_oitenv_to_itenv; auto.

  destruct oiv; inversion H1.
  rewrite <-H3, <-H4, <-H5 in *; clear H3 H4 H5.
  apply Ldna_in_oival0_Rec_Closure; auto.
  apply H0.
  rewrite H6.
  rewrite oienv_to_oitenv_via_ienv_to_oienv_or_via_oitenv_to_itenv; auto.
  
  destruct oiv; inversion H1.
  apply Ldna_in_oival0_Couple; auto.

  destruct oic; inversion H.
  apply Ldna_in_oienv_empty.

  destruct oic; inversion H1.
  apply Ldna_in_oienv_cons; auto.

  destruct oitc; inversion H.
  apply Ldna_in_oitenv_empty.

  destruct oitc; inversion H1.
  apply Ldna_in_oitenv_cons; auto.

  apply Ldna_in_expr_Num.
  apply Ldna_in_expr_Constr0.
  apply Ldna_in_expr_Constr1; auto.
  rewrite H0 in e.
  apply assoc_ident_in_approximated_oitenv_via_itenv in e.
  inversion_clear e as [oitu HH].
  inversion_clear HH as [H_assoc_oitc H_uu_oitu].
  apply Ldna_in_expr_Var with (uu:=oitu); auto.
  apply Ldna_in_expr_Var2.
  apply assoc_ident_not_in_approximated_oitenv_via_itenv.
  rewrite <-H; auto.
  apply Ldna_in_expr_Lambda; auto.
  apply Ldna_in_expr_Rec; auto.
  apply Ldna_in_expr_Apply; auto.
  apply Ldna_in_expr_If; auto.
  apply Ldna_in_expr_Expr_match1; auto.
  apply Ldna_in_expr_Expr_match2; auto.
  apply Ldna_in_expr_Couple; auto.
  apply Ldna_in_expr_Annot; auto.
  apply Ldna_in_expr_Let_in; auto.
Qed.



(* correctness of the instrumented semantics
 wrt. the semantics with injection *)
Theorem ival_of_correctness_global :
  forall (l:label) (vl:val) (itc:itenv) (e:expr) (itu:itval),
  ival_of itc e itu
  -> label_does_not_appear_in_itdeps_of_itenv l itc
  -> label_does_not_appear_in_itval l itu
  -> val_of_with_injection l vl (itenv_to_oitenv itc) e (itval_to_val itu).
Proof.
  intros l vl itc e itu H H0 H1.

  apply ival_of_correctness in H.
  inversion_clear H as [oitu HH].
  inversion_clear HH as [H_oival_of H_oitu_itu].

  apply oival_of_correctness with (uu:=oitu); auto.
  apply label_does_not_appear_in_oitdeps_of_oitenv_is_instantiable.
  apply ldna_in_oitdeps_of_itenv_to_oitenv; auto.
  apply ldna_in_itval_to_oitval in H1.
  rewrite instantiate_oitval_when_ldna_in_oitval; auto.
  rewrite <-H_oitu_itu.
  rewrite oitval_to_itval_to_val; auto.
  rewrite <-H_oitu_itu in H1.
  destruct oitu.
  inversion H1.
  apply ldna_in_oitval_to_itval_to_oitval with (oitu_:=itval_to_oitval (oitval_to_itval (OIV td u))); auto.
Qed.

