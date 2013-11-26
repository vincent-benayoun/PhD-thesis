Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.

Require Import over_instrumented_values.
Require Import oitval_val_conversion.
Require Import oitval_instantiation.

Require Import injection_operational_semantics.

Require Import partially_approximated.

Lemma val_of_with_injection_in_partially_approximated_oitenv :
  forall (oitc oitc':oitenv) (l:label) (vl:val) (e:expr) (v':val),
    partially_approximated_oitenv oitc oitc'
    -> val_of_with_injection l vl oitc' e v'
    -> exists (v:val), val_of_with_injection l vl oitc e v
                       /\ partially_approximated_val v v'.
Proof.
  intros oitc oitc' l vl e v' H H0.
  revert oitc H.
  induction H0; intros oitc H_papprox_oitc.

  exists (V_Num v); split; [auto with val_of_with_injection|auto_papprox].

  (* case Var *)
  destruct (assoc_in_partially_approximated_oitenv oitc c uu i H_papprox_oitc H) as [oitu].
  inversion_clear H1 as [H_assoc_in_oitc H_papprox_oitu].
  symmetry in H0.
  destruct (instantiate_partially_approximated_oitval oitu uu l vl v H_papprox_oitu H0) as [v' HH].
  inversion_clear HH as [H_inst_oitu H_papprox_v'].
  exists v'; split; [eauto with val_of_with_injection|auto].

  (* case Lambda *)
  symmetry in H.
  destruct (instantiate_partially_approximated_oitenv _ _ _ _ _ H_papprox_oitc H) as [cc].
  inversion_clear H1.
  exists (V_Closure x e cc); split; [eauto with val_of_with_injection|rewrite H0; auto_papprox].

  (* case Rec *)
  symmetry in H.
  destruct (instantiate_partially_approximated_oitenv _ _ _ _ _ H_papprox_oitc H) as [cc].
  inversion_clear H1.
  exists (V_Rec_Closure f x e cc); split; [eauto with val_of_with_injection|rewrite H0; auto_papprox].

  (* case Apply *)
  (** val of e1 *)
  specialize (IHval_of_with_injection1 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection1 as [v'1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v'1].
  inversion H_papprox_v'1.
  rewrite H, H2 in *; clear H H2 H3 x0 e0 c'.
  rewrite <-H0 in H_val_of_e1.
  (** val of e2 *)
  specialize (IHval_of_with_injection2 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection2 as [v'2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v'2].
  (** val of the body *)
  specialize (IHval_of_with_injection3 (OITEnv_cons x (val_to_oitval v'2) (env_to_oitenv c0))).
  assert(HH_papprox:partially_approximated_oitenv (OITEnv_cons x (val_to_oitval v'2) (env_to_oitenv c0))
                                                  (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c1))).
  apply PApprox_oitenv_cons.
  apply partially_approximated_val_to_oitval; auto.
  apply partially_approximated_env_to_oitenv; auto.
  specialize (IHval_of_with_injection3 HH_papprox).
  clear HH_papprox.
  inversion_clear IHval_of_with_injection3 as [v' HH].
  inversion_clear HH as [H_val_of_e H_papprox_v'].
  exists v'.
  split; eauto with val_of_with_injection.


  (* case Apply_rec *)
  (** val of e1 *)
  specialize (IHval_of_with_injection1 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection1 as [v'1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v'1].
  inversion H_papprox_v'1.
  rewrite H, H2, H3 in *; clear H H2 H3 H4 f0 x0 e0 c'.
  rewrite <-H0 in H_val_of_e1.
  (** val of e2 *)
  specialize (IHval_of_with_injection2 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection2 as [v'2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v'2].
  (** val of the body *)
  specialize (IHval_of_with_injection3 (OITEnv_cons f (val_to_oitval (V_Rec_Closure f x e c0))
                                                    (OITEnv_cons x (val_to_oitval v'2) (env_to_oitenv c0)))).
  simpl in IHval_of_with_injection3.
  assert(HH_papprox:
           partially_approximated_oitenv (OITEnv_cons f (val_to_oitval (V_Rec_Closure f x e c0))
                                                      (OITEnv_cons x (val_to_oitval v'2) (env_to_oitenv c0)))
                                         (OITEnv_cons f (val_to_oitval (V_Rec_Closure f x e c1))
                                                      (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c1)))).
  apply PApprox_oitenv_cons.
  apply partially_approximated_val_to_oitval; auto_papprox.
  apply PApprox_oitenv_cons.
  apply partially_approximated_val_to_oitval; auto_papprox.
  apply partially_approximated_env_to_oitenv; auto.
  specialize (IHval_of_with_injection3 HH_papprox).
  clear HH_papprox.
  inversion_clear IHval_of_with_injection3 as [v' HH].
  inversion_clear HH as [H_val_of_e H_papprox_v'].
  exists v'.
  split; eauto with val_of_with_injection.

  (* case Let_in *)
  (** val of e1 *)
  specialize (IHval_of_with_injection1 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection1 as [v'1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v'1].
  (** val of e2 *)
  specialize (IHval_of_with_injection2 (OITEnv_cons i (val_to_oitval v'1) oitc)).
  assert(HH_papprox:partially_approximated_oitenv (OITEnv_cons i (val_to_oitval v'1) oitc)
                                                  (OITEnv_cons i (val_to_oitval v1) c)).
  auto_papprox.
  apply partially_approximated_val_to_oival; auto_papprox.
  specialize (IHval_of_with_injection2 HH_papprox).
  clear HH_papprox.
  inversion_clear IHval_of_with_injection2 as [v'2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v'2].
  exists v'2.
  split; eauto with val_of_with_injection.

  (* case If_true *)
  (** val of e *)
  specialize (IHval_of_with_injection1 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection1 as [v' HH].
  inversion_clear HH as [H_val_of_e H_papprox_v'].
  inversion H_papprox_v'.
  rewrite H1 in *; clear H1 b.
  rewrite <-H in H_val_of_e.
  (** val of e1 *)
  specialize (IHval_of_with_injection2 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection2 as [v'1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v'1].
  exists v'1.
  split; eauto with val_of_with_injection.

  (* case If_false *)
  (** val of e *)
  specialize (IHval_of_with_injection1 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection1 as [v' HH].
  inversion_clear HH as [H_val_of_e H_papprox_v'].
  inversion H_papprox_v'.
  rewrite H1 in *; clear H1 b.
  rewrite <-H in H_val_of_e.
  (** val of e2 *)
  specialize (IHval_of_with_injection2 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection2 as [v'2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v'2].
  exists v'2.
  split; eauto with val_of_with_injection.

  (* case Match *)
  (** val of e *)
  specialize (IHval_of_with_injection1 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection1 as [v' HH].
  inversion_clear HH as [H_val_of_e H_papprox_v'].
  apply is_filtered_partially_approximated_val with (v:=v') in H; auto.
  inversion_clear H as [c_p' HH].
  inversion_clear HH as [H_is_filtered_v' H_papprox_c_p'].
  (** val of e1 *)
  specialize (IHval_of_with_injection2 (conc_oitenv (env_to_oitenv c_p') oitc)).
  assert(HH_papprox:partially_approximated_oitenv (conc_oitenv (env_to_oitenv c_p') oitc)
                                                  (conc_oitenv (env_to_oitenv c_p) c)).
  apply partially_approximated_conc_oitenv; auto.
  apply partially_approximated_env_to_oitenv; auto.
  specialize (IHval_of_with_injection2 HH_papprox).
  inversion_clear IHval_of_with_injection2 as [v'1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v'1].
  exists v'1.
  split; eauto with val_of_with_injection.

  (* case Match_var *)
  (** val of e *)
  specialize (IHval_of_with_injection1 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection1 as [v' HH].
  inversion_clear HH as [H_val_of_e H_papprox_v'].
  apply is_not_filtered_partially_approximated_val with (v:=v') in H; auto.
  (** val of e2 *)
  specialize (IHval_of_with_injection2 (OITEnv_cons x (val_to_oitval v') oitc)).
  assert(HH_papprox:partially_approximated_oitenv (OITEnv_cons x (val_to_oitval v') oitc)
                                                  (OITEnv_cons x (val_to_oitval v_e) c)).
  auto_papprox.
  apply partially_approximated_val_to_oival; auto.
  specialize (IHval_of_with_injection2 HH_papprox).
  inversion_clear IHval_of_with_injection2 as [v'2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v'2].
  exists v'2.
  split; eauto with val_of_with_injection.

  (* case Constr0 *)
  exists (V_Constr0 n); split; [auto with val_of_with_injection|auto_papprox].

  (* case Constr1 *)
  (** val of e *)
  specialize (IHval_of_with_injection oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection as [v' HH].
  inversion_clear HH as [H_val_of_e H_papprox_v'].
  exists (V_Constr1 n v').
  split; eauto with val_of_with_injection; auto_papprox.

  (* case Couple *)
  (** val of e1 *)
  specialize (IHval_of_with_injection1 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection1 as [v'1 HH].
  inversion_clear HH as [H_val_of_e1 H_papprox_v'1].
  (** val of e2 *)
  specialize (IHval_of_with_injection2 oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection2 as [v'2 HH].
  inversion_clear HH as [H_val_of_e2 H_papprox_v'2].
  exists (V_Couple v'1 v'2).
  split; eauto with val_of_with_injection; auto_papprox.

  (* case Annot_same_label *)
  (** val of e *)
  exists vl.
  split; eauto with val_of_with_injection; auto_papprox.
  apply partially_approximated_val_refl.
  
  (* case Annot_other_label *)
  (** val of e *)
  specialize (IHval_of_with_injection oitc H_papprox_oitc).
  inversion_clear IHval_of_with_injection as [v' HH].
  inversion_clear HH as [H_val_of_e H_papprox_v'].
  exists v'.
  split; eauto with val_of_with_injection.
Qed.
