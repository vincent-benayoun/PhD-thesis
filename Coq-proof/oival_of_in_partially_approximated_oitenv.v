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
Require Import val_of_with_injection_in_partially_approximated_oitenv.

Require Import deps_spec_in_partially_approximated.


Lemma assoc_ident_in_strictly_partially_approximated_oitenv :
  forall (oitc oitc':oitenv) (x:identifier) (oitu':oitval),
    strictly_partially_approximated_oitenv oitc oitc'
    -> assoc_ident_in_oitenv x oitc' = Ident_in_oitenv oitu'
    -> exists (oitu:oitval),
         assoc_ident_in_oitenv x oitc = Ident_in_oitenv oitu
         /\ strictly_partially_approximated_oitval oitu oitu'.
Proof.
  intros oitc oitc' x oitu' H H0.
  induction H.
  inversion H0.
  
  simpl in H0.
  destruct (beq_identifier x x0) eqn:H_x_x0.
  exists oitu.
  inversion H0.
  rewrite H3 in H.
  split; auto.
  simpl; rewrite H_x_x0; auto.

  specialize (IHstrictly_partially_approximated_oitenv H0).
  inversion IHstrictly_partially_approximated_oitenv as [oitu0].
  exists oitu0.
  simpl.
  rewrite H_x_x0; auto.
Qed.



Lemma strictly_partially_approximated_oitenv_to_oienv :
  forall (oitc oitc':oitenv),
    strictly_partially_approximated_oitenv oitc oitc'
    -> strictly_partially_approximated_oienv (oitenv_to_oienv oitc) (oitenv_to_oienv oitc').
Proof.
  intros oitc oitc' H.
  induction H.
  simpl; auto_papprox.

  simpl; auto_papprox.
  induction H.

  simpl; auto_papprox.
Qed.

Lemma strictly_partially_approximated_oienv_to_oitenv :
  forall (oic oic':oienv),
    strictly_partially_approximated_oienv oic oic'
    -> strictly_partially_approximated_oitenv (oienv_to_oitenv oic) (oienv_to_oitenv oic').
Proof.
  intros oic oic' H.
  induction H; simpl; auto_papprox.
Qed.


Lemma partially_approximated_conc_oitdeps :
  forall (oitd1 oitd1' oitd2 oitd2':oitdeps),
    partially_approximated_oitdeps oitd1 oitd1'
    -> partially_approximated_oitdeps oitd2 oitd2'
    -> partially_approximated_oitdeps (conc_oitdeps oitd1 oitd2) (conc_oitdeps oitd1' oitd2').
Proof.
  induction 1.
  intros H.
  simpl; auto.

  intros H1.
  simpl.
  auto_papprox.
Qed.

Lemma partially_approximated_conc_oideps :
  forall (oid1 oid1' oid2 oid2':oideps),
    partially_approximated_oideps oid1 oid1'
    -> partially_approximated_oideps oid2 oid2'
    -> partially_approximated_oideps (conc_oideps oid1 oid2) (conc_oideps oid1' oid2').
Proof.
  induction 1.
  intros H.
  simpl; auto.

  intros H1.
  simpl.
  auto_papprox.
Qed.











Lemma oival_of_in_strictly_partially_approximated_oitenv :
  forall (oitc oitc':oitenv) (e:expr) (oitu:oitval),
    oival_of oitc' e oitu
    -> strictly_partially_approximated_oitenv oitc oitc'
    -> exists (oitu':oitval), oival_of oitc e oitu'
                              /\ strictly_partially_approximated_oitval oitu' oitu.
Proof.

  intros oitc oitc' e oitu H H_spapprox_oitc.
  revert dependent oitc.
  induction H;
    eauto with oival_of;
    intros oitc H_spapprox_oitc;
    try solve [eexists; split; auto with oival_of;
               apply approximated_oitval_implies_strictly_partially_approximated; auto].

  (* case Ident *)
  apply assoc_ident_in_strictly_partially_approximated_oitenv with (oitc:=oitc) in H; auto.
  inversion_clear H as [oitu' HH].
  inversion_clear HH as [HH1 HH2].
  exists(oitu').
  split; auto.
  apply OIVal_of_Ident; auto.

  (* case Lambda *)
  exists (OIV nil (OIV_ nil (OIV_Closure x e (oitenv_to_oienv oitc)))).
  split; auto with oival_of.
  rewrite H.
  apply SPApprox_oitval; auto_papprox.
  apply strictly_partially_approximated_oitenv_to_oienv; auto.

  (* case Rec *)
  exists (OIV nil (OIV_ nil (OIV_Rec_Closure f x e (oitenv_to_oienv oitc)))).
  split; auto with oival_of.
  rewrite H.
  apply SPApprox_oitval; auto_papprox.
  apply strictly_partially_approximated_oitenv_to_oienv; auto.

  (* case Apply *)

  (** value of e1 *)
  specialize (IHoival_of1 oitc H_spapprox_oitc).
  inversion_clear IHoival_of1 as [oitu1 IHoival_of_1].
  inversion_clear IHoival_of_1 as [IHoival_of_e1 H_oitu1_uu1].
  destruct oitu1 as [oitd1 oiu1].
  destruct oiu1 as [oid1 oiv1].
  inversion H_oitu1_uu1.
  inversion H10.
  clear H5 H6 H7 H9 H11 H12 H13 H15 oitd oiu oitd' oiu' oid oiv oid' oiv'.
  inversion H16.
  rewrite H5 in *; clear H5.
  rewrite H9 in *; clear H9.
  rewrite <-H6 in *; clear H6.
  clear H8 H10 H14 H16 oic' x0 e0 H7 H11.

  (** value of e2 *)
  specialize (IHoival_of2 oitc H_spapprox_oitc).
  inversion_clear IHoival_of2 as [oitu2 IHoival_of_2].
  inversion_clear IHoival_of_2 as [IHoival_of_e2 H_oitu2_uu2].

  (** value of the body *)
  specialize (IHoival_of3 (OITEnv_cons x oitu2 (oienv_to_oitenv oic))).
  assert(IHoival_of_e:=SPApprox_oitenv_cons x oitu2 uu2 (oienv_to_oitenv oic) (oienv_to_oitenv c1)).  
  apply IHoival_of3 in IHoival_of_e; auto;
  [|inversion H_oitu1_uu1; inversion H10; inversion H16; apply strictly_partially_approximated_oienv_to_oitenv; auto].
  clear IHoival_of3.
  inversion_clear IHoival_of_e as [oitu IHoival_of].
  inversion_clear IHoival_of as [IHoival_of_e H_oitu_].
  
  (** application of the Apply rule *)
  destruct oitu2 as [oitd2 oiu2] eqn:H_oitu2; rewrite <-H_oitu2 in *.
  destruct oitu as [oitd oiu] eqn:H_oitu.
  destruct oiu as [oid oiv].
  assert(H_td'_d' := exists_deps_spec_Apply oid1 oitu2).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_Apply].
  exists (OIV (conc_oitdeps oitd1 (conc_oitdeps oitd2 (conc_oitdeps oitd oitd')))
              (OIV_ (conc_oideps oid' oid) oiv)).
  split.
  apply (OIVal_of_Apply oitc oic e1 e2 e x oitu2 _ oiu2 oid oid' oid1 oitd1 oitd2 oitd oitd' oiv); auto.
  inversion H_oitu1_uu1.
  inversion H10.

  assert(H_papprox_oitu2:= strictly_partially_approximated_oitval_implies_partially_approximated
                             oitu2 uu2 H_oitu2_uu2).
  assert(H_td'_d':=deps_spec_Apply_in_partially_approximated oitu2 uu2 oid1 d1 oid' d' oitd' td'
                                             H_deps_spec_Apply H3 H_papprox_oitu2 H14).

  inversion H_td'_d' as [H_td' H_d'].

  rewrite H4; simpl.
  inversion H_oitu_.
  repeat f_equal.
  
  rewrite H1, H_oitu2 in H_oitu2_uu2.
  inversion H_oitu2_uu2.
  inversion H22.
  auto_papprox.

  repeat apply partially_approximated_conc_oitdeps; auto.
  repeat apply partially_approximated_conc_oideps; auto.

  (* case Apply_Rec *)

  (** value of e1 *)
  specialize (IHoival_of1 oitc H_spapprox_oitc).
  inversion_clear IHoival_of1 as [oitu1 IHoival_of_1].
  inversion_clear IHoival_of_1 as [IHoival_of_e1 H_oitu1_uu1].
  destruct oitu1 as [oitd1 oiu1].
  destruct oiu1 as [oid1 oiv1].
  rewrite H0 in H_oitu1_uu1.
  inversion H_oitu1_uu1.
  inversion H11.
  clear H6 H7 H8 H10 H12 H13 H14 H16 oitd oitd' oiu oiu' oid oid' oiv oiv'.
  inversion H17.
  rewrite H6 in *; clear H6.
  rewrite H10 in *; clear H10.
  rewrite H12 in *; clear H12.
  rewrite <-H7 in *; clear H7.
  clear H9 H11 H15 H17 oic' f0 x0 e0 H8 H13.

  (** value of e2 *)
  specialize (IHoival_of2 oitc H_spapprox_oitc).
  inversion_clear IHoival_of2 as [oitu2 IHoival_of_2].
  inversion_clear IHoival_of_2 as [IHoival_of_e2 H_oitu2_uu2].

  (** value of the body *)
  remember (OIV oitd1 (OIV_ oid1 (OIV_Rec_Closure f x e oic))) as oitu1.
  specialize (IHoival_of3 (OITEnv_cons f oitu1 (OITEnv_cons x oitu2 (oienv_to_oitenv oic)))).
  assert(IHoival_of_e:=SPApprox_oitenv_cons f oitu1 uu1 (OITEnv_cons x oitu2 (oienv_to_oitenv oic)) (OITEnv_cons x uu2 (oienv_to_oitenv c1))).
  rewrite <-H0 in H_oitu1_uu1.
  apply IHoival_of3 in IHoival_of_e; auto_papprox;
  [|rewrite H0, Heqoitu1 in H_oitu1_uu1;
     inversion H_oitu1_uu1; inversion H11; inversion H17;
     apply strictly_partially_approximated_oienv_to_oitenv; auto].
  clear IHoival_of3.
  inversion_clear IHoival_of_e as [oitu IHoival_of].
  inversion_clear IHoival_of as [IHoival_of_e H_oitu_].
  
  (** application of the Apply_rec rule *)
  destruct oitu2 as [oitd2 oiu2] eqn:H_oitu2; rewrite <-H_oitu2 in *.
  destruct oitu as [oitd oiu] eqn:H_oitu.
  destruct oiu as [oid oiv].
  assert(H_td'_d' := exists_deps_spec_Apply oid1 oitu2).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_Apply].
  exists (OIV (conc_oitdeps oitd1 (conc_oitdeps oitd2 (conc_oitdeps oitd oitd')))
              (OIV_ (conc_oideps oid' oid) oiv)).
  split.
  apply (OIVal_of_Apply_Rec oitc oic e1 e2 e f x oitu1 oitu2 _ oiu2 oid oid' oid1 oitd1 oitd2 oitd oitd' oiv); auto.
  rewrite H0, Heqoitu1 in H_oitu1_uu1;
  inversion H_oitu1_uu1.
  inversion H11.

  
  assert(H_papprox_oitu2:= strictly_partially_approximated_oitval_implies_partially_approximated
                             oitu2 uu2 H_oitu2_uu2).
  assert(H_td'_d':=deps_spec_Apply_in_partially_approximated oitu2 uu2 oid1 d1 oid' d' oitd' td'
                                             H_deps_spec_Apply H4 H_papprox_oitu2 H15).

  inversion H_td'_d' as [H_td' H_d'].

  rewrite H5; simpl.
  inversion H_oitu_.
  repeat f_equal.
  
  rewrite H3, H_oitu2 in H_oitu2_uu2.
  inversion H_oitu2_uu2.
  inversion H23.
  auto_papprox.

  repeat apply partially_approximated_conc_oitdeps; auto.
  repeat apply partially_approximated_conc_oideps; auto.

  (* case Let_in *)

  (** value of e1 *)
  specialize (IHoival_of1 oitc H_spapprox_oitc).
  inversion_clear IHoival_of1 as [oitu1 IHoival_of_1].
  inversion_clear IHoival_of_1 as [IHoival_of_e1 H_oitu1_uu1].
  destruct oitu1 as [oitd1 oiu1] eqn:H_oitu1.
  destruct oiu1 as [oid1 oiv1] eqn:H_oiu1.
  rewrite H0 in H_oitu1_uu1.
  inversion H_oitu1_uu1.
  clear H3 H4 H5 H7 oitd oitd' oiu oiu'.
  rewrite <-H0, <-H_oitu1 in H_oitu1_uu1.

  (** value of the body *)
  specialize (IHoival_of2 (OITEnv_cons x oitu1 oitc)
                          (SPApprox_oitenv_cons x oitu1 uu1 oitc c H_oitu1_uu1 H_spapprox_oitc)).
  inversion_clear IHoival_of2 as [oitu2 IHHoival_of_e2].
  inversion_clear IHHoival_of_e2 as [IHoival_of_e2 H_oitu2_uu2].
  destruct oitu2 as [oitd2 oiu2] eqn:H_oitu2.
  
  (** application of the Let_in rule *)
  exists (OIV (conc_oitdeps oitd1 oitd2) oiu2).
  split.
  apply OIVal_of_Let_in with (uu1:=oitu1) (uu2:=oitu2) (u1:=oiu1).
  rewrite H_oitu1; auto.
  rewrite H_oiu1; auto.
  rewrite H_oitu2; auto.
  assumption.

  rewrite H2 in H_oitu2_uu2.
  inversion H_oitu2_uu2; auto_papprox.
  repeat apply partially_approximated_conc_oitdeps; auto.

  (* case If true *)
  
  (** value of e *)
  specialize (IHoival_of1 oitc H_spapprox_oitc).
  inversion_clear IHoival_of1 as [oitu IHoival_of_].
  inversion_clear IHoival_of_ as [IHoival_of_e H_oitu_uu].
  destruct oitu as [oitd oiu] eqn:H_oitu.
  destruct oiu as [oid oiv] eqn:H_oiu.
  inversion H_oitu_uu.
  clear H3 H4 H5 H7 oitd0 oitd' oiu0 oiu'.
  remember (OIV td (OIV_ d (OIV_Bool true))) as uu.
  rewrite <-H_oitu in H_oitu_uu.
  destruct oiv; inversion H8;  inversion H10.
  rewrite H13 in *; clear H13.
  clear H3 H4 H5 H9 H12 b0 oid0 oid' oiv oiv'.

  (** value of e1 *)
  specialize (IHoival_of2 oitc H_spapprox_oitc).
  inversion_clear IHoival_of2 as [oitu1 IHoival_of_1].
  inversion_clear IHoival_of_1 as [IHoival_of_e1 H_oitu1_uu1].
  destruct oitu1 as [oitd1 oiu1] eqn:H_oitu1.
  destruct oiu1 as [oid1 oiv1] eqn:H_oiu1.
  rewrite H1 in H_oitu1_uu1.
  inversion H_oitu1_uu1.
  clear H3 H4 H5 H11 oitd0 oitd' oiu0 oiu'.
  rewrite <-H1, <-H_oitu1 in H_oitu1_uu1.

  (** application of the If_true rule *)
  rewrite <-H_oitu1 in IHoival_of_e1.
  assert(H_td'_d' := exists_deps_spec_If oitc e1 e2 oid).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_If].
  exists (OIV (conc_oitdeps oitd' (conc_oitdeps oitd oitd1)) (OIV_ (conc_oideps oid' oid1) oiv1)).

  split.

  apply OIVal_of_If_true with (d:=oid) (uu1:=oitu1); auto.


  assert(H_papprox_oitc:= strictly_partially_approximated_oitenv_implies_partially_approximated
                             oitc c H_spapprox_oitc).
  assert(H_td'_d':=deps_spec_If_in_partially_approximated oitc c e1 e2 oid d oid' d' oitd' td'
                                             H_deps_spec_If H2 H_papprox_oitc H7).
  inversion H_td'_d' as [H_td' H_d'].

  inversion H12.
  auto_papprox.

  repeat apply partially_approximated_conc_oitdeps; auto.
  repeat apply partially_approximated_conc_oideps; auto.

  (* case If false *)
  
  (** value of e *)
  specialize (IHoival_of1 oitc H_spapprox_oitc).
  inversion_clear IHoival_of1 as [oitu IHoival_of_].
  inversion_clear IHoival_of_ as [IHoival_of_e H_oitu_uu].
  destruct oitu as [oitd oiu] eqn:H_oitu.
  destruct oiu as [oid oiv] eqn:H_oiu.
  inversion H_oitu_uu.
  clear H3 H4 H5 H7 oitd0 oitd' oiu0 oiu'.
  remember (OIV td (OIV_ d (OIV_Bool true))) as uu.
  rewrite <-H_oitu in H_oitu_uu.
  destruct oiv; inversion H8;  inversion H10.
  rewrite H13 in *; clear H13.
  clear H3 H4 H5 H9 H12 b0 oid0 oid' oiv oiv'.

  (** value of e2 *)
  specialize (IHoival_of2 oitc H_spapprox_oitc).
  inversion_clear IHoival_of2 as [oitu2 IHoival_of_2].
  inversion_clear IHoival_of_2 as [IHoival_of_e2 H_oitu2_uu2].
  destruct oitu2 as [oitd2 oiu2] eqn:H_oitu2.
  destruct oiu2 as [oid2 oiv2] eqn:H_oiu2.
  rewrite H1 in H_oitu2_uu2.
  inversion H_oitu2_uu2.
  clear H3 H4 H5 H11 oitd0 oitd' oiu0 oiu'.
  rewrite <-H1, <-H_oitu2 in H_oitu2_uu2.

  (** application of the If_false rule *)
  rewrite <-H_oitu2 in IHoival_of_e2.
  assert(H_td'_d' := exists_deps_spec_If oitc e1 e2 oid).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_If].
  exists (OIV (conc_oitdeps oitd' (conc_oitdeps oitd oitd2)) (OIV_ (conc_oideps oid' oid2) oiv2)).

  split.

  apply OIVal_of_If_false with (d:=oid) (uu2:=oitu2); auto.

  assert(H_papprox_oitc:= strictly_partially_approximated_oitenv_implies_partially_approximated
                             oitc c H_spapprox_oitc).
  assert(H_td'_d':=deps_spec_If_in_partially_approximated oitc c e1 e2 oid d oid' d' oitd' td'
                                             H_deps_spec_If H2 H_papprox_oitc H7).
  inversion H_td'_d' as [H_td' H_d'].

  inversion H12.
  auto_papprox.

  repeat apply partially_approximated_conc_oitdeps; auto.
  repeat apply partially_approximated_conc_oideps; auto.

  (* case Match *)
  
  (** value of e *)
  specialize (IHoival_of1 oitc H_spapprox_oitc).
  inversion_clear IHoival_of1 as [oitu IHoival_of_].
  inversion_clear IHoival_of_ as [IHoival_of_e H_oitu_uu].
  destruct oitu as [oitd oiu] eqn:H_oitu.
  destruct oiu as [oid oiv] eqn:H_oiu.
  rewrite H0 in H_oitu_uu.
  inversion H_oitu_uu.
  clear H5 H6 H7 H9 oitd0 oitd' oiu0 oiu'.
  rewrite <-H0, <-H_oitu in H_oitu_uu.

  (** value of e1 *)
  apply is_filtered_strictly_partially_approximated_oitval with (oitu:=oitu) in H1; auto.
  inversion_clear H1 as [c_p' HH].
  inversion_clear HH as [H_is_filtered_oitu H_c_p_c_p'].
  specialize (IHoival_of2 (conc_oitenv c_p' oitc)).
  specialize (IHoival_of2 (strictly_partially_approximated_conc_oitenv _ _ _ _ H_c_p_c_p' H_spapprox_oitc)).
  inversion_clear IHoival_of2 as [oitu1 IHoival_of_1].
  inversion_clear IHoival_of_1 as [IHoival_of_e1 H_oitu1_uu1].
  destruct oitu1 as [oitd1 oiu1] eqn:H_oitu1.
  destruct oiu1 as [oid1 oiv1] eqn:H_oiu1.
  rewrite H3 in H_oitu1_uu1.
  inversion H_oitu1_uu1.
  clear H1 H5 H6 H9 oitd0 oitd' oiu0 oiu'.
  rewrite <-H3, <-H_oitu1 in H_oitu1_uu1.

  (** application of the Match rule *)
  assert(H_td'_d' := exists_deps_spec_Match oitc p x e1 e2 oid).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_Match].
  exists (OIV (conc_oitdeps oitd' (conc_oitdeps oitd oitd1)) (OIV_ (conc_oideps oid' oid1) oiv1)).
  split.
  rewrite <-H_oitu in IHoival_of_e.
  rewrite <-H_oitu1 in IHoival_of_e1.
  apply OIVal_of_Match with (c_p:=c_p') (uu:=oitu) (uu1:=oitu1) (d:=oid) (v:=oiv); auto.

  inversion H10.
  assert(H_papprox_oitc:= strictly_partially_approximated_oitenv_implies_partially_approximated
                             oitc c H_spapprox_oitc).
  assert(H_td'_d':=deps_spec_Match_in_partially_approximated oitc c p x e1 e2 oid d oid' d' oitd' td'
                                             H_deps_spec_Match H4 H_papprox_oitc H9).
  inversion H_td'_d' as [H_td' H_d'].

  inversion H11.
  auto_papprox.

  repeat apply partially_approximated_conc_oitdeps; auto.
  repeat apply partially_approximated_conc_oideps; auto.

  (* case Match_var *)
  
  (** value of e *)
  specialize (IHoival_of1 oitc H_spapprox_oitc).
  inversion_clear IHoival_of1 as [oitu IHoival_of_].
  inversion_clear IHoival_of_ as [IHoival_of_e H_oitu_uu].
  destruct oitu as [oitd oiu] eqn:H_oitu.
  destruct oiu as [oid oiv] eqn:H_oiu.
  rewrite H0 in H_oitu_uu.
  inversion H_oitu_uu.
  clear H5 H6 H7 H9 oitd0 oitd' oiu0 oiu'.
  rewrite <-H0, <-H_oitu in H_oitu_uu.

  (** value of e2 *)
  apply is_not_filtered_strictly_partially_approximated_oitval with (oitu:=oitu) in H1; auto.
  specialize (IHoival_of2 (OITEnv_cons x oitu oitc)).
  simpl in IHoival_of2.
  specialize (IHoival_of2 (SPApprox_oitenv_cons x oitu uu oitc c H_oitu_uu H_spapprox_oitc)).
  inversion_clear IHoival_of2 as [oitu2 IHoival_of_2].
  inversion_clear IHoival_of_2 as [IHoival_of_e2 H_oitu2_uu2].
  destruct oitu2 as [oitd2 oiu2] eqn:H_oitu2.
  destruct oiu2 as [oid2 oiv2] eqn:H_oiu2.
  rewrite H3 in H_oitu2_uu2.
  inversion H_oitu2_uu2.
  clear H5 H6 H7 H11 oitd0 oitd' oiu0 oiu'.
  rewrite <-H3, <-H_oitu2 in H_oitu2_uu2.

  (** application of the Match rule *)
  assert(H_td'_d' := exists_deps_spec_Match oitc p x e1 e2 oid).
  inversion_clear H_td'_d' as [oitd' H_d'].
  inversion_clear H_d' as [oid' H_deps_spec_Match].
  exists (OIV (conc_oitdeps oitd' (conc_oitdeps oitd oitd2)) (OIV_ (conc_oideps oid' oid2) oiv2)).
  split.
  rewrite <-H_oitu in IHoival_of_e.
  rewrite <-H_oitu2 in IHoival_of_e2.
  apply OIVal_of_Match_var with (uu:=oitu) (uu2:=oitu2) (d:=oid) (v:=oiv); auto.

  inversion H10.
  assert(H_papprox_oitc:= strictly_partially_approximated_oitenv_implies_partially_approximated
                             oitc c H_spapprox_oitc).
  assert(H_td'_d':=deps_spec_Match_in_partially_approximated oitc c p x e1 e2 oid d oid' d' oitd' td'
                                             H_deps_spec_Match H4 H_papprox_oitc H11).
  inversion H_td'_d' as [H_td' H_d'].

  inversion H12.
  auto_papprox.

  repeat apply partially_approximated_conc_oitdeps; auto.
  repeat apply partially_approximated_conc_oideps; auto.

  (* case Constr1 *)
  specialize (IHoival_of oitc H_spapprox_oitc).
  inversion_clear IHoival_of as [oitu IHoival_of_].
  inversion_clear IHoival_of_ as [IHoival_of_e H_oitu_uu].
  destruct oitu as [oitd oiu].
  exists (OIV oitd (OIV_ nil (OIV_Constr1 n oiu))).
  split; auto with oival_of.
  simpl.
  inversion_clear H_oitu_uu; auto_papprox.

  (* case Couple *)
  specialize (IHoival_of1 oitc H_spapprox_oitc).
  inversion_clear IHoival_of1 as [oitu1 IHoival_of_1].
  inversion_clear IHoival_of_1 as [IHoival_of_e1 H_oitu1_uu1].
  destruct oitu1 as [oitd1 oiu1].
  specialize (IHoival_of2 oitc H_spapprox_oitc).
  inversion_clear IHoival_of2 as [oitu2 IHoival_of_2].
  inversion_clear IHoival_of_2 as [IHoival_of_e2 H_oitu2_uu2].
  destruct oitu2 as [oitd2 oiu2].
  exists (OIV (conc_oitdeps oitd1 oitd2) (OIV_ nil (OIV_Couple oiu1 oiu2))).
  split; auto with oival_of.
  simpl.
  inversion_clear H_oitu1_uu1; inversion_clear H_oitu2_uu2; auto_papprox.
  apply partially_approximated_conc_oitdeps; auto.  

  (* case Annot *)
  specialize (IHoival_of oitc H_spapprox_oitc).
  inversion_clear IHoival_of as [oitu IHoival_of_].
  inversion_clear IHoival_of_ as [IHoival_of_e H_oitu_uu].
  destruct oitu as [oitd oiu].
  destruct oiu as [oid oiv].
  exists (OIV oitd (OIV_ ((l, fun x : val => x) :: oid)%list oiv)).
  split; auto with oival_of.
  simpl.
  inversion_clear H_oitu_uu. 
  inversion_clear H1.
  auto_papprox.
  apply PApprox_oideps_fun.
  apply partially_approximated_val_refl.
Qed.



Lemma oival_of_in_approximated_oitenv_via_itenv :
  forall (oitc:oitenv) (e:expr) (oitu:oitval),
    oival_of (itenv_to_oitenv (oitenv_to_itenv oitc)) e oitu
    -> exists (oitu':oitval), oival_of oitc e oitu'
                              /\ strictly_partially_approximated_oitval oitu' oitu.
Proof.
  intros oitc e oitu H.
  remember (itenv_to_oitenv (oitenv_to_itenv oitc)) as oitc_.

  apply oival_of_in_strictly_partially_approximated_oitenv with (oitc':=oitc_); auto.
  apply approximated_oitenv_implies_strictly_partially_approximated; auto.
Qed.


