
Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import instrumented_values.
Require Import instrumented_semantics.

Require Import itval_val_conversion.

Require Import ensembles.

Require Import instrumented_multiple_values.
Require Import instrumented_multiple_semantics.

Require Import collecting_values.
Require Import collecting_semantics.

Require Import ctval_imval_conversion.

Require Import imval_order.



Lemma assoc_ident_in_imenv_to_ctenv :
  forall (imc:imenv) (ctc:ctenv)
         (x:identifier)
         (ctv:ctval) (itc:itenv) (itu:itval),
  imenv_to_ctenv imc ctc
  -> assoc_ident_in_ctenv x ctc = Ident_in_ctenv ctv
  -> In itenv imc itc
  -> assoc_ident_in_itenv x itc = Ident_in_itenv itu
  -> exists itu2 : itval, ctval_to_imval ctv itu2 /\ le_itval itu itu2.
Proof.
  intros imc ctc x ctv itc itu H_imc_ctc H_assoc_in_ctc H_itc_in_imc H_assoc_in_itc.
  revert dependent imc.
  revert dependent itc.
  induction ctc.
  (*** ctc is empty *)
  inversion H_assoc_in_ctc.
  (*** ctc is not empty *)
  intros itc H_assoc_in_itc imc H_imc_ctc H_itc_in_imc.
  simpl in H_assoc_in_ctc.
  destruct (beq_identifier x x0) eqn:H_x_x0.

  (**** x is the first identifier in ctc *)
  clear IHctc (* unused hypothesis *).
  (***** rewrite redondant notations *)
  rewrite <-(beq_identifier_eq _ _ H_x_x0) in H_imc_ctc.
  clear dependent x0.
  inversion H_assoc_in_ctc.
  rewrite H0 in H_imc_ctc.
  clear dependent ctv0.

  inversion H_imc_ctc.
  (***** rewrite redondant notations *)
  clear dependent imc0.
  clear dependent x0.
  clear dependent ctv0.
  clear dependent ctc'.

  (***** deduct the form of itc *)
  assert(HHH_itc_in_imc:=H_itc_in_imc).
  apply H2 in H_itc_in_imc.
  unfold In, SetMap2 in H_itc_in_imc.
  destruct itc as [|x' itu' itc'] eqn:H_itc; try solve [inversion H_assoc_in_itc].
  inversion_clear H_itc_in_imc as [itu'' HH].
  inversion_clear HH as [itc'' HHH].
  inversion_clear HHH as [HH HHHH].
  inversion_clear HHHH as [H_itu'_in_imv H_itc'_in_imc'].
  inversion HH.
  rewrite H0, <-H1, <-H5 in *.
  clear dependent x'.
  clear dependent itu''.
  clear dependent itc''.
  simpl in H_assoc_in_itc.
  rewrite (eq_beq_identifier x x eq_refl) in H_assoc_in_itc.
  inversion H_assoc_in_itc.
  rewrite H0 in *.
  clear dependent itu'.

  destruct itu as [itd iu] eqn:H_itu.
  destruct iu as [id iv].

  exists (IV td (IV_ d iv)).
  split.
  rewrite H3.
  simpl.
  unfold SetMap.
  exists iv; split; auto.
  apply H7.
  unfold In.

  unfold SetMap.
  exists (IV itd (IV_ id iv)); auto.

  tac_le_itval.
  intros l H.
  inversion H4.
  specialize (H0 l).
  apply H0.
  exists itd, id, iv; auto.

  intros l H.
  inversion H6.
  specialize (H0 l).
  apply H0.
  exists itd, id, iv; auto.

  apply le_ival0_refl.

  (**** x is not the first identifier in ctc *)
  inversion H_imc_ctc.
  clear dependent imc0.
  clear dependent x1.
  clear dependent ctv1.
  clear dependent ctc'.

  (***** deduct the form of itc *)
  apply H2 in H_itc_in_imc.
  unfold In in H_itc_in_imc.
  destruct itc; try solve [inversion H_assoc_in_itc].
  inversion_clear H_itc_in_imc as [itu'' HH].
  inversion_clear HH as [itc'' HHH].
  inversion_clear HHH as [HH HHHH].
  inversion_clear HHHH as [H_itu'_in_imv H_itc'_in_imc'].
  inversion HH.
  rewrite H0, <-H1, <-H5 in *.
  clear dependent x1.
  clear dependent itu''.
  clear dependent itc''.

  simpl in H_assoc_in_itc.
  rewrite H_x_x0 in H_assoc_in_itc.

  specialize (IHctc H_assoc_in_ctc itc H_assoc_in_itc imc' H8 H_itc'_in_imc').
  assumption.
Qed.

Lemma assoc_ident_not_in_imenv_to_ctenv :
  forall (imc:imenv) (ctc:ctenv) (x:identifier) (itc:itenv),
  imenv_to_ctenv imc ctc
  -> assoc_ident_in_ctenv x ctc = Ident_not_in_ctenv
  -> In itenv imc itc
  -> assoc_ident_in_itenv x itc = Ident_not_in_itenv.
Proof.
  intros imc ctc x itc H H0 H1.
  revert dependent x.
  revert dependent itc.
  induction H;
    try rename x into x';
    intros itc H_itc_in_imc x H_assoc_in_ctc.

  rewrite H in H_itc_in_imc.
  inversion H_itc_in_imc; auto.

  rewrite (Extensionality_Ensembles _ _ _ H) in H_itc_in_imc.
  inversion_clear H_itc_in_imc as [itu HH].
  inversion_clear HH as [itc' HHH].
  inversion_clear HHH.
  inversion_clear H6.
  rewrite H5.
  simpl.

  inversion H_assoc_in_ctc.
  destruct (beq_identifier x x');
    try solve [inversion H9].
  auto.
Qed.


Lemma imenv_to_ctenv_to_imenv_increasing :
  forall (imc:imenv) (ctc:ctenv),
    imenv_to_ctenv imc ctc
    -> le_imenv imc (ctenv_to_imenv ctc).
Proof.
  induction 1.

  rewrite H.
  intros itc H_itc_in.
  inversion H_itc_in.
  simpl.
  exists ITEnv_empty.
  unfold In.
  split.
  apply In_singleton.
  tac_le_itval.


  intros itc H_itc_in_imc.
  unfold Same_set, SetMap2 in H.
  apply H in H_itc_in_imc.
  inversion_clear H_itc_in_imc as [itu HH].
  inversion_clear HH as [itc' HHH].
  inversion_clear HHH as [H_itc HH].
  inversion_clear HH as [H_itu_in_imv H_itc'_in_imc'].
  
  specialize (IHimenv_to_ctenv itc' H_itc'_in_imc').
  inversion_clear IHimenv_to_ctenv as [itc'2 HH].
  inversion_clear HH as [H_itc'2_in H_itc'_itc'2].

  rewrite H0.
  simpl.
  unfold In, SetMap2.
  destruct itu as [itd iu].
  destruct iu as [id iv].

  exists (ITEnv_cons x (IV td (IV_ d iv)) itc'2).
  split.

  exists iv, itc'2.
  repeat split; auto.
  apply H3.
  unfold In.
  exists (IV itd (IV_ id iv)); auto.

  rewrite H_itc.
  tac_le_itval.
  
  intros l H_l.
  inversion_clear H1.
  apply H5.
  exists itd, id, iv; auto.

  intros l H_l.
  inversion_clear H2.
  apply H5.
  exists itd, id, iv; auto.

  apply le_ival0_refl.

  assumption.
Qed.



Lemma label_in_conc_itdeps_1 :
  forall (l:label) (itd1 itd2:itdeps),
  List.In l itd1
  -> List.In l (conc_itdeps itd1 itd2).
Proof.
  induction itd1; intros itd2 H.

  inversion H.

  simpl.
  simpl in H.
  inversion H.
  left; auto.
  right; auto.
Qed.

Lemma label_in_conc_itdeps_2 :
  forall (l:label) (itd1 itd2:itdeps),
  List.In l itd2
  -> List.In l (conc_itdeps itd1 itd2).
Proof.
  induction itd1; intros itd2 H.

  simpl; assumption.

  simpl; auto.
Qed.

Lemma conc_itdeps_included :
  forall (itd1 itd1' itd2 itd2':itdeps),
    list_Included itd1 itd1'
    -> list_Included itd2 itd2'
    -> list_Included (conc_itdeps itd1 itd2) (conc_itdeps itd1' itd2').
Proof.
  induction itd1; intros itd1' itd2 itd2' H_incl_itd1_itd1' H_incl_itd2_itd2' l H_l_in_conc.

  simpl in H_l_in_conc.
  specialize (H_incl_itd2_itd2' l H_l_in_conc).
  apply label_in_conc_itdeps_2; auto.


  inversion H_l_in_conc.
  apply label_in_conc_itdeps_1.
  apply H_incl_itd1_itd1'.
  simpl; auto.

  unfold list_Included in IHitd1 at 3.
  apply IHitd1 with (itd2:=itd2); auto.

  unfold list_Included in H_incl_itd1_itd1'.
  intros l' H_l'_in_itd1.
  apply H_incl_itd1_itd1'.
  right; assumption.
Qed.

Lemma included_in_conc_itdeps_1 :
  forall (itd itd1 itd2:itdeps),
    list_Included itd itd1
    -> list_Included itd (conc_itdeps itd1 itd2).
Proof.
  intros itd itd1 itd2 H.
  intros l H_l.
  apply label_in_conc_itdeps_1; auto.
Qed.

Lemma included_in_conc_itdeps_2 :
  forall (itd itd1 itd2:itdeps),
    list_Included itd itd2
    -> list_Included itd (conc_itdeps itd1 itd2).
Proof.
  intros itd itd1 itd2 H.
  intros l H_l.
  apply label_in_conc_itdeps_2; auto.
Qed.

Lemma label_in_conc_ideps_1 :
  forall (l:label) (id1 id2:ideps),
  List.In l id1
  -> List.In l (conc_ideps id1 id2).
Proof.
  induction id1; intros id2 H.

  inversion H.

  simpl.
  simpl in H.
  inversion H.
  left; auto.
  right; auto.
Qed.

Lemma label_in_conc_ideps_2 :
  forall (l:label) (id1 id2:ideps),
  List.In l id2
  -> List.In l (conc_ideps id1 id2).
Proof.
  induction id1; intros id2 H.

  simpl; assumption.

  simpl; auto.
Qed.

Lemma conc_ideps_included :
  forall (id1 id1' id2 id2':ideps),
    list_Included id1 id1'
    -> list_Included id2 id2'
    -> list_Included (conc_ideps id1 id2) (conc_ideps id1' id2').
Proof.
  induction id1; intros id1' id2 id2' H_incl_id1_id1' H_incl_id2_id2' l H_l_in_conc.

  simpl in H_l_in_conc.
  specialize (H_incl_id2_id2' l H_l_in_conc).
  apply label_in_conc_ideps_2; auto.


  inversion H_l_in_conc.
  apply label_in_conc_ideps_1.
  apply H_incl_id1_id1'.
  simpl; auto.

  unfold list_Included in IHid1 at 3.
  apply IHid1 with (id2:=id2); auto.

  unfold list_Included in H_incl_id1_id1'.
  intros l' H_l'_in_id1.
  apply H_incl_id1_id1'.
  right; assumption.
Qed.


Lemma assoc_in_le_itenv :
  forall (itc itc_2:itenv) (x:identifier) (itu:itval),
    le_itenv itc itc_2
    -> assoc_ident_in_itenv x itc = Ident_in_itenv itu
    -> exists (itu_2:itval), assoc_ident_in_itenv x itc_2 = Ident_in_itenv itu_2
                            /\ le_itval itu itu_2.
Proof.
  induction itc;
  intros itc0_2 x' itu H_le_itc_itc_2 H_assoc_in_itc.

  inversion H_assoc_in_itc.

  inversion H_le_itc_itc_2 as [|x0 uu' uu_2 itc' itc_2].
  clear dependent x0.
  clear dependent uu'.
  clear dependent itc'.

  simpl in H_assoc_in_itc.
  simpl.
  destruct (beq_identifier x' x).

  inversion H_assoc_in_itc.
  rewrite <-H0.
  eexists; split; auto.

  specialize (IHitc itc_2 x' itu H4 H_assoc_in_itc).
  inversion_clear IHitc as [itu_2 HH].
  inversion HH as [H_assoc_in_itc_2 H_le_itu_itu_2].

  exists itu_2; auto.
Qed.

Lemma is_filtered_le_itval :
  forall (itu itu_2:itval) (p:pattern) (itc_p:itenv),
    le_itval itu itu_2
    -> is_filtered_itval itu p = Filtered_itval_result_Match itc_p
    -> exists (itc_p_2:itenv),
         is_filtered_itval itu_2 p = Filtered_itval_result_Match itc_p_2
         /\ le_itenv itc_p itc_p_2.
Proof.
  intros itu itu_2 p.
  induction itu_2 as [itd_2 iu_2];
  induction iu_2 as [id_2 iv_2];
  induction itu as [itd iu];
  induction iu as [id iv];
  induction iv;
  induction p;
  intros itc_p H_le_itu_itu_2 H_is_filtered_itu;
  try solve [inversion H_is_filtered_itu];
  simpl in H_is_filtered_itu.

  inversion H_le_itu_itu_2.
  inversion H4.
  inversion H10.
  simpl.
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H_is_filtered_itu.
  exists ITEnv_empty.
  split; tac_le_itval; auto.

  inversion H_le_itu_itu_2.
  inversion H4.
  inversion H10.
  simpl.
  destruct (eq_nat_dec n c) eqn:H_n_c; inversion H_is_filtered_itu.
  exists (ITEnv_cons i (IV nil itu') ITEnv_empty).
  split; tac_le_itval; auto.

  inversion H_le_itu_itu_2.
  inversion H4.
  inversion H10.
  simpl.
  exists (ITEnv_cons i (IV nil itu1') (ITEnv_cons i0 (IV nil itu2') ITEnv_empty)).
  inversion H_is_filtered_itu.
  split; tac_le_itval; auto.
Qed.

Lemma is_not_filtered_le_itval :
  forall (itu itu_2:itval) (p:pattern),
    le_itval itu itu_2
    -> is_filtered_itval itu p = Filtered_itval_result_Match_var
    -> is_filtered_itval itu_2 p = Filtered_itval_result_Match_var.
Proof.
  intros itu itu_2 p.
  induction itu_2 as [itd_2 iu_2];
  induction iu_2 as [id_2 iv_2];
  induction itu as [itd iu];
  induction iu as [id iv];
  induction iv;
  induction p;
  intros H_le_itu_itu_2 H_is_filtered_itu;
  try solve [inversion H_is_filtered_itu];
  simpl in H_is_filtered_itu;

  try solve [
  inversion H_le_itu_itu_2;
  inversion H4;
  inversion H10;
  simpl;
  try (destruct (eq_nat_dec n c) eqn:H_n_c; inversion H_is_filtered_itu);
  auto].
Qed.  
  


Lemma le_itenv_conc :
  forall (itc1 itc1_2 itc2 itc2_2:itenv),
    le_itenv itc1 itc1_2
    -> le_itenv itc2 itc2_2
    -> le_itenv (conc_itenv itc1 itc2) (conc_itenv itc1_2 itc2_2).
Proof.
  induction itc1; intros itc1_2 itc2 itc2_2 H_le_itc1_itc1_2 H_le_itc2_itc2_2.

  inversion H_le_itc1_itc1_2.
  simpl; auto.

  inversion H_le_itc1_itc1_2.
  simpl.
  tac_le_itval; auto.
Qed.

Lemma ival_of_in_le_itenv :
  forall (itc itc2:itenv) (e:expr) (itu:itval),
    le_itenv itc itc2
    -> ival_of itc e itu
    -> exists (itu2:itval),
         ival_of itc2 e itu2
         /\ le_itval itu itu2.
Proof.
  intros itc itc2 e itu H H_ival_of.
  revert dependent itc2.
  induction H_ival_of; intros itc2 H_le_itenv.

  (* case Num *)
  eexists; split; auto with ival_of; tac_le_itval.

  (* case Ident *)
  apply assoc_in_le_itenv with (itc_2:=itc2) in H; auto.
  inversion_clear H as [itu2 HH].
  inversion_clear HH as [H_assoc H_le_itval].
  exists itu2.
  split; auto.
  apply IVal_of_Ident; auto.

  (* case Lambda *)
  exists (IV nil (IV_ nil (IV_Closure x e (itenv_to_ienv itc2)))).
  rewrite H.
  split; tac_le_itval.
  apply IVal_of_Lambda; auto.
  apply le_itenv_to_ienv; auto.

  (* case Rec *)
  exists (IV nil (IV_ nil (IV_Rec_Closure f x e (itenv_to_ienv itc2)))).
  rewrite H.
  split; tac_le_itval.
  apply IVal_of_Rec; auto.
  apply le_itenv_to_ienv; auto.

  (* case Apply *)
  specialize (IHH_ival_of1 itc2 H_le_itenv).
  inversion_clear IHH_ival_of1 as [itu1_2 HH].
  inversion_clear HH as [H_ival_of_e1 H_le_itu1_itu1_2].
  destruct itu1_2 as [itd1_2 iu1_2].
  inversion_clear H_le_itu1_itu1_2 as [H_unused1 H_unused2 H_unused3 H_unused4 H_td1_itd1_2 H_le_iu1_iu1_2].
  destruct iu1_2 as [id1_2 iv1_2].
  inversion_clear H_le_iu1_iu1_2 as [H_unused1 H_unused2 H_unused3 H_unused4 H_d1_id1_2 H_le_iv1_iv1_2].
  inversion H_le_iv1_iv1_2 as [ | | | | | x1_2 e1_2 ic1 ic1_2 H_le_ic1_ic1_2 | ].
  clear dependent x1_2.
  clear dependent e1_2.
  clear dependent ic1.
  rewrite <-H1 in H_ival_of_e1.

  specialize (IHH_ival_of2 itc2 H_le_itenv).
  inversion_clear IHH_ival_of2 as [itu2_2 HH].
  inversion_clear HH as [H_ival_of_e2 H_le_itu2_itu2_2].
  destruct itu2_2 as [itd2_2 iu2_2] eqn:H_itu2_2.
  rewrite <-H_itu2_2 in H_ival_of_e2.

  specialize (IHH_ival_of3 (ITEnv_cons x itu2_2 (ienv_to_itenv ic1_2))).
  elim IHH_ival_of3.
  intros itu_2 HH.
  inversion_clear HH as [H_ival_of_e H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].
  exists (IV (conc_itdeps itd1_2 (conc_itdeps itd2_2 (conc_itdeps itd_2 id1_2)))
             (IV_ (conc_ideps id1_2 id_2) iv_2)).
  split.
  apply (IVal_of_Apply _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H_ival_of_e1 H_ival_of_e2 H_itu2_2 H_ival_of_e); auto.

  rewrite H0.
  tac_le_itval.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=itd1_2) (itd2':=conc_itdeps itd2_2 (conc_itdeps itd_2 id1_2)) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd2_2) (itd2':=conc_itdeps itd_2 id1_2) in H_l'; auto.
  rewrite H in H_le_itu2_itu2_2.
  inversion_clear H_le_itu2_itu2_2; auto.
  intros l'' H_l''.
  apply conc_itdeps_included with (itd1':=itd_2) (itd2':=id1_2) in H_l''; auto.
  inversion H_le_itu_itu_2; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id1_2) (id2':=id_2) in H_l; auto.
  inversion H_le_itu_itu_2; auto.
  inversion H7; auto.

  inversion H_le_itu_itu_2; auto.
  inversion H7; auto.

  tac_le_itval.
  rewrite H_itu2_2; auto.
  apply le_ienv_to_itenv; auto.

  (* case Apply_rec *)
  specialize (IHH_ival_of1 itc2 H_le_itenv).
  inversion_clear IHH_ival_of1 as [itu1_2 HH].
  inversion_clear HH as [H_ival_of_e1 H_le_itu1_itu1_2].
  destruct itu1_2 as [itd1_2 iu1_2] eqn:H_itu1_2.
  rewrite H in H_le_itu1_itu1_2.
  inversion_clear H_le_itu1_itu1_2 as [H_unused1 H_unused2 H_unused3 H_unused4 H_td1_itd1_2 H_le_iu1_iu1_2].
  destruct iu1_2 as [id1_2 iv1_2].
  inversion_clear H_le_iu1_iu1_2 as [H_unused1 H_unused2 H_unused3 H_unused4 H_d1_id1_2 H_le_iv1_iv1_2].
  inversion H_le_iv1_iv1_2 as [ | | | | | | f1_2 x1_2 e1_2 ic1 ic1_2 H_le_ic1_ic1_2 ].
  clear dependent f1_2.
  clear dependent x1_2.
  clear dependent e1_2.
  clear dependent ic1.
  rewrite <-H2 in H_ival_of_e1.

  specialize (IHH_ival_of2 itc2 H_le_itenv).
  inversion_clear IHH_ival_of2 as [itu2_2 HH].
  inversion_clear HH as [H_ival_of_e2 H_le_itu2_itu2_2].
  destruct itu2_2 as [itd2_2 iu2_2] eqn:H_itu2_2.
  rewrite <-H_itu2_2 in H_ival_of_e2.

  specialize (IHH_ival_of3 (ITEnv_cons f (IV itd1_2 (IV_ id1_2 (IV_Rec_Closure f x e ic1_2))) (ITEnv_cons x itu2_2 (ienv_to_itenv ic1_2)))).
  elim IHH_ival_of3.
  intros itu_2 HH.
  inversion_clear HH as [H_ival_of_e H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].
  exists (IV (conc_itdeps itd1_2 (conc_itdeps itd2_2 (conc_itdeps itd_2 id1_2)))
             (IV_ (conc_ideps id1_2 id_2) iv_2)).
  split.
  apply (IVal_of_Apply_Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H_ival_of_e1 eq_refl H_ival_of_e2 H_ival_of_e H_itu2_2); auto.

  rewrite H1.
  tac_le_itval.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=itd1_2) (itd2':=conc_itdeps itd2_2 (conc_itdeps itd_2 id1_2)) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd2_2) (itd2':=conc_itdeps itd_2 id1_2) in H_l'; auto.
  rewrite H0 in H_le_itu2_itu2_2.
  inversion_clear H_le_itu2_itu2_2; auto.
  intros l'' H_l''.
  apply conc_itdeps_included with (itd1':=itd_2) (itd2':=id1_2) in H_l''; auto.
  inversion H_le_itu_itu_2; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id1_2) (id2':=id_2) in H_l; auto.
  inversion H_le_itu_itu_2; auto.
  inversion H8; auto.

  inversion H_le_itu_itu_2; auto.
  inversion H8; auto.

  rewrite H.
  tac_le_itval; auto.
  rewrite H_itu2_2; auto.
  apply le_ienv_to_itenv; auto.

  (* case Let_in *)
  specialize (IHH_ival_of1 itc2 H_le_itenv).
  inversion_clear IHH_ival_of1 as [itu1_2 HH].
  inversion_clear HH as [H_ival_of_e1 H_le_itu1_itu1_2].
  destruct itu1_2 as [itd1_2 iu1_2] eqn:H_itu1_2.

  specialize (IHH_ival_of2 (ITEnv_cons x itu1_2 itc2)).
  elim IHH_ival_of2.
  intros itu2_2 HH.
  inversion_clear HH as [H_ival_of_e2 H_le_itu2_itu2_2].
  destruct itu2_2 as [itd2_2 iu2_2] eqn:H_itu2_2.

  exists (IV (conc_itdeps itd1_2 itd2_2) iu2_2).
  split.
  eapply IVal_of_Let_in; auto.
  apply H_ival_of_e1.
  rewrite H_itu1_2 in H_ival_of_e2.
  apply H_ival_of_e2.
  tac_le_itval.

  intros l H_l.
  apply conc_itdeps_included with (itd1':=itd1_2) (itd2':=itd2_2) in H_l; auto.
  rewrite H in H_le_itu1_itu1_2.
  inversion_clear H_le_itu1_itu1_2; auto.
  rewrite H0 in H_le_itu2_itu2_2.
  inversion_clear H_le_itu2_itu2_2; auto.
  rewrite H0 in H_le_itu2_itu2_2.
  inversion_clear H_le_itu2_itu2_2; auto.

  tac_le_itval; auto.
  rewrite H_itu1_2; auto.

  (* case If_true *)
  (** specialize induction hypothesis *)
  specialize (IHH_ival_of1 itc2 H_le_itenv).
  inversion_clear IHH_ival_of1 as [itu_2 HH].
  inversion_clear HH as [H_ival_of_e H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2] eqn:H_itu_2.
  destruct iu_2 as [id_2 iv_2].

  specialize (IHH_ival_of2 itc2 H_le_itenv).
  inversion_clear IHH_ival_of2 as [itu1_2 HH].
  inversion_clear HH as [H_ival_of_e1 H_le_itu1_itu1_2].
  destruct itu1_2 as [itd1_2 iu1_2] eqn:H_itu1_2.
  destruct iu1_2 as [id1_2 iv1_2].

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_td_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_d_id_2 H_le_iv_iv_2].
  inversion H_le_iv_iv_2 as [ | b H_b H_iv_2 | | | | | ].
  clear dependent b.

  rewrite H in H_le_itu1_itu1_2.
  inversion_clear H_le_itu1_itu1_2 as [uH1 uH2 uH3 uH4 H_td1_itd1_2 H_le_iu1_iu1_2].
  inversion_clear H_le_iu1_iu1_2 as [uH1 uH2 uH3 uH4 H_d1_id1_2 H_le_iv1_iv1_2].

  exists (IV (conc_itdeps id_2 (conc_itdeps itd_2 itd1_2)) (IV_ (conc_ideps id_2 id1_2) iv1_2)).
  split.

  apply IVal_of_If_true with (uu1:=itu1_2); auto.

  rewrite <-H_iv_2 in H_ival_of_e; auto.

  rewrite H_itu1_2; auto.

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=id_2) (itd2':=conc_itdeps itd_2 itd1_2) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd_2) (itd2':=itd1_2) in H_l'; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id_2) (id2':=id1_2) in H_l; auto.

  (* case If_false *)
  (** specialize induction hypothesis *)
  specialize (IHH_ival_of1 itc2 H_le_itenv).
  inversion_clear IHH_ival_of1 as [itu_2 HH].
  inversion_clear HH as [H_ival_of_e H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2] eqn:H_itu_2.
  destruct iu_2 as [id_2 iv_2].

  specialize (IHH_ival_of2 itc2 H_le_itenv).
  inversion_clear IHH_ival_of2 as [itu2_2 HH].
  inversion_clear HH as [H_ival_of_e2 H_le_itu2_itu2_2].
  destruct itu2_2 as [itd2_2 iu2_2] eqn:H_itu2_2.
  destruct iu2_2 as [id2_2 iv2_2].

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_td_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_d_id_2 H_le_iv_iv_2].
  inversion H_le_iv_iv_2 as [ | b H_b H_iv_2 | | | | | ].
  clear dependent b.

  rewrite H in H_le_itu2_itu2_2.
  inversion_clear H_le_itu2_itu2_2 as [uH1 uH2 uH3 uH4 H_td2_itd2_2 H_le_iu2_iu2_2].
  inversion_clear H_le_iu2_iu2_2 as [uH1 uH2 uH3 uH4 H_d2_id2_2 H_le_iv2_iv2_2].

  exists (IV (conc_itdeps id_2 (conc_itdeps itd_2 itd2_2)) (IV_ (conc_ideps id_2 id2_2) iv2_2)).
  split.

  apply IVal_of_If_false with (uu2:=itu2_2); auto.

  rewrite <-H_iv_2 in H_ival_of_e; auto.

  rewrite H_itu2_2; auto.

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=id_2) (itd2':=conc_itdeps itd_2 itd2_2) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd_2) (itd2':=itd2_2) in H_l'; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id_2) (id2':=id2_2) in H_l; auto.

  (* case Match *)
  (** specialize induction hypothesis *)
  specialize (IHH_ival_of1 itc2 H_le_itenv).
  inversion_clear IHH_ival_of1 as [itu_2 HH].
  inversion_clear HH as [H_ival_of_e H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2] eqn:H_itu_2.
  destruct iu_2 as [id_2 iv_2].

  rewrite <-H_itu_2 in H_le_itu_itu_2.
  assert(HH_is_filtered_itu_2 := is_filtered_le_itval uu itu_2 p c_p H_le_itu_itu_2 H0).
  inversion_clear HH_is_filtered_itu_2 as [itc_p_2 HH].
  inversion_clear HH as [H_is_filtered_itu_2 H_le_c_p_itc_p_2].

  specialize (IHH_ival_of2 (conc_itenv itc_p_2 itc2)).
  elim IHH_ival_of2.
  intros itu1_2 HH.
  inversion_clear HH as [H_ival_of_e1 H_le_itu1_itu1_2].
  destruct itu1_2 as [itd1_2 iu1_2] eqn:H_itu1_2.
  destruct iu1_2 as [id1_2 iv1_2].
  clear IHH_ival_of2.

  exists (IV (conc_itdeps id_2 (conc_itdeps itd_2 itd1_2)) (IV_ (conc_ideps id_2 id1_2) iv1_2)).
  split.

  apply IVal_of_Match with (c_p:=itc_p_2) (uu:=itu_2) (uu1:=itu1_2) (v:=iv_2); auto.
  rewrite H_itu_2; auto.
  rewrite H_itu1_2; auto.

  (** inverse le_itval relations *)
  rewrite H, H_itu_2 in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_td_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_d_id_2 H_le_iv_iv_2].

  rewrite H1 in H_le_itu1_itu1_2.
  inversion_clear H_le_itu1_itu1_2 as [uH1 uH2 uH3 uH4 H_td1_itd1_2 H_le_iu1_iu1_2].
  inversion_clear H_le_iu1_iu1_2 as [uH1 uH2 uH3 uH4 H_d1_id1_2 H_le_iv1_iv1_2].

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=id_2) (itd2':=conc_itdeps itd_2 itd1_2) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd_2) (itd2':=itd1_2) in H_l'; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id_2) (id2':=id1_2) in H_l; auto.

  apply le_itenv_conc; auto.

  (* case Match_var *)
  (** specialize induction hypothesis *)
  specialize (IHH_ival_of1 itc2 H_le_itenv).
  inversion_clear IHH_ival_of1 as [itu_2 HH].
  inversion_clear HH as [H_ival_of_e H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2] eqn:H_itu_2.
  destruct iu_2 as [id_2 iv_2].

  specialize (IHH_ival_of2 (ITEnv_cons x itu_2 itc2)).
  elim IHH_ival_of2.
  intros itu2_2 HH.
  inversion_clear HH as [H_ival_of_e2 H_le_itu2_itu2_2].
  destruct itu2_2 as [itd2_2 iu2_2] eqn:H_itu2_2.
  destruct iu2_2 as [id2_2 iv2_2].
  clear IHH_ival_of2.

  exists (IV (conc_itdeps id_2 (conc_itdeps itd_2 itd2_2)) (IV_ (conc_ideps id_2 id2_2) iv2_2)).
  split.

  apply IVal_of_Match_var with (uu:=itu_2) (uu2:=itu2_2) (v:=iv_2);
  try rewrite H_itu_2 in *; try rewrite H_itu2_2 in *; auto.

  apply is_not_filtered_le_itval with (itu:=uu); auto.

  (** inverse le_itval relations *)
  rewrite H in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_td_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_d_id_2 H_le_iv_iv_2].

  rewrite H1 in H_le_itu2_itu2_2.
  inversion_clear H_le_itu2_itu2_2 as [uH1 uH2 uH3 uH4 H_td2_itd2_2 H_le_iu2_iu2_2].
  inversion_clear H_le_iu2_iu2_2 as [uH1 uH2 uH3 uH4 H_d2_id2_2 H_le_iv2_iv2_2].

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=id_2) (itd2':=conc_itdeps itd_2 itd2_2) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd_2) (itd2':=itd2_2) in H_l'; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id_2) (id2':=id2_2) in H_l; auto.

  tac_le_itval; auto.
  rewrite H_itu_2; auto.

  (* case Constr0 *)
  eexists; split; auto with ival_of; tac_le_itval.

  (* case Constr1 *)
  specialize (IHH_ival_of itc2 H_le_itenv).
  inversion_clear IHH_ival_of as [itu_2 HH].
  inversion_clear HH as [H_ival_of_e H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  eexists; split; auto with ival_of; tac_le_itval.
  apply IVal_of_Constr1.
  apply H_ival_of_e.

  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_td_itd_2 H_le_iu_iu_2].
  tac_le_itval; auto.

  (* case Couple *)
  (** specialize induction hypothesis *)
  specialize (IHH_ival_of1 itc2 H_le_itenv).
  inversion_clear IHH_ival_of1 as [itu1_2 HH].
  inversion_clear HH as [H_ival_of_e1 H_le_itu1_itu1_2].
  destruct itu1_2 as [itd1_2 iu1_2].

  specialize (IHH_ival_of2 itc2 H_le_itenv).
  inversion_clear IHH_ival_of2 as [itu2_2 HH].
  inversion_clear HH as [H_ival_of_e2 H_le_itu2_itu2_2].
  destruct itu2_2 as [itd2_2 iu2_2] eqn:H_itu2_2.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu1_itu1_2 as [uH1 uH2 uH3 uH4 H_td1_itd1_2 H_le_iu1_iu1_2].
  inversion_clear H_le_itu2_itu2_2 as [uH1 uH2 uH3 uH4 H_td2_itd2_2 H_le_iu2_iu2_2].

  exists (IV (conc_itdeps itd1_2 itd2_2) (IV_ nil (IV_Couple iu1_2 iu2_2))).
  split; tac_le_itval; auto.  

  apply IVal_of_Couple; auto.

  intros l H_l.
  apply conc_itdeps_included with (itd1':=itd1_2) (itd2':=itd2_2) in H_l; auto.

  (* case Annot *)
  specialize (IHH_ival_of itc2 H_le_itenv).
  inversion_clear IHH_ival_of as [itu_2 HH].
  inversion_clear HH as [H_ival_of_e H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  exists (IV itd_2 (IV_ (cons l id_2) iv_2)).
  split.

  apply IVal_of_Annot; auto.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_td_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_d_id_2 H_le_iv_iv_2].

  tac_le_itval; auto.

  (** ideps *)
  intros l' H_l'.
  simpl.
  inversion H_l'; auto.
Qed.

Inductive inhabited_ctenv : ctenv -> Prop :=
| Inhabited_ctenv_empty :
    inhabited_ctenv CTEnv_empty
| Inhabited_ctenv_cons :
    forall (ctc:ctenv) (x:identifier) (td:itdeps) (d:ideps) (ivs:Ensemble ival0),
      inhabited_ctenv ctc
      -> Inhabited _ ivs
      -> inhabited_ctenv (CTEnv_cons x (CTVal td d ivs) ctc).

Lemma imenv_to_ctenv_of_append_ctenv_to_imenv :
  forall (ctc' ctc:ctenv) (imc:imenv),
    imenv_to_ctenv imc ctc
    -> inhabited_ctenv ctc'
    -> imenv_to_ctenv (append_ctenv_to_imenv ctc' imc) (conc_ctenv ctc' ctc).
Proof.
  induction ctc'; intros ctc imc H H_inhabited_cons_ctc'; auto.

  destruct ctv.
  specialize (IHctc' ctc imc H).
  simpl.


  apply Imenv_to_ctenv_cons with (imc':=(append_ctenv_to_imenv ctc' imc))
                                   (td:=td) (d:=d) (ivs:=ivs)
                                   (imv:=SetMap (fun iv => IV td (IV_ d iv)) ivs); auto.
  unfold Included, SetMap2, SetMap, In.
  split.
  intros itc'' HH.
  inversion_clear HH as [iv HHH].
  inversion_clear HHH as [itc' HH].
  inversion_clear HH as [H_itc'' HHH].
  inversion_clear HHH as [H_iv_in_ivs1 H_itc'_in_imc].
  rewrite H_itc''.
  unfold In.
  exists (IV td (IV_ d iv)), itc'.
  repeat split; auto.
  exists iv; split; auto.
  
  intros itc'' HH.
  inversion_clear HH as [itu HHH].
  inversion_clear HHH as [itc' HH].
  inversion_clear HH as [H_itc'' HHH].
  inversion_clear HHH as [HH H_itc'_in_imc].
  inversion_clear HH as [iv1 HHH].
  inversion_clear HHH as [H_itu HH_iv1_in_ivs1].
  exists iv1, itc'.
  repeat split; auto.
  rewrite H_itc'', H_itu; auto.


  apply Td_of_imval.
  split.
  intros HH.
  inversion_clear HH as [itd HHH].
  inversion_clear HHH as [id HH].
  inversion_clear HH as [iv HHH].
  inversion_clear HHH as [H_l_in_itd HH].
  inversion_clear HH as [H_iv' HHH].
  inversion_clear HHH as [H_itu H_iv'_in_ivs1].
  inversion H_itu.
  congruence.

  inversion H_inhabited_cons_ctc'.
  inversion H6 as [iv H_iv_in_ivs].
  intros H_l_in_td.
  exists td, d, iv.
  split; auto.
  exists iv; auto.

  apply D_of_imval.
  split.
  intros HH.
  inversion_clear HH as [itd HHH].
  inversion_clear HHH as [id HH].
  inversion_clear HH as [iv HHH].
  inversion_clear HHH as [H_l_in_itd HH].
  inversion_clear HH as [H_iv' HHH].
  inversion_clear HHH as [H_itu H_iv'_in_ivs1].
  inversion H_itu.
  congruence.

  inversion H_inhabited_cons_ctc'.
  inversion H6 as [iv H_iv_in_ivs].
  intros H_l_in_td.
  exists td, d, iv.
  split; auto.
  exists iv; auto.

  unfold Same_set, SetMap.
  split.
  intros iv HH.
  exists (IV td (IV_ d iv)).
  split; auto.
  exists iv; auto.

  intros iv HH.
  inversion HH as [itu HHH].
  inversion_clear HHH as [HH1 HH2].
  destruct itu as [itd iu].
  destruct iu as [id iv'].
  inversion HH2.
  inversion H0.
  inversion H1.
  congruence.

  inversion H_inhabited_cons_ctc'.
  auto.
Qed.


Lemma ctenv_to_imenv_to_ctenv :
  forall (ctc:ctenv),
    inhabited_ctenv ctc
    -> imenv_to_ctenv (ctenv_to_imenv ctc) ctc.
Proof.
  intros ctc H.
  unfold ctenv_to_imenv.
  simpl.

  assert(ctc = conc_ctenv ctc CTEnv_empty).
  induction ctc; auto.
  simpl.
  f_equal.
  inversion H; auto.
  rewrite H0 at 2.
  apply imenv_to_ctenv_of_append_ctenv_to_imenv.
  
  apply Imenv_to_ctenv_empty; auto.
  auto.
Qed.


Lemma imenv_to_ctenv_cons :
  forall (imc:imenv) (ctc:ctenv)
         (x:identifier) (td:itdeps) (d:ideps) (ivs:Ensemble ival0),
    imenv_to_ctenv imc ctc
    -> Inhabited _ ivs
    -> imenv_to_ctenv
         (SetMap2
            (fun (iv0 : ival0) (itc0 : itenv) =>
               ITEnv_cons x (IV td (IV_ d iv0)) itc0) ivs imc)
         (CTEnv_cons x (CTVal td d ivs) ctc).
Proof.
  intros imc ctc x td d ivs H_imc_to_ctc H_ivs_not_empty.

  apply Imenv_to_ctenv_cons with (imc':=imc)
                                   (td:=td) (d:=d) (ivs:=ivs)
                                   (imv:=SetMap (fun iv => IV td (IV_ d iv)) ivs); auto.

  split.
  intros itc H_itc_in.
  inversion_clear H_itc_in as [iv HH].
  inversion_clear HH as [itc' HHH].
  inversion_clear HHH as [H_itc HH].
  inversion_clear HH as [H_iv_in_ivs H_itc'_in_imc].
  exists (IV td (IV_ d iv)), itc'.
  repeat split; auto.
  exists iv; auto.

  intros itc H_itc_in.
  inversion_clear H_itc_in as [itu HH].
  inversion_clear HH as [itc' HHH].
  inversion_clear HHH as [H_itc HH].
  inversion_clear HH as [H_itu_in H_itc'_in_imc].
  inversion H_itu_in as [iv HH].
  inversion_clear HH as [H_itu H_iv_in_ivs].
  exists iv, itc'.
  repeat split; auto.
  congruence.

  apply Td_of_imval.
  split.
  intros HH.
  inversion_clear HH as [itd HHH].
  inversion_clear HHH as [id HH].
  inversion_clear HH as [iv HHH].
  inversion_clear HHH as [H_l_in_itd HH].
  inversion_clear HH as [H_iv' HHH].
  inversion_clear HHH as [H_itu H_iv'_in_ivs1].
  inversion H_itu.
  congruence.

  inversion H_ivs_not_empty as [iv H_iv_in_ivs].
  intros H_l_in_td.
  exists td, d, iv.
  split; auto.
  exists iv; auto.

  apply D_of_imval.
  split.
  intros HH.
  inversion_clear HH as [itd HHH].
  inversion_clear HHH as [id HH].
  inversion_clear HH as [iv HHH].
  inversion_clear HHH as [H_l_in_itd HH].
  inversion_clear HH as [H_iv' HHH].
  inversion_clear HHH as [H_itu H_iv'_in_ivs1].
  inversion H_itu.
  congruence.

  inversion H_ivs_not_empty as [iv H_iv_in_ivs].
  intros H_l_in_td.
  exists td, d, iv.
  split; auto.
  exists iv; auto.

  unfold Same_set, SetMap.
  split.
  intros iv HH.
  exists (IV td (IV_ d iv)).
  split; auto.
  exists iv; auto.

  intros iv HH.
  inversion HH as [itu HHH].
  inversion_clear HHH as [HH1 HH2].
  destruct itu as [itd iu].
  destruct iu as [id iv'].
  inversion HH2.
  inversion H.
  inversion H0.
  congruence.
Qed.


Lemma Inhabited_Intersection_1 :
  forall (U:Type) (s1 s2:Ensemble U),
    Inhabited _ (Intersection _ s1 s2)
    -> Inhabited _ s1.
Proof.
  intros U s1 s2 H.
  inversion H.
  inversion H0.
  exists x; auto.
Qed.

Lemma inhabited_ctenv_from_is_filtered :
  forall (ctv:ctval) (td:itdeps) (d:ideps) (ivs:Ensemble ival0)
         (p:pattern) (ctc_p:ctenv),
  ctv = CTVal td d ivs
  -> Inhabited _ (Intersection ival0 ivs ivs_of_matchable)
  -> is_filtered_ctval ctv p (Filtered_ctval_result_Match ctc_p)
  -> inhabited_ctenv ctc_p.
Proof.
  intros ctv td d ivs p ctc_p H_ctv H_matchable_of_ivs_not_empty H_is_filtered.

  inversion H_is_filtered.

  apply Inhabited_ctenv_empty.

  rewrite H1.
  apply Inhabited_ctenv_cons.
  apply Inhabited_ctenv_empty.
  rewrite H_ctv in H2; inversion H2.
  inversion H_matchable_of_ivs_not_empty as [iv H_iv_in_matchable_of_ivs].
  rewrite H8 in H0.
  specialize (H0 iv H_iv_in_matchable_of_ivs).
  unfold In, ivs_Constr1 in H0.
  destruct iv; inversion H0.
  destruct u.
  exists v.
  exists (IV_Constr1 n0 (IV_ d1 v)).
  inversion H_iv_in_matchable_of_ivs.
  auto.

  rewrite H1, H2.
  apply Inhabited_ctenv_cons.
  apply Inhabited_ctenv_cons.
  apply Inhabited_ctenv_empty.

  rewrite H_ctv in H4; inversion H4.
  inversion H_matchable_of_ivs_not_empty as [iv H_iv_in_matchable_of_ivs].
  rewrite H10 in H0.
  specialize (H0 iv H_iv_in_matchable_of_ivs).
  unfold In, ivs_Couple in H0.
  destruct iv; inversion H0.
  destruct u2.
  exists v.
  exists (IV_Couple u1 (IV_ d1 v)).
  inversion H_iv_in_matchable_of_ivs.
  auto.

  rewrite H_ctv in H4; inversion H4.
  inversion H_matchable_of_ivs_not_empty as [iv H_iv_in_matchable_of_ivs].
  rewrite H10 in H0.
  specialize (H0 iv H_iv_in_matchable_of_ivs).
  unfold In, ivs_Couple in H0.
  destruct iv; inversion H0.
  destruct u1.
  exists v.
  exists (IV_Couple (IV_ d1 v) u2).
  inversion H_iv_in_matchable_of_ivs.
  auto.
Qed.


Lemma inhabited_ctenv_from_is_filtered_unknown :
  forall (ctv:ctval) (td:itdeps) (d:ideps) (ivs:Ensemble ival0)
         (p:pattern) (ctc_p:ctenv),
  ctv = CTVal td d ivs
  -> Inhabited _ (Intersection ival0 ivs ivs_of_matchable)
  -> is_filtered_ctval ctv p (Filtered_ctval_result_Match_unknown ctc_p)
  -> inhabited_ctenv ctc_p.
Proof.
  intros ctv td d ivs p ctc_p H_ctv H_matchable_of_ivs_not_empty H_is_filtered.

  inversion H_is_filtered.

  apply Inhabited_ctenv_empty.

  rewrite H2.
  apply Inhabited_ctenv_cons.
  apply Inhabited_ctenv_empty.
  rewrite H_ctv in H3; inversion H3.
  inversion H_matchable_of_ivs_not_empty as [iv H_iv_in_matchable_of_ivs].
  rewrite H9 in *.
  inversion_clear H1 as [iv' H_iv'_in_ivs_Constr1].
  destruct iv'; inversion H_iv'_in_ivs_Constr1; try solve [inversion H6].
  destruct u.
  exists v.
  exists (IV_Constr1 n0 (IV_ d1 v)); auto.

  rewrite H2, H3.
  apply Inhabited_ctenv_cons.
  apply Inhabited_ctenv_cons.
  apply Inhabited_ctenv_empty.

  rewrite H_ctv in H5; inversion H5.
  inversion H_matchable_of_ivs_not_empty as [iv H_iv_in_matchable_of_ivs].
  rewrite H11 in *.
  inversion_clear H1 as [iv' H_iv'_in_ivs_Constr1].
  destruct iv'; inversion H_iv'_in_ivs_Constr1; try solve [inversion H8].
  destruct u2.
  exists v.
  exists (IV_Couple u1 (IV_ d1 v)); auto.

  inversion_clear H1 as [iv' H_iv'_in_ivs_Constr1].
  destruct iv'; inversion H_iv'_in_ivs_Constr1; try solve [inversion H8].
  destruct u1.
  exists v.
  exists (IV_Couple (IV_ d1 v) u2); auto.
Qed.


Lemma is_filtered_itval_in_ctval_exists :
  forall (ctv:ctval) (td:itdeps) (d:ideps) (ivs:Ensemble ival0)
         (itu:itval) (iv:ival0)
         (p:pattern) (ctc_p:ctenv),
  ctv = CTVal td d ivs
  -> itu = IV td (IV_ d iv)
  -> In ival0 ivs iv
  -> is_filtered_ctval ctv p (Filtered_ctval_result_Match ctc_p)
  -> is_filtered_itval itu p <> Filtered_itval_result_Match_var.
Proof.
  intros ctv td d ivs itu iv p ctc_p H H0 H1 H2.

  inversion H2.

  (* the matchables of ivs are in (ivs_Constr0 n) *)
  rewrite H in H4; inversion H4.
  rewrite H10 in *.
  clear dependent td0.
  clear dependent d0.
  clear dependent ivs0.
  rewrite H0; simpl.
  destruct iv; try solve [inversion 1].

  destruct (eq_nat_dec n0 n); try solve [inversion 1].
  unfold Included in H6.
  absurd(In ival0 (ivs_Constr0 n) (IV_Constr0 n0)).
  intros HH.
  unfold In, ivs_Constr0 in HH.
  congruence.
  apply H6.
  apply Intersection_intro; auto.
  unfold In, ivs_of_matchable.
  auto.

  unfold Included in H6.
  absurd(In ival0 (ivs_Constr0 n) (IV_Constr1 n0 u)).
  intros HH.
  unfold In, ivs_Constr0 in HH.
  congruence.
  apply H6.
  apply Intersection_intro; auto.
  unfold In, ivs_of_matchable.
  auto.

  unfold Included in H6.
  absurd(In ival0 (ivs_Constr0 n) (IV_Couple u1 u2)).
  intros HH.
  unfold In, ivs_Constr0 in HH.
  congruence.
  apply H6.
  apply Intersection_intro; auto.
  unfold In, ivs_of_matchable.
  auto.

  (* the matchables of ivs are in (ivs_Constr1 n) *)
  rewrite H in H6; inversion H6.
  rewrite H12 in *.
  clear dependent td0.
  clear dependent d0.
  clear dependent ivs0.
  rewrite H0; simpl.
  destruct iv; try solve [inversion 1].

  unfold Included in H4.
  absurd(In ival0 (ivs_Constr1 n) (IV_Constr0 n0)).
  intros HH.
  unfold In, ivs_Constr1 in HH.
  congruence.
  apply H4.
  apply Intersection_intro; auto.
  unfold In, ivs_of_matchable.
  auto.

  destruct (eq_nat_dec n0 n); try solve [inversion 1].
  unfold Included in H4.
  absurd(In ival0 (ivs_Constr1 n) (IV_Constr1 n0 u)).
  intros HH.
  unfold In, ivs_Constr1 in HH.
  congruence.
  apply H4.
  apply Intersection_intro; auto.
  unfold In, ivs_of_matchable.
  auto.

  unfold Included in H4.
  absurd(In ival0 (ivs_Constr1 n) (IV_Couple u1 u2)).
  intros HH.
  unfold In, ivs_Constr1 in HH.
  congruence.
  apply H4.
  apply Intersection_intro; auto.
  unfold In, ivs_of_matchable.
  auto.

  (* the matchables of ivs are only (ivs_Couple) *)
  rewrite H in H8; inversion H8.
  rewrite H14 in *.
  clear dependent td0.
  clear dependent d0.
  clear dependent ivs0.
  rewrite H0; simpl.
  destruct iv; try solve [inversion 1].
  
  unfold Included in H4.
  absurd(In ival0 (ivs_Couple) (IV_Constr0 n)).
  intros HH.
  unfold In, ivs_Couple in HH.
  congruence.
  apply H4.
  apply Intersection_intro; auto.
  unfold In, ivs_of_matchable.
  auto.

  unfold Included in H4.
  absurd(In ival0 (ivs_Couple) (IV_Constr1 n u)).
  intros HH.
  unfold In, ivs_Couple in HH.
  congruence.
  apply H4.
  apply Intersection_intro; auto.
  unfold In, ivs_of_matchable.
  auto.
Qed.


Lemma is_not_filtered_itval_in_ctval_exists :
  forall (ctv:ctval) (td:itdeps) (d:ideps) (ivs:Ensemble ival0)
         (itu:itval) (iv:ival0)
         (p:pattern) (itc_p:itenv),
  ctv = CTVal td d ivs
  -> itu = IV td (IV_ d iv)
  -> In ival0 ivs iv
  -> is_filtered_ctval ctv p Filtered_ctval_result_Match_var
  -> is_filtered_itval itu p <> Filtered_itval_result_Match itc_p.
Proof.
  intros ctv td d ivs itu iv p itc_p H H0 H1 H2.

  rewrite H0.
  inversion H2.


  (* the matchables of ivs are in (ivs_Constr0 n) *)
  rewrite H in H4;
    inversion H4;
    rewrite H9 in *;
    clear dependent td0;
    clear dependent d0;
    clear dependent ivs0.

  destruct iv; try solve [inversion 1].
  simpl.
  destruct (eq_nat_dec n0 n); try solve [inversion 1].
  rewrite e in *; clear dependent n0.
  rewrite <-H5 in *; clear dependent p.
  intros HH.
  apply H3.
  exists (IV_Constr0 n).
  apply Intersection_intro; auto.
  unfold In, ivs_Constr0; auto.
  
  (* the matchables of ivs are in (ivs_Constr1 n) *)
  rewrite H in H4;
    inversion H4;
    rewrite H9 in *;
    clear dependent td0;
    clear dependent d0;
    clear dependent ivs0.

  destruct iv; try solve [inversion 1].
  simpl.
  destruct (eq_nat_dec n0 n); try solve [inversion 1].
  rewrite e in *; clear dependent n0.
  rewrite <-H5 in *; clear dependent p.
  intros HH.
  apply H3.
  exists (IV_Constr1 n u).
  apply Intersection_intro; auto.
  unfold In, ivs_Constr1; auto.
  
  (* the matchables of ivs are in (ivs_Couple) *)
  rewrite H in H4;
    inversion H4;
    rewrite H9 in *;
    clear dependent td0;
    clear dependent d0;
    clear dependent ivs0.

  destruct iv; try solve [inversion 1].
  simpl.
  rewrite <-H5 in *; clear dependent p.
  intros HH.
  apply H3.
  exists (IV_Couple u1 u2).
  apply Intersection_intro; auto.
  unfold In, ivs_Couple; auto.
Qed.


Lemma is_filtered_itval_in_ctval :
  forall (ctv:ctval) (td:itdeps) (d:ideps) (ivs:Ensemble ival0)
         (itu:itval) (iv:ival0)
         (p:pattern) (ctc_p:ctenv) (itc_p:itenv),
  ctv = CTVal td d ivs
  -> itu = IV td (IV_ d iv)
  -> In ival0 ivs iv
  -> is_filtered_ctval ctv p (Filtered_ctval_result_Match ctc_p)
  -> is_filtered_itval itu p = Filtered_itval_result_Match itc_p
  -> exists (itc_p_2:itenv),
       In itenv (ctenv_to_imenv ctc_p) itc_p_2
       /\ le_itenv itc_p itc_p_2.
Proof.
  intros ctv td d ivs itu iv p ctc_p itc_p H_ctv H_itu H_iv_in_ivs H_is_filtered_ctv H_is_filtered_itu.

  inversion H_is_filtered_ctv.

  (* case Constr0 *)
  rewrite H_ctv in H0.
  inversion H0.
  rewrite H4, H5, H6, <-H1 in *.
  clear dependent td0.
  clear dependent d0.
  clear dependent ivs0.
  clear dependent p.

  rewrite H_itu in H_is_filtered_itu.
  simpl in H_is_filtered_itu.
  destruct iv; try solve [inversion H_is_filtered_itu].
  destruct (eq_nat_dec n0 n); inversion H_is_filtered_itu.
  unfold ctenv_to_imenv.
  exists ITEnv_empty.
  split.
  apply In_singleton.
  apply le_itenv_refl.

  (* case Constr1 *)
  rewrite H_ctv in H2.
  inversion H2.
  rewrite H6, H7, H8, <-H3 in *.
  clear dependent td0.
  clear dependent d0.
  clear dependent ivs0.
  clear dependent p.

  rewrite H_itu in H_is_filtered_itu.
  simpl in H_is_filtered_itu.
  destruct iv; try solve [inversion H_is_filtered_itu].
  destruct (eq_nat_dec n0 n); inversion H_is_filtered_itu.
  unfold ctenv_to_imenv.
  simpl.

  destruct u.
  exists (ITEnv_cons x (IV nil (IV_ d' v)) ITEnv_empty).
  split.
  exists v, ITEnv_empty.
  repeat split; auto.
  rewrite H1.
  exists (IV_Constr1 n0 (IV_ d0 v)); auto.
  tac_le_itval.
  intros l H_l.
  inversion H4.
  apply H3.
  exists nil, d0, v.
  split; auto.
  exists (IV_Constr1 n0 (IV_ d0 v)); auto.
  apply le_ival0_refl.

  (* case Couple *)
  rewrite H_ctv in H4.
  inversion H4.
  rewrite H10, <-H5 in *.
  clear dependent td0.
  clear dependent d0.
  clear dependent ivs0.
  clear dependent p.

  rewrite H_itu in H_is_filtered_itu.
  simpl in H_is_filtered_itu.
  destruct iv; inversion H_is_filtered_itu.
  unfold ctenv_to_imenv.
  simpl.

  destruct u1 as [d1 v1], u2 as [d2 v2].
  exists (ITEnv_cons x1 (IV nil (IV_ d1' v1)) (ITEnv_cons x2 (IV nil (IV_ d2' v2)) ITEnv_empty)).
  split.
  exists v1, (ITEnv_cons x2 (IV nil (IV_ d2' v2)) ITEnv_empty).
  repeat split.
  rewrite H1.
  exists (IV_Couple (IV_ d1 v1) (IV_ d2 v2)); auto.
  exists v2, ITEnv_empty.
  repeat split; auto.
  rewrite H2.
  exists (IV_Couple (IV_ d1 v1) (IV_ d2 v2)); auto.
  
  tac_le_itval.
  intros l H_l.
  inversion H3.
  apply H4.
  exists nil, d1, v1.
  split; auto.
  exists (IV_Couple (IV_ d1 v1) (IV_ d2 v2)); auto.
  apply le_ival0_refl.

  tac_le_itval.
  intros l H_l.
  inversion H6.
  apply H4.
  exists nil, d2, v2.
  split; auto.
  exists (IV_Couple (IV_ d1 v1) (IV_ d2 v2)); auto.
  apply le_ival0_refl.
Qed.


Lemma is_filtered_itval_in_ctval_unknown :
  forall (ctv:ctval) (td:itdeps) (d:ideps) (ivs:Ensemble ival0)
         (itu:itval) (iv:ival0)
         (p:pattern) (ctc_p:ctenv) (itc_p:itenv),
  ctv = CTVal td d ivs
  -> itu = IV td (IV_ d iv)
  -> In ival0 ivs iv
  -> is_filtered_ctval ctv p (Filtered_ctval_result_Match_unknown ctc_p)
  -> is_filtered_itval itu p = Filtered_itval_result_Match itc_p
  -> exists (itc_p_2:itenv),
       In itenv (ctenv_to_imenv ctc_p) itc_p_2
       /\ le_itenv itc_p itc_p_2.
Proof.
  intros ctv td d ivs itu iv p ctc_p itc_p H_ctv H_itu H_iv_in_ivs H_is_filtered_ctv H_is_filtered_itu.

  inversion H_is_filtered_ctv.

  (* case Constr0 *)
  rewrite H_ctv in H1.
  inversion H1.
  rewrite H5, H6, H7, <-H2 in *.
  clear dependent td0.
  clear dependent d0.
  clear dependent ivs0.
  clear dependent p.

  rewrite H_itu in H_is_filtered_itu.
  simpl in H_is_filtered_itu.
  destruct iv; try solve [inversion H_is_filtered_itu].
  destruct (eq_nat_dec n0 n); inversion H_is_filtered_itu.
  unfold ctenv_to_imenv.
  exists ITEnv_empty.
  split.
  apply In_singleton.
  apply le_itenv_refl.

  (* case Constr1 *)
  rewrite H_ctv in H3.
  inversion H3.
  rewrite H7, H8, H9, <-H4 in *.
  clear dependent td0.
  clear dependent d0.
  clear dependent ivs0.
  clear dependent p.

  rewrite H_itu in H_is_filtered_itu.
  simpl in H_is_filtered_itu.
  destruct iv; try solve [inversion H_is_filtered_itu].
  destruct (eq_nat_dec n0 n); inversion H_is_filtered_itu.
  unfold ctenv_to_imenv.
  simpl.

  destruct u.
  exists (ITEnv_cons x (IV nil (IV_ d' v)) ITEnv_empty).
  split.
  exists v, ITEnv_empty.
  repeat split; auto.
  rewrite H2.
  exists (IV_Constr1 n0 (IV_ d0 v)); auto.
  split; auto.
  apply Intersection_intro; auto.
  unfold In, ivs_Constr1; auto.
  tac_le_itval.
  intros l H_l.
  inversion H5.
  apply H4.
  exists nil, d0, v.
  split; auto.
  exists (IV_Constr1 n0 (IV_ d0 v)); auto.
  split; auto.
  apply Intersection_intro; auto.
  unfold In, ivs_Constr1; auto.
  apply le_ival0_refl.

  (* case Couple *)
  rewrite H_ctv in H5.
  inversion H5.
  rewrite H11, <-H6 in *.
  clear dependent td0.
  clear dependent d0.
  clear dependent ivs0.
  clear dependent p.

  rewrite H_itu in H_is_filtered_itu.
  simpl in H_is_filtered_itu.
  destruct iv; inversion H_is_filtered_itu.
  unfold ctenv_to_imenv.
  simpl.

  destruct u1 as [d1 v1], u2 as [d2 v2].
  exists (ITEnv_cons x1 (IV nil (IV_ d1' v1)) (ITEnv_cons x2 (IV nil (IV_ d2' v2)) ITEnv_empty)).
  split.
  exists v1, (ITEnv_cons x2 (IV nil (IV_ d2' v2)) ITEnv_empty).
  repeat split.
  rewrite H2.
  exists (IV_Couple (IV_ d1 v1) (IV_ d2 v2)); auto.
  split; auto.
  apply Intersection_intro; auto.
  unfold In, ivs_Couple; auto.
  exists v2, ITEnv_empty.
  repeat split; auto.
  rewrite H3.
  exists (IV_Couple (IV_ d1 v1) (IV_ d2 v2)); auto.
  split; auto.
  apply Intersection_intro; auto.
  unfold In, ivs_Couple; auto.
  
  tac_le_itval.
  intros l H_l.
  inversion H4.
  apply H5.
  exists nil, d1, v1.
  split; auto.
  exists (IV_Couple (IV_ d1 v1) (IV_ d2 v2)); auto.
  split; auto.
  apply Intersection_intro; auto.
  unfold In, ivs_Couple; auto.
  apply le_ival0_refl.

  intros l H_l.
  inversion H7.
  apply H5.
  exists nil, d2, v2.
  split; auto.
  exists (IV_Couple (IV_ d1 v1) (IV_ d2 v2)); auto.
  split; auto.
  apply Intersection_intro; auto.
  unfold In, ivs_Couple; auto.
  apply le_ival0_refl.
Qed.



Lemma conc_itenv_in_append_ctenv_to_imenv :
  forall (imc:imenv) (ctc':ctenv) (itc itc':itenv),
    In itenv imc itc
    -> In itenv (ctenv_to_imenv ctc') itc'
    -> In itenv (append_ctenv_to_imenv ctc' imc) (conc_itenv itc' itc).
Proof.
  induction ctc'; intros itc itc' H H0.

  inversion H0; auto.

  destruct ctv as [td d v].
  inversion H0 as [iv HH].
  inversion_clear HH as [itc'' HHH].
  inversion_clear HHH as [H_itc' HH].
  inversion_clear HH as [H_iv_in_v H_itc''_in].

  rewrite H_itc'.
  simpl.
  exists iv, (conc_itenv itc'' itc).
  split; auto.
Qed.

Lemma is_filtered_itval_implies_is_matchable :
  forall (td:itdeps) (d:ideps) (iv:ival0) (p:pattern) (itc_p:itenv),
    is_filtered_itval (IV td (IV_ d iv)) p = Filtered_itval_result_Match itc_p
    -> In _ ivs_of_matchable iv.
Proof.
  intros td d iv p itc_p H.
  unfold In, ivs_of_matchable.
  destruct iv; inversion H; auto.
Qed.

Lemma is_not_filtered_itval_implies_is_matchable :
  forall (td:itdeps) (d:ideps) (iv:ival0) (p:pattern),
    is_filtered_itval (IV td (IV_ d iv)) p = Filtered_itval_result_Match_var
    -> In _ ivs_of_matchable iv.
Proof.
  intros td d iv p H.
  unfold In, ivs_of_matchable.
  destruct iv; inversion H; auto.
Qed.



Theorem ctval_of_correctness :
  forall (imc:imenv) (e:expr) (imv:imval)
         (ctv:ctval) (ctc:ctenv),
    imval_of imc e imv
    -> imenv_to_ctenv imc ctc
    -> ctval_of ctc e ctv
    -> le_imval imv (ctval_to_imval ctv).
Proof.
  intros imc e imv ctv ctc H_imval_of H_imenv_to_ctenv H_ctval_of.
  inversion H_imval_of.
  clear H0 H1 H2.
  clear imc0 e0 imv0.
  rename H into H_imv.

  revert dependent imv.
  revert dependent imc.
  induction H_ctval_of;
    try rename imv into imv0;
    intros imc H_imenv_to_ctenv imv H_imval_of H_imv.

  (* case Num *)
  intros itu H_itu_in_imv.
  exists itu.
  rewrite H_imv in H_itu_in_imv.
  unfold In in H_itu_in_imv.
  inversion H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].
  inversion H_ival_of.
  simpl.
  unfold SetMap.
  unfold In.
  split.
  eexists.
  split.
  reflexivity.
  apply In_singleton.
  tac_le_itval.


  (* case Constr0 *)
  intros itu H_itu_in_imv.
  exists itu.
  rewrite H_imv in H_itu_in_imv.
  inversion H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].
  inversion H_ival_of.
  simpl.
  unfold SetMap.
  unfold In.
  split.
  eexists.
  split.
  reflexivity.
  apply In_singleton.
  tac_le_itval.

  (* case Constr1 *)

  (** induction hypothesis*)
  specialize(IHH_ctval_of imc H_imenv_to_ctenv
                          (fun itu =>
                             exists (itc:itenv), In _ imc itc
                                                 /\ ival_of itc e itu)
                          (IMVal_of imc e _ eq_refl)
                          eq_refl).


  (** simplify the goal *)
  intros itu H_itu_in_imv.
  unfold In.
  rewrite H_imv in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].
  inversion H_ival_of.

  (** specialize induction hypothesis *)
  specialize(IHH_ctval_of (IV td0 u)).

  assert(IH_ctval_of : exists itu2 : itval,
                         In itval (ctval_to_imval (CTVal td d ivs)) itu2 /\
                         le_itval (IV td0 u) itu2).
  apply IHH_ctval_of.
  unfold In.
  exists itc.
  auto.
  clear IHH_ctval_of.
  inversion_clear IH_ctval_of as [itu2 H_itu2_in_].
  inversion_clear H_itu2_in_ as [H_itu2_in_ctval_to_imval H_le_itu2_].

  destruct itu2.
  destruct u0.


  inversion H_itu2_in_ctval_to_imval as [v2].
  inversion_clear H5.
  inversion H6.

  exists (IV td (IV_ nil (IV_Constr1 n (IV_ d v)))).
  split.
  simpl.
  unfold SetMap.
  eexists; split.
  reflexivity.
  rewrite H.
  unfold In, SetMap.
  eexists; split; auto.
  simpl in H_itu2_in_ctval_to_imval.
  unfold In, SetMap in H_itu2_in_ctval_to_imval.
  rewrite H10; assumption.

  tac_le_itval.
  inversion H_le_itu2_.
  rewrite <-H8.
  assumption.

  inversion H_le_itu2_.
  rewrite <-H9.
  assumption.

  
  (* case Ident *)
  (** simplify the goal *)
  intros itu H_itu_in_imv.
  unfold In.
  rewrite H_imv in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].
  inversion H_ival_of.

  apply assoc_ident_in_imenv_to_ctenv with (imc:=imc) (ctc:=ctc) (x:=x) (itc:=itc); auto.

  (* case Ident_empty *)
  (** simplify the goal *)
  intros itu H_itu_in_imv.
  unfold In.
  rewrite H_imv in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].
  inversion H_ival_of.

  apply assoc_ident_not_in_imenv_to_ctenv with (imc:=imc) (itc:=itc) in H; auto.
  congruence.

  (* case Lambda *)
  (** let's take a itu in imv and prove that it there is itu2 > itu in the ctval_to_imval *)
  intros itu H_itu_in_imv.

  (** itu is in imv, so there is some itc in imc in which the evaluation of (Lambda x e) gives itu *)
  rewrite H_imv in H_itu_in_imv.
  unfold In in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** itu is a Closure *)
  inversion_clear H_ival_of.

  (** the composition of abstraction and concretization of imc is greater than imc *)
  assert(H_le_imenv := imenv_to_ctenv_to_imenv_increasing imc ctc H_imenv_to_ctenv).
  specialize(H_le_imenv itc H_itc_in_imc).
  inversion_clear H_le_imenv as [itc2 HH].
  inversion_clear HH as [H_itc2_in_ctenv_to_imenv H_itc_itc2].

  exists (IV nil (IV_ nil (IV_Closure x e (itenv_to_ienv itc2)))).
  split.
  rewrite H.
  simpl.
  unfold In, SetMap.
  exists (IV_Closure x e (itenv_to_ienv itc2)).
  split; auto.
  unfold In.
  exists itc2; split; auto.

  rewrite H0.
  tac_le_itval.
  apply le_itenv_to_ienv; assumption.
  
  (* case Rec *)
  (** let's take a itu in imv and prove that it there is itu2 > itu in the ctval_to_imval *)
  intros itu H_itu_in_imv.

  (** itu is in imv, so there is some itc in imc in which the evaluation of (Rec f x e) gives itu *)
  rewrite H_imv in H_itu_in_imv.
  unfold In in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** itu is a Rec_Closure *)
  inversion_clear H_ival_of.

  (** the composition of abstraction and concretization of imc is greater than imc *)
  assert(H_le_imenv := imenv_to_ctenv_to_imenv_increasing imc ctc H_imenv_to_ctenv).
  specialize(H_le_imenv itc H_itc_in_imc).
  inversion_clear H_le_imenv as [itc2 HH].
  inversion_clear HH as [H_itc2_in_ctenv_to_imenv H_itc_itc2].

  exists (IV nil (IV_ nil (IV_Rec_Closure f x e (itenv_to_ienv itc2)))).
  split.
  rewrite H.
  simpl.
  unfold In, SetMap.
  exists (IV_Rec_Closure f x e (itenv_to_ienv itc2)).
  split; auto.
  unfold In.
  exists itc2; split; auto.

  rewrite H0.
  tac_le_itval.
  apply le_itenv_to_ienv; assumption.


  (* case Apply *)
  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu H_itu_in_imv.

  (** itu is in imv, so there is some itc in imc in which the evaluation of (e1 e2) gives itu *)
  rewrite H_imv in H_itu_in_imv.
  unfold In in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | |
                           | c ic1 e0 e3 e x itu2 uu u2 id id1 itd1 itd2 itd v
                               H_ival_of_e1 H_ival_of_e2 H_itu2 H_ival_of_e H_itu
                           | c ic1 e0 e3 e f x itu1 itu2 uu u2 id id1 itd1 itd2 itd v
                               H_ival_of_e1 H_itu1 H_ival_of_e2 H_ival_of_e H_itu2 H_itu
                           | | | | | | | | | ].

  (*** the function is not recursive *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent uu.
  (**** instantiate the induction hypothesis *)
  specialize(IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize(IHH_ctval_of1 (fun itu : itval =>
                              exists itc : itenv, In itenv imc itc /\ ival_of itc e1 itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).
  specialize(IHH_ctval_of2 imc H_imenv_to_ctenv).
  specialize(IHH_ctval_of2 (fun itu : itval =>
                              exists itc : itenv, In itenv imc itc /\ ival_of itc e2 itu)).
  specialize(IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of2 eq_refl).
  
  specialize(IHH_ctval_of1 (IV itd1 (IV_ id1 (IV_Closure x e ic1)))).
  specialize(IHH_ctval_of2 itu2).

  assert(IH_ctval_of1 : exists itu1_2 : itval,
                          In itval (ctval_to_imval (CTVal td1 d1 ivs1)) itu1_2 /\
                          le_itval (IV itd1 (IV_ id1 (IV_Closure x e ic1))) itu1_2).
  apply IHH_ctval_of1.
  unfold In.
  exists itc.
  split; auto.
  
  assert(IH_ctval_of2 : exists itu2_2 : itval,
                          In itval (ctval_to_imval (CTVal td2 d2 ivs2)) itu2_2 /\
                          le_itval itu2 itu2_2).
  apply IHH_ctval_of2.
  unfold In.
  exists itc.
  split; auto.

  clear IHH_ctval_of1.
  clear IHH_ctval_of2.

  inversion_clear IH_ctval_of1 as [itu1_2 HH].
  inversion_clear HH as [H_itu1_2_in_ctval_to_imval H_itu1_itu1_2].
  inversion_clear IH_ctval_of2 as [itu2_2 HH].
  inversion_clear HH as [H_itu2_2_in_ctval_to_imval H_itu2_itu2_2].

  simpl in H_itu1_2_in_ctval_to_imval.
  unfold In, SetMap in H_itu1_2_in_ctval_to_imval.
  inversion_clear H_itu1_2_in_ctval_to_imval as [iv1_2 HH].
  inversion_clear HH as [H_itu1_2 H_iv1_2_in_ivs1].
  simpl in H_itu2_2_in_ctval_to_imval.
  unfold In, SetMap in H_itu2_2_in_ctval_to_imval.
  inversion_clear H_itu2_2_in_ctval_to_imval as [iv2_2 HH].
  inversion_clear HH as [H_itu2_2 H_iv2_2_in_ivs2].

  (**** itu1_2 is a Closure *)
  rewrite H_itu1_2 in H_itu1_itu1_2.
  inversion_clear H_itu1_itu1_2 as [HH_unused1 HH_unused2 HH_unused3 HH_unused4
                                               H_itd1_incl_in_td1 H_iu1_iu1_2].
  inversion_clear H_iu1_iu1_2 as [HH_unused1 HH_unused2 HH_unused3 HH_unused4
                                             H_id1_incl_in_d1 H_iv1_iv1_2].
  inversion H_iv1_iv1_2 as [ | | | | | x1_2 e1_2 ic ic1_2 H_ic1_ic1_2 HH H_iv1_2 | ].
  clear dependent x1_2.
  clear dependent e1_2.
  clear dependent ic.

  apply ival_of_in_le_itenv with (itc2:=ITEnv_cons x itu2_2 (ienv_to_itenv ic1_2)) in H_ival_of_e
  ; try solve [tac_le_itval; [assumption | apply le_ienv_to_itenv; assumption]].

  inversion_clear H_ival_of_e as [itu_2 HH].
  inversion_clear HH as [H_ival_of_e H_le_itval__itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  exists (IV td (IV_ d iv_2)).
  split.
  rewrite H2.
  simpl.
  unfold In, SetMap.
  exists iv_2.
  split; auto.
  unfold In.
  exists (IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd_2 d1)))
             (IV_ (conc_ideps d1 id_2) iv_2)).
  split; auto.
  rewrite H.
  left.
  exists x, e, ic1_2, iv2_2, itd_2, id_2, iv_2.
  repeat split.  
  rewrite H_iv1_2; assumption.
  assumption.
  rewrite <-H_itu2_2; assumption.
  rewrite H_itu.
  tac_le_itval.

  (**** inclusion of the itdeps *)
  intros l H_l.
  apply H0.
  exists (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd_2 d1))).
  split.
  apply conc_itdeps_included with (itd1':=td1) (itd2':=conc_itdeps td2 (conc_itdeps itd_2 d1)) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=td2) (itd2':=conc_itdeps itd_2 d1) in H_l'; auto.
  rewrite H_itu2, H_itu2_2 in H_itu2_itu2_2.
  inversion_clear H_itu2_itu2_2; auto.
  intros l'' H_l''.
  apply conc_itdeps_included with (itd1':=itd_2) (itd2':=d1) in H_l''; auto.
  inversion H_le_itval__itu_2; auto.

  unfold In, SetMap.
  exists (IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd_2 d1)))
             (IV_ (conc_ideps d1 id_2) iv_2)).
  split; auto.
  rewrite H.
  unfold In.
  left.
  exists x, e, ic1_2, iv2_2, itd_2, id_2, iv_2.
  repeat split.  
  rewrite H_iv1_2; assumption.
  assumption.
  rewrite <-H_itu2_2; assumption.

  (**** inclusion of the ideps *)
  intros l H_l.
  apply H1.
  exists (conc_ideps d1 id_2).
  split.
  apply conc_ideps_included with (id1':=d1) (id2':=id_2) in H_l; auto.
  inversion H_le_itval__itu_2.
  inversion H8; auto.  

  unfold In, SetMap.
  exists (IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd_2 d1)))
             (IV_ (conc_ideps d1 id_2) iv_2)).
  split; auto.
  rewrite H.
  unfold In.
  left.
  exists x, e, ic1_2, iv2_2, itd_2, id_2, iv_2.
  repeat split.  
  rewrite H_iv1_2; assumption.
  assumption.
  rewrite <-H_itu2_2; assumption.
  inversion H_le_itval__itu_2.
  inversion H8; auto.

  (*** the function is recursive *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent uu.
  (**** instantiate the induction hypothesis *)
  specialize(IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize(IHH_ctval_of1 (fun itu : itval =>
                              exists itc : itenv, In itenv imc itc /\ ival_of itc e1 itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).
  specialize(IHH_ctval_of2 imc H_imenv_to_ctenv).
  specialize(IHH_ctval_of2 (fun itu : itval =>
                              exists itc : itenv, In itenv imc itc /\ ival_of itc e2 itu)).
  specialize(IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of2 eq_refl).
  
  specialize(IHH_ctval_of1 (IV itd1 (IV_ id1 (IV_Rec_Closure f x e ic1)))).
  specialize(IHH_ctval_of2 itu2).

  assert(IH_ctval_of1 : exists itu1_2 : itval,
                          In itval (ctval_to_imval (CTVal td1 d1 ivs1)) itu1_2 /\
                          le_itval (IV itd1 (IV_ id1 (IV_Rec_Closure f x e ic1))) itu1_2).
  apply IHH_ctval_of1.
  unfold In.
  exists itc.
  rewrite <- H_itu1.
  split; auto.
  
  assert(IH_ctval_of2 : exists itu2_2 : itval,
                          In itval (ctval_to_imval (CTVal td2 d2 ivs2)) itu2_2 /\
                          le_itval itu2 itu2_2).
  apply IHH_ctval_of2.
  unfold In.
  exists itc.
  split; auto.

  clear IHH_ctval_of1.
  clear IHH_ctval_of2.

  inversion_clear IH_ctval_of1 as [itu1_2 HH].
  inversion_clear HH as [H_itu1_2_in_ctval_to_imval H_itu1_itu1_2].
  inversion_clear IH_ctval_of2 as [itu2_2 HH].
  inversion_clear HH as [H_itu2_2_in_ctval_to_imval H_itu2_itu2_2].

  simpl in H_itu1_2_in_ctval_to_imval.
  unfold In, SetMap in H_itu1_2_in_ctval_to_imval.
  inversion_clear H_itu1_2_in_ctval_to_imval as [iv1_2 HH].
  inversion_clear HH as [H_itu1_2 H_iv1_2_in_ivs1].
  simpl in H_itu2_2_in_ctval_to_imval.
  unfold In, SetMap in H_itu2_2_in_ctval_to_imval.
  inversion_clear H_itu2_2_in_ctval_to_imval as [iv2_2 HH].
  inversion_clear HH as [H_itu2_2 H_iv2_2_in_ivs2].

  (**** itu1_2 is a Rec_Closure *)
  rewrite H_itu1_2 in H_itu1_itu1_2.
  inversion_clear H_itu1_itu1_2 as [HH_unused1 HH_unused2 HH_unused3 HH_unused4
                                               H_itd1_incl_in_td1 H_iu1_iu1_2].
  inversion_clear H_iu1_iu1_2 as [HH_unused1 HH_unused2 HH_unused3 HH_unused4
                                             H_id1_incl_in_d1 H_iv1_iv1_2].
  inversion H_iv1_iv1_2 as [ | | | | | | f1_2 x1_2 e1_2 ic ic1_2 H_ic1_ic1_2 HH H_iv1_2 ].
  clear dependent f1_2.
  clear dependent x1_2.
  clear dependent e1_2.
  clear dependent ic.

  apply ival_of_in_le_itenv with (itc2:=ITEnv_cons f itu1_2 (ITEnv_cons x itu2_2 (ienv_to_itenv ic1_2))) in H_ival_of_e
  ; try solve [rewrite H_itu1, H_itu1_2; tac_le_itval; auto; apply le_ienv_to_itenv; assumption].

  inversion_clear H_ival_of_e as [itu_2 HH].
  inversion_clear HH as [H_ival_of_e H_le_itval__itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  exists (IV td (IV_ d iv_2)).
  split.
  rewrite H2.
  simpl.
  unfold In, SetMap.
  exists iv_2.
  split; auto.
  unfold In.
  exists (IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd_2 d1)))
             (IV_ (conc_ideps d1 id_2) iv_2)).
  split; auto.
  rewrite H.
  right.
  exists f, x, e, ic1_2, iv2_2, itd_2, id_2, iv_2.
  repeat split.  
  rewrite H_iv1_2; assumption.
  assumption.
  rewrite H_iv1_2, <-H_itu1_2, <-H_itu2_2; assumption.
  rewrite H_itu.
  tac_le_itval.

  (**** inclusion of the itdeps *)
  intros l H_l.
  apply H0.
  exists (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd_2 d1))).
  split.
  apply conc_itdeps_included with (itd1':=td1) (itd2':=conc_itdeps td2 (conc_itdeps itd_2 d1)) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=td2) (itd2':=conc_itdeps itd_2 d1) in H_l'; auto.
  rewrite H_itu2, H_itu2_2 in H_itu2_itu2_2.
  inversion_clear H_itu2_itu2_2; auto.
  intros l'' H_l''.
  apply conc_itdeps_included with (itd1':=itd_2) (itd2':=d1) in H_l''; auto.
  inversion H_le_itval__itu_2; auto.

  unfold In, SetMap.
  exists (IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd_2 d1)))
             (IV_ (conc_ideps d1 id_2) iv_2)).
  split; auto.
  rewrite H.
  unfold In.
  right.
  exists f, x, e, ic1_2, iv2_2, itd_2, id_2, iv_2.
  repeat split.  
  rewrite H_iv1_2; assumption.
  assumption.
  rewrite H_iv1_2, <-H_itu1_2, <-H_itu2_2; assumption.

  (**** inclusion of the ideps *)
  intros l H_l.
  apply H1.
  exists (conc_ideps d1 id_2).
  split.
  apply conc_ideps_included with (id1':=d1) (id2':=id_2) in H_l; auto.
  inversion H_le_itval__itu_2.
  inversion H8; auto.  

  unfold In, SetMap.
  exists (IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd_2 d1)))
             (IV_ (conc_ideps d1 id_2) iv_2)).
  split; auto.
  rewrite H.
  unfold In.
  right.
  exists f, x, e, ic1_2, iv2_2, itd_2, id_2, iv_2.
  repeat split.  
  rewrite H_iv1_2; assumption.
  assumption.
  rewrite H_iv1_2, <-H_itu1_2, <-H_itu2_2; assumption.

  inversion H_le_itval__itu_2.
  inversion H8; auto.

  (* case If_true *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of1 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).

  specialize (IHH_ctval_of2 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of2 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e1 itu)).
  specialize(IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of2 eq_refl).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu H_itu_in_imv.

  rewrite H_imv in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | |
                           | c e0 e3 e4 itd_e itd1 id_e id1 itu1 iv1
                           | c e0 e3 e4 itd_e itd2 id_e id2 itu2 iv2
                           | | | | | | ].

  (*** the condition evaluates to True *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent e4.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of1 (IV itd_e (IV_ id_e (IV_Bool true)))).
  elim IHH_ctval_of1.
  intros itu_e_2 HH.
  inversion_clear HH as [H_itu_e_2_in_ctval_to_imval H_le_itu_e_itu_e_2].
  destruct itu_e_2 as [itd_e_2 iu_e_2].
  destruct iu_e_2 as [id_e_2 iv_e_2].

  specialize (IHH_ctval_of2 itu1).
  elim IHH_ctval_of2.
  intros itu1_2 HH.
  inversion_clear HH as [H_itu1_2_in_ctval_to_imval H_le_itu1_itu1_2].
  destruct itu1_2 as [itd1_2 iu1_2].
  destruct iu1_2 as [id1_2 iv1_2].

  exists (IV (conc_itdeps id_e_2 (conc_itdeps itd_e_2 itd1_2)) (IV_ (conc_ideps id_e_2 id1_2) iv1_2)).
  split.

  simpl.
  unfold In, SetMap.
  exists iv1_2.

  simpl in H_itu_e_2_in_ctval_to_imval.
  inversion_clear H_itu_e_2_in_ctval_to_imval as [iv_e_2'].
  inversion_clear H1.
  inversion_clear H2.

  simpl in H_itu1_2_in_ctval_to_imval.
  inversion_clear H_itu1_2_in_ctval_to_imval as [iv1_2'].
  inversion_clear H1.
  inversion_clear H2.

  split; auto.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_e_itu_e_2 as [uH1 uH2 uH3 uH4 H_itd_e_itd_e_2 H_le_iu_e_iu_e_2].
  inversion_clear H_le_iu_e_iu_e_2 as [uH1 uH2 uH3 uH4 H_id_e_id_e_2 H_le_iv_e_iv_e_2].

  rewrite H8 in H_le_itu1_itu1_2.
  inversion_clear H_le_itu1_itu1_2 as [uH1 uH2 uH3 uH4 H_itd1_itd1_2 H_le_iu1_iu1_2].
  inversion_clear H_le_iu1_iu1_2 as [uH1 uH2 uH3 uH4 H_id1_id1_2 H_le_iv1_iv1_2].

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=id_e_2) (itd2':=conc_itdeps itd_e_2 itd1_2) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd_e_2) (itd2':=itd1_2) in H_l'; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id_e_2) (id2':=id1_2) in H_l; auto.

  exists itc; auto.
  exists itc; auto.

  (*** the condition evaluates to False *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent e4.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of1 (IV itd_e (IV_ id_e (IV_Bool false)))).
  elim IHH_ctval_of1.
  intros itu_e_2 HH.
  inversion_clear HH as [H_itu_e_2_in_ctval_to_imval H_le_itu_e_itu_e_2].
  destruct itu_e_2 as [itd_e_2 iu_e_2].
  destruct iu_e_2 as [id_e_2 iv_e_2].

  simpl in H_itu_e_2_in_ctval_to_imval.
  inversion_clear H_itu_e_2_in_ctval_to_imval as [iv_e_2'].
  inversion_clear H1.
  inversion H2.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_e_itu_e_2 as [uH1 uH2 uH3 uH4 H_itd_e_itd_e_2 H_le_iu_e_iu_e_2].
  inversion_clear H_le_iu_e_iu_e_2 as [uH1 uH2 uH3 uH4 H_id_e_id_e_2 H_le_iv_e_iv_e_2].
  inversion H_le_iv_e_iv_e_2.
  congruence.

  exists itc; auto.

  (* case If_false *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of1 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).

  specialize (IHH_ctval_of2 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of2 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e2 itu)).
  specialize(IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of2 eq_refl).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu H_itu_in_imv.

  rewrite H_imv in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | |
                           | c e0 e3 e4 itd_e itd1 id_e id1 itu1 iv1
                           | c e0 e3 e4 itd_e itd2 id_e id2 itu2 iv2
                           | | | | | | ].

  (*** the condition evaluates to True *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent e4.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of1 (IV itd_e (IV_ id_e (IV_Bool true)))).
  elim IHH_ctval_of1.
  intros itu_e_2 HH.
  inversion_clear HH as [H_itu_e_2_in_ctval_to_imval H_le_itu_e_itu_e_2].
  destruct itu_e_2 as [itd_e_2 iu_e_2].
  destruct iu_e_2 as [id_e_2 iv_e_2].

  simpl in H_itu_e_2_in_ctval_to_imval.
  inversion_clear H_itu_e_2_in_ctval_to_imval as [iv_e_2'].
  inversion_clear H2.
  inversion H3.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_e_itu_e_2 as [uH1 uH2 uH3 uH4 H_itd_e_itd_e_2 H_le_iu_e_iu_e_2].
  inversion_clear H_le_iu_e_iu_e_2 as [uH1 uH2 uH3 uH4 H_id_e_id_e_2 H_le_iv_e_iv_e_2].
  inversion H_le_iv_e_iv_e_2.
  congruence.

  exists itc; auto.

  (*** the condition evaluates to False *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent e4.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of1 (IV itd_e (IV_ id_e (IV_Bool false)))).
  elim IHH_ctval_of1.
  intros itu_e_2 HH.
  inversion_clear HH as [H_itu_e_2_in_ctval_to_imval H_le_itu_e_itu_e_2].
  destruct itu_e_2 as [itd_e_2 iu_e_2].
  destruct iu_e_2 as [id_e_2 iv_e_2].

  specialize (IHH_ctval_of2 itu2).
  elim IHH_ctval_of2.
  intros itu2_2 HH.
  inversion_clear HH as [H_itu2_2_in_ctval_to_imval H_le_itu2_itu2_2].
  destruct itu2_2 as [itd2_2 iu2_2].
  destruct iu2_2 as [id2_2 iv2_2].

  exists (IV (conc_itdeps id_e_2 (conc_itdeps itd_e_2 itd2_2)) (IV_ (conc_ideps id_e_2 id2_2) iv2_2)).
  split.

  simpl.
  unfold In, SetMap.
  exists iv2_2.

  simpl in H_itu_e_2_in_ctval_to_imval.
  inversion_clear H_itu_e_2_in_ctval_to_imval as [iv_e_2'].
  inversion_clear H2.
  inversion_clear H3.

  simpl in H_itu2_2_in_ctval_to_imval.
  inversion_clear H_itu2_2_in_ctval_to_imval as [iv2_2'].
  inversion_clear H2.
  inversion_clear H3.

  split; auto.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_e_itu_e_2 as [uH1 uH2 uH3 uH4 H_itd_e_itd_e_2 H_le_iu_e_iu_e_2].
  inversion_clear H_le_iu_e_iu_e_2 as [uH1 uH2 uH3 uH4 H_id_e_id_e_2 H_le_iv_e_iv_e_2].

  rewrite H9 in H_le_itu2_itu2_2.
  inversion_clear H_le_itu2_itu2_2 as [uH1 uH2 uH3 uH4 H_itd2_itd2_2 H_le_iu2_iu2_2].
  inversion_clear H_le_iu2_iu2_2 as [uH1 uH2 uH3 uH4 H_id2_id2_2 H_le_iv2_iv2_2].

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=id_e_2) (itd2':=conc_itdeps itd_e_2 itd2_2) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd_e_2) (itd2':=itd2_2) in H_l'; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id_e_2) (id2':=id2_2) in H_l; auto.

  exists itc; auto.
  exists itc; auto.

  (* case If_unknown *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of1 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).

  specialize (IHH_ctval_of2 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of2 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e1 itu)).
  specialize(IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of2 eq_refl).

  specialize (IHH_ctval_of3 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of3 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e2 itu)).
  specialize(IHH_ctval_of3 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of3 eq_refl).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu H_itu_in_imv.

  rewrite H_imv in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | |
                           | c e0 e3 e4 itd_e itd1 id_e id1 itu1 iv1
                           | c e0 e3 e4 itd_e itd2 id_e id2 itu2 iv2
                           | | | | | | ].

  (*** the condition evaluates to True *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent e4.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of1 (IV itd_e (IV_ id_e (IV_Bool true)))).
  elim IHH_ctval_of1.
  intros itu_e_2 HH.
  inversion_clear HH as [H_itu_e_2_in_ctval_to_imval H_le_itu_e_itu_e_2].
  destruct itu_e_2 as [itd_e_2 iu_e_2].
  destruct iu_e_2 as [id_e_2 iv_e_2].

  specialize (IHH_ctval_of2 itu1).
  elim IHH_ctval_of2.
  intros itu1_2 HH.
  inversion_clear HH as [H_itu1_2_in_ctval_to_imval H_le_itu1_itu1_2].
  destruct itu1_2 as [itd1_2 iu1_2].
  destruct iu1_2 as [id1_2 iv1_2].

  exists (IV (conc_itdeps id_e_2 (conc_itdeps itd_e_2 (conc_itdeps itd1_2 td2))) (IV_ (conc_ideps id_e_2 (conc_ideps id1_2 d2)) iv1_2)).
  split.

  simpl.
  unfold In, SetMap.
  exists iv1_2.

  simpl in H_itu_e_2_in_ctval_to_imval.
  inversion_clear H_itu_e_2_in_ctval_to_imval as [iv_e_2'].
  inversion_clear H0.
  inversion_clear H1.

  simpl in H_itu1_2_in_ctval_to_imval.
  inversion_clear H_itu1_2_in_ctval_to_imval as [iv1_2'].
  inversion_clear H0.
  inversion_clear H1.

  split; auto.
  apply Union_introl; auto.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_e_itu_e_2 as [uH1 uH2 uH3 uH4 H_itd_e_itd_e_2 H_le_iu_e_iu_e_2].
  inversion_clear H_le_iu_e_iu_e_2 as [uH1 uH2 uH3 uH4 H_id_e_id_e_2 H_le_iv_e_iv_e_2].

  rewrite H7 in H_le_itu1_itu1_2.
  inversion_clear H_le_itu1_itu1_2 as [uH1 uH2 uH3 uH4 H_itd1_itd1_2 H_le_iu1_iu1_2].
  inversion_clear H_le_iu1_iu1_2 as [uH1 uH2 uH3 uH4 H_id1_id1_2 H_le_iv1_iv1_2].

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=id_e_2) (itd2':=conc_itdeps itd_e_2 (conc_itdeps itd1_2 td2)) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd_e_2) (itd2':=(conc_itdeps itd1_2 td2)) in H_l'; auto.
  apply included_in_conc_itdeps_1; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id_e_2) (id2':=conc_ideps id1_2 d2) in H_l; auto.
  apply included_in_conc_itdeps_1; auto.

  exists itc; auto.
  exists itc; auto.

  (*** the condition evaluates to False *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent e4.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of1 (IV itd_e (IV_ id_e (IV_Bool false)))).
  elim IHH_ctval_of1.
  intros itu_e_2 HH.
  inversion_clear HH as [H_itu_e_2_in_ctval_to_imval H_le_itu_e_itu_e_2].
  destruct itu_e_2 as [itd_e_2 iu_e_2].
  destruct iu_e_2 as [id_e_2 iv_e_2].

  specialize (IHH_ctval_of3 itu2).
  elim IHH_ctval_of3.
  intros itu2_2 HH.
  inversion_clear HH as [H_itu2_2_in_ctval_to_imval H_le_itu2_itu2_2].
  destruct itu2_2 as [itd2_2 iu2_2].
  destruct iu2_2 as [id2_2 iv2_2].

  exists (IV (conc_itdeps id_e_2 (conc_itdeps itd_e_2 (conc_itdeps td1 itd2_2))) (IV_ (conc_ideps id_e_2 (conc_ideps d1 id2_2)) iv2_2)).
  split.

  simpl.
  unfold In, SetMap.
  exists iv2_2.

  simpl in H_itu_e_2_in_ctval_to_imval.
  inversion_clear H_itu_e_2_in_ctval_to_imval as [iv_e_2'].
  inversion_clear H0.
  inversion_clear H1.

  simpl in H_itu2_2_in_ctval_to_imval.
  inversion_clear H_itu2_2_in_ctval_to_imval as [iv2_2'].
  inversion_clear H0.
  inversion_clear H1.

  split; auto.
  apply Union_intror; auto.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_e_itu_e_2 as [uH1 uH2 uH3 uH4 H_itd_e_itd_e_2 H_le_iu_e_iu_e_2].
  inversion_clear H_le_iu_e_iu_e_2 as [uH1 uH2 uH3 uH4 H_id_e_id_e_2 H_le_iv_e_iv_e_2].

  rewrite H7 in H_le_itu2_itu2_2.
  inversion_clear H_le_itu2_itu2_2 as [uH1 uH2 uH3 uH4 H_itd2_itd2_2 H_le_iu2_iu2_2].
  inversion_clear H_le_iu2_iu2_2 as [uH1 uH2 uH3 uH4 H_id2_id2_2 H_le_iv2_iv2_2].

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=id_e_2) (itd2':=conc_itdeps itd_e_2 (conc_itdeps td1 itd2_2)) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=itd_e_2) (itd2':=conc_itdeps td1 itd2_2) in H_l'; auto.
  apply included_in_conc_itdeps_2; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=id_e_2) (id2':=conc_ideps d1 id2_2) in H_l; auto.
  apply included_in_conc_itdeps_2; auto.

  exists itc; auto.
  exists itc; auto.


  (* case If_empty *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e itu)).
  specialize(IHH_ctval_of (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of eq_refl).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu H_itu_in_imv.

  rewrite H_imv in H_itu_in_imv.
  inversion_clear H_itu_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | |
                           | c e0 e3 e4 itd_e itd1 id_e id1 itu1 iv1
                           | c e0 e3 e4 itd_e itd2 id_e id2 itu2 iv2
                           | | | | | | ].

  (*** the condition evaluates to True *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent e4.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of (IV itd_e (IV_ id_e (IV_Bool true)))).
  elim IHH_ctval_of.
  intros itu_e_2 HH.
  inversion_clear HH as [H_itu_e_2_in_ctval_to_imval H_le_itu_e_itu_e_2].
  destruct itu_e_2 as [itd_e_2 iu_e_2].
  destruct iu_e_2 as [id_e_2 iv_e_2].

  simpl in H_itu_e_2_in_ctval_to_imval.
  inversion_clear H_itu_e_2_in_ctval_to_imval as [iv_e_2'].
  inversion_clear H1.
  inversion H2.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_e_itu_e_2 as [uH1 uH2 uH3 uH4 H_itd_e_itd_e_2 H_le_iu_e_iu_e_2].
  inversion_clear H_le_iu_e_iu_e_2 as [uH1 uH2 uH3 uH4 H_id_e_id_e_2 H_le_iv_e_iv_e_2].
  inversion H_le_iv_e_iv_e_2.
  congruence.

  exists itc; auto.

  (*** the condition evaluates to False *)
  clear dependent c.
  clear dependent e0.
  clear dependent e3.
  clear dependent e4.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of (IV itd_e (IV_ id_e (IV_Bool false)))).
  elim IHH_ctval_of.
  intros itu_e_2 HH.
  inversion_clear HH as [H_itu_e_2_in_ctval_to_imval H_le_itu_e_itu_e_2].
  destruct itu_e_2 as [itd_e_2 iu_e_2].
  destruct iu_e_2 as [id_e_2 iv_e_2].

  simpl in H_itu_e_2_in_ctval_to_imval.
  inversion_clear H_itu_e_2_in_ctval_to_imval as [iv_e_2'].
  inversion_clear H1.
  inversion H2.

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_e_itu_e_2 as [uH1 uH2 uH3 uH4 H_itd_e_itd_e_2 H_le_iu_e_iu_e_2].
  inversion_clear H_le_iu_e_iu_e_2 as [uH1 uH2 uH3 uH4 H_id_e_id_e_2 H_le_iv_e_iv_e_2].
  inversion H_le_iv_e_iv_e_2.
  congruence.

  exists itc; auto.


  (* case Match *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of1 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).

  specialize (IHH_ctval_of2 (append_ctenv_to_imenv ctc_p imc)).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu0 H_itu0_in_imv.

  rewrite H_imv in H_itu0_in_imv.
  inversion_clear H_itu0_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | | | |
                           | c c_p e0 e2 e' p0 x itu itu1 itd itd1 id id1 v v1
                           | c e0 e1' e2 p0 x itu itu2 itd itd2 id id2 iv iv2
                           | | | | ].


  (*** itu is matched by the pattern  *)
  clear dependent e0.
  clear dependent p0.
  clear dependent e2.
  clear dependent c.

  (**** exists itu_2 > itu such as itu_2 is in (ctval_to_imval ctv) *)
  specialize (IHH_ctval_of1 itu).
  elim IHH_ctval_of1; try solve [exists itc; auto].
  intros itu_2 HH.
  inversion_clear HH as [H_itu_2_in_ctval_to_imval H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  (**** exists itc_p_2 > c_p such as is_filtered_itval itu_2 p = Filtered_itval_result_Match itc_p_2 *)
  assert(HH := is_filtered_le_itval _ _ _ _ H_le_itu_itu_2 H10).
  inversion_clear HH as [itc_p_2 HHH].
  inversion_clear HHH as [H_is_filtered_itu_2 H_le_c_p_itc_p_2].

  (**** inverse le_itval relations *)
  rewrite H8 in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_itd_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_id_id_2 H_le_iv_iv_2].

  (**** inverse In relations *)
  rewrite H in H_itu_2_in_ctval_to_imval.
  inversion H_itu_2_in_ctval_to_imval as [iv_2' HH].
  inversion_clear HH as [H_itu_2_itu_2' H_iv_2_in_ivs].
  inversion H_itu_2_itu_2' as [[H_itd_2 H_id_2 H_iv_2']].
  rewrite H_itd_2 in *; clear dependent itd_2.
  rewrite H_id_2 in *; clear dependent id_2.
  rewrite <-H_iv_2' in *; clear dependent iv_2'.

  (**** exists itc_p_2' > itc_p_2 such as itc_p_2' is in (ctenv_to_imenv ctc_p) *)
  assert (HH:=is_filtered_itval_in_ctval _ _ _ _ _ _ _ _ _ H H_itu_2_itu_2' H_iv_2_in_ivs H1 H_is_filtered_itu_2).
  inversion_clear HH as [itc_p_2' HHH].
  inversion_clear HHH as [H_itc_p_2'_in_ctc_p H_le_itc_p_2_itc_p_2'].

  (**** exists itu1_2 > itu1 such as ival_of (conc_itenv itc_p_2 itc) e1 itu1_2 *)
  apply ival_of_in_le_itenv with (itc2:=conc_itenv itc_p_2' itc) in H11.
  inversion_clear H11 as [itu1_2 HH].
  inversion_clear HH as [H_ival_of_e1 H_le_itu1_itu1_2].

  (**** inverse le_itval relations *)
  rewrite H12 in H_le_itu1_itu1_2.
  destruct itu1_2 as [itd1_2 iu1_2].
  destruct iu1_2 as [id1_2 iv1_2].
  inversion_clear H_le_itu1_itu1_2 as [uH1 uH2 uH3 uH4 H_itd1_itd1_2 H_le_iu1_iu1_2].
  inversion_clear H_le_iu1_iu1_2 as [uH1 uH2 uH3 uH4 H_id1_id1_2 H_le_iv1_iv1_2].


  (**** instantiate the induction hypothesis for e1 *)
  assert (H_ctc_p_not_empty := inhabited_ctenv_from_is_filtered _ _ _ _ _ _ H H0 H1).
  specialize (IHH_ctval_of2 (imenv_to_ctenv_of_append_ctenv_to_imenv _ _ _ H_imenv_to_ctenv H_ctc_p_not_empty)).
  specialize (IHH_ctval_of2 (fun itu : itval =>
                               exists itc : itenv,
                                 In itenv (append_ctenv_to_imenv ctc_p imc) itc /\
                                 ival_of itc e1 itu)).
  specialize (IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize (IHH_ctval_of2 eq_refl).
  specialize (IHH_ctval_of2 (IV itd1_2 (IV_ id1_2 iv1_2))).

  elim IHH_ctval_of2.
  intros itu1_2' HH.
  inversion_clear HH as [H_itu1_2'_in_imv1 H_le_itu1_2_itu1_2'].
  destruct itu1_2' as [itd1_2' iu1_2'].
  destruct iu1_2' as [id1_2' iv1_2'].

  (**** inverse le_itval relations *)
  inversion_clear H_le_itu1_2_itu1_2' as [uH1 uH2 uH3 uH4 H_itd1_2_itd1_2' H_le_iu1_2_iu1_2'].
  inversion_clear H_le_iu1_2_iu1_2' as [uH1 uH2 uH3 uH4 H_id1_2_id1_2' H_le_iv1_2_iv1_2'].

  (**** inverse In relations *)
  inversion H_itu1_2'_in_imv1 as [iv1_2'' HH].
  inversion_clear HH as [H_itu1_2'_itu1_2'' H_iv1_2'_in_ivs1].
  inversion H_itu1_2'_itu1_2'' as [[H_itd1_2' H_id1_2' H_iv1_2'']].
  rewrite H_itd1_2' in *; clear dependent itd1_2'.

  rewrite H_id1_2' in *; clear dependent id1_2'.
  rewrite <-H_iv1_2'' in *; clear dependent iv1_2''.
  
  exists (IV (conc_itdeps d (conc_itdeps td td1)) (IV_ (conc_ideps d d1) iv1_2')).
  split.

  exists iv1_2'; split; auto.

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=d) (itd2':=conc_itdeps td td1) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=td) (itd2':=td1) in H_l'; auto.
  intros l'' H_l''.
  auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=d) (id2':=d1) in H_l; auto.
  intros l' H_l'; auto.

  apply le_ival0_trans with (iv2:=iv1_2); auto.

  exists (conc_itenv itc_p_2' itc); auto.
  split; auto.

  apply conc_itenv_in_append_ctenv_to_imenv; auto.

  apply le_itenv_conc; auto.
  apply le_itenv_trans with (itc2:=itc_p_2); auto.
  apply le_itenv_refl.

  (*** itu is not matched by the pattern *)
  clear dependent e0.
  clear dependent p0.
  clear dependent e1'.
  clear dependent c.

  (**** exists itu_2 > itu such as itu_2 is in (ctval_to_imval ctv) *)
  specialize (IHH_ctval_of1 itu).
  elim IHH_ctval_of1; try solve [exists itc; auto].
  intros itu_2 HH.
  inversion_clear HH as [H_itu_2_in_ctval_to_imval H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  (**** is_filtered_itval itu_2 p = Filtered_itval_result_Match_var *)
  assert(H_is_not_filtered := is_not_filtered_le_itval _ _ _ H_le_itu_itu_2 H10).

  (**** inverse le_itval relations  *)
  rewrite H8 in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_itd_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_id_id_2 H_le_iv_iv_2].

  (**** inverse In relations *)
  rewrite H in H_itu_2_in_ctval_to_imval.
  inversion H_itu_2_in_ctval_to_imval as [iv_2' HH].
  inversion_clear HH as [H_itu_2_itu_2' H_iv_2_in_ivs].
  inversion H_itu_2_itu_2' as [[H_itd_2 H_id_2 H_iv_2']].
  rewrite H_itd_2 in *; clear dependent itd_2.
  rewrite H_id_2 in *; clear dependent id_2.
  rewrite <-H_iv_2' in *; clear dependent iv_2'.

  assert (HH:=is_filtered_itval_in_ctval_exists _ td d _ (IV td (IV_ d iv_2)) _ _ _ H eq_refl H_iv_2_in_ivs H1).
  congruence.

  (* case Match_var *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of1 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).

  specialize (IHH_ctval_of2 (SetMap2 (fun iv itc => ITEnv_cons x (IV td (IV_ d iv)) itc)
                                     ivs
                                     imc)).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu0 H_itu0_in_imv.

  rewrite H_imv in H_itu0_in_imv.
  inversion_clear H_itu0_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | | | |
                           | c c_p e0 e1' e2' p0 x' itu itu1 itd itd1 id id1 v v1
                           | c e0 e1' e2' p0 x' itu itu2 itd itd2 id id2 iv iv2
                           | | | | ].


  (*** itu is matched by the pattern  *)
  clear dependent e0.
  clear dependent p0.
  clear dependent e1'.
  clear dependent e2'.
  clear dependent x'.
  clear dependent c.

  (**** exists itu_2 > itu such as itu_2 is in (ctval_to_imval ctv) *)
  specialize (IHH_ctval_of1 itu).
  elim IHH_ctval_of1; try solve [exists itc; auto].
  intros itu_2 HH.
  inversion_clear HH as [H_itu_2_in_ctval_to_imval H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  (**** exists itc_p_2 > c_p such as is_filtered_itval itu_2 p = Filtered_itval_result_Match itc_p_2 *)
  assert(H_is_filtered := is_filtered_le_itval _ _ _ _ H_le_itu_itu_2 H11).
  inversion_clear H_is_filtered as [itc_p_2 HH].
  inversion_clear HH as [H_is_filtered H_le_c_p_itc_p_2].

  (**** inverse le_itval relations  *)
  rewrite H10 in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_itd_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_id_id_2 H_le_iv_iv_2].

  (**** inverse In relations *)
  rewrite H in H_itu_2_in_ctval_to_imval.
  inversion H_itu_2_in_ctval_to_imval as [iv_2' HH].
  inversion_clear HH as [H_itu_2_itu_2' H_iv_2_in_ivs].
  inversion H_itu_2_itu_2' as [[H_itd_2 H_id_2 H_iv_2']].
  rewrite H_itd_2 in *; clear dependent itd_2.
  rewrite H_id_2 in *; clear dependent id_2.
  rewrite <-H_iv_2' in *; clear dependent iv_2'.

  elim (is_not_filtered_itval_in_ctval_exists _ td d _ (IV td (IV_ d iv_2)) _ _ _ H eq_refl H_iv_2_in_ivs H1 H_is_filtered).

  (*** itu is not matched by the pattern *)
  clear dependent e0.
  clear dependent p0.
  clear dependent e1'.
  clear dependent e2'.
  clear dependent x'.
  clear dependent c.

  (**** exists itu_2 > itu such as itu_2 is in (ctval_to_imval ctv) *)
  specialize (IHH_ctval_of1 itu).
  elim IHH_ctval_of1; try solve [exists itc; auto]; clear IHH_ctval_of1.
  intros itu_2 HH.
  inversion_clear HH as [H_itu_2_in_ctval_to_imval H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  (**** is_filtered_itval itu_2 p = Filtered_itval_result_Match_var *)
  assert(H_is_not_filtered := is_not_filtered_le_itval _ _ _ H_le_itu_itu_2 H11).

  (**** inverse le_itval relations *)
  rewrite H10 in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_itd_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_id_id_2 H_le_iv_iv_2].

  (**** inverse In relations *)
  rewrite H in H_itu_2_in_ctval_to_imval.
  inversion H_itu_2_in_ctval_to_imval as [iv_2' HH].
  inversion_clear HH as [H_itu_2_itu_2' H_iv_2_in_ivs].
  inversion H_itu_2_itu_2' as [[H_itd_2 H_id_2 H_iv_2']].
  rewrite H_itd_2 in *; clear dependent itd_2.
  rewrite H_id_2 in *; clear dependent id_2.
  rewrite <-H_iv_2' in *; clear dependent iv_2'.

  (**** exists itu2_2 > itu2 such as ival_of (ITEnv_cons x itu_2 itc) e2 itu2_2 *)
  apply ival_of_in_le_itenv with (itc2:=ITEnv_cons x (IV td (IV_ d iv_2)) itc) in H12.
  inversion_clear H12 as [itu2_2 HH].
  inversion_clear HH as [H_ival_of_e1 H_le_itu1_itu2_2].

  (**** inverse le_itval relations *)
  rewrite H13 in H_le_itu1_itu2_2.
  destruct itu2_2 as [itd2_2 iu2_2].
  destruct iu2_2 as [id2_2 iv2_2].
  inversion_clear H_le_itu1_itu2_2 as [uH1 uH2 uH3 uH4 H_itd1_itd2_2 H_le_iu1_iu2_2].
  inversion_clear H_le_iu1_iu2_2 as [uH1 uH2 uH3 uH4 H_id1_id2_2 H_le_iv1_iv2_2].

  (**** instantiate the induction hypothesis for e2 *)
  rewrite H in IHH_ctval_of2.
  specialize (IHH_ctval_of2 (imenv_to_ctenv_cons _ _ _ _ _ _ H_imenv_to_ctenv (Inhabited_Intersection_1 _ _ _ H0))).
  specialize (IHH_ctval_of2 (fun itu : itval =>
                               exists itc : itenv,
                                 In itenv
                                    (SetMap2
                                       (fun (iv : ival0) (itc0 : itenv) =>
                                          ITEnv_cons x (IV td (IV_ d iv)) itc0) ivs imc) itc /\
                                 ival_of itc e2 itu)).
  specialize (IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize (IHH_ctval_of2 eq_refl).
  specialize (IHH_ctval_of2 (IV itd2_2 (IV_ id2_2 iv2_2))).
  elim IHH_ctval_of2;
    try solve [exists (ITEnv_cons x (IV td (IV_ d iv_2)) itc); split; auto; exists iv_2, itc; auto].
  intros itu2_2' HH.
  inversion_clear HH as [H_itu2_2'_in_imv2 H_le_itu2_2_itu2_2'].
  destruct itu2_2' as [itd2_2' iu2_2'].
  destruct iu2_2' as [id2_2' iv2_2'].

  (**** inverse le_itval relations *)
  inversion_clear H_le_itu2_2_itu2_2' as [uH1 uH2 uH3 uH4 H_itd2_2_itd2_2' H_le_iu2_2_iu2_2'].
  inversion_clear H_le_iu2_2_iu2_2' as [uH1 uH2 uH3 uH4 H_id2_2_id2_2' H_le_iv2_2_iv2_2'].

  (**** inverse In relations *)
  inversion H_itu2_2'_in_imv2 as [iv2_2'' HH].
  inversion_clear HH as [H_itu2_2'_itu2_2'' H_iv2_2'_in_ivs1].
  inversion H_itu2_2'_itu2_2'' as [[H_itd2_2' H_id2_2' H_iv2_2'']].
  rewrite H_itd2_2' in *; clear dependent itd2_2'.

  rewrite H_id2_2' in *; clear dependent id2_2'.
  rewrite <-H_iv2_2'' in *; clear dependent iv2_2''.
  
  exists (IV (conc_itdeps d (conc_itdeps td td2)) (IV_ (conc_ideps d d2) iv2_2')).
  split.

  exists iv2_2'; split; auto.

  tac_le_itval; auto.
  
  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=d) (itd2':=conc_itdeps td td2) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=td) (itd2':=td2) in H_l'; auto.
  intros l'' H_l''.
  auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=d) (id2':=d2) in H_l; auto.
  intros l' H_l'; auto.

  apply le_ival0_trans with (iv2:=iv2_2); auto.
  
  rewrite H10.
  tac_le_itval; auto.
  apply le_itenv_refl.

  (* case Match_unknown *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of1 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).

  specialize (IHH_ctval_of2 (append_ctenv_to_imenv ctc_p imc)).

  specialize (IHH_ctval_of3 (SetMap2 (fun iv itc => ITEnv_cons x (IV td (IV_ d iv)) itc)
                                     ivs
                                     imc)).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu0 H_itu0_in_imv.

  rewrite H_imv in H_itu0_in_imv.
  inversion_clear H_itu0_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | | | |
                           | c c_p e0 e1' e2' p0 x' itu itu1 itd itd1 id id1 v v1
                           | c e0 e1' e2' p0 x' itu itu2 itd itd2 id id2 iv iv2
                           | | | | ].


  (*** itu is matched by the pattern  *)
  clear dependent e0.
  clear dependent p0.
  clear dependent e1'.
  clear dependent e2'.
  clear dependent x'.
  clear dependent c.

  (**** exists itu_2 > itu such as itu_2 is in (ctval_to_imval ctv) *)
  specialize (IHH_ctval_of1 itu).
  elim IHH_ctval_of1; try solve [exists itc; auto].
  intros itu_2 HH.
  inversion_clear HH as [H_itu_2_in_ctval_to_imval H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  (**** exists itc_p_2 > c_p such as is_filtered_itval itu_2 p = Filtered_itval_result_Match itc_p_2 *)
  assert(HH := is_filtered_le_itval _ _ _ _ H_le_itu_itu_2 H11).
  inversion_clear HH as [itc_p_2 HHH].
  inversion_clear HHH as [H_is_filtered_itu_2 H_le_c_p_itc_p_2].

  (**** inverse le_itval relations *)
  rewrite H10 in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_itd_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_id_id_2 H_le_iv_iv_2].

  (**** inverse In relations *)
  rewrite H in H_itu_2_in_ctval_to_imval.
  inversion H_itu_2_in_ctval_to_imval as [iv_2' HH].
  inversion_clear HH as [H_itu_2_itu_2' H_iv_2_in_ivs].
  inversion H_itu_2_itu_2' as [[H_itd_2 H_id_2 H_iv_2']].
  rewrite H_itd_2 in *; clear dependent itd_2.
  rewrite H_id_2 in *; clear dependent id_2.
  rewrite <-H_iv_2' in *; clear dependent iv_2'.

  (**** exists itc_p_2' > itc_p_2 such as itc_p_2' is in (ctenv_to_imenv ctc_p) *)
  assert (HH:=is_filtered_itval_in_ctval_unknown _ _ _ _ _ _ _ _ _ H H_itu_2_itu_2' H_iv_2_in_ivs H1 H_is_filtered_itu_2).
  inversion_clear HH as [itc_p_2' HHH].
  inversion_clear HHH as [H_itc_p_2'_in_ctc_p H_le_itc_p_2_itc_p_2'].

  (**** exists itu1_2 > itu1 such as ival_of (conc_itenv itc_p_2 itc) e1 itu1_2 *)
  apply ival_of_in_le_itenv with (itc2:=conc_itenv itc_p_2' itc) in H12.
  inversion_clear H12 as [itu1_2 HH].
  inversion_clear HH as [H_ival_of_e1 H_le_itu1_itu1_2].

  (**** inverse le_itval relations *)
  rewrite H13 in H_le_itu1_itu1_2.
  destruct itu1_2 as [itd1_2 iu1_2].
  destruct iu1_2 as [id1_2 iv1_2].
  inversion_clear H_le_itu1_itu1_2 as [uH1 uH2 uH3 uH4 H_itd1_itd1_2 H_le_iu1_iu1_2].
  inversion_clear H_le_iu1_iu1_2 as [uH1 uH2 uH3 uH4 H_id1_id1_2 H_le_iv1_iv1_2].


  (**** instantiate the induction hypothesis for e1 *)
  assert (H_ctc_p_not_empty := inhabited_ctenv_from_is_filtered_unknown _ _ _ _ _ _ H H0 H1).
  specialize (IHH_ctval_of2 (imenv_to_ctenv_of_append_ctenv_to_imenv _ _ _ H_imenv_to_ctenv H_ctc_p_not_empty)).
  specialize (IHH_ctval_of2 (fun itu : itval =>
                               exists itc : itenv,
                                 In itenv (append_ctenv_to_imenv ctc_p imc) itc /\
                                 ival_of itc e1 itu)).
  specialize (IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize (IHH_ctval_of2 eq_refl).
  specialize (IHH_ctval_of2 (IV itd1_2 (IV_ id1_2 iv1_2))).

  elim IHH_ctval_of2.
  intros itu1_2' HH.
  inversion_clear HH as [H_itu1_2'_in_imv1 H_le_itu1_2_itu1_2'].
  destruct itu1_2' as [itd1_2' iu1_2'].
  destruct iu1_2' as [id1_2' iv1_2'].

  (**** inverse le_itval relations *)
  inversion_clear H_le_itu1_2_itu1_2' as [uH1 uH2 uH3 uH4 H_itd1_2_itd1_2' H_le_iu1_2_iu1_2'].
  inversion_clear H_le_iu1_2_iu1_2' as [uH1 uH2 uH3 uH4 H_id1_2_id1_2' H_le_iv1_2_iv1_2'].

  (**** inverse In relations *)
  inversion H_itu1_2'_in_imv1 as [iv1_2'' HH].
  inversion_clear HH as [H_itu1_2'_itu1_2'' H_iv1_2'_in_ivs1].
  inversion H_itu1_2'_itu1_2'' as [[H_itd1_2' H_id1_2' H_iv1_2'']].
  rewrite H_itd1_2' in *; clear dependent itd1_2'.

  rewrite H_id1_2' in *; clear dependent id1_2'.
  rewrite <-H_iv1_2'' in *; clear dependent iv1_2''.
  
  exists (IV (conc_itdeps d (conc_itdeps td (conc_itdeps td1 td2))) (IV_ (conc_ideps d (conc_ideps d1 d2)) iv1_2')).
  split.

  exists iv1_2'; split; auto.
  apply Union_introl; auto.

  tac_le_itval; auto.

  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=d) (itd2':=conc_itdeps td (conc_itdeps td1 td2)) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=td) (itd2':=(conc_itdeps td1 td2)) in H_l'; auto.
  intros l'' H_l''.
  apply label_in_conc_itdeps_1; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=d) (id2':=(conc_ideps d1 d2)) in H_l; auto.
  intros l' H_l'.
  apply label_in_conc_ideps_1; auto.

  apply le_ival0_trans with (iv2:=iv1_2); auto.

  exists (conc_itenv itc_p_2' itc); auto.
  split; auto.

  apply conc_itenv_in_append_ctenv_to_imenv; auto.

  apply le_itenv_conc; auto.
  apply le_itenv_trans with (itc2:=itc_p_2); auto.
  apply le_itenv_refl.

  (*** itu is not matched by the pattern  *)
  clear dependent e0.
  clear dependent p0.
  clear dependent e1'.
  clear dependent e2'.
  clear dependent x'.
  clear dependent c.

  (**** exists itu_2 > itu such as itu_2 is in (ctval_to_imval ctv) *)
  specialize (IHH_ctval_of1 itu).
  elim IHH_ctval_of1; try solve [exists itc; auto]; clear IHH_ctval_of1.
  intros itu_2 HH.
  inversion_clear HH as [H_itu_2_in_ctval_to_imval H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  (**** is_filtered_itval itu_2 p = Filtered_itval_result_Match_var *)
  assert(H_is_not_filtered := is_not_filtered_le_itval _ _ _ H_le_itu_itu_2 H11).

  (**** inverse le_itval relations *)
  rewrite H10 in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_itd_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_id_id_2 H_le_iv_iv_2].

  (**** inverse In relations *)
  rewrite H in H_itu_2_in_ctval_to_imval.
  inversion H_itu_2_in_ctval_to_imval as [iv_2' HH].
  inversion_clear HH as [H_itu_2_itu_2' H_iv_2_in_ivs].
  inversion H_itu_2_itu_2' as [[H_itd_2 H_id_2 H_iv_2']].
  rewrite H_itd_2 in *; clear dependent itd_2.
  rewrite H_id_2 in *; clear dependent id_2.
  rewrite <-H_iv_2' in *; clear dependent iv_2'.

  (**** exists itu2_2 > itu2 such as ival_of (ITEnv_cons x itu_2 itc) e2 itu2_2 *)
  apply ival_of_in_le_itenv with (itc2:=ITEnv_cons x (IV td (IV_ d iv_2)) itc) in H12.
  inversion_clear H12 as [itu2_2 HH].
  inversion_clear HH as [H_ival_of_e1 H_le_itu2_itu2_2].

  (**** inverse le_itval relations *)
  rewrite H13 in H_le_itu2_itu2_2.
  destruct itu2_2 as [itd2_2 iu2_2].
  destruct iu2_2 as [id2_2 iv2_2].
  inversion_clear H_le_itu2_itu2_2 as [uH1 uH2 uH3 uH4 H_itd2_itd2_2 H_le_iu2_iu2_2].
  inversion_clear H_le_iu2_iu2_2 as [uH1 uH2 uH3 uH4 H_id2_id2_2 H_le_iv2_iv2_2].

  (**** instantiate the induction hypothesis for e2 *)
  rewrite H in IHH_ctval_of3.
  specialize (IHH_ctval_of3 (imenv_to_ctenv_cons _ _ _ _ _ _ H_imenv_to_ctenv (Inhabited_Intersection_1 _ _ _ H0))).
  specialize (IHH_ctval_of3 (fun itu : itval =>
                               exists itc : itenv,
                                 In itenv
                                    (SetMap2
                                       (fun (iv : ival0) (itc0 : itenv) =>
                                          ITEnv_cons x (IV td (IV_ d iv)) itc0) ivs imc) itc /\
                                 ival_of itc e2 itu)).
  specialize (IHH_ctval_of3 (IMVal_of _ _ _ eq_refl)).
  specialize (IHH_ctval_of3 eq_refl).
  specialize (IHH_ctval_of3 (IV itd2_2 (IV_ id2_2 iv2_2))).
  elim IHH_ctval_of3;
    try solve [exists (ITEnv_cons x (IV td (IV_ d iv_2)) itc); split; auto; exists iv_2, itc; auto].
  intros itu2_2' HH.
  inversion_clear HH as [H_itu2_2'_in_imv2 H_le_itu2_2_itu2_2'].
  destruct itu2_2' as [itd2_2' iu2_2'].
  destruct iu2_2' as [id2_2' iv2_2'].

  (**** inverse le_itval relations *)
  inversion_clear H_le_itu2_2_itu2_2' as [uH1 uH2 uH3 uH4 H_itd2_2_itd2_2' H_le_iu2_2_iu2_2'].
  inversion_clear H_le_iu2_2_iu2_2' as [uH1 uH2 uH3 uH4 H_id2_2_id2_2' H_le_iv2_2_iv2_2'].

  (**** inverse In relations *)
  inversion H_itu2_2'_in_imv2 as [iv2_2'' HH].
  inversion_clear HH as [H_itu2_2'_itu2_2'' H_iv2_2'_in_ivs1].
  inversion H_itu2_2'_itu2_2'' as [[H_itd2_2' H_id2_2' H_iv2_2'']].
  rewrite H_itd2_2' in *; clear dependent itd2_2'.

  rewrite H_id2_2' in *; clear dependent id2_2'.
  rewrite <-H_iv2_2'' in *; clear dependent iv2_2''.
  
  exists (IV (conc_itdeps d (conc_itdeps td (conc_itdeps td1 td2))) (IV_ (conc_ideps d (conc_ideps d1 d2)) iv2_2')).
  split.

  exists iv2_2'; split; auto.
  apply Union_intror; auto.

  tac_le_itval; auto.
  
  (** itdeps *)
  intros l H_l.
  apply conc_itdeps_included with (itd1':=d) (itd2':=conc_itdeps td (conc_itdeps td1 td2)) in H_l; auto.
  intros l' H_l'.
  apply conc_itdeps_included with (itd1':=td) (itd2':=(conc_itdeps td1 td2)) in H_l'; auto.
  intros l'' H_l''.
  apply label_in_conc_itdeps_2; auto.

  (** ideps *)
  intros l H_l.
  apply conc_ideps_included with (id1':=d) (id2':=(conc_ideps d1 d2)) in H_l; auto.
  intros l' H_l'.
  apply label_in_conc_ideps_2; auto.

  apply le_ival0_trans with (iv2:=iv2_2); auto.
  
  rewrite H10.
  tac_le_itval; auto.
  apply le_itenv_refl.

  (* case Match_empty *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e itu)).
  specialize(IHH_ctval_of (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of eq_refl).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu0 H_itu0_in_imv.

  rewrite H_imv in H_itu0_in_imv.
  inversion_clear H_itu0_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | | | |
                           | c c_p e0 e1' e2' p0 x' itu itu1 itd itd1 id id1 v v1
                           | c e0 e1' e2' p0 x' itu itu2 itd itd2 id id2 iv iv2
                           | | | | ].


  (*** itu is matched by the pattern  *)
  clear dependent e0.
  clear dependent p0.
  clear dependent e1'.
  clear dependent e2'.
  clear dependent x'.
  clear dependent c.

  (**** exists itu_2 > itu such as itu_2 is in (ctval_to_imval ctv) *)
  specialize (IHH_ctval_of itu).
  elim IHH_ctval_of; try solve [exists itc; auto]; clear IHH_ctval_of.
  intros itu_2 HH.
  inversion_clear HH as [H_itu_2_in_ctval_to_imval H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  (**** exists itc_p_2 > c_p such as is_filtered_itval itu_2 p = Filtered_itval_result_Match itc_p_2 *)
  assert(H_is_filtered := is_filtered_le_itval _ _ _ _ H_le_itu_itu_2 H9).
  inversion_clear H_is_filtered as [itc_p_2 HH].
  inversion_clear HH as [H_is_filtered H_le_c_p_itc_p_2].

  (**** inverse le_itval relations  *)
  rewrite H7 in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_itd_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_id_id_2 H_le_iv_iv_2].

  (**** inverse In relations *)
  rewrite H in H_itu_2_in_ctval_to_imval.
  inversion H_itu_2_in_ctval_to_imval as [iv_2' HH].
  inversion_clear HH as [H_itu_2_itu_2' H_iv_2_in_ivs].
  inversion H_itu_2_itu_2' as [[H_itd_2 H_id_2 H_iv_2']].
  rewrite H_itd_2 in *; clear dependent itd_2.
  rewrite H_id_2 in *; clear dependent id_2.
  rewrite <-H_iv_2' in *; clear dependent iv_2'.

  elim H0.
  exists iv_2.
  apply Intersection_intro; auto.

  apply (is_filtered_itval_implies_is_matchable _ _ _ _ _ H_is_filtered).

  (*** itu is not matched by the pattern *)
  clear dependent e0.
  clear dependent p0.
  clear dependent e1'.
  clear dependent c.

  (**** exists itu_2 > itu such as itu_2 is in (ctval_to_imval ctv) *)
  specialize (IHH_ctval_of itu).
  elim IHH_ctval_of; try solve [exists itc; auto].
  intros itu_2 HH.
  inversion_clear HH as [H_itu_2_in_ctval_to_imval H_le_itu_itu_2].
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  (**** is_filtered_itval itu_2 p = Filtered_itval_result_Match_var *)
  assert(H_is_not_filtered := is_not_filtered_le_itval _ _ _ H_le_itu_itu_2 H9).

  (**** inverse le_itval relations  *)
  rewrite H7 in H_le_itu_itu_2.
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_itd_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_id_id_2 H_le_iv_iv_2].

  (**** inverse In relations *)
  rewrite H in H_itu_2_in_ctval_to_imval.
  inversion H_itu_2_in_ctval_to_imval as [iv_2' HH].
  inversion_clear HH as [H_itu_2_itu_2' H_iv_2_in_ivs].
  inversion H_itu_2_itu_2' as [[H_itd_2 H_id_2 H_iv_2']].
  rewrite H_itd_2 in *; clear dependent itd_2.
  rewrite H_id_2 in *; clear dependent id_2.
  rewrite <-H_iv_2' in *; clear dependent iv_2'.

  elim H0.
  exists iv_2.
  apply Intersection_intro; auto.

  apply (is_not_filtered_itval_implies_is_matchable _ _ _ _ H_is_not_filtered).

  (* case Couple *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of1 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e1 itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).

  specialize (IHH_ctval_of2 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of2 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e2 itu)).
  specialize(IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of2 eq_refl).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu0 H_itu0_in_imv.

  rewrite H_imv in H_itu0_in_imv.
  inversion_clear H_itu0_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | | | | | | | |
                           | c e1' e2' itd1 itd2 iu1 iu2
                           | ].

  clear dependent c.
  clear dependent e1'.
  clear dependent e2'.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of1 (IV itd1 iu1)).
  elim IHH_ctval_of1; try solve [exists itc; auto];
  clear IHH_ctval_of1.
  intros itu1_2 HH.
  inversion_clear HH as [H_itu1_2_in_ivs1 H_le_itu1_itu1_2].

  specialize (IHH_ctval_of2 (IV itd2 iu2)).
  elim IHH_ctval_of2; try solve [exists itc; auto];
  clear IHH_ctval_of2.
  intros itu2_2 HH.
  inversion_clear HH as [H_itu2_2_in_ivs2 H_le_itu2_itu2_2].

  (** destruct the _2 values *)
  destruct itu1_2 as [itd1_2 iu1_2].
  destruct itu2_2 as [itd2_2 iu2_2].

  (** inverse le_itval relations *)
  inversion_clear H_le_itu1_itu1_2 as [uH1 uH2 uH3 uH4 H_itd1_itd1_2 H_le_iu1_iu1_2].
  inversion_clear H_le_itu2_itu2_2 as [uH1 uH2 uH3 uH4 H_itd2_itd2_2 H_le_iu2_iu2_2].

  (** inverse In relations *)
  destruct iu1_2 as [id1_2 iv1_2].
  inversion H_itu1_2_in_ivs1 as [iv1_2' HH].
  inversion_clear HH as [H_itu1_2_itu1_2' H_iv1_2_in_ivs1].
  inversion H_itu1_2_itu1_2' as [[H_itd1_2 H_id1_2 H_iv1_2']].
  rewrite H_itd1_2 in *; clear dependent itd1_2.
  rewrite H_id1_2 in *; clear dependent id1_2.
  rewrite <-H_iv1_2' in *; clear dependent iv1_2'.


  destruct iu2_2 as [id2_2 iv2_2].
  inversion H_itu2_2_in_ivs2 as [iv2_2' HH].
  inversion_clear HH as [H_itu2_2_itu2_2' H_iv2_2_in_ivs1].
  inversion H_itu2_2_itu2_2' as [[H_itd2_2 H_id2_2 H_iv2_2']].
  rewrite H_itd2_2 in *; clear dependent itd2_2.
  rewrite H_id2_2 in *; clear dependent id2_2.
  rewrite <-H_iv2_2' in *; clear dependent iv2_2'.

  exists (IV (conc_itdeps td1 td2) (IV_ nil (IV_Couple (IV_ d1 iv1_2) (IV_ d2 iv2_2)))).
  split.

  rewrite H.
  unfold In, SetMap2, SetMap.
  exists (IV_Couple (IV_ d1 iv1_2) (IV_ d2 iv2_2)).
  split; auto.
  exists iv1_2, iv2_2; auto.

  tac_le_itval; try congruence.
  
  intros l H_l.
  apply conc_itdeps_included with (itd1':=td1) (itd2':=td2) in H_l; auto.

  (* case Annot *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e itu)).
  specialize(IHH_ctval_of (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of eq_refl).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu0 H_itu0_in_imv.

  rewrite H_imv in H_itu0_in_imv.
  inversion_clear H_itu0_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | | | | | | | | | | |  ].
  clear dependent c.
  clear dependent l0.
  clear dependent e0.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of (IV td0 (IV_ d0 v))).
  elim IHH_ctval_of; try solve [exists itc; auto];
  clear IHH_ctval_of.
  intros itu_2 HH.
  inversion_clear HH as [H_itu_2_in_ivs H_le_itu_itu_2].

  (** destruct the _2 values *)
  destruct itu_2 as [itd_2 iu_2].
  destruct iu_2 as [id_2 iv_2].

  (** inverse le_itval relations *)
  inversion_clear H_le_itu_itu_2 as [uH1 uH2 uH3 uH4 H_itd_itd_2 H_le_iu_iu_2].
  inversion_clear H_le_iu_iu_2 as [uH1 uH2 uH3 uH4 H_id_id_2 H_le_iv_iv_2].

  (** inverse In relations *)
  inversion H_itu_2_in_ivs as [iv_2' HH].
  inversion_clear HH as [H_itu_2_itu_2' H_iv_2_in_ivs].
  inversion H_itu_2_itu_2' as [[H_itd_2 H_id_2 H_iv_2']].
  rewrite H_itd_2 in *; clear dependent itd_2.
  rewrite H_id_2 in *; clear dependent id_2.
  rewrite <-H_iv_2' in *; clear dependent iv_2'.

  exists (IV td (IV_ (l :: d)%list iv_2)).
  split.

  exists iv_2; auto.

  tac_le_itval; auto.

  intros l' H_l'.
  simpl; simpl in H_l'.
  inversion H_l'; auto.

  (* case Let_in *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of1 imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of1 (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e1 itu)).
  specialize(IHH_ctval_of1 (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of1 eq_refl).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu0 H_itu0_in_imv.

  rewrite H_imv in H_itu0_in_imv.
  inversion_clear H_itu0_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | |
                           | c x0 e0 e3 itu1 itu2 itd1 itd2 iu1 iu2
                               H_ival_of_e1 H_itu1 H_ival_of_e2 H_itu2 H_itu0
                           | | | | | | | | ].
  clear dependent x0.
  clear dependent e0.
  clear dependent e3.
  clear dependent c.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of1 itu1).
  elim IHH_ctval_of1; try solve [eexists itc; auto].
  clear IHH_ctval_of1.
  intros itu1_2 HH.
  inversion_clear HH as [H_itu1_2_in_ctv1 H_le_itu1_itu1_2].

  specialize (IHH_ctval_of2 (SetMap2 (fun iv itc => ITEnv_cons x (IV td1 (IV_ d1 iv)) itc)
                                     ivs1
                                     imc)).
  assert(HH_imenv_to_ctenv : imenv_to_ctenv
                               (SetMap2
                                  (fun (iv : ival0) (itc : itenv) =>
                                     ITEnv_cons x (IV td1 (IV_ d1 iv)) itc) ivs1 imc)
                               (CTEnv_cons x ctv1 ctc)).
  apply Imenv_to_ctenv_cons with (imc':=imc) (td:=td1) (d:=d1) (ivs:=ivs1)
                                             (imv:=SetMap (fun iv1 => IV td1 (IV_ d1 iv1)) ivs1); auto.
  unfold Included, SetMap2, SetMap, In.
  split.
  intros itc'' HH.
  inversion_clear HH as [iv HHH].
  inversion_clear HHH as [itc' HH].
  inversion_clear HH as [H_itc'' HHH].
  inversion_clear HHH as [H_iv_in_ivs1 H_itc'_in_imc].
  rewrite H_itc''.
  unfold In.
  exists (IV td1 (IV_ d1 iv)), itc'.
  repeat split; auto.
  exists iv; split; auto.
  
  intros itc'' HH.
  inversion_clear HH as [itu HHH].
  inversion_clear HHH as [itc' HH].
  inversion_clear HH as [H_itc'' HHH].
  inversion_clear HHH as [HH H_itc'_in_imc].
  inversion_clear HH as [iv1 HHH].
  inversion_clear HHH as [H_itu HH_iv1_in_ivs1].
  exists iv1, itc'.
  repeat split; auto.
  rewrite H_itc'', H_itu; auto.


  apply Td_of_imval.
  split.
  intros HH.
  inversion_clear HH as [itd HHH].
  inversion_clear HHH as [id HH].
  inversion_clear HH as [iv HHH].
  inversion_clear HHH as [H_l_in_itd HH].
  inversion_clear HH as [H_iv' HHH].
  inversion_clear HHH as [H_itu H_iv'_in_ivs1].
  inversion H_itu.
  rewrite <-H4; auto.

  intros H_l_in_td1.
  inversion H0 as [iv1 H_iv1_in_ivs1].
  exists td1, d1, iv1.
  split; auto.
  exists iv1; auto.

  apply D_of_imval.
  split.
  intros HH.
  inversion_clear HH as [itd HHH].
  inversion_clear HHH as [id HH].
  inversion_clear HH as [iv HHH].
  inversion_clear HHH as [H_l_in_itd HH].
  inversion_clear HH as [H_iv' HHH].
  inversion_clear HHH as [H_itu H_iv'_in_ivs1].
  inversion H_itu.
  rewrite <-H5; auto.

  intros H_l_in_td1.
  inversion H0 as [iv1 H_iv1_in_ivs1].
  exists td1, d1, iv1.
  split; auto.
  exists iv1; auto.

  unfold Same_set, SetMap.
  split.
  intros iv HH.
  exists (IV td1 (IV_ d1 iv)).
  split; auto.
  exists iv; auto.

  intros iv HH.
  inversion HH as [itu HHH].
  inversion_clear HHH as [HH1 HH2].
  destruct itu as [itd iu].
  destruct iu as [id iv'].
  inversion HH2.
  inversion H1.
  inversion H2.
  congruence.


  specialize (IHH_ctval_of2 HH_imenv_to_ctenv); clear HH_imenv_to_ctenv.
  specialize (IHH_ctval_of2 (fun itu : itval =>
                               exists itc : itenv,
                                 In itenv
                                    (SetMap2
                                       (fun (iv : ival0) (itc0 : itenv) =>
                                          ITEnv_cons x (IV td1 (IV_ d1 iv)) itc0) ivs1 imc)
                                    itc /\ ival_of itc e2 itu)).
  specialize (IHH_ctval_of2 (IMVal_of _ _ _ eq_refl)).
  specialize (IHH_ctval_of2 eq_refl).


  destruct iu1 as [id1 iv1].
  destruct itu1_2 as [itd1_2 iu1_2] eqn:H_itu1_2.
  destruct iu1_2 as [id1_2 iv1_2].

  (** inverse le_itval relations *)
  rewrite H_itu1 in H_le_itu1_itu1_2.
  inversion_clear H_le_itu1_itu1_2 as [uH1 uH2 uH3 uH4 H_itd1_itd1_2 H_le_iu1_iu1_2].
  inversion_clear H_le_iu1_iu1_2 as [uH1 uH2 uH3 uH4 H_id1_id1_2 H_le_iv1_iv1_2].

  (** inverse In relations *)
  rewrite H in H_itu1_2_in_ctv1.
  inversion_clear H_itu1_2_in_ctv1 as [iv1_2' HH].
  inversion_clear HH as [H_itu1_2_ H_iv1_2_in_ivs1].
  inversion H_itu1_2_.
  rewrite H4 in *.
  rewrite H5 in *.
  rewrite <-H6 in *.
  clear dependent itd1_2.
  clear dependent id1_2.
  clear dependent iv1_2'.
  clear H_itu1_2_.


  apply ival_of_in_le_itenv with (itc2:=ITEnv_cons x (IV td1 (IV_ d1 iv1_2)) itc) in H_ival_of_e2.
  inversion_clear H_ival_of_e2 as [itu2_2 HH].
  inversion_clear HH as [H_ival_of_e2 H_le_itu2_itu2_2].

  specialize (IHH_ctval_of2 itu2_2).


  elim IHH_ctval_of2.

  intros itu2_2' HH.
  inversion_clear HH as [H_itu2_2'_in_ctv2 H_le_itu2_2_itu2_2'].
  destruct itu2_2' as [itd2_2' iu2_2'].
  destruct iu2_2' as [id2_2' iv2_2'].
  exists (IV (conc_itdeps td1 td2) (IV_ d2 iv2_2')).
  split.
  
  simpl.
  exists iv2_2'; split; auto.
  rewrite H1 in H_itu2_2'_in_ctv2.
  inversion_clear H_itu2_2'_in_ctv2 as [iv2_2'' HH].
  inversion_clear HH.
  inversion H2; auto.

  (** inverse le_itval relations *)
  assert(H_le_itu2_itu2_2' := le_itval_trans _ _ _ H_le_itu2_itu2_2 H_le_itu2_2_itu2_2').
  rewrite H_itu2 in H_le_itu2_itu2_2'.
  inversion_clear H_le_itu2_itu2_2' as [uH1 uH2 uH3 uH4 H_itd2_itd2_2' H_le_iu2_iu2_2'].
  destruct iu2 as [id2 iv2].
  inversion_clear H_le_iu2_iu2_2' as [uH1 uH2 uH3 uH4 H_id2_id2_2' H_le_iv2_iv2_2'].
  

  (** inverse In relations *)
  rewrite H1 in H_itu2_2'_in_ctv2.
  inversion_clear H_itu2_2'_in_ctv2 as [iv2_2'' HH].
  inversion_clear HH as [H_itu2_2'_ H_iv2_2'_in_ivs2].
  inversion H_itu2_2'_.
  rewrite H4 in *.
  rewrite H5 in *.
  rewrite <-H6 in *.
  clear dependent itd2_2'.
  clear dependent id2_2'.
  clear dependent iv2_2''.
  clear H_itu2_2'_.

  tac_le_itval; auto.
  intros l H_l.
  apply conc_itdeps_included with (itd1':=td1) (itd2':=td2) in H_l; auto.

  exists (ITEnv_cons x (IV td1 (IV_ d1 iv1_2)) itc).
  split; auto.
  exists iv1_2, itc; repeat split; repeat f_equal; auto.

  rewrite H_itu1.
  tac_le_itval; auto.
  apply le_itenv_refl.

  (* case Let_in_empty *)
  (** instantiate the induction hypothesis *)
  specialize (IHH_ctval_of imc H_imenv_to_ctenv).
  specialize (IHH_ctval_of (fun itu : itval =>
                               exists itc : itenv, In itenv imc itc /\ ival_of itc e1 itu)).
  specialize(IHH_ctval_of (IMVal_of _ _ _ eq_refl)).
  specialize(IHH_ctval_of eq_refl).

  (** let's take a itu in imv and prove that there is itu2 > itu in the ctval_to_imval *)
  intros itu0 H_itu0_in_imv.

  rewrite H_imv in H_itu0_in_imv.
  inversion_clear H_itu0_in_imv as [itc HH].
  inversion_clear HH as [H_itc_in_imc H_ival_of].

  (** inversion of the ival_of rule *)
  inversion H_ival_of as [ | | | | |
                           | c x0 e0 e3 itu1 itu2 itd1 itd2 iu1 iu2
                               H_ival_of_e1 H_itu1 H_ival_of_e2 H_itu2 H_itu0
                           | | | | | | | | ].
  clear dependent x0.
  clear dependent e0.
  clear dependent e3.
  clear dependent c.

  (** instantiate again the induction hypothesis *)
  specialize (IHH_ctval_of itu1).
  elim IHH_ctval_of; try solve [eexists itc; auto];
  clear IHH_ctval_of.
  intros itu1_2 HH.
  inversion_clear HH as [H_itu1_2_in_ctv1 H_le_itu1_itu1_2].

  (** destruct the _2 value *)
  destruct itu1_2 as [itd1_2 iu1_2].
  destruct iu1_2 as [id1_2 iv1_2].

  (** inverse In relations *)
  rewrite H in H_itu1_2_in_ctv1.
  inversion_clear H_itu1_2_in_ctv1 as [iv1_2'' HH].
  inversion_clear HH as [H_itu1_2'_ H_iv1_2'_in_ivs1].

  elim H0.
  exists iv1_2''; auto.
Qed.


(*
TODO: déplacer ce commentaire dans un endroit approprié
 (il peut servir de brouillon pour la rédaction du manuscrit de thèse)


Explication de la preuve de ctval_of :

On a un jugement de la sémantique instrumentée multiple.
On a un jugement de la sémantique collectrice.
L'environnement collecteur est l'abstraction de l'environnement instrumenté multiple.
On veut vérifier que la valeur instrumentée multiple est plus petite que la concrétisation de la valeur collectrice.

On fait la preuve par induction sur le jugement de la sémantique collectrice.

Dans le cas Let_in :

On prend un élément de la valeur IM pour montrer qu'il est dans l'abstraction de la valeur COL.
Cette valeur instrumentée vient d'un jugement instrumenté de l'expression globale.
Ce jugement vient d'un jugement pour e1 et d'un jugement pour e2.
D'après l'hypothèse d'induction pour e1, on a une valeur itu1_2 > itu1 telle que itu1_2 est dans l'abstraction de ctv1.
Le jugement pour e2 est établi pour un environnement construit à partir de itu1.
Il existe un environnement plus grand, construit à partir de itu1_2, qui fait partie d'un environnement instrumenté multiple dont l'abstraction est l'environnement collecteur du jugement de la sémantique collectrice de e2.
La valeur de e2 dans cet environnement plus grand est un itu2_2 > itu2.
D'après l'hypothèse d'induction, il existe une valeur itu2_2' > itu2_2 qui soit dans l'abstraction de ctv2.
A partir de itu1_2 et de itu2_2', on peut construire une valeur itu_2 > itu qui soit dans l'abstraction de ctv.

*)
