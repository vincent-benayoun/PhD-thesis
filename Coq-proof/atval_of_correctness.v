
Add Rec LoadPath "." as DEP_AI.

Require Import language.

Require Import instrumented_values.
Require Import itval_val_conversion.

Require Import collecting_values.
Require Import collecting_semantics.

Require Import abstract_values.
Require Import abstract_semantics.

Require Import ctval_order.
Require Import ctval_imval_conversion.
Require Import atval_ctval_conversion.

Require Import ensembles.
Require Import imval_order.

Require Import instrumented_semantics.
Require Import instrumented_multiple_values.
Require Import instrumented_multiple_semantics.
Require Import ctval_of_correctness.



Lemma assoc_ident_in_ctenv_to_atenv :
  forall (ctc:ctenv) (atc:atenv) (x:identifier)
         (ctv:ctval) (atu:atval),
  ctenv_to_atenv ctc atc
  -> assoc_ident_in_ctenv x ctc = Ident_in_ctenv ctv
  -> assoc_ident_in_atenv x atc = Ident_in_atenv atu
  -> ctval_to_atval ctv atu.
Proof.

Admitted.
  
Lemma ctval_to_atval_to_ctval :
  forall (ctv:ctval) (atu:atval),
    ctval_to_atval ctv atu
    -> le_ctval ctv (atval_to_ctval atu).
Proof.

Admitted.


Lemma ctenv_to_atenv_to_cenv :
  forall (ctc:ctenv) (itc:itenv) (atc:atenv),
    In itenv (ctenv_to_imenv ctc) itc
    -> ctenv_to_atenv ctc atc
    -> exists (ic2:ienv),
         In _ (aenv_to_cenv (atenv_to_aenv atc)) ic2
         /\ le_ienv (itenv_to_ienv itc) ic2.
Proof.

Admitted.


Hint Constructors ctval_of : ctval_of.

Lemma exists_td_of_imv :
  forall (imv:instrumented_multiple_values.imval),
    exists (td:itdeps),
      (forall l:label, List.In l td
                       <-> (exists td',
                              List.In l td'
                              /\ In _ (SetMap (fun itu => match itu with | IV td (IV_ d iv) => td end) imv) td')).
Proof.

Admitted.

Lemma exists_d_of_imv :
  forall (imv:instrumented_multiple_values.imval),
    exists (d:itdeps),
      (forall l:label, List.In l d
                       <-> (exists d',
                              List.In l d'
                              /\ In _ (SetMap (fun itu => match itu with | IV td (IV_ d iv) => d end) imv) d')).
Proof.

Admitted.


Lemma ctval_of_total :
  forall (e:expr) (ctc:ctenv),
    exists (ctv:ctval),
      ctval_of ctc e ctv.
Proof.
  induction e;
  intros ctc.

  eexists; auto with ctval_of.
  eexists; auto with ctval_of.

  (* case Constr1 *)
  specialize(IHe ctc).
  inversion_clear IHe as [ctv H_ctval_of_e].
  destruct ctv as [td d ivs].
  exists (CTVal td nil (SetMap (fun iv => IV_Constr1 c (IV_ d iv)) ivs)).
  apply CTVal_of_Constr1 with (d:=d) (ivs:=ivs); auto.

  (* case Var *)
  destruct(assoc_ident_in_ctenv i ctc) eqn:H_assoc.
  (** ident in ctc *)
  eexists; auto with ctval_of.  
  (** ident not in ctc *)
  exists (c); auto with ctval_of.

  (* case Lambda *)
  specialize(IHe ctc).
  inversion_clear IHe as [ctv H_ctval_of_e].
  eexists; auto with ctval_of.

  (* case Rec *)
  specialize(IHe ctc).
  inversion_clear IHe as [ctv H_ctval_of_e].
  eexists; auto with ctval_of.

  (* case Apply *)
  specialize(IHe1 ctc).
  specialize(IHe2 ctc).
  inversion_clear IHe1 as [ctv1 H_ctval_of_e1].
  inversion_clear IHe2 as [ctv2 H_ctval_of_e2].
  destruct ctv1 as [td1 d1 ivs1].
  destruct ctv2 as [td2 d2 ivs2].
  set(imv:=(fun itu => (exists x e ic1 iv2 itd id iv,
                             In _ ivs1 (IV_Closure x e ic1)
                             /\ In _ ivs2 iv2
                             /\ instrumented_semantics.ival_of (ITEnv_cons x (IV td2 (IV_ d2 iv2)) (ienv_to_itenv ic1))
                                                               e
                                                               (IV itd (IV_ id iv))
                             /\ itu = IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd d1)))
                                         (IV_ (conc_ideps d1 id) iv))
                          \/ (exists f x e ic iv2 itd id iv,
                                In _ ivs1 (IV_Rec_Closure f x e ic)
                                /\ In _ ivs2 iv2
                                /\ instrumented_semantics.ival_of (ITEnv_cons f (IV td1 (IV_ d1 (IV_Rec_Closure f x e ic)))
                                                                              (ITEnv_cons x (IV td2 (IV_ d2 iv2)) (ienv_to_itenv ic)))
                                                                  e
                                                                  (IV itd (IV_ id iv))
                                /\ itu = IV (conc_itdeps td1 (conc_itdeps td2 (conc_itdeps itd d1)))
                                            (IV_ (conc_ideps d1 id) iv))) : Ensemble itval).
  destruct(exists_td_of_imv imv) as [td H_td].
  destruct(exists_d_of_imv imv) as [d H_d].
  exists (CTVal td d (SetMap (fun itu => match itu with | IV td (IV_ d iv) => iv end) imv)).
  apply CTVal_of_Apply with (td1:=td1) (td2:=td2) (d1:=d1) (d2:=d2) (ivs1:=ivs1) (ivs2:=ivs2)
                                       (imv:=imv) (td:=td) (d:=d); auto.


Admitted.

Lemma atval_to_ctval_to_atval :
  forall (atu:atval), ctval_to_atval (atval_to_ctval atu) atu.
Proof.

Admitted.

Lemma atenv_to_ctenv_to_atenv :
  forall (atc:atenv), ctenv_to_atenv (atenv_to_ctenv atc) atc.
Proof.
  induction atc.
  
  apply Ctenv_to_atenv_empty.
  apply Ctenv_to_atenv_cons.
  apply atval_to_ctval_to_atval.
  auto.
Qed.

Lemma ienv_to_itenv_in_aenv_to_to_imenv :
  forall (ac:aenv) (ic:ienv),
    In ienv (aenv_to_cenv ac) ic
    -> In _ (ctenv_to_imenv (atenv_to_ctenv (aenv_to_atenv ac))) (ienv_to_itenv ic).
Proof.

Admitted.


Lemma le_ienv_to_itenv :
  forall (ic ic':ienv),
    le_ienv ic ic'
    -> le_itenv (ienv_to_itenv ic) (ienv_to_itenv ic').
Proof.

Admitted.




Theorem atval_of_correctness :
  forall (e:expr) (ctc:ctenv) (ctv:ctval)
         (atc:atenv) (atu:atval),
    ctenv_to_atenv ctc atc
    -> ctval_of ctc e ctv
    -> atval_of atc e atu
    -> le_ctval ctv (atval_to_ctval atu).
Proof.
  intros e ctc ctv atc atu H_ctc_atc H_ctval_of H_atval_of.

  revert dependent ctc.
  revert dependent ctv.
  induction H_atval_of;
    intros ctv ctc H_ctc_atc H_ctval_of.

  (* case Num *)
  inversion H_ctval_of.
  simpl.
  apply Le_ctval; try solve [intros l; auto].
  intros iv H_iv_in.
  exists iv.
  split.
  unfold In; auto.
  apply le_ival0_refl.

  (* case Var *)
  inversion H_ctval_of.
  assert(H_ctv_atu:= assoc_ident_in_ctenv_to_atenv _ _ _ _ _ H_ctc_atc H2 H).
  apply ctval_to_atval_to_ctval; auto.
  destruct atu.
  destruct au.
  simpl.
  apply Le_ctval; try solve [intros l; inversion 1].

  (* case Lambda *)
  inversion H_ctval_of.
  clear dependent ctc0.
  clear dependent ctv0.
  clear dependent x0.
  clear dependent e0.
  rewrite H.
  apply Le_ctval; try solve [intros l; inversion 1].
  rewrite H4.
  clear dependent ivs.
  intros iv H_iv_in_ivs.
  simpl.
  inversion_clear H_iv_in_ivs as [itc HH].
  inversion_clear HH as [H_iv H_itc_in_ctc].

  assert(H_ex_ic2:=ctenv_to_atenv_to_cenv _ _ _ H_itc_in_ctc H_ctc_atc).
  inversion_clear H_ex_ic2 as [ic2 HH].
  inversion_clear HH as [H_ic2_in_ H_le_ic_ic2].

  exists (IV_Closure x e ic2).
  split.
  exists ic2; auto.
  rewrite H_iv.
  tac_le_itval; auto.

  (* case Rec *)
  inversion H_ctval_of.
  clear dependent ctc0.
  clear dependent ctv0.
  clear dependent f0.
  clear dependent x0.
  clear dependent e0.
  rewrite H.
  apply Le_ctval; try solve [intros l; inversion 1].
  rewrite H5.
  clear dependent ivs.
  intros iv H_iv_in_ivs.
  simpl.
  inversion_clear H_iv_in_ivs as [itc HH].
  inversion_clear HH as [H_iv H_itc_in_ctc].

  assert(H_ex_ic2:=ctenv_to_atenv_to_cenv _ _ _ H_itc_in_ctc H_ctc_atc).
  inversion_clear H_ex_ic2 as [ic2 HH].
  inversion_clear HH as [H_ic2_in_ H_le_ic_ic2].

  exists (IV_Rec_Closure f x e ic2).
  split.
  exists ic2; auto.
  rewrite H_iv.
  tac_le_itval; auto.


  Focus 1.
  (* case Apply *)
  rename H0 into H_atu, H into H_atu2.
  inversion H_ctval_of as [ | | | | | |
                            | ctc0 e0 e3 td1 td2 td d1 d2 d ivs1 ivs2 ctv0 imv
                                   H_ctval_of_e1 H_ctval_of_e2 H_imv H_spec_td H_spec_d H_ctv
                            | | | | | | | | | | | | ].
  clear dependent ctc0.
  clear dependent ctv0.
  clear dependent e0.
  clear dependent e3.

  (** specialize the induction hypothesis *)
  specialize (IHH_atval_of1 _ _ H_ctc_atc H_ctval_of_e1).
  specialize (IHH_atval_of2 _ _ H_ctc_atc H_ctval_of_e2).


  (** split the goal *)
  rewrite H_ctv, H_atu.
  apply Le_ctval.

  (*** inclusion of the collecting td in the abstract td *)
  intros l H_l.
  apply H_spec_td in H_l.
  inversion_clear H_l as [td' HH].
  inversion_clear HH as [H_l_in_td' H_td'_in_imv].
  inversion_clear H_td'_in_imv as [itu HH].
  destruct itu as [itd iu].
  destruct iu as [id iv].
  inversion_clear HH as [H_td'_itd H_itu_in_imv].
  rewrite H_imv in H_itu_in_imv.
  inversion_clear H_itu_in_imv.
  (**** itu comes from the application of a non-recursive closure *)
  inversion_clear H as [x' HH].
  inversion_clear HH as [e' HHH].
  inversion_clear HHH as [ic1 HH].
  inversion_clear HH as [iv2 HHH].
  inversion_clear HHH as [itd0 HH].
  inversion_clear HH as [id0 HHH].
  inversion_clear HHH as [iv0 HH].
  inversion_clear HH as [H_in_ivs1 HHH].
  inversion_clear HHH as [H_iv2_in_ivs2 HH].
  inversion_clear HH as [H_ival_of_e' H_itu].
  inversion H_itu.

  inversion IHH_atval_of1.
  rewrite H_atu2 in IHH_atval_of2.
  destruct au2 as [ad2 av2].
  inversion IHH_atval_of2.

  revert l H_l_in_td'.
  rewrite H_td'_itd, H0.
  repeat apply conc_itdeps_included; auto.

  clear dependent itd1.
  clear dependent id1.
  clear dependent ivs0.
  clear dependent itd2.
  clear dependent id2.
  clear dependent itd3.
  clear dependent id3.
  clear dependent ivs4.
  clear dependent itd4.
  clear dependent id4.

  (***** x' = x /\ e' = e *)
  assert(HH : x' = x /\ e' = e).
  specialize(H10 (IV_Closure x' e' ic1) H_in_ivs1).
  inversion_clear H10 as [iv1_2 HH].
  inversion_clear HH as [H_iv1_2_in H_iv1_iv1_2].
  inversion_clear H_iv1_2_in as [ic1_2 HH].
  inversion_clear HH as [H_iv1_2 H_ic1_2_in].
  rewrite H_iv1_2 in H_iv1_iv1_2.
  inversion_clear H_iv1_iv1_2.
  auto.
  inversion_clear HH as [H_x' H_e'].
  rewrite H_x' in *; clear dependent x'.
  rewrite H_e' in *; clear dependent e'.

  (***** evaluates e in a well-suited ctenv *)
  destruct(ctval_of_total e (atenv_to_ctenv (ATEnv_cons x atu2 (aenv_to_atenv ac1)))) as [ctv_e H_ctval_of_e].

  (***** the abstraction of this ctenv corresponds to the abstract evaluation of e *)
  assert(H_ctenv_to_atenv:=atenv_to_ctenv_to_atenv (ATEnv_cons x atu2 (aenv_to_atenv ac1))).

  (***** specialize the induction hypothesis *)
  specialize (IHH_atval_of3 _ _ H_ctenv_to_atenv H_ctval_of_e).
  
  destruct ctv_e as [ctd_e cd_e ivs_e].
  inversion_clear IHH_atval_of3.

  (***** evaluates e in a well-suited imenv *)
  remember(atenv_to_ctenv (ATEnv_cons x atu2 (aenv_to_atenv ac1))) as ctc_e eqn:H_ctc_e.
  remember (ctenv_to_imenv ctc_e) as imc_e eqn:H_imc_e.
  remember((fun itu => exists (itc:itenv), In _ imc_e itc
                                           /\ ival_of itc e itu) : imval) as imv_e eqn:H_imv_e.
  assert(H_imval_of_e:=IMVal_of imc_e e imv_e H_imv_e).
  
  (***** the itenv is in the imenv *)
  assert(le_imenv (Singleton _ (ITEnv_cons x (IV td2 (IV_ d2 iv2)) (ienv_to_itenv ic1))) imc_e).
  rewrite H_imc_e, H_ctc_e.
  simpl.
  unfold ctenv_to_imenv.
  rewrite H_atu2.
  simpl.
  unfold In, SetMap2.
  intros itc H_itc_in_imc_e.
  inversion H_itc_in_imc_e.
  (****** find an abstraction of iv2 in the concretization of av2 *)
  assert(HH:=H19 iv2 H_iv2_in_ivs2).
  inversion_clear HH as [iv2_2 HHH].
  inversion_clear HHH as [H_iv2_2_in H_le_iv2_iv2_2].
  (****** find an abstraction of ic1 in the concretization of ac1 *)
  assert(HH:=H10 (IV_Closure x e ic1) H_in_ivs1).
  inversion_clear HH as [iv1_2 HHH].
  inversion_clear HHH as [H_iv1_2_in H_le_iv1_iv1_2].
  destruct iv1_2 as [ | | | | x1_2 e1_2 ic1_2 | | ]; inversion H_le_iv1_iv1_2.
  rewrite <-H14, <-H16 in *.
  clear dependent x0.
  clear dependent e0.
  clear dependent ic.
  clear dependent ic'.
  clear dependent x1_2.
  clear dependent e1_2.
  inversion_clear H_iv1_2_in as [ic1_2' HH].
  inversion_clear HH as [HHH H_ic1_2'_in_ac1].
  inversion HHH as [H_ic1_2_ic1_2']; clear HHH.
  rewrite <-H_ic1_2_ic1_2' in *; clear dependent ic1_2'.
  (****** propose a well-suited itenv *)
  exists (ITEnv_cons x (IV atd2 (IV_ ad2 iv2_2)) (ienv_to_itenv ic1_2)).
  split.
  unfold In.
  exists iv2_2, (ienv_to_itenv ic1_2).
  repeat split; auto.
  apply ienv_to_itenv_in_aenv_to_to_imenv; auto.
  tac_le_itval; auto.
  apply le_ienv_to_itenv; auto.

  (***** apply correctness of ctval_of *)
  Check (ctval_of_correctness imc_e e imv_e (CTVal ctd_e cd_e ivs_e) ctc_e
                              H_imval_of_e (ctenv_to_imenv_to_ctenv ctc_e)).


  (**** itu comes from the application of a recursive closure *)

  (*** inclusion of the collecting d in the abstract d *)
  (*** inclusion of the td *)







  Focus 12.
  (* case Constr1 *)
  inversion H_ctval_of as [ | | ctc0 n0 e0 td d ivs ivs' H_ctval_of_e H_ivs' Hu1 Hu2 H_ctv | | | | | | | | | | | | | | | | | ].
  clear dependent ctc0.
  clear dependent n0.
  clear dependent e0.
  
  (** specialize the induction hypothesis *)
  specialize (IHH_atval_of _ _ H_ctc_atc H_ctval_of_e).
  destruct au as [ad av].
  inversion_clear IHH_atval_of as [uH1 uH2 uH3 uH4 IH IIH H_td_atd H_d_ad H_ivs_av].

  apply Le_ctval; auto.

  intro l; auto.

  rewrite H_ivs'.
  intros iv H_iv_in.
  inversion_clear H_iv_in as [iv' HH].
  inversion_clear HH as [H_iv H_iv'_in_ivs].
  specialize (H_ivs_av iv' H_iv'_in_ivs).
  inversion_clear H_ivs_av as [iv'_2 HH].
  inversion_clear HH as [H_iv'_2_in_av H_le_iv'_iv'_2].
  exists (IV_Constr1 n (IV_ ad iv'_2)).
  split.
  exists iv'_2; auto.
  rewrite H_iv.
  tac_le2_ival; auto.



Admitted.
