Add Rec LoadPath "." as DEP_AI.

Require utils.
Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import over_instrumented_values.
Require Import oitval_instantiation.
Require Import oitval_val_conversion.
Require Import oitval_val_conversion_facts.
Require Import is_instantiable_oitval.

Require Import injection_operational_semantics.

Require Import over_instrumented_semantics.

Ltac ind_inst_oienv l vl c H :=
  assert(H_SUM : {instantiate_oienv l vl c = None} + {exists x, instantiate_oienv l vl c = Some x});
    [induction (instantiate_oienv l vl c) as [cc|cc]; [right; exists cc; reflexivity| left; reflexivity]
      | inversion H_SUM as [H_SUM1|H_SUM2]; [rewrite H_SUM1 in H; inversion H|inversion H_SUM2 as [c_inst H_SUM3_oienv]; rewrite H_SUM3_oienv in H; inversion H as [HHHH]]];
    clear H_SUM.

Lemma option_dec :
  forall (A:Type) (o:option A),
    {o = None} + {exists (x:A), o = Some x}.
Proof.
  intros A o.
  induction o.
  right; exists a; reflexivity.
  left; reflexivity.
Qed.

Definition is_instantiable_oitenv (l:label) (vl:val) (c:oitenv) :=
  exists (c':env), Some c' = instantiate_oitenv l vl c.

Lemma is_instantiable_oitenv_cons :
  forall (l:label) (vl v:val) (c:oitenv) (x:identifier) (uu:oitval),
    is_instantiable_oitenv l vl c
    -> instantiate_oitval l vl uu = Some v
    -> is_instantiable_oitenv l vl (OITEnv_cons x uu c).
Proof.
  intros l vl v c x uu H H0.
  inversion_clear H as [c'].
  exists (Env_cons x v c').
  simpl.
  unfold option_map2.
  rewrite H0.
  rewrite <- H1.
  reflexivity.
Qed.

Lemma is_instantiable_oitenv_conc :
  forall (l:label) (vl:val) (c1 c2:oitenv),
    is_instantiable_oitenv l vl c1
    -> is_instantiable_oitenv l vl c2
    -> is_instantiable_oitenv l vl (conc_oitenv c1 c2).
Proof.
  intros l vl c1 c2 HH_inst_c1 HH_inst_c2.
  induction c1.
  auto.

  simpl.
  inversion HH_inst_c1 as [c' H_inst_c].
  simpl in H_inst_c.
  induction (instantiate_oitval l vl uu) as [v|] eqn:H_inst_uu;
    induction (instantiate_oitenv l vl c1) as [c1'|] eqn:H_inst_c1; simpl in H_inst_c; try solve [inversion H_inst_c].
  apply is_instantiable_oitenv_cons with (v:=v);auto.
  apply IHc1.
  exists c1'.
  auto.
Qed.

Axiom excluded_middle : forall A:Prop, A \/ ~A.

Lemma not_loop_in_conc_oitdeps1 :
  forall (l:label) (vl:val) (td td':oitdeps),
    apply_timpact_fun l vl (conc_oitdeps td td') <> Some true
    -> apply_timpact_fun l vl td <> Some true.
Proof.
  intros l vl td td' H.
  induction td.
  inversion 1.
  simpl.
  induction a as [l' f].
  simpl in H.
  induction (eq_label_dec l l').
  induction (apply_timpact_fun l vl (conc_oitdeps td td')).
  induction a0.
  contradiction H.
  f_equal.
  induction (f vl); auto.
  induction (f vl).
  contradiction H; auto.
  induction (apply_timpact_fun l vl td); auto.
  induction (f vl).
  contradiction H; auto.
  induction (apply_timpact_fun l vl td); auto.
  simpl.
  apply IHtd.
  inversion 1.
  apply (IHtd H).
Qed.

Lemma not_loop_in_conc_oitdeps2 :
  forall (l:label) (vl:val) (td td':oitdeps),
    apply_timpact_fun l vl (conc_oitdeps td td') <> Some true
    -> apply_timpact_fun l vl td' <> Some true.
Proof.
  intros l vl td td' H.
  induction td.
  simpl in H.
  assumption.
  induction a as [l' f].
  simpl in H.
  induction (eq_label_dec l l').
  induction (apply_timpact_fun l vl (conc_oitdeps td td')).
  induction a0.
  contradiction H.
  f_equal.
  induction (f vl); auto.
  induction (f vl).
  contradiction H; auto.
  induction (apply_timpact_fun l vl td); auto.
  induction (f vl).
  contradiction H; auto.
  induction (apply_timpact_fun l vl td); auto.
  simpl.
  apply IHtd.
  inversion 1.
  apply IHtd; inversion 1.
  apply IHtd; assumption.
Qed.

Lemma not_loop_in_conc_oitdeps :
  forall (l:label) (vl:val) (td td':oitdeps),
    apply_timpact_fun l vl td <> Some true
    -> apply_timpact_fun l vl td' <> Some true
    -> apply_timpact_fun l vl (conc_oitdeps td td') <> Some true.
Proof.
  intros l vl td td' H_td H_td'.
  
  induction td as [|l'_tf]; auto.

  simpl; simpl in H_td.
  destruct l'_tf as [l' tf].
  destruct (eq_label_dec l l') as [H_l_l'|H_l_l'].
  destruct (tf vl).
  destruct (apply_timpact_fun l vl td); elim (H_td eq_refl).
  destruct (apply_timpact_fun l vl td).
  destruct b.
  elim (H_td eq_refl).
  apply IHtd in H_td.
  destruct (apply_timpact_fun l vl (conc_oitdeps td td')); auto.
  inversion 1.
  destruct (apply_timpact_fun l vl (conc_oitdeps td td')); auto.
  rewrite Bool.orb_false_l.
  apply IHtd.
  inversion 1.
  auto.
Qed.

Lemma not_loop_in_cons_oitdeps2 :
  forall (l:label) (vl:val) (lf:label*(val->bool)) (td:oitdeps),
    apply_timpact_fun l vl (cons lf td) <> Some true
    -> apply_timpact_fun l vl td <> Some true.
Proof.
  intros l vl lf td H.

  simpl in H.
  destruct lf as [l' f].
  destruct (eq_label_dec l l') as [H_l_l'|H_l_l']; auto.
  destruct (apply_timpact_fun l vl td).
  destruct (f vl); auto.
  inversion 1.
Qed.
  

  

Lemma instantiate_oitval_to_oival :
  forall (l:label) (vl:val) (uu:oitval) (v:val),
  instantiate_oitval l vl uu = Some v
  -> instantiate_oival l vl (oitval_to_oival uu) = Some v.
Proof.
  induction uu.
  simpl.
  intros v H.
  induction (apply_timpact_fun l vl td); try assumption.
  induction a; try assumption.
  inversion H.
Qed.

Lemma instantiate_oitenv_to_oienv :
  forall (l:label) (vl:val) (c:oitenv) (c_inst:env),
  instantiate_oitenv l vl c = Some c_inst
  -> instantiate_oienv l vl (oitenv_to_oienv c) = Some c_inst.
Proof.
  induction c; intros.
  inversion H.
  auto.

  simpl in H. unfold option_map2 in H.
  induction (instantiate_oitval l vl uu) as [v|] eqn:HHH; try solve [inversion H].
  induction (instantiate_oitenv l vl c) as [c'|]; try solve [inversion H].
  specialize (IHc c' eq_refl).
  inversion H.
  simpl.
  rewrite IHc.
  unfold option_map2.
  rewrite instantiate_oitval_to_oival with (v:=v).
  reflexivity.
  assumption.
Qed.


Lemma is_filtered_oitval_is_filtered :
  forall (l:label) (vl:val) (uu:oitval) (td:oitdeps) (u:oival) (d:oideps) (v0:oival0) (p:pattern) (c_p:oitenv),
  is_filtered_oitval uu p = Filtered_oitval_result_Match c_p
  -> uu = (OIV td u)
  -> u = OIV_ d v0
  -> apply_impact_fun l vl d = None
  -> (exists (v':val) (c_p':env),
        instantiate_oival l vl u = Some v'
        /\ instantiate_oitenv l vl c_p = Some c_p'
        /\ is_filtered v' p = Filtered_result_Match c_p').
Proof.
  intros l vl uu td u d v0 p c_p H H_uu H_u H_d.
  rewrite H_u in H_uu; rewrite H_uu in H.
  rewrite H_u.
  induction v0; induction p; inversion H.

  exists (V_Constr0 n), (Env_empty).
  simpl; rewrite H_d.
  induction (eq_nat_dec n c); inversion H1.
  auto.

  assert(HH_inst_u0 := is_instantiable_oival u0 l vl).
  inversion_clear HH_inst_u0 as [v0' H_inst_u0].
  exists (V_Constr1 n v0'), (Env_cons i v0' Env_empty).
  simpl; rewrite H_d.
  induction (eq_nat_dec n c); inversion H1.
  simpl.
  rewrite H_inst_u0; simpl.
  auto.
  
  assert(HH_inst_u1 := is_instantiable_oival u1 l vl).
  inversion_clear HH_inst_u1 as [v1' H_inst_u1].
  assert(HH_inst_u2 := is_instantiable_oival u2 l vl).
  inversion_clear HH_inst_u2 as [v2' H_inst_u2].
  exists (V_Couple v1' v2'), (Env_cons i v1' (Env_cons i0 v2' Env_empty)).
  simpl; rewrite H_d.
  rewrite H_inst_u2; rewrite H_inst_u1; simpl.
  auto.
Qed.
  
Ltac aux_rewrite_is_instantiable_oival l vl u0 :=
  let v := fresh "v_" u0 in
  let H_inst := fresh "H_inst_" u0 in
  let HH_inst := fresh "HH_inst_" u0 in
  assert(HH_inst := is_instantiable_oival u0 l vl);
    inversion_clear HH_inst as [v H_inst];
    rewrite H_inst.

Ltac rewrite_is_instantiable_oival :=
  let rec search_u e :=
      match e with
        | instantiate_oival ?l ?vl ?u0 => aux_rewrite_is_instantiable_oival l vl u0
        | ?f ?x => search_u f; search_u x
        | ?x => idtac
      end
  in
  let e := match goal with |- ?x => x end in
  search_u e.

Ltac aux_rewrite_is_instantiable_oienv l vl c :=
  let c' := fresh "c'_" c in
  let H_inst := fresh "H_inst_" c in
  let HH_inst := fresh "HH_inst_" c in
  assert(HH_inst := is_instantiable_oienv c l vl);
    inversion_clear HH_inst as [v H_inst];
    rewrite H_inst.



Lemma is_filtered_oitval_is_filtered_not :
  forall (l:label) (vl:val) (uu:oitval) (td:oitdeps) (u:oival) (d:oideps) (v0:oival0) (p:pattern),
  is_filtered_oitval uu p = Filtered_oitval_result_Match_var
  -> uu = (OIV td u)
  -> u = OIV_ d v0
  -> apply_impact_fun l vl d = None
  -> (exists (v':val),
        instantiate_oival l vl u = Some v'
        /\ is_filtered v' p = Filtered_result_Match_var).
Proof.
  intros l vl uu td u d v0 p H H_uu H_u H_d.
  rewrite H_u in H_uu; rewrite H_uu in H.
  rewrite H_u.
  induction v0; induction p;
  try solve [simpl; rewrite H_d; eexists; auto];
  try solve [inversion H].

  simpl; rewrite H_d; eexists; auto;
  split; auto;
  simpl in H; simpl;
  induction (eq_nat_dec n c); try solve [inversion H]; auto.

  simpl; rewrite H_d; aux_rewrite_is_instantiable_oival l vl u0;
  eexists; simpl; auto.

  simpl; rewrite H_d; aux_rewrite_is_instantiable_oival l vl u0.
  eexists; simpl; auto.
  split; auto;
  simpl in H; simpl;
  induction (eq_nat_dec n c); try solve [inversion H]; auto.

  simpl; rewrite H_d; aux_rewrite_is_instantiable_oival l vl u0.
  eexists; simpl; auto.

  simpl; rewrite H_d; aux_rewrite_is_instantiable_oival l vl u1; aux_rewrite_is_instantiable_oival l vl u2;
  eexists; simpl; auto.

  simpl; rewrite H_d; aux_rewrite_is_instantiable_oival l vl u1; aux_rewrite_is_instantiable_oival l vl u2;
  eexists; simpl; auto.
Qed.

  
(*************** PROOF OF CORRECTNESS ****************)

(*
Lemma apply_timpact_fun_on_instantiable1 :
  forall (l:label) (vl v_inst:val) (uu:oitval) (td td' td1 td2:oitdeps) (d d':oideps) (v:oival0),
    Some v_inst = instantiate_oitval l vl uu
    -> uu =
       OIV (conc_oitdeps td1 (conc_oitdeps td2 (conc_oitdeps td td')))
         (OIV_ (conc_oideps d' d) v)
    -> apply_timpact_fun l vl td1 <> Some true.
Proof.
  intros l vl v_inst uu td td' td1 td2 d d' v H_inst H_uu.
  rewrite H_uu in H_inst.
  assert(H_tmp : apply_timpact_fun l vl td1 = Some true 
    -> apply_timpact_fun l vl (conc_oitdeps td1 (conc_oitdeps td2 (conc_oitdeps td td'))) = Some true).
  intro HH; apply apply_timpact_fun_in_conc_oitdeps_1; assumption.
  induction (apply_timpact_fun l vl td1).
  simpl in H_inst.
  induction a.
  rewrite (H_tmp eq_refl) in H_inst.
  inversion H_inst.
  intro HHH; inversion HHH.
  intro HHH; inversion HHH.
Qed.
*)



Lemma apply_timpact_fun_on_instantiable :
  forall (l:label) (vl v_inst:val) (uu:oitval) (td:oitdeps) (u:oival),
    Some v_inst = instantiate_oitval l vl uu
    -> uu = OIV td u
    -> apply_timpact_fun l vl td <> Some true.
Proof.
  intros l vl v_inst uu td u H_inst H_uu.
  rewrite H_uu in H_inst.
  simpl in H_inst.
  induction (apply_timpact_fun l vl td).
  induction a.
  inversion H_inst.
  inversion 1.
  inversion 1.
Qed.


Lemma deps_spec_Apply_l_not_in_d1 :
  forall (l:label) (vl:val) (td':oitdeps) (d1 d':oideps) (uu2:oitval),
  deps_spec_Apply uu2 d1 td' d'
  -> apply_impact_fun l vl d1 = None
  -> (apply_timpact_fun l vl td' = None
      /\ apply_impact_fun l vl d' = None).
Proof.
  intros l vl td' d1 d' uu2 H H0.
  induction H.
  auto.
  simpl; simpl in H0.
  destruct (eq_label_dec l l0).
  inversion H0.
  auto.
Qed.


Lemma oival_Apply_correctness :
  forall (l:label) (vl v_inst v1:val) (c:oitenv) (e1 e2:expr) (td td' td1 td2:oitdeps) (d d' d1:oideps) (uu uu2:oitval) (v v1':oival0),
    deps_spec_Apply uu2 d1 td' d'
    -> apply_impact_fun l vl d1 = Some v1
    -> Some v_inst = instantiate_oitval l vl uu
    -> uu =
         OIV (conc_oitdeps td1 (conc_oitdeps td2 (conc_oitdeps td td')))
         (OIV_ (conc_oideps d' d) v)
    -> (forall v : val,
      Some v =
      instantiate_oitval l vl
      (OIV td1 (OIV_ d1 v1')) ->
      val_of_with_injection l vl c e1 v)
    -> (forall v : val,
                Some v = instantiate_oitval l vl uu2 ->
                val_of_with_injection l vl c e2 v)
    -> val_of_with_injection l vl c (Apply e1 e2) v_inst.
Proof.  (* induction on d1 *)
  intros l vl v_inst v1 c e1 e2 td td' td1 td2 d d' d1 uu uu2 v v1' H_deps_spec.
  revert vl uu.
  induction H_deps_spec.
  inversion 1.
  intros vl uu H_aif_d1 H_inst_uu H_uu H_val_of_inj_e1 H_val_of_inj_e2.
  rename l0 into l'.


  assert(H_l_vl_not_loop_in_uu := apply_timpact_fun_on_instantiable _ _ _ _ _ _ H_inst_uu H_uu).
  (** d1 is now ((l', f_) :: d1) *)
  (** either l = l' or l <> l' *)

  induction (eq_label_decide l l') as [H_eq_l_l'|H_neq_l_l'].
  (*** case l = l' *)
  clear IHH_deps_spec.
  apply eq_label_eq in H_eq_l_l'.
  rewrite <- H_eq_l_l' in *; clear H_eq_l_l'.
  unfold deps_spec_Apply_funs in H.
  specialize (H vl).

  (*** tf' vl = true is absurd *)
  assert(H_tf'_absurd : tf' vl = true -> False).
  clear H_deps_spec H_val_of_inj_e1 H_val_of_inj_e2.
  intro H_tf'.
  rewrite H_uu in H_inst_uu.
  simpl in H_inst_uu.
  rewrite apply_timpact_fun_in_conc_oitdeps_2 in H_inst_uu.
  inversion H_inst_uu.
  repeat rewrite apply_timpact_fun_in_conc_oitdeps_2; try reflexivity.
  simpl.
  destruct (eq_label_dec l l) as [H_l|H_l]; try elim (H_l eq_refl).
  rewrite H_tf'.
  destruct (apply_timpact_fun l vl oitd'); auto.

  (*** all possible values for f vl *)
  destruct (f vl) eqn:H_f_vl;
    try solve [inversion H as [H_tf' H_f']; elim (H_tf'_absurd H_tf')].
  (***- remains only case Closure and Rec_Closure *)

  (**** case Closure *)
  inversion_clear H as [H_exists H_not_exists].
  induction (excluded_middle (exists v2 v' : val,
    instantiate_oitval l vl oitu2 = Some v2 /\
    val_of_with_injection l vl
    (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c0)) e v')) as [H_ex|H_nex].
  (***** there is a value v' for the application *)
  clear H_not_exists.
  inversion_clear H_ex as [v2 HHH];
    inversion_clear HHH as [v' HH];
    inversion_clear HH as [H_inst_uu2 H_val_of_inj_e].

  (***** v' equals v_inst (the instantiation of uu) *)
  assert(H_v' : v' = v_inst).
  specialize(H_exists v2 v' H_inst_uu2 H_val_of_inj_e).
  inversion_clear H_exists as [H_tf' H_f'].
  rewrite H_uu in H_inst_uu.
  simpl in H_inst_uu.
  destruct (apply_timpact_fun l vl
                              (conc_oitdeps td1
                                            (conc_oitdeps td2
                                                          (conc_oitdeps td ((l, tf') :: oitd')%list)))) as [b|].
  destruct b.
  inversion H_inst_uu.
  destruct (eq_label_dec l l) as [H_l|H_l]; try elim (H_l eq_refl).
  rewrite H_f' in H_inst_uu.
  inversion H_inst_uu; reflexivity.
  destruct (eq_label_dec l l) as [H_l|H_l]; try elim (H_l eq_refl).
  rewrite H_f' in H_inst_uu.
  inversion H_inst_uu; reflexivity.

  rewrite <-H_v'; clear H_v'.

  (**** value of the e1 *)
  simpl in H_val_of_inj_e1.
  simpl in H_aif_d1.
  destruct (eq_label_dec l l) as [H_l|H_l]; try elim (H_l eq_refl).
  inversion H_aif_d1.
  rewrite H_aif_d1 in H_val_of_inj_e1.
  specialize (H_val_of_inj_e1 v1).
  assert(H_l_vl_not_loop_in_td1 := not_loop_in_conc_oitdeps1 _ _ _ _ H_l_vl_not_loop_in_uu).
  rewrite utils.match_option_bool_not_true in H_val_of_inj_e1; auto.
  specialize (H_val_of_inj_e1 eq_refl).
  rewrite H_f_vl in H0; rewrite <-H0 in H_val_of_inj_e1.
  clear H0.
  (**** value of e2 *)
  specialize (H_val_of_inj_e2 _ (eq_sym H_inst_uu2)).

  apply Val_of_with_injection_Apply with (c1:=c0) (e:=e) (x:=x) (v2:=v2); auto.

  (***** there is no value for the application *)
  
  apply H_not_exists in H_nex.
  inversion H_nex as [H_tf' H_f'].
  elim (H_tf'_absurd H_tf').

  (**** case Rec_Closure *)
  inversion_clear H as [H_exists H_not_exists].
  induction (excluded_middle (exists v2 v' : val,
                                instantiate_oitval l vl oitu2 = Some v2 /\
                                val_of_with_injection l vl
                                                      (env_to_oitenv
                                                         (add_env f0 (V_Rec_Closure f0 x e c0) (add_env x v2 c0))) e v')) as [H_ex|H_nex].
  (***** there is a value v' for the application *)
  clear H_not_exists.
  inversion_clear H_ex as [v2 HHH];
    inversion_clear HHH as [v' HH];
    inversion_clear HH as [H_inst_uu2 H_val_of_inj_e].

  (***** v' equals v_inst (the instantiation of uu) *)
  assert(H_v' : v' = v_inst).
  specialize(H_exists v2 v' H_inst_uu2 H_val_of_inj_e).
  inversion_clear H_exists as [H_tf' H_f'].
  rewrite H_uu in H_inst_uu.
  simpl in H_inst_uu.
  destruct (apply_timpact_fun l vl
                              (conc_oitdeps td1
                                            (conc_oitdeps td2
                                                          (conc_oitdeps td ((l, tf') :: oitd')%list)))) as [b|].
  destruct b.
  inversion H_inst_uu.
  destruct (eq_label_dec l l) as [H_l|H_l]; try elim (H_l eq_refl).
  rewrite H_f' in H_inst_uu.
  inversion H_inst_uu; reflexivity.
  destruct (eq_label_dec l l) as [H_l|H_l]; try elim (H_l eq_refl).
  rewrite H_f' in H_inst_uu.
  inversion H_inst_uu; reflexivity.

  rewrite <-H_v'; clear H_v'.

  (**** value of the e1 *)
  simpl in H_val_of_inj_e1.
  simpl in H_aif_d1.
  destruct (eq_label_dec l l) as [H_l|H_l]; try elim (H_l eq_refl).
  inversion H_aif_d1.
  rewrite H_aif_d1 in H_val_of_inj_e1.
  specialize (H_val_of_inj_e1 v1).
  assert(H_l_vl_not_loop_in_td1 := not_loop_in_conc_oitdeps1 _ _ _ _ H_l_vl_not_loop_in_uu).
  rewrite utils.match_option_bool_not_true in H_val_of_inj_e1; auto.
  specialize (H_val_of_inj_e1 eq_refl).
  rewrite H_f_vl in H0; rewrite <-H0 in H_val_of_inj_e1.
  clear H0.
  (**** value of e2 *)
  specialize (H_val_of_inj_e2 _ (eq_sym H_inst_uu2)).

  apply Val_of_with_injection_Apply_rec with (c1:=c0) (e:=e) (f:=f0) (x:=x) (v2:=v2); auto.

  (***** there is no value for the application *)
  
  apply H_not_exists in H_nex.
  inversion H_nex as [H_tf' H_f'].
  elim (H_tf'_absurd H_tf').

  (*** case l <> l' *)

  assert (H1 := not_loop_in_conc_oitdeps1 _ _ _ _ H_l_vl_not_loop_in_uu).
  apply not_loop_in_conc_oitdeps2 in H_l_vl_not_loop_in_uu.
  assert (H2 := not_loop_in_conc_oitdeps1 _ _ _ _ H_l_vl_not_loop_in_uu).
  apply not_loop_in_conc_oitdeps2 in H_l_vl_not_loop_in_uu.
  assert (H3 := not_loop_in_conc_oitdeps1 _ _ _ _ H_l_vl_not_loop_in_uu).
  assert (H4 := not_loop_in_conc_oitdeps2 _ _ _ _ H_l_vl_not_loop_in_uu).
  clear H_l_vl_not_loop_in_uu.

  simpl in H_aif_d1.
  destruct (eq_label_dec l l') as [H_l|H_l].
  rewrite H_l in H_neq_l_l'; elim (H_neq_l_l' (eq_eq_label _ _ eq_refl)).
  apply IHH_deps_spec with (uu:= OIV
                                   (conc_oitdeps td1
                                                 (conc_oitdeps td2 (conc_oitdeps td oitd')))
                                   (OIV_ (conc_oideps oid' d) v)); try assumption.
  simpl.
  rewrite utils.match_option_bool_not_true.
  rewrite H_uu in H_inst_uu.
  simpl in H_inst_uu.
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  destruct (eq_label_dec l l') as [H_l_|_].
  rewrite H_l_ in H_neq_l_l'; elim (H_neq_l_l' (eq_eq_label _ _ eq_refl)).
  assumption.

  repeat apply not_loop_in_conc_oitdeps; auto.
  repeat apply not_loop_in_conc_oitdeps; auto.
  apply (not_loop_in_cons_oitdeps2 _ _ _ _ H4).
  reflexivity.

  intros v0 H0.
  apply H_val_of_inj_e1.
  simpl; simpl in H0.
  rewrite utils.match_option_bool_not_true.
  rewrite utils.match_option_bool_not_true in H0.
  destruct (eq_label_dec l l').
  elim (H_l e).
  assumption.
  intro HH.
  rewrite HH in H0.
  inversion H0.
  intro HH.
  rewrite HH in H0.
  inversion H0.
Qed.


Lemma is_instantiable_oitenv_of_is_filtered :
  forall (uu:oitval) (p:pattern) (c_p:oitenv) (l:label) (vl:val),
    is_filtered_oitval uu p = Filtered_oitval_result_Match c_p
    -> is_instantiable_oitenv l vl c_p.
Proof.
  intros uu p c_p l vl H.
  destruct uu.
  destruct u.
  destruct v; destruct p; try solve [inversion H]; simpl in H.
  
  (* case Constr0 *)
  destruct (eq_nat_dec n c); inversion H.
  exists Env_empty.
  auto.

  (* case Constr1 *)
  destruct (eq_nat_dec n c); inversion H.
  assert(HH:= is_instantiable_oival u l vl).
  inversion HH as [v HHH].
  exists (Env_cons i v Env_empty).
  simpl.
  unfold option_map2.
  rewrite HHH.
  auto.

  (* case Couple *)
  inversion H.
  assert(HH1:= is_instantiable_oival u1 l vl); inversion_clear HH1 as [v1 HHH1].
  assert(HH2:= is_instantiable_oival u2 l vl); inversion_clear HH2 as [v2 HHH2].
  exists (Env_cons i v1 (Env_cons i0 v2 Env_empty)).
  simpl.
  unfold option_map2.
  rewrite HHH1, HHH2.
  reflexivity.
Qed.  


Lemma is_not_filtered_instantiate_oitval :
  forall (l:label) (vl:val) (td:oitdeps) (d:oideps) (v:oival0) (v':val) (p:pattern),
  is_filtered_oitval (OIV td (OIV_ d v)) p = Filtered_oitval_result_Match_var
  -> apply_timpact_fun l vl td <> Some true
  -> apply_impact_fun l vl d = None
  -> instantiate_oitval l vl (OIV td (OIV_ d v)) = Some v'
  -> is_filtered v' p = Filtered_result_Match_var.
Proof.
  intros l vl td d v v' p H_is_filtered_oitval H_atif_td H_aif_d H_inst_uu.
  destruct v; destruct p;
  simpl in H_inst_uu;
  rewrite utils.match_option_bool_not_true in H_inst_uu; auto;
  rewrite H_aif_d in H_inst_uu;
  try solve [inversion H_inst_uu; auto];
  try solve [inversion H_is_filtered_oitval].

  inversion H_inst_uu;
  simpl in H_is_filtered_oitval; simpl;
  destruct (eq_nat_dec n c) as [H_eq_n_c|H_neq_n_c]; [inversion H_is_filtered_oitval|auto].

  inversion H_inst_uu;
  unfold option_map in H0;
    destruct (instantiate_oival l vl u); inversion H0; auto.

  simpl in H_is_filtered_oitval; simpl.
  destruct (is_instantiable_oival u l vl) as [v H].
  rewrite H in H_inst_uu; inversion_clear H_inst_uu; simpl.
  destruct (eq_nat_dec n c) as [H_eq_n_c|H_neq_n_c]; [inversion H_is_filtered_oitval|auto].
  
  destruct (is_instantiable_oival u l vl) as [v H];
  rewrite H in H_inst_uu; inversion_clear H_inst_uu; simpl; auto.

  destruct (is_instantiable_oival u1 l vl) as [v1 H1];
  destruct (is_instantiable_oival u2 l vl) as [v2 H2];
  rewrite H1, H2 in H_inst_uu; inversion_clear H_inst_uu; simpl; auto.

  destruct (is_instantiable_oival u1 l vl) as [v1 H1];
  destruct (is_instantiable_oival u2 l vl) as [v2 H2];
  rewrite H1, H2 in H_inst_uu; inversion_clear H_inst_uu; simpl; auto.
Qed.


Ltac replaceH H H' :=
  let HH := fresh "HH" in
  assert(HH:=H'); clear H; rename HH into H.


(*
   A propos de l'hypothèse (is_instantiable_oitenv l vl c) dans le théorème de correction :
   --------------------------------------------------------------------------------------
   il n'y a aucun intérêt à considérer les jugements pour lesquels l'environnement n'est pas instantiable
   car cela signifie que cet environnement n'aurait pas pu être construit à partir d'un programme,
   le programme aurait bouclé ou aurait produit une erreur
   et on ne serait jamais arrivé à l'évaluation de l'expression du jugement considéré
   *)

Theorem oival_of_correctness :
  forall (c:oitenv) (e:expr) (uu:oitval),
    oival_of c e uu
    -> forall (l:label) (vl:val),
      is_instantiable_oitenv l vl c
      -> forall (v:val),
        Some v = instantiate_oitval l vl uu
        -> val_of_with_injection l vl c e v.
Proof.
  intros c e u H l vl.
  induction H; intros H_inst_c v_inst H_inst_uu.

  (* case Num *)
  inversion H_inst_uu.
  auto with val_of_with_injection.

  (* case Ident *)
  apply Val_of_with_injection_Ident with (uu:=uu);
    assumption.

  (* case Lambda *)
  rewrite H in H_inst_uu.
  simpl in H_inst_uu.
  unfold option_map in H_inst_uu.
  induction (instantiate_oienv l vl (oitenv_to_oienv c)) as [c_inst|] eqn:HH; try solve [inversion H_inst_uu].
  apply Val_of_with_injection_Lambda with (c':=c_inst).
  inversion H_inst_c as [c_inst'].
  rewrite instantiate_oitenv_to_oienv with (c_inst:=c_inst') in HH.
  rewrite <- HH; assumption.
  rewrite H0; reflexivity.
  inversion H_inst_uu; reflexivity.

  (* case Rec *)
  rewrite H in H_inst_uu.
  simpl in H_inst_uu.
  unfold option_map in H_inst_uu.
  induction (instantiate_oienv l vl (oitenv_to_oienv c)) as [c_inst|] eqn:HH; try solve [inversion H_inst_uu].
  apply Val_of_with_injection_Rec with (c':=c_inst).
  inversion H_inst_c as [c_inst'].
  rewrite instantiate_oitenv_to_oienv with (c_inst:=c_inst') in HH.
  rewrite <- HH; assumption.
  rewrite H0; reflexivity.
  inversion H_inst_uu; reflexivity.

  (* case Apply *)

  (** first of all : prove that the injection (l,vl) produces a value for e1 *)
  rename
    
    H3 into H_deps_spec,
    H4 into H_uu.
  assert(H_l_vl_not_loop_in_td1 := apply_timpact_fun_on_instantiable _ _ _ _ _ _ H_inst_uu H_uu).
  apply not_loop_in_conc_oitdeps1 in H_l_vl_not_loop_in_td1.

  (** induction on possible values of e1 after injection *)
  induction (apply_impact_fun l vl d1) as [v1|] eqn:H_aif_d1.

  (** the injection (l,vl) is in d1 *)

  apply (oival_Apply_correctness l vl v_inst v1 c e1 e2 td td' td1 td2 d d' d1 uu uu2 v (OIV_Closure x e c1) H_deps_spec H_aif_d1 H_inst_uu H_uu (IHoival_of1 H_inst_c) (IHoival_of2 H_inst_c)).

  assert( forall c1', Some c1' = instantiate_oienv l vl c1
    -> Some (V_Closure x e c1') =
    instantiate_oitval l vl
    (OIV td1 (OIV_ d1 (OIV_Closure x e c1)))).
  intros c1' H5.
  simpl.
  induction (apply_timpact_fun l vl td1).
  induction a.
  induction (H_l_vl_not_loop_in_td1 eq_refl).
  rewrite H_aif_d1.
  symmetry in H5; rewrite H5.
  simpl.
  reflexivity.
  rewrite H_aif_d1.
  symmetry in H5; rewrite H5.
  simpl.
  reflexivity.

  (** the injection (l,vl) is not in d1 *)

  (*
     uu est instantiable donc (l,vl) n'est pas dans td2
     donc uu2 est instantiable en v2
     c1 est instantiable en c1'
     on peut appliquer Val_of_with_injection_Apply with (c1:=c1') (e:=e) (x:=x) (v2:=v2)
     *)
  (* on a besoin de savoir que c1 s'instancie *)

  (*** instantiation of c1 *)
  induction (is_instantiable_oienv c1 l vl) as [c1'].
  
  (*** the injection (l,vl) has no impact in td2 *)
  assert(H_lvl_td2 : apply_timpact_fun l vl td2 <> Some true).
  intros H_l_vl_in_td2.
  rewrite H_uu in H_inst_uu.
  simpl in H_inst_uu.  
  apply apply_timpact_fun_in_conc_oitdeps_1 with (td':=(conc_oitdeps td td')) in H_l_vl_in_td2.
  apply apply_timpact_fun_in_conc_oitdeps_2 with (td:=td1) in H_l_vl_in_td2.
  rewrite H_l_vl_in_td2 in H_inst_uu.
  inversion H_inst_uu.

  (*** instantiation of uu2 *)
  induction (is_instantiable_oitval) with (uu:=uu2) (td:=td2) (u:=u2) (l:=l) (vl:=vl) as [v2 H_inst_uu2];
    try assumption.

  (*** application of the inference rule : 1 premise remains over 3 after auto *)
  apply Val_of_with_injection_Apply with (c1:=c1') (e:=e) (x:=x) (v2:=v2); auto.

  replace (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c1')) with (env_to_oitenv (Env_cons x v2 c1')); auto.
  apply val_of_with_injection_in_instantiated_oitenv with (c:=OITEnv_cons x uu2 (oienv_to_oitenv c1)).
  apply IHoival_of3.
  apply is_instantiable_oitenv_cons with (v:=v2).
  exists c1'.
  rewrite <- instantiate_oienv_to_oitenv.
  auto.
  assumption.

  assert (H_l_vl_not_in_td : apply_timpact_fun l vl td <> Some true).
  intros H_l_vl_in_td.
  rewrite H_uu in H_inst_uu; simpl in H_inst_uu.
  apply apply_timpact_fun_in_conc_oitdeps_1 with (td':=td') in H_l_vl_in_td.
  apply apply_timpact_fun_in_conc_oitdeps_2 with (td:=td2) in H_l_vl_in_td.
  apply apply_timpact_fun_in_conc_oitdeps_2 with (td:=td1) in H_l_vl_in_td.
  rewrite H_l_vl_in_td in H_inst_uu.
  inversion H_inst_uu.

  assert(HH_inst_uu:
           Some v_inst = match apply_impact_fun l vl (conc_oideps d' d) with
                           | Some v => Some v
                           | None => instantiate_oival0 l vl v
                         end).
  rewrite H_uu in H_inst_uu.
  simpl in H_inst_uu.
  induction (apply_timpact_fun l vl
                               (conc_oitdeps td1 (conc_oitdeps td2 (conc_oitdeps td td')))).
  induction a.
  inversion H_inst_uu.
  assumption.
  assumption.  

  simpl.
  
  rewrite utils.match_option_bool_not_true; auto.
  assert(H_l_not_in_td'_d':= deps_spec_Apply_l_not_in_d1 l vl _ _ _ _ H_deps_spec H_aif_d1).
  inversion H_l_not_in_td'_d'.
  rewrite (apply_impact_fun_conc_oideps_rev_none l vl d' d) in HH_inst_uu; auto.

  simpl.
  rewrite H_inst_uu2.
  rewrite <- instantiate_oienv_to_oitenv.
  rewrite H4.
  unfold option_map2.
  reflexivity.

  (* case Apply_rec *)
  rename
    H0 into H_uu1,
    H4 into H_deps_spec,
    H5 into H_uu.

  (** induction on possible values of e1 after injection *)
  induction (apply_impact_fun l vl d1) as [v1|] eqn:H_aif_d1.


  (** the injection (l,vl) is in d1 *)

  rewrite H_uu1 in IHoival_of1.
  apply (oival_Apply_correctness l vl v_inst v1 c e1 e2 td td' td1 td2 d d' d1 uu uu2 v (OIV_Rec_Closure f x e c1) H_deps_spec H_aif_d1 H_inst_uu H_uu (IHoival_of1 H_inst_c) (IHoival_of2 H_inst_c)).

  (** the injection (l,vl) is not in d1 *)

  (*** instantiation of c1 *)
  induction (is_instantiable_oienv c1 l vl) as [c1'].

  (*** the injection (l,vl) has no impact in td2 *)
  assert(H_lvl_td2 : apply_timpact_fun l vl td2 <> Some true).
  intros H_l_vl_in_td2.
  rewrite H_uu in H_inst_uu.
  simpl in H_inst_uu.  
  apply apply_timpact_fun_in_conc_oitdeps_1 with (td':=(conc_oitdeps td td')) in H_l_vl_in_td2.
  apply apply_timpact_fun_in_conc_oitdeps_2 with (td:=td1) in H_l_vl_in_td2.
  rewrite H_l_vl_in_td2 in H_inst_uu.
  inversion H_inst_uu.

  (*** instantiation of uu2 *)
  induction (is_instantiable_oitval) with (uu:=uu2) (td:=td2) (u:=u2) (l:=l) (vl:=vl) as [v2 H_inst_uu2];
    try assumption.

  (*** the injection (l,vl) has no impact in td1 *)
  assert(H_lvl_td1 : apply_timpact_fun l vl td1 <> Some true).
  intros H_l_vl_in_td1.
  rewrite H_uu in H_inst_uu.
  simpl in H_inst_uu.  
  apply apply_timpact_fun_in_conc_oitdeps_1 with (td':=conc_oitdeps td2 (conc_oitdeps td td')) in H_l_vl_in_td1.
  rewrite H_l_vl_in_td1 in H_inst_uu.
  inversion H_inst_uu.

  (*** instantiation of uu1 *)
  induction (is_instantiable_oitval) with (uu:=uu1) (td:=td1) (u:=OIV_ d1 (OIV_Rec_Closure f x e c1)) (l:=l) (vl:=vl) as [v1 H_inst_uu1];
    try assumption.
  assert (H_v1: v1 = V_Rec_Closure f x e c1').
  rewrite H_uu1 in H_inst_uu1.
  simpl in H_inst_uu1.
  rewrite H_aif_d1 in H_inst_uu1.
  rewrite H0 in H_inst_uu1.
  simpl in H_inst_uu1.
  induction (apply_timpact_fun l vl td1).
  induction a.
  elim H_lvl_td1; reflexivity.
  inversion H_inst_uu1; reflexivity.
  inversion H_inst_uu1; reflexivity.


  (*** application of the inference rule : 2 premise remains over 3 after auto *)
  apply Val_of_with_injection_Apply_rec with (c1:=c1') (e:=e) (f:=f) (x:=x) (v2:=v2); auto.


  assert(H_l_vl_not_loop_in_td1 := apply_timpact_fun_on_instantiable _ _ _ _ _ _ H_inst_uu H_uu).
  apply not_loop_in_conc_oitdeps1 in H_l_vl_not_loop_in_td1.
  assert( Some (V_Rec_Closure f x e c1') =
    instantiate_oitval l vl
    (OIV td1 (OIV_ d1 (OIV_Rec_Closure f x e c1)))).
  simpl.
  induction (apply_timpact_fun l vl td1).
  induction a.
  induction (H_l_vl_not_loop_in_td1 eq_refl).
  rewrite H_aif_d1.
  rewrite H0.
  simpl.
  reflexivity.
  rewrite H_aif_d1.
  rewrite H0.
  simpl.
  reflexivity.
  rewrite <- H_uu1 in H4.

  auto.

  simpl.

  replace (OITEnv_cons f (val_to_oitval (V_Rec_Closure f x e c1'))
    (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c1'))) with (env_to_oitenv (Env_cons f (V_Rec_Closure f x e c1') (Env_cons x v2 c1'))); auto.

  assert(H_inst_env : instantiate_oitenv l vl
                                         (OITEnv_cons f uu1 (OITEnv_cons x uu2 (oienv_to_oitenv c1))) =
                      Some (Env_cons f (V_Rec_Closure f x e c1') (Env_cons x v2 c1'))).
  simpl.
  rewrite H_inst_uu1.
  rewrite H_inst_uu2.
  rewrite <- instantiate_oienv_to_oitenv.
  rewrite H0.
  simpl.
  rewrite <- H_v1; reflexivity.
  
  apply val_of_with_injection_in_instantiated_oitenv with (c:=OITEnv_cons f uu1 (OITEnv_cons x uu2 (oienv_to_oitenv c1))); auto.

  apply IHoival_of3.
  exists(Env_cons f (V_Rec_Closure f x e c1') (Env_cons x v2 c1')).
  auto.


  assert (H_l_vl_not_in_td : apply_timpact_fun l vl td <> Some true).
  intros H_l_vl_in_td.
  rewrite H_uu in H_inst_uu; simpl in H_inst_uu.
  apply apply_timpact_fun_in_conc_oitdeps_1 with (td':=td') in H_l_vl_in_td.
  apply apply_timpact_fun_in_conc_oitdeps_2 with (td:=td2) in H_l_vl_in_td.
  apply apply_timpact_fun_in_conc_oitdeps_2 with (td:=td1) in H_l_vl_in_td.
  rewrite H_l_vl_in_td in H_inst_uu.
  inversion H_inst_uu.

  assert(HH_inst_uu:
           Some v_inst = match apply_impact_fun l vl (conc_oideps d' d) with
                           | Some v => Some v
                           | None => instantiate_oival0 l vl v
                         end).
  rewrite H_uu in H_inst_uu.
  simpl in H_inst_uu.
  induction (apply_timpact_fun l vl
                               (conc_oitdeps td1 (conc_oitdeps td2 (conc_oitdeps td td')))).
  induction a.
  inversion H_inst_uu.
  assumption.
  assumption.  

  simpl.

  rewrite utils.match_option_bool_not_true; auto.
  assert(H_l_not_in_td'_d':= deps_spec_Apply_l_not_in_d1 l vl _ _ _ _ H_deps_spec H_aif_d1).
  inversion H_l_not_in_td'_d'.
  rewrite (apply_impact_fun_conc_oideps_rev_none l vl d' d) in HH_inst_uu; auto.

  (* case Let_in *)
  rename H0 into H_uu1;
    rename H2 into H_uu2.

  (** instantiation of uu1 *)
  assert(H_inst_uu1 : exists (v1:val), instantiate_oitval l vl uu1 = Some v1).
  eapply apply_timpact_fun_on_instantiable with (td:=conc_oitdeps td1 td2) in H_inst_uu; auto.
  apply not_loop_in_conc_oitdeps1 in H_inst_uu.
  apply is_instantiable_oitval with (uu:=uu1) (u:=u1) in H_inst_uu; auto.
  inversion_clear H_inst_uu1 as [v1].

  apply Val_of_with_injection_Let_in with (v1:=v1).

  apply IHoival_of1.
  assumption.
  auto.

  apply val_of_with_injection_in_partially_instantiated_oitenv with (c1:=OITEnv_cons x uu1 c).
  apply IHoival_of2.
  inversion H_inst_c as [c'].
  exists (Env_cons x v1 c').
  simpl.
  rewrite H0; rewrite <- H2.
  simpl.
  reflexivity.
  rewrite H_uu2; simpl.
  simpl in H_inst_uu.

  assert(H_td1_td2: apply_timpact_fun l vl (conc_oitdeps td1 td2) <> Some true).
  intro HH.
  induction (apply_timpact_fun l vl (conc_oitdeps td1 td2)); try solve [inversion HH].
  induction a; try solve [inversion HH].
  inversion H_inst_uu.

  rewrite utils.match_option_bool_not_true in H_inst_uu; try assumption.
  rewrite utils.match_option_bool_not_true; try assumption.
  apply not_loop_in_conc_oitdeps2 with (td:=td1); assumption.

  apply Partially_instantiated_oitenv_cons_inst with (v1:=v1); auto.
  apply partially_instantiated_oitenv_refl.

  (* case If true *)
  rename H0 into H_oival_of_e1, H1 into H_uu1, H2 into H_deps_spec.

  (** not loop in td *)
  assert(H_not_loop_in_td: apply_timpact_fun l vl td <> Some true).
  apply not_loop_in_conc_oitdeps1 with (td':=td1).
  apply not_loop_in_conc_oitdeps2 with (td:=td').
  simpl in H_inst_uu.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (** not loop in td1 *)
  assert(H_not_loop_in_td1: apply_timpact_fun l vl td1 <> Some true).
  apply not_loop_in_conc_oitdeps2 with (td:=td).
  apply not_loop_in_conc_oitdeps2 with (td:=td').
  simpl in H_inst_uu.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (** value of e with injection *)
  replaceH IHoival_of1 (fun (b:bool) => IHoival_of1 H_inst_c (V_Bool b)).

  (** value of e1 with injection *)
  specialize (IHoival_of2 H_inst_c v_inst).
  rewrite H_uu1 in IHoival_of2; simpl in IHoival_of2.
  rewrite utils.match_option_bool_not_true in IHoival_of2; auto.

  clear H. assert (H:=0).
  induction H_deps_spec.

  (*** d = nil *)
  simpl in H_inst_uu.
  specialize (IHoival_of1 true).
  simpl in IHoival_of1.
  rewrite utils.match_option_bool_not_true in IHoival_of1; auto.
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  specialize (IHoival_of1 eq_refl).
  specialize (IHoival_of2 H_inst_uu).
  apply Val_of_with_injection_If_true; auto.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (*** d = cons *)
  simpl in IHoival_of1.
  simpl in H_inst_uu.
  destruct (eq_label_dec l l0).
  (**** l = l0 *)
  clear IHH_deps_spec.
  specialize (H0 vl).
  destruct (f vl);
    try solve [inversion H0;
                rewrite H1 in H_inst_uu;
                simpl in H_inst_uu;
                destruct (apply_timpact_fun l vl
                                            (conc_oitdeps oitd' (conc_oitdeps td td1))); inversion H_inst_uu].
  destruct b.
  (***** f vl = V_Bool true *)
  specialize (IHoival_of1 true).
  simpl in IHoival_of1.
  rewrite utils.match_option_bool_not_true in IHoival_of1; auto.
  specialize (IHoival_of1 eq_refl).
  inversion_clear H0 as [H_ex H_nex].
  destruct(excluded_middle (exists v1 : val, val_of_with_injection l0 vl c e1 v1)).
  clear H_nex.
  inversion_clear H0 as [vv1 H_val_e1].
  specialize (H_ex vv1 H_val_e1).
  inversion_clear H_ex as [H_tf' H_f'].
  rewrite H_tf', H_f' in H_inst_uu.
  simpl in H_inst_uu.
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  inversion H_inst_uu.
  rewrite <-e0 in H_val_e1.
  apply Val_of_with_injection_If_true; auto.
  destruct (apply_timpact_fun l vl (conc_oitdeps oitd' (conc_oitdeps td td1))).
  destruct b.
  inversion H_inst_uu.
  inversion 1.
  inversion 1.
  specialize (H_nex H0).
  inversion H_nex.
  rewrite H1 in H_inst_uu;
    simpl in H_inst_uu;
    destruct (apply_timpact_fun l vl
                                (conc_oitdeps oitd' (conc_oitdeps td td1))); inversion H_inst_uu.

  (***** f vl = V_Bool false *)
  specialize (IHoival_of1 false).
  simpl in IHoival_of1.
  rewrite utils.match_option_bool_not_true in IHoival_of1; auto.
  specialize (IHoival_of1 eq_refl).
  inversion_clear H0 as [H_ex H_nex].
  destruct(excluded_middle (exists v2 : val, val_of_with_injection l0 vl c e2 v2)).
  clear H_nex.
  inversion_clear H0 as [vv2 H_val_e2].
  specialize (H_ex vv2 H_val_e2).
  inversion_clear H_ex as [H_tf' H_f'].
  rewrite H_tf', H_f' in H_inst_uu.
  simpl in H_inst_uu.
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  inversion H_inst_uu.
  rewrite <-e0 in H_val_e2.
  apply Val_of_with_injection_If_false; auto.
  destruct (apply_timpact_fun l vl (conc_oitdeps oitd' (conc_oitdeps td td1))).
  destruct b.
  inversion H_inst_uu.
  inversion 1.
  inversion 1.
  specialize (H_nex H0).
  inversion H_nex.
  rewrite H1 in H_inst_uu;
    simpl in H_inst_uu;
    destruct (apply_timpact_fun l vl
                                (conc_oitdeps oitd' (conc_oitdeps td td1))); inversion H_inst_uu.

  (**** l <> l0 *)
  apply IHH_deps_spec; auto.


  (* case If false *)
  rename H0 into H_oival_of_e2, H1 into H_uu2, H2 into H_deps_spec.

  (** not loop in td *)
  assert(H_not_loop_in_td: apply_timpact_fun l vl td <> Some true).
  apply not_loop_in_conc_oitdeps1 with (td':=td2).
  apply not_loop_in_conc_oitdeps2 with (td:=td').
  simpl in H_inst_uu.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (** not loop in td1 *)
  assert(H_not_loop_in_td1: apply_timpact_fun l vl td2 <> Some true).
  apply not_loop_in_conc_oitdeps2 with (td:=td).
  apply not_loop_in_conc_oitdeps2 with (td:=td').
  simpl in H_inst_uu.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (** value of e with injection *)
  replaceH IHoival_of1 (fun (b:bool) => IHoival_of1 H_inst_c (V_Bool b)).

  (** value of e1 with injection *)
  specialize (IHoival_of2 H_inst_c v_inst).
  rewrite H_uu2 in IHoival_of2; simpl in IHoival_of2.
  rewrite utils.match_option_bool_not_true in IHoival_of2; auto.

  clear H. assert (H:=0).
  induction H_deps_spec.

  (*** d = nil *)
  simpl in H_inst_uu.
  specialize (IHoival_of1 false).
  simpl in IHoival_of1.
  rewrite utils.match_option_bool_not_true in IHoival_of1; auto.
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  specialize (IHoival_of1 eq_refl).
  specialize (IHoival_of2 H_inst_uu).
  apply Val_of_with_injection_If_false; auto.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (*** d = cons *)
  simpl in IHoival_of1.
  simpl in H_inst_uu.
  destruct (eq_label_dec l l0).
  (**** l = l0 *)
  clear IHH_deps_spec.
  specialize (H0 vl).
  destruct (f vl);
    try solve [inversion H0;
                rewrite H1 in H_inst_uu;
                simpl in H_inst_uu;
                destruct (apply_timpact_fun l vl
                                            (conc_oitdeps oitd' (conc_oitdeps td td2))); inversion H_inst_uu].
  destruct b.
  (***** f vl = V_Bool true *)
  specialize (IHoival_of1 true).
  simpl in IHoival_of1.
  rewrite utils.match_option_bool_not_true in IHoival_of1; auto.
  specialize (IHoival_of1 eq_refl).
  inversion_clear H0 as [H_ex H_nex].
  destruct(excluded_middle (exists v1 : val, val_of_with_injection l0 vl c e1 v1)).
  clear H_nex.
  inversion_clear H0 as [vv1 H_val_e1].
  specialize (H_ex vv1 H_val_e1).
  inversion_clear H_ex as [H_tf' H_f'].
  rewrite H_tf', H_f' in H_inst_uu.
  simpl in H_inst_uu.
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  inversion H_inst_uu.
  rewrite <-e0 in H_val_e1.
  apply Val_of_with_injection_If_true; auto.
  destruct (apply_timpact_fun l vl (conc_oitdeps oitd' (conc_oitdeps td td2))).
  destruct b.
  inversion H_inst_uu.
  inversion 1.
  inversion 1.
  specialize (H_nex H0).
  inversion H_nex.
  rewrite H1 in H_inst_uu;
    simpl in H_inst_uu;
    destruct (apply_timpact_fun l vl
                                (conc_oitdeps oitd' (conc_oitdeps td td2))); inversion H_inst_uu.

  (***** f vl = V_Bool false *)
  specialize (IHoival_of1 false).
  simpl in IHoival_of1.
  rewrite utils.match_option_bool_not_true in IHoival_of1; auto.
  specialize (IHoival_of1 eq_refl).
  inversion_clear H0 as [H_ex H_nex].
  destruct(excluded_middle (exists v2 : val, val_of_with_injection l0 vl c e2 v2)).
  clear H_nex.
  inversion_clear H0 as [vv2 H_val_e2].
  specialize (H_ex vv2 H_val_e2).
  inversion_clear H_ex as [H_tf' H_f'].
  rewrite H_tf', H_f' in H_inst_uu.
  simpl in H_inst_uu.
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  inversion H_inst_uu.
  rewrite <-e0 in H_val_e2.
  apply Val_of_with_injection_If_false; auto.
  destruct (apply_timpact_fun l vl (conc_oitdeps oitd' (conc_oitdeps td td2))).
  destruct b.
  inversion H_inst_uu.
  inversion 1.
  inversion 1.
  specialize (H_nex H0).
  inversion H_nex.
  rewrite H1 in H_inst_uu;
    simpl in H_inst_uu;
    destruct (apply_timpact_fun l vl
                                (conc_oitdeps oitd' (conc_oitdeps td td2))); inversion H_inst_uu.

  (**** l <> l0 *)
  apply IHH_deps_spec; auto.

  (* case Match *)
  rename H into H_oival_of_e, H0 into H_uu, H1 into H_is_filtered, H2 into H_oival_of_e1;
    rename H3 into H_uu1, H4 into H_deps_spec.

  (** not loop in td *)
  assert(H_not_loop_in_td: apply_timpact_fun l vl td <> Some true).
  apply not_loop_in_conc_oitdeps1 with (td':=td1).
  apply not_loop_in_conc_oitdeps2 with (td:=td').
  simpl in H_inst_uu.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (** not loop in td1 *)
  assert(H_not_loop_in_td1: apply_timpact_fun l vl td1 <> Some true).
  apply not_loop_in_conc_oitdeps2 with (td:=td).
  apply not_loop_in_conc_oitdeps2 with (td:=td').
  simpl in H_inst_uu.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (** value of e with injection *)
  specialize (IHoival_of1 H_inst_c).

  (** value of e1 with injection *)
  specialize (IHoival_of2 (is_instantiable_oitenv_conc l vl _ _ (is_instantiable_oitenv_of_is_filtered _ _ _ _ _ H_is_filtered) H_inst_c) v_inst).
  rewrite H_uu1 in IHoival_of2; simpl in IHoival_of2.
  rewrite utils.match_option_bool_not_true in IHoival_of2; auto.

  clear H_oival_of_e.
  revert dependent uu.
  induction H_deps_spec;
  intros uu H_uu H_is_filtered IHoival_of1.

  (*** d = nil *)
  rewrite H_uu in H_is_filtered.
  simpl in H_inst_uu.
  rewrite utils.match_option_bool_not_true in H_inst_uu;
    try apply (not_loop_in_conc_oitdeps l vl td td1 H_not_loop_in_td H_not_loop_in_td1).
  specialize (IHoival_of2 H_inst_uu).
  destruct v; destruct p; inversion H_is_filtered.

  destruct (eq_nat_dec n c0) eqn:Heq_n_c0; inversion H0.
  apply Val_of_with_injection_Match with (c_p:=Env_empty) (v_e:=V_Constr0 n).
  apply IHoival_of1; rewrite H_uu; simpl.
  rewrite utils.match_option_bool_not_true; auto.
  simpl.
  rewrite Heq_n_c0; auto.
  rewrite <-H1 in IHoival_of2.
  apply IHoival_of2.
  
  destruct (eq_nat_dec n c0) eqn:Heq_n_c0; inversion H0.
  assert(H_inst_u:=is_instantiable_oival u l vl).
  inversion_clear H_inst_u as [v' HH_inst_u].
  specialize (IHoival_of1 (V_Constr1 n v')).
  apply Val_of_with_injection_Match with (c_p:=Env_cons i v' Env_empty) (v_e:=V_Constr1 n v'); auto.
  apply IHoival_of1; rewrite H_uu; simpl.
  rewrite utils.match_option_bool_not_true; auto.
  rewrite HH_inst_u; auto.
  simpl.
  rewrite Heq_n_c0; auto.
  simpl.
  rewrite <-H1 in IHoival_of2; simpl in IHoival_of2.
  apply val_of_with_injection_in_partially_instantiated_oitenv with (c1:=OITEnv_cons i (OIV nil u) c); auto.
  apply Partially_instantiated_oitenv_cons_inst with (v1:= v'); auto.
  apply partially_instantiated_oitenv_refl.

  assert(H_inst_u1:=is_instantiable_oival u1 l vl).
  inversion_clear H_inst_u1 as [v1' HH_inst_u1].
  assert(H_inst_u2:=is_instantiable_oival u2 l vl).
  inversion_clear H_inst_u2 as [v2' HH_inst_u2].
  apply Val_of_with_injection_Match with (c_p:=Env_cons i v1' (Env_cons i0 v2' Env_empty)) (v_e:=V_Couple v1' v2'); auto.
  apply IHoival_of1; rewrite H_uu; simpl.
  rewrite utils.match_option_bool_not_true; auto.
  rewrite HH_inst_u1, HH_inst_u2; auto.
  simpl.
  rewrite <-H0 in IHoival_of2; simpl in IHoival_of2.
  apply val_of_with_injection_in_partially_instantiated_oitenv with (c1:=OITEnv_cons i (OIV nil u1) (OITEnv_cons i0 (OIV nil u2) c)); auto.
  apply Partially_instantiated_oitenv_cons_inst with (v1:= v1'); auto.
  apply Partially_instantiated_oitenv_cons_inst with (v1:= v2'); auto.
  apply partially_instantiated_oitenv_refl.

  (*** d = cons *)
  rewrite H_uu in IHoival_of1.
  simpl in IHoival_of1.
  rewrite utils.match_option_bool_not_true in IHoival_of1; auto.
  simpl in H_inst_uu.
  destruct (eq_label_dec l l0).
  (**** l = l0 *)
  clear IHH_deps_spec.
  specialize (H vl).
  specialize (IHoival_of1 (f vl) eq_refl).

  (***** tf' vl = true is absurd *)
  assert(H_tf'_absurd : tf' vl = true -> False).
  intro H_tf'.
  rewrite H_tf' in H_inst_uu.
  destruct (apply_timpact_fun l vl
                    (conc_oitdeps oitd' (conc_oitdeps td td1))); inversion H_inst_uu.

  (***** v_inst = f' vl *)
  assert(H_v_inst_f'_vl: v_inst = f' vl).
  destruct (match
                  apply_timpact_fun l vl
                    (conc_oitdeps oitd' (conc_oitdeps td td1))
                with
                | Some b => Some (tf' vl || b)%bool
                | None => Some (tf' vl)
                end); [destruct b|auto]; inversion H_inst_uu; auto.
  
  clear dependent c_p.
  clear dependent H_inst_uu.
  clear dependent uu1.
  clear dependent td1.
  clear dependent d1.
  clear dependent v1.
  let tac_ex2 :=
      clear H_nex;
        inversion_clear H_exists as [v2 H_val_of_e2];
        specialize (H_ex v2 H_val_of_e2);
        inversion_clear H_ex as [H_tf' H_f'];
        apply Val_of_with_injection_Match_var with (v_e:=f vl); rewrite H_f_vl; auto;
        rewrite H_v_inst_f'_vl, H_f', e0, <-H_f_vl; auto
  in
    let tac_nex :=
        clear H_ex;
          specialize (H_nex H_not_exists);
          inversion_clear H_nex as [H_tf' H_f'];
          elim(H_tf'_absurd H_tf')
    in
    let tac_excluded_middle2 :=
        destruct(excluded_middle (exists v2 : val,
                                    val_of_with_injection l0 vl
                                                          (OITEnv_cons x (val_to_oitval (f vl)) c) e2 v2)) as [H_exists|H_not_exists]; idtac
    in
    let tac_excluded_middle1 :=
        destruct(excluded_middle (exists v1 : val,
                                             val_of_with_injection l0 vl
                                                                   (conc_oitenv (env_to_oitenv Env_empty) c) e1 v1)) as [H_exists|H_not_exists]; idtac
    in
    let tac_not_match :=
        inversion_clear H as [H_ex H_nex];
        rewrite <- H_f_vl in H_ex; rewrite <- H_f_vl in H_nex;
        tac_excluded_middle2;
        [tac_ex2|tac_nex]
    in
    let tac_ex1_Constr0 :=
        clear H_nex;
          inversion_clear H_exists as [v1' H_val_of_e1];
          specialize (H_ex v1' H_val_of_e1);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match with (c_p:=Env_empty) (v_e:=V_Constr0 n); auto;
          [simpl; rewrite H_n_c0; reflexivity
          |rewrite H_v_inst_f'_vl, H_f', e0; auto]
    in
    let tac_ex2_Constr0 :=
        clear H_nex;
          inversion_clear H_exists as [v2 H_val_of_e2];
          specialize (H_ex v2 H_val_of_e2);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match_var with (v_e:=f vl); rewrite H_f_vl; auto;
          [simpl; rewrite H_n_c0; reflexivity
          |rewrite H_v_inst_f'_vl, H_f', e0, <-H_f_vl; auto]
    in
    let tac_match_Constr0 :=
        simpl in H;
                destruct(eq_nat_dec n c0) eqn:H_n_c0;
                inversion_clear H as [H_ex H_nex];
                [tac_excluded_middle1;[tac_ex1_Constr0|tac_nex]
                |rewrite <- H_f_vl in H_ex; rewrite <- H_f_vl in H_nex;tac_excluded_middle2;[tac_ex2_Constr0|tac_nex]]
    in
    let tac_excluded_middle1_Constr1 :=
        destruct(excluded_middle (exists v1 : val,
             val_of_with_injection l0 vl
               (conc_oitenv (env_to_oitenv (Env_cons i v0 Env_empty)) c) e1
               v1)) as [H_exists|H_not_exists]; idtac
    in
    let tac_excluded_middle2_Constr1 :=
        destruct(excluded_middle (exists v2 : val,
             val_of_with_injection l0 vl
               (OITEnv_cons x (val_to_oitval (V_Constr1 n v0)) c) e2 v2)) as [H_exists|H_not_exists]; idtac
    in
    let tac_ex1_Constr1 :=
        clear H_nex;
          inversion_clear H_exists as [v1' H_val_of_e1];
          specialize (H_ex v1' H_val_of_e1);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match with (c_p:=Env_cons i v0 Env_empty) (v_e:=V_Constr1 n v0); auto;
          [simpl; rewrite H_n_c0; reflexivity
          |rewrite H_v_inst_f'_vl, H_f', e0; auto]
    in
    let tac_ex2_Constr1 :=
        clear H_nex;
          inversion_clear H_exists as [v2 H_val_of_e2];
          specialize (H_ex v2 H_val_of_e2);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match_var with (v_e:=f vl); rewrite H_f_vl; auto;
          [simpl; rewrite H_n_c0; reflexivity
          |rewrite H_v_inst_f'_vl, H_f', e0; auto]
    in
    let tac_match_Constr1 :=
        simpl in H;
                destruct(eq_nat_dec n c0) eqn:H_n_c0;
                inversion_clear H as [H_ex H_nex];
                [tac_excluded_middle1_Constr1;[tac_ex1_Constr1|tac_nex]
                |tac_excluded_middle2_Constr1;[tac_ex2_Constr1|tac_nex] ]
    in
    let tac_excluded_middle_Couple :=
        destruct(excluded_middle (exists v1 : val,
             val_of_with_injection l0 vl
               (OITEnv_cons i (val_to_oitval v0_1)
                  (OITEnv_cons i0 (val_to_oitval v0_2) c)) e1 v1)) as [H_exists|H_not_exists]; idtac
    in
    let tac_ex_Couple :=
        clear H_nex;
          inversion_clear H_exists as [v1' H_val_of_e1];
          specialize (H_ex v1' H_val_of_e1);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match with (c_p:=Env_cons i v0_1 (Env_cons i0 v0_2 Env_empty)) (v_e:=V_Couple v0_1 v0_2); auto;
          simpl; rewrite H_v_inst_f'_vl, H_f', e0; auto;
          idtac
    in
    let tac_match_Couple :=
        simpl in H;
                inversion_clear H as [H_ex H_nex];
                tac_excluded_middle_Couple;
                [tac_ex_Couple|tac_nex];
                idtac
    in
    let tac_match_error :=
        inversion_clear H as [H_tf' H_f']; elim (H_tf'_absurd H_tf')
    in
    destruct (f vl) eqn:H_f_vl; destruct p;
          try solve [tac_not_match|tac_match_Constr0|tac_match_Constr1];
          try tac_match_error;
          tac_match_Couple.


  (**** l <> l0 *)
  apply IHH_deps_spec with (uu:=OIV td (OIV_ oid v)); auto.

  rewrite H_uu in H_is_filtered.
  simpl; induction v; inversion H_is_filtered; auto.

  intros v0 H0.
  apply IHoival_of1.
  simpl in H0.
  rewrite utils.match_option_bool_not_true in H0; auto.


  (* case Match_var *)
  rename H into H_oival_of_e, H0 into H_uu, H1 into H_is_filtered, H2 into H_oival_of_e2;
    rename H3 into H_uu2, H4 into H_deps_spec.

  (** not loop in td *)
  assert(H_not_loop_in_td: apply_timpact_fun l vl td <> Some true).
  apply not_loop_in_conc_oitdeps1 with (td':=td2).
  apply not_loop_in_conc_oitdeps2 with (td:=td').
  simpl in H_inst_uu.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (** not loop in td1 *)
  assert(H_not_loop_in_td2: apply_timpact_fun l vl td2 <> Some true).
  apply not_loop_in_conc_oitdeps2 with (td:=td).
  apply not_loop_in_conc_oitdeps2 with (td:=td').
  simpl in H_inst_uu.
  intro HHH; rewrite HHH in H_inst_uu; inversion H_inst_uu.
  
  (** value of e with injection *)
  specialize (IHoival_of1 H_inst_c).

  (** value of e1 with injection *)
  assert (HH_inst_uu:= is_instantiable_oitval uu td (OIV_ d v) l vl H_uu H_not_loop_in_td).
  inversion_clear HH_inst_uu as [v' HHH_inst_uu].
  specialize (IHoival_of2 (is_instantiable_oitenv_cons l vl v' c x uu H_inst_c HHH_inst_uu) v_inst).
  rewrite H_uu2 in IHoival_of2; simpl in IHoival_of2.
  rewrite utils.match_option_bool_not_true in IHoival_of2; auto.

  clear H_oival_of_e.
  clear H_oival_of_e2.
  revert dependent uu.
  revert dependent uu2.
  induction H_deps_spec;
  intros uu2 H_uu2 uu H_uu H_is_filtered IHoival_of1 IHoival_of2 HHH_inst_uu.

  (*** d = nil *)
  rewrite H_uu in H_is_filtered.
  simpl in H_inst_uu.
  rewrite utils.match_option_bool_not_true in H_inst_uu;
    try apply (not_loop_in_conc_oitdeps l vl td td2 H_not_loop_in_td H_not_loop_in_td2).
  specialize (IHoival_of2 H_inst_uu).
  
  specialize (IHoival_of1 v' (eq_sym HHH_inst_uu)).
  rewrite H_uu in HHH_inst_uu.
  apply is_not_filtered_instantiate_oitval with (l:=l) (vl:=vl) (v':=v') in H_is_filtered; auto.
  rewrite <-H_uu in HHH_inst_uu.
  
  apply Val_of_with_injection_Match_var with (v_e:=v'); auto.
  
  apply val_of_with_injection_in_partially_instantiated_oitenv with (c1:=OITEnv_cons x uu c); auto.
  apply Partially_instantiated_oitenv_cons_inst with (v1:= v'); auto.
  apply partially_instantiated_oitenv_refl.

  (*** d = cons *)
  rewrite H_uu in IHoival_of1.
  simpl in IHoival_of1.
  rewrite utils.match_option_bool_not_true in IHoival_of1; auto.
  simpl in H_inst_uu.
  destruct (eq_label_dec l l0).
  (**** l = l0 *)
  clear IHH_deps_spec.
  specialize (H vl).
  specialize (IHoival_of1 (f vl) eq_refl).

  (***** tf' vl = true is absurd *)
  assert(H_tf'_absurd : tf' vl = true -> False).
  intro H_tf'.
  rewrite H_tf' in H_inst_uu.
  destruct (apply_timpact_fun l vl
                    (conc_oitdeps oitd' (conc_oitdeps td td2))); inversion H_inst_uu.

  (***** v_inst = f' vl *)
  assert(H_v_inst_f'_vl: v_inst = f' vl).
  destruct (match
                  apply_timpact_fun l vl
                    (conc_oitdeps oitd' (conc_oitdeps td td2))
                with
                | Some b => Some (tf' vl || b)%bool
                | None => Some (tf' vl)
                end); [destruct b|auto]; inversion H_inst_uu; auto.
  
  clear dependent H_inst_uu.
  clear dependent v'.
  clear dependent uu2.
  clear dependent td2.
  clear dependent d2.
  clear dependent v2.
  let tac_ex2 :=
      clear H_nex;
        inversion_clear H_exists as [v2 H_val_of_e2];
        specialize (H_ex v2 H_val_of_e2);
        inversion_clear H_ex as [H_tf' H_f'];
        apply Val_of_with_injection_Match_var with (v_e:=f vl); rewrite H_f_vl; auto;
        rewrite H_v_inst_f'_vl, H_f', e0, <-H_f_vl; auto
  in
    let tac_nex :=
        clear H_ex;
          specialize (H_nex H_not_exists);
          inversion_clear H_nex as [H_tf' H_f'];
          elim(H_tf'_absurd H_tf')
    in
    let tac_excluded_middle2 :=
        destruct(excluded_middle (exists v2 : val,
                                    val_of_with_injection l0 vl
                                                          (OITEnv_cons x (val_to_oitval (f vl)) c) e2 v2)) as [H_exists|H_not_exists]; idtac
    in
    let tac_excluded_middle1 :=
        destruct(excluded_middle (exists v1 : val,
                                             val_of_with_injection l0 vl
                                                                   (conc_oitenv (env_to_oitenv Env_empty) c) e1 v1)) as [H_exists|H_not_exists]; idtac
    in
    let tac_not_match :=
        inversion_clear H as [H_ex H_nex];
        rewrite <- H_f_vl in H_ex; rewrite <- H_f_vl in H_nex;
        tac_excluded_middle2;
        [tac_ex2|tac_nex]
    in
    let tac_ex1_Constr0 :=
        clear H_nex;
          inversion_clear H_exists as [v1' H_val_of_e1];
          specialize (H_ex v1' H_val_of_e1);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match with (c_p:=Env_empty) (v_e:=V_Constr0 n); auto;
          [simpl; rewrite H_n_c0; reflexivity
          |rewrite H_v_inst_f'_vl, H_f', e0; auto]
    in
    let tac_ex2_Constr0 :=
        clear H_nex;
          inversion_clear H_exists as [v2 H_val_of_e2];
          specialize (H_ex v2 H_val_of_e2);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match_var with (v_e:=f vl); rewrite H_f_vl; auto;
          [simpl; rewrite H_n_c0; reflexivity
          |rewrite H_v_inst_f'_vl, H_f', e0, <-H_f_vl; auto]
    in
    let tac_match_Constr0 :=
        simpl in H;
                destruct(eq_nat_dec n c0) eqn:H_n_c0;
                inversion_clear H as [H_ex H_nex];
                [tac_excluded_middle1;[tac_ex1_Constr0|tac_nex]
                |rewrite <- H_f_vl in H_ex; rewrite <- H_f_vl in H_nex;tac_excluded_middle2;[tac_ex2_Constr0|tac_nex]]
    in
    let tac_excluded_middle1_Constr1 :=
        destruct(excluded_middle (exists v1 : val,
             val_of_with_injection l0 vl
               (conc_oitenv (env_to_oitenv (Env_cons i v0 Env_empty)) c) e1
               v1)) as [H_exists|H_not_exists]; idtac
    in
    let tac_excluded_middle2_Constr1 :=
        destruct(excluded_middle (exists v2 : val,
             val_of_with_injection l0 vl
               (OITEnv_cons x (val_to_oitval (V_Constr1 n v0)) c) e2 v2)) as [H_exists|H_not_exists]; idtac
    in
    let tac_ex1_Constr1 :=
        clear H_nex;
          inversion_clear H_exists as [v1' H_val_of_e1];
          specialize (H_ex v1' H_val_of_e1);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match with (c_p:=Env_cons i v0 Env_empty) (v_e:=V_Constr1 n v0); auto;
          [simpl; rewrite H_n_c0; reflexivity
          |rewrite H_v_inst_f'_vl, H_f', e0; auto]
    in
    let tac_ex2_Constr1 :=
        clear H_nex;
          inversion_clear H_exists as [v2 H_val_of_e2];
          specialize (H_ex v2 H_val_of_e2);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match_var with (v_e:=f vl); rewrite H_f_vl; auto;
          [simpl; rewrite H_n_c0; reflexivity
          |rewrite H_v_inst_f'_vl, H_f', e0; auto]
    in
    let tac_match_Constr1 :=
        simpl in H;
                destruct(eq_nat_dec n c0) eqn:H_n_c0;
                inversion_clear H as [H_ex H_nex];
                [tac_excluded_middle1_Constr1;[tac_ex1_Constr1|tac_nex]
                |tac_excluded_middle2_Constr1;[tac_ex2_Constr1|tac_nex] ]
    in
    let tac_excluded_middle_Couple :=
        destruct(excluded_middle (exists v1 : val,
             val_of_with_injection l0 vl
               (OITEnv_cons i (val_to_oitval v0_1)
                  (OITEnv_cons i0 (val_to_oitval v0_2) c)) e1 v1)) as [H_exists|H_not_exists]; idtac
    in
    let tac_ex_Couple :=
        clear H_nex;
          inversion_clear H_exists as [v1' H_val_of_e1];
          specialize (H_ex v1' H_val_of_e1);
          inversion_clear H_ex as [H_tf' H_f'];
          apply Val_of_with_injection_Match with (c_p:=Env_cons i v0_1 (Env_cons i0 v0_2 Env_empty)) (v_e:=V_Couple v0_1 v0_2); auto;
          simpl; rewrite H_v_inst_f'_vl, H_f', e0; auto;
          idtac
    in
    let tac_match_Couple :=
        simpl in H;
                inversion_clear H as [H_ex H_nex];
                tac_excluded_middle_Couple;
                [tac_ex_Couple|tac_nex];
                idtac
    in
    let tac_match_error :=
        inversion_clear H as [H_tf' H_f']; elim (H_tf'_absurd H_tf')
    in
    destruct (f vl) eqn:H_f_vl; destruct p;
          try solve [tac_not_match|tac_match_Constr0|tac_match_Constr1];
          try tac_match_error;
          tac_match_Couple.

  (**** l <> l0 *)
          
  rewrite H_uu in H_is_filtered.
  rewrite H_uu in IHoival_of2.
  rewrite H_uu in HHH_inst_uu.
  apply IHH_deps_spec with (uu:=OIV td (OIV_ oid v)) (uu2:=uu2); auto.

  intros v0 H0.
  apply IHoival_of1.
  simpl in H0.
  rewrite utils.match_option_bool_not_true in H0; auto.

  rewrite utils.match_option_bool_not_true in H_inst_uu;
  [|intros H_atif; rewrite H_atif in H_inst_uu; inversion H_inst_uu].

  intro H_inst_uu2.
  apply val_of_with_injection_in_simplified_oitenv with (l':=l0) (c2:=OITEnv_cons x (OIV td (OIV_ oid v)) c) in IHoival_of2; auto.
  apply Simplified_oitenv_cons.
  apply simplified_oitenv_refl.
  eapply Simplified_oitval_cons_simpl; auto.
  apply Simplified_oitval_refl.
  
  simpl in HHH_inst_uu; simpl.
  rewrite utils.match_option_bool_not_true in HHH_inst_uu; auto.
  rewrite utils.match_option_bool_not_true; auto.
  destruct (eq_label_dec l l0); auto.
  elim (n e0).


  (* case Constr0 *)
  simpl in H_inst_uu.
  inversion H_inst_uu.
  apply Val_of_with_injection_Constr0.

  (* case Constr1 *)
  simpl in H_inst_uu.
  assert(HH_inst_uu := H_inst_uu).
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  assert(HH_inst_u := is_instantiable_oival u l vl);
    inversion_clear HH_inst_u as [v H_inst_u];
    rewrite H_inst_u in H_inst_uu.
  simpl in H_inst_uu.
  inversion_clear H_inst_uu.
  apply Val_of_with_injection_Constr1.
  apply IHoival_of; auto.
  simpl.
  rewrite utils.match_option_bool_not_true; auto.
  intros HHH; rewrite HHH in HH_inst_uu; inversion HH_inst_uu.
  intros HHH; rewrite HHH in HH_inst_uu; inversion HH_inst_uu.

  (* case Couple *)
  simpl in H_inst_uu.
  assert(HH_inst_uu := H_inst_uu).
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  assert(HH_inst_u1 := is_instantiable_oival u1 l vl);
    inversion_clear HH_inst_u1 as [v1 H_inst_u1];
    rewrite H_inst_u1 in H_inst_uu.
  assert(HH_inst_u2 := is_instantiable_oival u2 l vl);
    inversion_clear HH_inst_u2 as [v2 H_inst_u2];
    rewrite H_inst_u2 in H_inst_uu.
  simpl in H_inst_uu; inversion H_inst_uu.
  apply Val_of_with_injection_Couple.

  apply IHoival_of1; auto.
  simpl.
  rewrite utils.match_option_bool_not_true; auto.
  apply not_loop_in_conc_oitdeps1 with (td':=td2).
  intros HHH; rewrite HHH in HH_inst_uu; inversion HH_inst_uu.

  apply IHoival_of2; auto.
  simpl.
  rewrite utils.match_option_bool_not_true; auto.
  apply not_loop_in_conc_oitdeps2 with (td:=td1).
  intros HHH; rewrite HHH in HH_inst_uu; inversion HH_inst_uu.

  intros HHH; rewrite HHH in HH_inst_uu; inversion HH_inst_uu.

  (* case Annot *)
  simpl in H_inst_uu.
  assert(HH_inst_uu := H_inst_uu).
  rewrite utils.match_option_bool_not_true in H_inst_uu.
  
  induction (eq_label_dec l l0) as [H_l_l0|].

  (* l = l0 *)
  inversion H_inst_uu.
  rewrite <- H1.
  rewrite H_l_l0.
  apply Val_of_with_injection_Annot_eq.

  (* l <> l0 *)
  apply Val_of_with_injection_Annot_neq; auto.
  
  intros HHH; rewrite HHH in HH_inst_uu; inversion HH_inst_uu.

Qed.




(**********************************)



Lemma val_of_with_injection_det :
  forall (l:label) (vl:val) (c:oitenv) (e:expr) (v v':val),
  val_of_with_injection l vl c e v
  -> val_of_with_injection l vl c e v'
  -> v = v'.
Proof.
  intros l vl c e v v' H_val_of H0.
  revert v' H0.
  induction H_val_of; intros v' H_val_of';
  inversion H_val_of'; auto.

  rewrite H in H2; inversion H2.
  rewrite H9 in H0; rewrite <-H0 in H6; inversion H6; auto.

  rewrite <-H in H6; inversion H6; auto.
  rewrite H10 in H8; rewrite <-H8 in H0; inversion H0; auto.

  rewrite <-H in H8; inversion H8; auto.
  rewrite H11 in H9; rewrite <-H9 in H0; inversion H0; auto.

  clear H2 H3 H4 H H0 H6.
  specialize (IHH_val_of1 _ H1); inversion IHH_val_of1.
  rewrite H0, H2, H3 in *; clear H0 H2 H3.
  specialize (IHH_val_of2 _ H5); inversion IHH_val_of2.
  rewrite H in *; clear H.
  specialize (IHH_val_of3 _ H7); inversion IHH_val_of3.
  auto.

  specialize (IHH_val_of1 _ H1); inversion IHH_val_of1.
  specialize (IHH_val_of1 _ H1); inversion IHH_val_of1.

  clear H2 H3 H4 H H0 H6.
  specialize (IHH_val_of1 _ H1); inversion IHH_val_of1.
  rewrite H0, H2, H3, H4 in *; clear H0 H2 H3 H4.
  specialize (IHH_val_of2 _ H5); inversion IHH_val_of2.
  rewrite H in *; clear H.
  specialize (IHH_val_of3 _ H7); inversion IHH_val_of3.
  auto.

  clear H1 H2 H3 H H0 H5 H4.
  specialize (IHH_val_of1 _ H6); inversion IHH_val_of1.
  rewrite H in *; clear H.
  specialize (IHH_val_of2 _ H7); inversion IHH_val_of2.
  auto.

  specialize (IHH_val_of1 _ H6); inversion IHH_val_of1.
  specialize (IHH_val_of1 _ H6); inversion IHH_val_of1.

  clear H0 H1 H2 H3 H4 H5 H6 H7.
  specialize (IHH_val_of1 _ H8); inversion IHH_val_of1.
  rewrite H0 in *; clear H0.
  rewrite H in H9; inversion H9.
  rewrite H1 in *; clear H1.
  specialize (IHH_val_of2 _ H10); inversion IHH_val_of2.
  auto.

  clear H0 H1 H2 H3 H4 H5 H6 H7.
  specialize (IHH_val_of1 _ H8); inversion IHH_val_of1.
  rewrite H0 in *; clear H0.
  rewrite H in H9; inversion H9.

  clear H0 H1 H2 H3 H4 H5 H6 H7.
  specialize (IHH_val_of1 _ H8); inversion IHH_val_of1.
  rewrite H0 in *; clear H0.
  rewrite H in H9; inversion H9.

  clear H0 H1 H2 H3 H4 H5 H6 H7.
  specialize (IHH_val_of1 _ H9); inversion IHH_val_of1.
  rewrite H0 in *; clear H8 H0.
  specialize (IHH_val_of2 _ H11); inversion IHH_val_of2.
  auto.

  specialize (IHH_val_of _ H5); inversion IHH_val_of.
  auto.

  specialize (IHH_val_of1 _ H4); inversion IHH_val_of1.
  specialize (IHH_val_of2 _ H6); inversion IHH_val_of2.
  auto.

  elim H6; auto.

  elim H; auto.
Qed.


Definition deps_spec_Apply_P (l:label) (vl:val) (uu2:oitval) (v2:val)
    (x_f:identifier) (c_f:env) (e_f:expr) (v':val) :=
  (instantiate_oitval l vl uu2 = Some v2
                /\ val_of_with_injection l vl (OITEnv_cons x_f (val_to_oitval v2) (env_to_oitenv c_f)) e_f v').

Lemma deps_spec_Apply_P_det :
  forall (l:label) (vl:val) (uu2:oitval) (v2 v2':val)
    (x_f:identifier) (c_f:env) (e_f:expr) (v' v'':val),
    deps_spec_Apply_P l vl uu2 v2 x_f c_f e_f v'
    -> deps_spec_Apply_P l vl uu2 v2' x_f c_f e_f v''
    -> (v2 = v2') /\ (v' = v'').
Proof.
  unfold deps_spec_Apply_P.
  intros l vl uu2 v2 v2' x_f c_f e_f v' v'' H H0.
  inversion_clear H as [H_uu2 H_val_of_e_f].
  inversion_clear H0 as [H_uu2' H_val_of_e_f'].
  rewrite H_uu2 in H_uu2'.
  inversion H_uu2'.
  rewrite <- H0 in H_val_of_e_f'.
  split; auto.

  apply (val_of_with_injection_det _ _ _ _ _ _ H_val_of_e_f H_val_of_e_f').
Qed.

Definition deps_spec_Apply_P_Rec (l:label) (vl:val) (uu2:oitval) (v2:val)
  (id_f:identifier) (x_f:identifier) (c_f:env) (e_f:expr) (v':val) :=
    (instantiate_oitval l vl uu2 = Some v2
                 /\ val_of_with_injection l vl (env_to_oitenv (add_env  id_f (V_Rec_Closure id_f x_f e_f c_f) (add_env x_f v2 c_f))) e_f v').

Lemma deps_spec_Apply_P_Rec_det :
  forall (l:label) (vl:val) (uu2:oitval) (v2 v2':val)
    (id_f:identifier) (x_f:identifier) (c_f:env) (e_f:expr) (v' v'':val),
    deps_spec_Apply_P_Rec l vl uu2 v2 id_f x_f c_f e_f v'
    -> deps_spec_Apply_P_Rec l vl uu2 v2' id_f x_f c_f e_f v''
    -> (v2 = v2') /\ (v' = v'').
Proof.
  unfold deps_spec_Apply_P_Rec.
  intros l vl uu2 v2 v2' id_f x_f c_f e_f v' v'' H H0.
  inversion_clear H as [H_uu2 H_val_of_e_f].
  inversion_clear H0 as [H_uu2' H_val_of_e_f'].
  rewrite H_uu2 in H_uu2'.
  inversion H_uu2'.
  rewrite <- H0 in H_val_of_e_f'.
  split; auto.

  apply (val_of_with_injection_det _ _ _ _ _ _ H_val_of_e_f H_val_of_e_f').
Qed.


Fixpoint remove_label_from_oitdeps (l:label) (td:oitdeps) :=
  match td with
    | nil => nil
    | cons (l',f) td' =>
      if eq_label_dec l l'
      then remove_label_from_oitdeps l td'
      else cons (l',f) (remove_label_from_oitdeps l td')
  end.

Lemma apply_timpact_fun_after_remove_label :
  forall (l:label) (vl:val) (td:oitdeps),
  apply_timpact_fun l vl (remove_label_from_oitdeps l td) = None.
Proof.
  induction td.
  simpl; reflexivity.

  simpl.
  destruct a as [l' f].
  induction (eq_label_dec l l').
  assumption.
  simpl.
  destruct (eq_label_dec l l').
  elim (b e).
  assumption.
Qed.

Lemma apply_timpact_fun_after_remove_other_label :
  forall (vl:val) (td:oitdeps) (l l':label),
    l <> l'
    -> apply_timpact_fun l vl (remove_label_from_oitdeps l' td) = apply_timpact_fun l vl td.
Proof.
  induction td.
  simpl; reflexivity.

  intros l l' H.
  destruct a as [l'' f].
  simpl.
  induction (eq_label_dec l' l'');
  destruct (eq_label_dec l l'').
  rewrite <- a in e; elim (H e).
  apply IHtd; assumption.

  simpl.
  destruct (eq_label_dec l l'').
  rewrite IHtd; [reflexivity | assumption].
  elim (n e).
  
  simpl.
  destruct (eq_label_dec l l'').
  elim (n e).

  auto.
Qed.


Require Import Logic.ChoiceFacts.
Axiom my_choice : forall A B, FunctionalChoice_on A B.

Definition deps_spec_Apply_funs_R (oitu2:oitval) (l:label) (f:val->val) (vl:val) (y:bool*val) :=
  (
    match f vl with
                  (* non recursive function *)
      | V_Closure x_f e_f c_f =>
        (forall v2 v' : val,
          instantiate_oitval l vl oitu2 = Some v2 ->
          val_of_with_injection l vl
          (OITEnv_cons x_f (val_to_oitval v2)
            (env_to_oitenv c_f)) e_f v' ->
          fst y = false /\ snd y = v') /\
        (~
          (exists v2 v' : val,
            instantiate_oitval l vl oitu2 = Some v2 /\
            val_of_with_injection l vl
            (OITEnv_cons x_f (val_to_oitval v2)
              (env_to_oitenv c_f)) e_f v') ->
          fst y = true /\ snd y = (V_Num 0))

                  (* recursive function *)
      | V_Rec_Closure id_f x_f e_f c_f =>
        (forall v2 v' : val,
          instantiate_oitval l vl oitu2 = Some v2 ->
          val_of_with_injection l vl
          (env_to_oitenv
            (add_env id_f
              (V_Rec_Closure id_f x_f e_f c_f)
              (add_env x_f v2 c_f))) e_f v' ->
          fst y = false /\ snd y = v') /\
        (~
          (exists v2 v' : val,
            instantiate_oitval l vl oitu2 = Some v2 /\
            val_of_with_injection l vl
            (env_to_oitenv
              (add_env id_f
                (V_Rec_Closure id_f x_f e_f c_f)
                (add_env x_f v2 c_f))) e_f v') ->
          fst y = true /\ snd y = (V_Num 0))

                  (* type error *)
      | _ => fst y = true /\ snd y = (V_Num 0)
    end
  ).

Lemma exists_deps_spec_Apply :
  forall (d1:oideps) (uu2:oitval),
    exists(td':oitdeps) (d':oideps),
      deps_spec_Apply uu2 d1 td' d'.
Proof.
  intros d1 uu2.
  induction d1.
  exists nil, nil.
  apply deps_spec_Apply_nil.

  induction a as [l f].
  inversion_clear IHd1 as [td' IHd1_].
  inversion_clear IHd1_ as [d' H_d1].

  assert(exists (tf'_f':val->bool*val),
     deps_spec_Apply uu2 ((l, f) :: d1)%list (cons (l,(fun v => fst (tf'_f' v))) td') (cons (l,fun v => snd (tf'_f' v)) d')).


  (* exists tf'_f' which satisfies deps_spec_Apply *)

  assert(exists tf'_f' : val -> bool * val,
           forall (vl : val),
             deps_spec_Apply_funs_R uu2 l f vl (tf'_f' vl)
        ).

  (** exists tf'_f' which satisfies deps_spec_Apply_funs_R *)

  apply my_choice.
  intros vl.

  unfold deps_spec_Apply_funs_R.
  destruct (f vl); try solve [exists (true, V_Num 0); auto].
                              
  destruct(excluded_middle (exists v2 v' : val,
                              instantiate_oitval l vl uu2 = Some v2 /\
                              val_of_with_injection l vl
                                                    (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c)) e v')).
  inversion H as [v2].
  inversion H0 as [v'].
  exists (false, v').
  split.
  intros v0 v'0 H7 H8.
  split; auto.
  simpl.
  inversion H1.
  rewrite H7 in H2; inversion H2.
  rewrite H5 in H8.
  apply (val_of_with_injection_det l vl (OITEnv_cons x (val_to_oitval v2) (env_to_oitenv c)) e); auto.
  intros H7.
  elim (H7 H).

  exists(true, V_Num 0).
  split.
  intros v0 v'0 H7 H8.
  elim H; exists v0, v'0; split; auto.
  intro; split; auto.

  destruct(excluded_middle (exists v2 v' : val,
         instantiate_oitval l vl uu2 = Some v2 /\
         val_of_with_injection l vl
           (env_to_oitenv
              (add_env f0 (V_Rec_Closure f0 x e c) (add_env x v2 c))) e v')).
  inversion H as [v2].
  inversion H0 as [v'].
  exists (false, v').
  split.
  intros v0 v'0 H7 H8.
  split; auto.
  simpl.
  inversion H1.
  rewrite H2 in H7; inversion H7.
  rewrite <-H5 in H8.
  apply (val_of_with_injection_det l vl (env_to_oitenv
              (add_env f0 (V_Rec_Closure f0 x e c) (add_env x v2 c))) e); auto.
  intros H7.
  elim (H7 H).

  exists(true, V_Num 0).
  split.
  intros v0 v'0 H7 H8.
  elim H; exists v0, v'0; split; auto.
  intro; split; auto.

  (* apply deps_spec_Apply_cons *)
  inversion_clear H as [tf'_f' HH].
  exists tf'_f'.
  apply deps_spec_Apply_cons.

  assumption.
  assumption.
  
  (* decomposing tf'_f' into tf' and f' *)
  inversion_clear H as [tf'_f'].
  exists (cons (l,fun v => fst (tf'_f' v)) td').
  exists (cons (l,fun v => snd (tf'_f' v)) d').
  assumption.
Qed.


Definition deps_spec_If_funs_R (c:oitenv) (e1 e2:expr) (l:label) (f:val->val) (vl:val) (y:bool*val) :=
  (
     match f vl with
       (* condition is true *)
       | V_Bool true =>
         (forall (v1:val),
            val_of_with_injection l vl c e1 v1
            -> (fst y = false /\ snd y = v1)
         ) /\ (
           ~(exists (v1:val), val_of_with_injection l vl c e1 v1)
           -> (fst y = true /\ snd y = (V_Num 0))
         )
       (* condition is false *)
       | V_Bool false =>
         (forall (v2:val),
            val_of_with_injection l vl c e2 v2
            -> (fst y = false /\ snd y = v2)
         ) /\ (
           ~(exists (v2:val), val_of_with_injection l vl c e2 v2)
           -> (fst y = true /\ snd y = (V_Num 0))
         )

       (* type error *)
       | _ => fst y = true /\ snd y = (V_Num 0)
     end
  ).

Lemma exists_deps_spec_If :
  forall (c:oitenv) (e1 e2:expr) (oid:oideps),
    exists(oitd':oitdeps) (oid':oideps),
      deps_spec_If c e1 e2 oid oitd' oid'.
Proof.
  intros c e1 e2 oid.
  induction oid.
  exists nil, nil.
  apply deps_spec_If_nil.

  induction a as [l f].
  inversion_clear IHoid as [td' IHoid_].
  inversion_clear IHoid_ as [d' H_oid].

  assert(exists (tf'_f':val->bool*val),
     deps_spec_If c e1 e2 ((l, f) :: oid)%list (cons (l,(fun v => fst (tf'_f' v))) td') (cons (l,fun v => snd (tf'_f' v)) d')).

  (* exists tf'_f' which satisfies deps_spec_If *)

  assert(exists tf'_f' : val -> bool * val,
           forall (vl : val),
             deps_spec_If_funs_R c e1 e2 l f vl (tf'_f' vl)
        ).

  (** exists tf'_f' which satisfies deps_spec_If_funs_R *)

  apply my_choice.
  intros vl.

  unfold deps_spec_If_funs_R.
  destruct (f vl); try solve [exists (true, V_Num 0); auto].
  destruct b.

  (*** case true *)
  destruct(excluded_middle (exists v1 : val, val_of_with_injection l vl c e1 v1)).
  inversion H as [v1].
  exists (false, v1).
  split.
  intros v0 H1.
  split; auto.
  simpl.
  apply (val_of_with_injection_det l vl c e1); auto.
  intros H1.
  elim (H1 H).

  exists(true, V_Num 0).
  split.
  intros v1 H0.
  elim H; exists v1; auto.
  intro; split; auto.

  (*** case false *)
  destruct(excluded_middle (exists v2 : val, val_of_with_injection l vl c e2 v2)).
  inversion H as [v2].
  exists (false, v2).
  split.
  intros v0 H1.
  split; auto.
  simpl.
  apply (val_of_with_injection_det l vl c e2); auto.
  intros H1.
  elim (H1 H).

  exists(true, V_Num 0).
  split.
  intros v2 H0.
  elim H; exists v2; auto.
  intro; split; auto.

  (* apply deps_spec_Apply_cons *)
  inversion_clear H as [tf'_f' HH].
  exists tf'_f'.
  apply deps_spec_If_cons.

  assumption.
  assumption.
  
  (* decomposing tf'_f' into tf' and f' *)
  inversion_clear H as [tf'_f'].
  exists (cons (l,fun v => fst (tf'_f' v)) td').
  exists (cons (l,fun v => snd (tf'_f' v)) d').
  assumption.
Qed.

Definition deps_spec_Match_funs_R (c:oitenv) (p:pattern) (x:identifier) (e1 e2:expr)
           (l:label) (f:val->val) (vl:val) (y:bool*val) :=
  (
     let v := f vl in
     match is_filtered v p with
       | Filtered_result_Match c_p =>
         (forall (v1:val),
            val_of_with_injection l vl (conc_oitenv (env_to_oitenv c_p) c) e1 v1
            -> (fst y = false /\ snd y = v1)
         ) /\ (
           ~(exists (v1:val), val_of_with_injection l vl (conc_oitenv (env_to_oitenv c_p) c) e1 v1)
           -> (fst y = true /\ snd y = (V_Num 0))
         )
       | Filtered_result_Match_var =>
         (forall (v2:val),
            val_of_with_injection l vl (OITEnv_cons x (val_to_oitval v) c) e2 v2
            -> (fst y = false /\ snd y = v2)
         ) /\ (
           ~(exists (v2:val), val_of_with_injection l vl (OITEnv_cons x (val_to_oitval v) c) e2 v2)
           -> (fst y = true /\ snd y = (V_Num 0))
         )
       | Filtered_result_Error => (fst y = true /\ snd y = (V_Num 0))
     end
  ).

Lemma exists_deps_spec_Match :
  forall (c:oitenv) (p:pattern) (x:identifier) (e1 e2:expr) (oid:oideps),
    exists(oitd':oitdeps) (oid':oideps),
      deps_spec_Match c p x e1 e2 oid oitd' oid'.
Proof.
  intros c p x e1 e2 oid.
  induction oid.
  exists nil, nil.
  apply deps_spec_Match_nil.

  induction a as [l f].
  inversion_clear IHoid as [td' IHoid_].
  inversion_clear IHoid_ as [d' H_oid].

  assert(exists (tf'_f':val->bool*val),
    deps_spec_Match c p x e1 e2 ((l, f) :: oid)%list ((l,fun v=>fst (tf'_f' v))::td')%list ((l,fun v=>snd (tf'_f' v))::d')%list).

  (* exists tf'_f' which satisfies deps_spec_Match *)

  assert(exists tf'_f' : val -> bool * val,
           forall (vl : val),
             deps_spec_Match_funs_R c p x e1 e2 l f vl (tf'_f' vl)
        ).

  (** exists tf'_f' which satisfies deps_spec_Match_funs_R *)

  apply my_choice.
  intros vl.

  unfold deps_spec_Match_funs_R.
  destruct (is_filtered (f vl) p) as [c_p| |]; try solve [exists (true, V_Num 0); auto].

  (*** case matches *)
  destruct(excluded_middle (exists v1 : val,
         val_of_with_injection l vl (conc_oitenv (env_to_oitenv c_p) c) e1 v1)).
  inversion_clear H as [v1].
  exists (false, v1).
  split.
  intros v0 H1.
  split; auto.
  simpl.
  apply (val_of_with_injection_det l vl (conc_oitenv (env_to_oitenv c_p) c) e1); auto.
  intros H1.
  elim H1.
  exists v1; auto.

  exists(true, V_Num 0).
  split.
  intros v1 H0.
  elim H; exists v1; auto.
  intro; split; auto.

  (*** case does not match *)
  destruct(excluded_middle (exists v2 : val,
         val_of_with_injection l vl (OITEnv_cons x (val_to_oitval (f vl)) c) e2 v2)).
  inversion H as [v2].
  exists (false, v2).
  split.
  intros v0 H1.
  split; auto.
  simpl.
  apply (val_of_with_injection_det l vl (OITEnv_cons x (val_to_oitval (f vl)) c) e2); auto.
  intros H1.
  elim H1;  exists v2; auto.

  exists(true, V_Num 0).
  split.
  intros v2 H0.
  elim H; exists v2; auto.
  intro; split; auto.

  (* apply deps_spec_Match_cons *)
  inversion_clear H as [tf'_f' HH].
  exists tf'_f'.
  apply deps_spec_Match_cons; auto.
  
  (* decomposing tf'_f' into tf' and f' *)
  inversion_clear H as [tf'_f'].
  exists (cons (l,fun v => fst (tf'_f' v)) td').
  exists (cons (l,fun v => snd (tf'_f' v)) d').
  assumption.
Qed.

