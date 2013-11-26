Add Rec LoadPath "." as DEP_AI.

Require utils.
Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import over_instrumented_values.
Require Import oitval_instantiation.
Require Import oitval_val_conversion.
Require Import oitval_val_conversion_facts.

Require Import injection_operational_semantics.
Require Import ldna_in.
Require Import ldna_in_facts.
Require Import proof_injection_op_sem.


Lemma commute_instantiate_oitenv_conc :
  forall (l:label) (vl:val) (c c':oitenv) (c_inst c'_inst:env),
  instantiate_oitenv l vl c = Some c_inst
  -> instantiate_oitenv l vl c' = Some c'_inst
  -> instantiate_oitenv l vl (conc_oitenv c c') = Some (conc_env c_inst c'_inst).
Proof.
  induction c; intros.
  inversion H.
  auto.

  simpl. simpl in H.
  unfold option_map2; unfold option_map2 in H.
  induction (instantiate_oitval l vl uu) as [v|]; try solve [inversion H].
  induction (instantiate_oitenv l vl c) as [c_inst0|]; try solve [inversion H].
  rewrite IHc with (c_inst:=c_inst0) (c'_inst:=c'_inst).
  inversion H.
  simpl.
  reflexivity.
  reflexivity.
  assumption.
Qed.

Lemma val_of_with_injection_in_instantiated_oitenv :
  forall (l:label) (vl:val) (c:oitenv) (e:expr) (v:val) (c':env),
  val_of_with_injection l vl c e v
  -> instantiate_oitenv l vl c = Some c'
  -> val_of_with_injection l vl (env_to_oitenv c') e v.
Proof.
  intros l vl c e v c' H H0.
  revert c' H0.
  induction H; intros c_inst H_inst_c; eauto with val_of_with_injection.

  apply Val_of_with_injection_Ident with (uu:=val_to_oitval v).
  induction assoc_ident_in_oitenv_env_to_oitenv_instantiate_oitenv with (i:=i) (c:=c) (c':=c_inst) (uu:=uu) (l:=l) (vl:=vl).
  inversion_clear H1.
  rewrite <- H3 in H0.
  inversion H0.
  assumption.
  assumption.
  auto.
  simpl.
  apply val_to_oival_instantiate.

  apply Val_of_with_injection_Lambda with (c':=c_inst).
  apply env_to_oitenv_instantiate.
  rewrite H_inst_c in H; inversion H.
  rewrite <- H2.
  assumption.

  apply Val_of_with_injection_Rec with (c':=c_inst).
  apply env_to_oitenv_instantiate.
  rewrite H_inst_c in H; inversion H.
  rewrite <- H2.
  assumption.

  apply Val_of_with_injection_Let_in with (v1:=v1); auto.
  replace (OITEnv_cons i (val_to_oitval v1) (env_to_oitenv c_inst)) with (env_to_oitenv (Env_cons i v1 c_inst)); auto.
  apply IHval_of_with_injection2.
  simpl.
  rewrite H_inst_c.
  rewrite <- val_to_oival_instantiate.
  unfold option_map2.
  reflexivity.

  apply Val_of_with_injection_Match with (c_p:=c_p) (v_e:=v_e); auto.
  rewrite commute_conc_env_to_oitenv.
  apply IHval_of_with_injection2.
  apply commute_instantiate_oitenv_conc.
  rewrite env_to_oitenv_instantiate with (l:=l) (vl:=vl); reflexivity.
  assumption.
  
  apply Val_of_with_injection_Match_var with (v_e:=v_e); auto.
  replace (OITEnv_cons x (val_to_oitval v_e) (env_to_oitenv c_inst)) with (env_to_oitenv (Env_cons x v_e c_inst)); auto.
  apply IHval_of_with_injection2.
  simpl.
  rewrite H_inst_c.
  unfold option_map2.
  rewrite <- val_to_oival_instantiate.
  reflexivity.
Qed.

(* TODO: déplacer vers un endroit approprié *)

(* express that c2 is a partial instantiation of c1 *)
Inductive partially_instantiated_oitenv : label -> val -> oitenv -> oitenv -> Prop :=
| Partially_instantiated_oitenv_empty :
    forall (l:label) (vl:val),
      partially_instantiated_oitenv l vl OITEnv_empty OITEnv_empty
| Partially_instantiated_oitenv_cons :
    forall (l:label) (vl:val) (c1 c2:oitenv) (x:identifier) (uu:oitval),
      partially_instantiated_oitenv l vl c1 c2
      -> partially_instantiated_oitenv l vl (OITEnv_cons x uu c1) (OITEnv_cons x uu c2)
| Partially_instantiated_oitenv_cons_inst :
    forall (l:label) (vl:val) (c1 c2:oitenv) (x:identifier) (uu1 uu2:oitval) (v1:val),
      partially_instantiated_oitenv l vl c1 c2
      -> instantiate_oitval l vl uu1 = Some v1
      -> uu2 = val_to_oitval v1
      -> partially_instantiated_oitenv l vl (OITEnv_cons x uu1 c1) (OITEnv_cons x uu2 c2).
    
Lemma partially_instantiated_oitenv_conc :
  forall (l:label) (vl:val) (c1 c2 c:oitenv),
  partially_instantiated_oitenv l vl c1 c2
  -> partially_instantiated_oitenv l vl (conc_oitenv c c1) (conc_oitenv c c2).
Proof.
  intros l vl c1 c2 c H.
  induction c.
  auto.
  simpl.
  apply Partially_instantiated_oitenv_cons; assumption.
Qed.

Lemma partially_instantiated_oitenv_refl :
  forall (l:label) (vl:val) (c:oitenv),
    partially_instantiated_oitenv l vl c c.
Proof.
  intros l vl c.
  induction c.
  apply Partially_instantiated_oitenv_empty.
  apply Partially_instantiated_oitenv_cons.
  assumption.
Qed.

Lemma instantiate_partially_instantiated_oitenv :
  forall (l:label) (vl:val) (c1 c2:oitenv),
    partially_instantiated_oitenv l vl c1 c2
    -> instantiate_oitenv l vl c2 = instantiate_oitenv l vl c1.
Proof.
  intros l vl c1 c2 H.
  induction H.
  reflexivity.
  simpl.  
  rewrite IHpartially_instantiated_oitenv.
  reflexivity.
  simpl.
  rewrite H1.
  simpl.
  rewrite <- val_to_oival_instantiate.
  rewrite IHpartially_instantiated_oitenv.
  rewrite H0.
  reflexivity.
Qed.

Lemma assoc_in_partially_instantiated_oitenv :
  forall (l:label) (vl:val) (c1 c2:oitenv) (i:identifier) (uu:oitval) (v:val),
  assoc_ident_in_oitenv i c1 = Ident_in_oitenv uu
  -> Some v = instantiate_oitval l vl uu
  -> partially_instantiated_oitenv l vl c1 c2
  -> (assoc_ident_in_oitenv i c2 = Ident_in_oitenv uu
     \/ assoc_ident_in_oitenv i c2 = Ident_in_oitenv (val_to_oitval v)).
Proof.
  intros l vl c1 c2 i uu v H H_inst_uu H_c1_c2.
  
  induction H_c1_c2.
  inversion H.

  simpl; simpl in H.
  induction (beq_identifier i x); auto.

  simpl; simpl in H.
  induction (beq_identifier i x); auto.
  right.
  f_equal.
  inversion H.
  rewrite H3 in H0; rewrite H0 in H_inst_uu; inversion H_inst_uu.
  assumption.
Qed.

Lemma val_of_with_injection_in_partially_instantiated_oitenv :
  forall (l:label) (vl:val) (c1 c2:oitenv) (e:expr) (v:val),
    val_of_with_injection l vl c1 e v
    -> partially_instantiated_oitenv l vl c1 c2
    -> val_of_with_injection l vl c2 e v.
Proof.
  intros l vl c1 c2 e v H H_c1_c2.
  revert c2 H_c1_c2.
  induction H; intros c2 H_c1_c2; eauto with val_of_with_injection.

  (* case Ident *)
  assert(HH:= assoc_in_partially_instantiated_oitenv l vl c c2 i uu v H H0 H_c1_c2).
  inversion HH.
  apply Val_of_with_injection_Ident with (uu:=uu); assumption.
  apply Val_of_with_injection_Ident with (uu:=val_to_oitval v).
  assumption.
  apply val_to_oival_instantiate.

  (* case Lambda *)
  apply Val_of_with_injection_Lambda with (c':=c'); auto.
  rewrite instantiate_partially_instantiated_oitenv with (c1:=c); assumption.

  (* case Rec *)
  apply Val_of_with_injection_Rec with (c':=c'); auto.
  rewrite instantiate_partially_instantiated_oitenv with (c1:=c); assumption.

  (* case Let_in *)
  apply Val_of_with_injection_Let_in with (v1:=v1); auto.
  apply IHval_of_with_injection2.
  apply Partially_instantiated_oitenv_cons; assumption.

  (* case Match *)
  apply Val_of_with_injection_Match with (c_p:=c_p) (v_e:=v_e); auto.
  apply IHval_of_with_injection2.
  apply partially_instantiated_oitenv_conc; assumption.

  (* case Match_var *)
  apply Val_of_with_injection_Match_var with (v_e:=v_e); auto.
  apply IHval_of_with_injection2.
  apply Partially_instantiated_oitenv_cons; assumption.
Qed.


(* TODO: rename simplified_oitval in stripped_label_in_oideps_of_oitval *)
Inductive simplified_oitval : label -> oitval -> oitval -> Prop :=
| Simplified_oitval_refl :
    forall (l:label) (uu:oitval),
      simplified_oitval l uu uu
| Simplified_oitval_cons_simpl :
    forall (l:label) (uu1 uu2 uu1':oitval) (td1 td2:oitdeps) (d1 d2:oideps) (v1 v2:oival0)
           (f:val->val),
    simplified_oitval l uu1 uu2
    -> uu1 = OIV td1 (OIV_ d1 v1)
    -> uu2 = OIV td2 (OIV_ d2 v2)
    -> uu1' = OIV td1 (OIV_ (cons (l,f) d1) v1)
    -> simplified_oitval l uu1' uu2.


(* express that c2 is some kind of simplified version of c1:
 the values in c2 are the same as in c1 eventually without l in top of their d *)
Inductive simplified_oitenv : label -> oitenv -> oitenv -> Prop :=
| Simplified_oitenv_empty :
    forall (l:label),
      simplified_oitenv l OITEnv_empty OITEnv_empty
| Simplified_oitenv_cons :
    forall (l:label) (c1 c2:oitenv) (x:identifier) (uu1 uu2:oitval),
      simplified_oitenv l c1 c2
      -> simplified_oitval l uu1 uu2
      -> simplified_oitenv l (OITEnv_cons x uu1 c1) (OITEnv_cons x uu2 c2).
    
Lemma simplified_oitenv_refl :
  forall (l:label) (c:oitenv),
    simplified_oitenv l c c.
Proof.
  intros l c.
  induction c.
  apply Simplified_oitenv_empty.
  apply Simplified_oitenv_cons.
  assumption.
  apply Simplified_oitval_refl.
Qed.

Lemma assoc_in_simplified_oitenv :
  forall (c1 c2:oitenv) (i:identifier) (uu1:oitval) (l:label),
  assoc_ident_in_oitenv i c1 = Ident_in_oitenv uu1
  -> simplified_oitenv l c1 c2
  -> exists (uu2:oitval),
       (assoc_ident_in_oitenv i c2 = Ident_in_oitenv uu2
        /\ simplified_oitval l uu1 uu2).
Proof.
  intros c1 c2 i uu1 l H_assoc_in_c1 H_c1_c2.

  induction H_c1_c2.

  inversion H_assoc_in_c1.

  simpl in H_assoc_in_c1; simpl.
  induction (beq_identifier i x); auto.

  exists uu2.
  inversion H_assoc_in_c1; rewrite H1 in H.
  split; auto.
Qed.

Lemma instantiate_simplified_oitval :
  forall (l:label) (vl:val) (l':label) (uu1 uu2:oitval),
    simplified_oitval l' uu1 uu2
    -> l <> l'
    -> instantiate_oitval l vl uu1 = instantiate_oitval l vl uu2.
Proof.
  intros l vl l' uu1 uu2 H H_l_l'.
  induction H; auto.

  rewrite <-IHsimplified_oitval, H0, H2; auto.
  simpl.
  destruct (eq_label_dec l l0); auto.
  elim (H_l_l' e).
Qed.

Lemma instantiate_simplified_oitenv :
  forall (l:label) (vl:val) (l':label) (c1 c2:oitenv),
    simplified_oitenv l' c1 c2
    -> l <> l'
    -> instantiate_oitenv l vl c2 = instantiate_oitenv l vl c1.
Proof.
  intros l vl l' c1 c2 H H_l_l'.
  induction H; auto.
  simpl.  
  rewrite IHsimplified_oitenv; auto.
  rewrite (instantiate_simplified_oitval _ _ _ _ _ H0); auto.
Qed.

Lemma simplified_oitenv_conc :
  forall (l:label) (c c1 c2:oitenv),
    simplified_oitenv l c1 c2
    -> simplified_oitenv l (conc_oitenv c c1) (conc_oitenv c c2).
Proof.
  intros l c c1 c2 H.
  induction c; auto.
  simpl.
  apply Simplified_oitenv_cons; auto.  
  apply Simplified_oitval_refl.
Qed.


Lemma val_of_with_injection_in_simplified_oitenv :
  forall (l:label) (vl:val) (l':label) (c1 c2:oitenv) (e:expr) (v:val),
    val_of_with_injection l vl c1 e v
    -> l <> l'
    -> simplified_oitenv l' c1 c2
    -> val_of_with_injection l vl c2 e v.
Proof.
  intros l vl l' c1 c2 e v H H_l_l' H_c1_c2.
  revert c2 H_c1_c2.
  induction H; intros c2 H_c1_c2; eauto with val_of_with_injection.

  (* case Ident *)
  destruct (assoc_in_simplified_oitenv _ _ _ _ _ H H_c1_c2) as [uu2 HH].
  inversion_clear HH as [H_assoc_c2 H_simpl].
  apply Val_of_with_injection_Ident with (uu:=uu2); auto.
  rewrite <-instantiate_simplified_oitval with (l':=l') (uu1:=uu); auto.

  (* case Lambda *)
  apply Val_of_with_injection_Lambda with (c':=c'); auto.
  rewrite instantiate_simplified_oitenv with (c1:=c) (l':=l'); assumption.

  (* case Rec *)
  apply Val_of_with_injection_Rec with (c':=c'); auto.
  rewrite instantiate_simplified_oitenv with (c1:=c) (l':=l'); assumption.

  (* case Let_in *)
  apply Val_of_with_injection_Let_in with (v1:=v1); auto.
  apply IHval_of_with_injection2; auto.
  apply Simplified_oitenv_cons; auto.
  apply Simplified_oitval_refl.

  (* case Match *)
  apply Val_of_with_injection_Match with (c_p:=c_p) (v_e:=v_e); auto.
  apply IHval_of_with_injection2; auto.
  apply simplified_oitenv_conc; assumption.

  (* case Match_var *)
  apply Val_of_with_injection_Match_var with (v_e:=v_e); auto.
  apply IHval_of_with_injection2; auto.
  apply Simplified_oitenv_cons; auto.
  apply Simplified_oitval_refl.
Qed.


(*****************************************************************************)
(*
   Definition of the over-instrumented semantics
   which evaluates an expression in an over-instrumented environment
   and returns an over-instrumented value.
   *)
(*****************************************************************************)

Lemma apply_timpact_fun_in_conc_oitdeps_1 :
  forall (td td':oitdeps) (l:label) (vl:val),
    apply_timpact_fun l vl td = Some true
    -> apply_timpact_fun l vl (conc_oitdeps td td') = Some true.
Proof.
  induction td.

  intros td' l vl H.
  inversion H.

  intros td' l vl H.
  induction a as [l' bb].
  simpl in  H.
  simpl.
  induction (eq_label_dec l l').
  assert(IHHtd := IHtd td' l vl).
  induction (apply_timpact_fun l vl td).
  induction a0.
  rewrite (IHHtd eq_refl).
  f_equal; induction (bb vl); auto.
  induction (bb vl).
  induction (apply_timpact_fun l vl (conc_oitdeps td td')).
  f_equal; induction (bb vl); auto.
  reflexivity.
  inversion H.
  inversion H.
  rewrite H1.
  induction (apply_timpact_fun l vl (conc_oitdeps td td')).
  f_equal; induction (bb vl); auto.
  reflexivity.
  apply IHtd; assumption.
Qed.

Lemma apply_timpact_fun_in_conc_oitdeps_2 :
  forall (td td':oitdeps) (l:label) (vl:val),
    apply_timpact_fun l vl td' = Some true
    -> apply_timpact_fun l vl (conc_oitdeps td td') = Some true.
Proof.
  induction td.
  auto.
  intros td' l vl H.
  induction a as [l' bb].
  simpl.
  induction (eq_label_dec l l').
  rewrite(IHtd td' l vl).
  f_equal.
  induction (bb vl); auto.
  assumption.
  apply IHtd; assumption.
Qed.

Lemma apply_impact_fun_conc_oideps :
  forall (l:label) (vl v:val) (d d':oideps),
    apply_impact_fun l vl d = Some v
    -> apply_impact_fun l vl (conc_oideps d d') = Some v.
Proof.
  induction d.
  intros d' H.
  inversion H.
  intros d' H.
  induction a as [l' f].
  simpl in H.
  simpl.
  induction (eq_label_dec l l').
  assumption.
  apply IHd; assumption.
Qed.

Lemma apply_impact_fun_conc_oideps_none_1 :
  forall (l:label) (vl:val) (d d':oideps),
    apply_impact_fun l vl (conc_oideps d d') = None
    -> apply_impact_fun l vl d = None.
Proof.
  intros l vl d d' H.
  induction d.
  simpl; reflexivity.
  simpl.
  induction a as [l' f].
  simpl in H.
  induction (eq_label_dec l l').
  inversion H.
  apply (IHd H).
Qed.

Lemma apply_impact_fun_conc_oideps_rev_none :
  forall (l:label) (vl:val) (d d':oideps),
    apply_impact_fun l vl d = None
    -> apply_impact_fun l vl (conc_oideps d d') = apply_impact_fun l vl d'.
Proof.
  intros l vl d d' H.
  induction d.
  simpl; reflexivity.
  simpl.
  induction a as [l' f].
  simpl in H.
  induction (eq_label_dec l l').
  inversion H.
  apply (IHd H).
Qed.

(*
TODO: il faut modifier la notion de fonction d'impact

Dans les 3 prédicats deps_spec_..., on utilise une valeur arbitraire (V_Num 0).
Si on modifie le langage (par exemple, en ajoutant une construction pour l'addition d'entiers),
 la preuve ne tiendra plus car deps_spec_..._in_partially_approximated ne sera plus prouvable.
Il faudrait que les fonctions dans les oideps ne soient pas val->val mais val->option(val).
Et on remplacerait ici (f' vl = V_Num 0) par (f' vl = None).

Cette modification nécessiterait une propriété de bonne formation sur les valeurs pour garantir que
 si on a une valeur [oitd|oiu]
 et que apply_timpact_fun l vl oitd <> Some true
 alors oiu est instantiable.

Il faudra montrer que toute valeur issue d'une évaluation satisfait cette propriété de bonne formation :
Lemma well_formed_oitval :
 oival_of c e (OIV oitd oiu)
 -> apply_timpact_fun l vl oitd <> Some true
 -> is_instantiable_oival oiu.
 
*)

Definition deps_spec_Apply_funs (oitu2:oitval) (l:label) (f:val->val) (tf':val->bool) (f':val->val) :=
  (forall (vl:val),
    match f vl with
      (* non recursive function *)
      | V_Closure x_f e_f c_f =>
        (forall v2 v' : val,
          instantiate_oitval l vl oitu2 = Some v2 ->
          val_of_with_injection l vl
          (OITEnv_cons x_f (val_to_oitval v2)
            (env_to_oitenv c_f)) e_f v' ->
          tf' vl = false /\ f' vl = v') /\
        (~
          (exists v2 v' : val,
            instantiate_oitval l vl oitu2 = Some v2 /\
            val_of_with_injection l vl
            (OITEnv_cons x_f (val_to_oitval v2)
              (env_to_oitenv c_f)) e_f v') ->
          tf' vl = true /\ f' vl = (V_Num 0))

      (* recursive function *)
      | V_Rec_Closure id_f x_f e_f c_f =>
        (forall v2 v' : val,
          instantiate_oitval l vl oitu2 = Some v2 ->
          val_of_with_injection l vl
          (env_to_oitenv
            (add_env id_f
              (V_Rec_Closure id_f x_f e_f c_f)
              (add_env x_f v2 c_f))) e_f v' ->
          tf' vl = false /\ f' vl = v') /\
        (~
          (exists v2 v' : val,
            instantiate_oitval l vl oitu2 = Some v2 /\
            val_of_with_injection l vl
            (env_to_oitenv
              (add_env id_f
                (V_Rec_Closure id_f x_f e_f c_f)
                (add_env x_f v2 c_f))) e_f v') ->
          tf' vl = true /\ f' vl = (V_Num 0))

      (* type error *)
      | _ => tf' vl = true /\ f' vl = (V_Num 0)
    end
  ).


Inductive deps_spec_Apply : oitval -> oideps -> oitdeps -> oideps -> Prop :=
| deps_spec_Apply_nil :
  forall (oitu2:oitval),
    deps_spec_Apply oitu2 nil nil nil
| deps_spec_Apply_cons :
  forall (oitd':oitdeps) (oid1 oid':oideps) (oitu2:oitval)
    (l:label) (tf':val->bool) (f f':val->val),
    deps_spec_Apply oitu2 oid1 oitd' oid'
    -> deps_spec_Apply_funs oitu2 l f tf' f'
    -> deps_spec_Apply oitu2 (cons (l,f) oid1) (cons (l,tf') oitd') (cons (l,f') oid').

Definition deps_spec_If_funs (c:oitenv) (e1 e2:expr) (l:label) (f:val->val) (tf':val->bool) (f':val->val) :=
  (forall (vl:val),
     match f vl with
       (* condition is true *)
       | V_Bool true =>
         (forall (v1:val),
            val_of_with_injection l vl c e1 v1
            -> (tf' vl = false /\ f' vl = v1)
         ) /\ (
           ~(exists (v1:val), val_of_with_injection l vl c e1 v1)
           -> (tf' vl = true /\ f' vl = (V_Num 0))
         )
       (* condition is false *)
       | V_Bool false =>
         (forall (v2:val),
            val_of_with_injection l vl c e2 v2
            -> (tf' vl = false /\ f' vl = v2)
         ) /\ (
           ~(exists (v2:val), val_of_with_injection l vl c e2 v2)
           -> (tf' vl = true /\ f' vl = (V_Num 0))
         )

       (* type error *)
       | _ => tf' vl = true /\ f' vl = (V_Num 0)
     end
  ).

Inductive deps_spec_If : oitenv -> expr -> expr -> oideps -> oitdeps -> oideps -> Prop :=
| deps_spec_If_nil :
  forall (c:oitenv) (e1 e2:expr),
    deps_spec_If c e1 e2 nil nil nil
| deps_spec_If_cons :
  forall (c:oitenv) (e1 e2:expr) (oid:oideps) (oitd':oitdeps) (oid':oideps)
    (l:label) (tf':val->bool) (f f':val->val),
    deps_spec_If c e1 e2 oid oitd' oid'
    -> deps_spec_If_funs c e1 e2 l f tf' f'
    -> deps_spec_If c e1 e2 (cons (l,f) oid) (cons (l,tf') oitd') (cons (l,f') oid').

Definition deps_spec_Match_funs (c:oitenv) (p:pattern) (x:identifier) (e1 e2:expr)
           (l:label) (f:val->val) (tf':val->bool) (f':val->val) :=
  (forall (vl:val),
     let v := f vl in
     match is_filtered v p with
       | Filtered_result_Match c_p =>
         (forall (v1:val),
            val_of_with_injection l vl (conc_oitenv (env_to_oitenv c_p) c) e1 v1
            -> (tf' vl = false /\ f' vl = v1)
         ) /\ (
           ~(exists (v1:val), val_of_with_injection l vl (conc_oitenv (env_to_oitenv c_p) c) e1 v1)
           -> (tf' vl = true /\ f' vl = (V_Num 0))
         )
       | Filtered_result_Match_var =>
         (forall (v2:val),
            val_of_with_injection l vl (OITEnv_cons x (val_to_oitval v) c) e2 v2
            -> (tf' vl = false /\ f' vl = v2)
         ) /\ (
           ~(exists (v2:val), val_of_with_injection l vl (OITEnv_cons x (val_to_oitval v) c) e2 v2)
           -> (tf' vl = true /\ f' vl = (V_Num 0))
         )
       | Filtered_result_Error => (tf' vl = true /\ f' vl = (V_Num 0))
     end
  ).

Inductive deps_spec_Match : oitenv -> pattern -> identifier -> expr -> expr
                            -> oideps -> oitdeps -> oideps -> Prop :=
| deps_spec_Match_nil :
  forall (c:oitenv) (p:pattern) (x:identifier) (e1 e2:expr),
    deps_spec_Match c p x e1 e2 nil nil nil
| deps_spec_Match_cons :
  forall (c:oitenv) (p:pattern) (x:identifier) (e1 e2:expr) (oid:oideps) (oitd':oitdeps) (oid':oideps)
    (l:label) (tf':val->bool) (f f':val->val),
    deps_spec_Match c p x e1 e2 oid oitd' oid'
    -> deps_spec_Match_funs c p x e1 e2 l f tf' f'
    -> deps_spec_Match c p x e1 e2 (cons (l,f) oid) (cons (l,tf') oitd') (cons (l,f') oid').

Definition is_filtered_oitval (uu:oitval) (p:pattern) : filtered_oitval_result :=
  match uu, p with
    | OIV _ (OIV_ _ (OIV_Constr0 n)), P_Constr0 n' =>
      if eq_nat_dec n n'
      then Filtered_oitval_result_Match OITEnv_empty
      else Filtered_oitval_result_Match_var
    | OIV _ (OIV_ _ (OIV_Constr0 _)), _ => Filtered_oitval_result_Match_var

    | OIV _ (OIV_ _ (OIV_Constr1 n u)), P_Constr1 n' x =>
      if eq_nat_dec n n'
      then Filtered_oitval_result_Match (OITEnv_cons x (OIV nil u) OITEnv_empty)
      else Filtered_oitval_result_Match_var
    | OIV _ (OIV_ _ (OIV_Constr1 _ _)), _ => Filtered_oitval_result_Match_var

    | OIV _ (OIV_ _ (OIV_Couple u1 u2)), P_Couple x1 x2 =>
      Filtered_oitval_result_Match (OITEnv_cons x1 (OIV nil u1) (OITEnv_cons x2 (OIV nil u2) OITEnv_empty))
    | OIV _ (OIV_ _ (OIV_Couple _ _)), _ => Filtered_oitval_result_Match_var

    | _,_ => Filtered_oitval_result_Error
  end.

Inductive oival_of : oitenv -> expr -> oitval -> Prop :=
| OIVal_of_Num :
  forall (v:Z) (c:oitenv),
    oival_of c (Num v) (OIV nil (OIV_ nil (OIV_Num v)))
| OIVal_of_Ident :
  forall (c:oitenv) (x:identifier) (uu:oitval),
    assoc_ident_in_oitenv x c = Ident_in_oitenv uu
    -> oival_of c (Var x) uu
| OIVal_of_Lambda :
  forall (c:oitenv) (x:identifier) (e:expr) (uu:oitval),
    uu = OIV nil (OIV_ nil (OIV_Closure x e (oitenv_to_oienv c)))
    -> oival_of c (Lambda x e) uu
| OIVal_of_Rec :
  forall (c:oitenv) (f x:identifier) (e:expr) (uu:oitval),
    uu = OIV nil (OIV_ nil (OIV_Rec_Closure f x e (oitenv_to_oienv c)))
    -> oival_of c (Rec f x e) uu

| OIVal_of_Apply :
  forall (c:oitenv) (c1:oienv) (e1 e2 e : expr) (x : identifier)
    (uu2 uu:oitval) (u2:oival) (d d' d1:oideps) (td1 td2 td td':oitdeps) (v:oival0),
(* construction de la valeur *)
    oival_of c e1 (OIV td1 (OIV_ d1 (OIV_Closure x e c1)))
    -> oival_of c e2 uu2
    -> uu2 = OIV td2 u2
    -> oival_of (OITEnv_cons x uu2 (oienv_to_oitenv c1)) e (OIV td (OIV_ d v))
(* construction des dépendances *)
(** spécification de td' et de d' *)
    -> deps_spec_Apply uu2 d1 td' d'
(* résultat de l'application *)
    -> uu = OIV (conc_oitdeps td1 (conc_oitdeps td2 (conc_oitdeps td td'))) (OIV_ (conc_oideps d' d) v)
    -> oival_of c (Apply e1 e2) uu

| OIVal_of_Apply_Rec :
  forall (c:oitenv) (c1:oienv) (e1 e2 e : expr) (f x:identifier)
    (uu1 uu2 uu:oitval) (u2:oival) (d d' d1:oideps) (td1 td2 td td':oitdeps) (v:oival0),
(* construction de la valeur *)
    oival_of c e1 uu1
    -> uu1 = (OIV td1 (OIV_ d1 (OIV_Rec_Closure f x e c1)))
    -> oival_of c e2 uu2
    -> oival_of (OITEnv_cons f uu1 (OITEnv_cons x uu2 (oienv_to_oitenv c1))) e (OIV td (OIV_ d v))
    -> uu2 = OIV td2 u2
(* construction des dépendances *)
(** spécification de td' et de d' *)
    -> deps_spec_Apply uu2 d1 td' d'
(* résultat de l'application *)
    -> uu = OIV (conc_oitdeps td1 (conc_oitdeps td2 (conc_oitdeps td td'))) (OIV_ (conc_oideps d' d) v)
    -> oival_of c (Apply e1 e2) uu

| OIVal_of_Let_in :
  forall (c:oitenv) (x:identifier) (e1 e2:expr) (uu1 uu2:oitval) (td1 td2:oitdeps) (u1 u2:oival),
    oival_of c e1 uu1
    -> uu1 = (OIV td1 u1)
    -> oival_of (OITEnv_cons x uu1 c) e2 uu2
    -> uu2 = (OIV td2 u2)
    -> oival_of c (Let_in x e1 e2) (OIV (conc_oitdeps td1 td2) u2)

| OIVal_of_If_true :
  forall (c:oitenv) (e e1 e2:expr) (td td1 td':oitdeps) (d d1 d':oideps) (uu1:oitval) (v1:oival0),
    oival_of c e (OIV td (OIV_ d (OIV_Bool true)))
    -> oival_of c e1 uu1
    -> uu1 = (OIV td1 (OIV_ d1 v1))
    (* specification of td' and d' *)
    -> deps_spec_If c e1 e2 d td' d'
    -> oival_of c (If e e1 e2) (OIV (conc_oitdeps td' (conc_oitdeps td td1)) (OIV_ (conc_oideps d' d1) v1))

| OIVal_of_If_false :
  forall (c:oitenv) (e e1 e2:expr) (td td2 td':oitdeps) (d d2 d':oideps) (uu2:oitval) (v2:oival0),
    oival_of c e (OIV td (OIV_ d (OIV_Bool false)))
    -> oival_of c e2 uu2
    -> uu2 = (OIV td2 (OIV_ d2 v2))
    (* specification of td' and d' *)
    -> deps_spec_If c e1 e2 d td' d'
    -> oival_of c (If e e1 e2) (OIV (conc_oitdeps td' (conc_oitdeps td td2)) (OIV_ (conc_oideps d' d2) v2))

| OIVal_of_Match : 
  forall (c c_p:oitenv) (e e1 e2: expr) (p:pattern) (x:identifier) (uu uu1:oitval) (td td1 td':oitdeps) (d d1 d':oideps) (v v1:oival0),
    oival_of c e uu
    -> uu = (OIV td (OIV_ d v))
    -> is_filtered_oitval uu p = Filtered_oitval_result_Match c_p
    -> oival_of (conc_oitenv c_p c) e1 uu1
    -> uu1 = (OIV td1 (OIV_ d1 v1))
    (* specification of td' and d' *)
    -> deps_spec_Match c p x e1 e2 d td' d'
    -> oival_of c (Expr_match e (p,e1) (Some (x,e2))) (OIV (conc_oitdeps td' (conc_oitdeps td td1)) (OIV_ (conc_oideps d' d1) v1))
(* TODO: il manque le cas de l'évaluation de (Expr_match e (p,e1) None), la match à une branche !!! *)

| OIVal_of_Match_var : 
  forall (c:oitenv) (e e1 e2: expr) (p:pattern) (x:identifier) (uu uu2:oitval) (td td2 td':oitdeps) (d d2 d':oideps) (v v2:oival0),
    oival_of c e uu
    -> uu = (OIV td (OIV_ d v))
    -> is_filtered_oitval uu p = Filtered_oitval_result_Match_var
    -> oival_of (OITEnv_cons x uu c) e2 uu2
    -> uu2 = (OIV td2 (OIV_ d2 v2))
    (* specification of td' and d' *)
    -> deps_spec_Match c p x e1 e2 d td' d'
    -> oival_of c (Expr_match e (p,e1) (Some (x,e2))) (OIV (conc_oitdeps td' (conc_oitdeps td td2)) (OIV_ (conc_oideps d' d2) v2))

| OIVal_of_Constr0 :
  forall (c:oitenv) (n:constr),
    oival_of c (Constr0 n) (OIV nil (OIV_ nil (OIV_Constr0 n)))

| OIVal_of_Constr1 :
  forall (c:oitenv) (n:constr) (e:expr) (td:oitdeps) (u:oival),
    oival_of c e (OIV td u)
    -> oival_of c (Constr1 n e) (OIV td (OIV_ nil (OIV_Constr1 n u)))
    
| OIVal_of_Couple :
  forall (c:oitenv) (e1 e2:expr) (td1 td2:oitdeps) (u1 u2:oival),
    oival_of c e1 (OIV td1 u1)
    -> oival_of c e2 (OIV td2 u2)
    -> oival_of c (Couple e1 e2) (OIV (conc_oitdeps td1 td2) (OIV_ nil (OIV_Couple u1 u2)))

| OIVal_of_Annot :
  forall (c:oitenv) (l:label) (e:expr) (td:oitdeps) (d:oideps) (v:oival0),
    oival_of c e (OIV td (OIV_ d v))
    -> oival_of c (Annot l e) (OIV td (OIV_ (cons (l, fun x=>x) d) v))
.


Hint Constructors oival_of : oival_of.

