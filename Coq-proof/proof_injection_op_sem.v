Add Rec LoadPath "." as DEP_AI.

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
Require Import ldna_in_instantiate_facts.
Require Import ldna_in_val_of_with_injection_facts.


Theorem injection_correctness :
  forall (l:label) (vl:val) (c:env) (c':oitenv) (e:expr) (v:val),
    label_does_not_appear_in_expr l c' e
    -> c = oitenv_to_env c'
    -> val_of c e v
    -> val_of_with_injection l vl c' e v.
Proof.
  intros l vl c c' e v H H_c H_semop.
  generalize dependent c'.
  induction H_semop; intros c' H_l H_c.
  
  apply Val_of_with_injection_Num.

  inversion H_l.
  assert(H_assoc_in_c' : exists (uu:oitval),
    assoc_ident_in_oitenv i c' = Ident_in_oitenv uu
    /\ v = oitval_to_val uu).
  apply (oitenv_to_env_assoc c); assumption.
  inversion H_assoc_in_c'.
  rewrite H1 in H5.
  inversion H5.
  inversion H6.
  assert (HH:=instantiate_oitval_when_ldna_in_oitval vl _ _ H4).
  apply Val_of_with_injection_Ident with (uu:=uu). assumption.
  symmetry in H9. rewrite H9 in H7.
  symmetry in H7. rewrite H7 in HH.
  auto.
  apply oitenv_to_env_assoc with (c':=c') in H.
  inversion H.
  inversion H4.
  rewrite H5 in H3.
  inversion H3.
  assumption.

  apply Val_of_with_injection_Lambda with (c':=c).
  inversion H_l.
  f_equal.
  rewrite H_c.
  symmetry.
  apply instantiate_oitenv_when_ldna_in_oitenv; assumption.
  reflexivity.

  apply Val_of_with_injection_Rec with (c':=c).
  inversion H_l.
  f_equal.
  rewrite H_c.
  symmetry.
  apply instantiate_oitenv_when_ldna_in_oitenv; assumption.
  reflexivity.

  inversion H_l.
  clear e3 H0 e0 H l0 H1 c0 H2.
  assert(H_seminj1 := IHH_semop1 _ H3 H_c).
  assert(H_seminj2 := IHH_semop2 _ H4 H_c).
  apply Val_of_with_injection_Apply with (c1:=c1) (e:=e) (x:=x) (v2:=v2);
  try assumption.
  apply IHH_semop3.
(*  apply label_does_not_appear_in_oienv_expr.
  apply Ldna_in_oienv_cons.*)
  assert (H_lcl := ldna_in_val_of_expr _ _ _ H3 _ _ H_seminj1 ).
  inversion H_lcl.
  apply ldna_in_expr_env_cons.
  assumption.
  assert (H_larg := ldna_in_val_of_expr _ _ _ H4 _ _ H_seminj2).
  apply ldna_in_val_to_oitval.
  assumption.
  simpl.
  unfold add_env.
  f_equal.
  apply val_to_oival_to_val.
  apply env_to_oitenv_to_env.

  inversion H_l.
  clear e3 H0 e0 H l0 H1 c0 H2.
  assert(H_seminj1 := IHH_semop1 _ H3 H_c).
  assert(H_seminj2 := IHH_semop2 _ H4 H_c).
  apply Val_of_with_injection_Apply_rec with (f:=f) (c1:=c1) (e:=e) (x:=x) (v2:=v2);
  try assumption.
  apply IHH_semop3.
  assert (H_lcl := ldna_in_val_of_expr _ _ _ H3 _ _ H_seminj1 ).
  inversion H_lcl.
  apply ldna_in_expr_env_cons.
  apply ldna_in_expr_env_cons.
  assumption.
  assert (H_larg := ldna_in_val_of_expr _ _ _ H4 _ _ H_seminj2).
  apply ldna_in_val_to_oitval.
  assumption.
  apply Ldna_in_oitval.
  auto with ldna_oitdeps.
  apply Ldna_in_oival.
  auto with ldna_oideps.
  apply Ldna_in_oival0_Rec_Closure.
  apply ldna_in_env_to_oienv; assumption.
  rewrite oienv_to_oitenv_env_to_oienv; assumption.
  unfold add_env.
  simpl.
  f_equal.
  rewrite <- env_to_oienv_to_env.
  reflexivity.
  f_equal.
  apply val_to_oival_to_val.
  apply env_to_oitenv_to_env.

  inversion H_l.
  clear e3 H4 e0 H0 l0 H1 c0 H2.
  apply Val_of_with_injection_Let_in with (v1:=v1).
  apply (IHH_semop1 _ H3 H_c).
  apply IHH_semop2.
  apply ldna_in_expr_env_cons.
  assumption.
  apply ldna_in_val_to_oitval.
  apply ldna_in_val_of_expr with (c:=c') (e:=e1) (vl:=vl).
  assumption.
  apply (IHH_semop1 _ H3 H_c).
  unfold add_env.
  simpl.
  f_equal.
  apply val_to_oival_to_val.
  assumption.

  inversion H_l.
  clear e3 H0 e0 H l0 H2 c0 H3.
  apply Val_of_with_injection_If_true.
  apply IHH_semop1; assumption.
  apply IHH_semop2; assumption.
  
  inversion H_l.
  clear e3 H0 e0 H l0 H2 c0 H3.
  apply Val_of_with_injection_If_false.
  apply IHH_semop1; assumption.
  apply IHH_semop2; assumption.
  
  inversion H_l.
  clear c0 H3 e0 H0 l0 H2 e2 H5 p0 H1.
  apply Val_of_with_injection_Match with (c_p:=c_p) (v_e:=v_e).
  apply IHH_semop1; assumption.
  assumption.
  apply IHH_semop2.
  apply ldna_in_expr_env_conc.
  assumption.
  apply ldna_in_is_filtered with (v:=v_e) (p:=p).
  apply ldna_in_val_of_expr with (c:=c') (e:=e) (vl:=vl).
  assumption.
  apply IHH_semop1; assumption.
  assumption.
  rewrite H_c.
  apply conc_oitenv_env_to_oitenv.
  apply Val_of_with_injection_Match with (c_p:=c_p) (v_e:=v_e).
  apply IHH_semop1; assumption.
  assumption.
  apply IHH_semop2.
  apply ldna_in_expr_env_conc.
  assumption.
  apply ldna_in_is_filtered with (v:=v_e) (p:=p).
  apply ldna_in_val_of_expr with (c:=c') (e:=e) (vl:=vl).
  assumption.
  apply IHH_semop1; assumption.
  assumption.
  rewrite H_c.
  apply conc_oitenv_env_to_oitenv.
  
  inversion H_l.
  clear l0 H3 c0 H4 e0 H0 e3 H2 e4 H7 p0 H1 x0 H6.
  apply Val_of_with_injection_Match_var with (v_e:=v_e).
  apply IHH_semop1; assumption.
  assumption.
  apply IHH_semop2.
  apply ldna_in_expr_env_cons.
  assumption.
  apply ldna_in_val_to_oitval.
  apply ldna_in_val_of_expr with (c:=c') (e:=e) (vl:=vl).
  assumption.
  apply IHH_semop1; assumption.
  unfold add_env.
  simpl.
  f_equal.
  apply val_to_oival_to_val.
  assumption.

  auto with val_of_with_injection.

  apply Val_of_with_injection_Constr1.
  inversion H_l.
  apply IHH_semop; assumption.

  inversion H_l.
  apply Val_of_with_injection_Couple.
  apply IHH_semop1; assumption.
  apply IHH_semop2; assumption.

  inversion H_l.
  apply Val_of_with_injection_Annot_neq.
  apply IHH_semop; assumption.
  assumption.
Qed.


Theorem injection_completeness :
  forall l vl c c' e v,
    label_does_not_appear_in_expr l c' e
    -> c = oitenv_to_env c'
    -> val_of_with_injection l vl c' e v
    -> val_of c e v.
Admitted. (* injection_completeness *)
