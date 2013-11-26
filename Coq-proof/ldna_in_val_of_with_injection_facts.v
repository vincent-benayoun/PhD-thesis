Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import operational_semantics.

Require Import over_instrumented_values.
Require Import injection_operational_semantics.

Require Import ldna_in.
Require Import ldna_in_facts.
Require Import ldna_in_instantiate_facts.

Lemma ldna_in_is_filtered :
  forall (l:label) (v:val) (p:pattern),
  label_does_not_appear_in_val l v
  -> forall (c:env), is_filtered v p = Filtered_result_Match c
  -> label_does_not_appear_in_env l c.
Proof.
  induction 1; intros.
  inversion H.
  inversion H.
  inversion H.
  induction p; inversion H1.
  induction eq_nat_dec; inversion H1.
  auto with ldna_env.
  inversion H0.
  induction p; inversion H2.
  induction eq_nat_dec; inversion H3.
  auto with ldna_env.
  inversion H1.
  induction p; inversion H3.
  auto with ldna_env.
  inversion H1.
  inversion H1.
Qed.


Lemma ldna_in_val_of_expr :
  forall (l:label) (c:oitenv) (e:expr),
  label_does_not_appear_in_expr l c e
  -> forall (vl v:val),
    val_of_with_injection l vl c e v
    -> label_does_not_appear_in_val l v
    .
Proof.
  intros l c e H_l vl v H_seminj.
  induction H_seminj; inversion H_l; auto with ldna_val.

  rewrite H2 in H.
  inversion H.
  rewrite H7 in H5.
  apply ldna_in_instantiate_oitval with (vl:=vl) (uu:=uu); assumption.

  rewrite H in H4.
  inversion H4.

  rewrite H0.
  apply Ldna_in_val_Closure.
  apply ldna_in_instantiate_oitenv with (vl:=vl) (c:=c); assumption.
  apply ldna_in_expr_env_to_oitenv_instantiate with (vl:=vl) (c:=c); assumption.

  rewrite H0.
  apply Ldna_in_val_Rec_Closure.
  apply ldna_in_instantiate_oitenv with (vl:=vl) (c:=c); assumption.
  apply ldna_in_expr_env_to_oitenv_instantiate with (vl:=vl) (c:=c); assumption.

  apply IHH_seminj3.
  apply ldna_in_expr_env_cons.
  assert(H_val : label_does_not_appear_in_val l (V_Closure x e c1)).
  apply IHH_seminj1; assumption.
  inversion H_val.
  assumption.
  apply ldna_in_val_to_oitval.
  apply IHH_seminj2; assumption.
  
  apply IHH_seminj3.
  assert(H_val : label_does_not_appear_in_val l (V_Rec_Closure f x e c1)).
  apply IHH_seminj1; assumption.
  inversion H_val.
  apply ldna_in_expr_env_cons.
  apply ldna_in_expr_env_cons.
  assumption.
  apply ldna_in_val_to_oitval.
  apply IHH_seminj2; assumption.
  apply ldna_in_val_to_oitval.
  apply IHH_seminj1; assumption.

  apply IHH_seminj2.
  apply ldna_in_expr_env_cons.
  assumption.
  apply ldna_in_val_to_oitval.
  apply IHH_seminj1; assumption.

  apply IHH_seminj2.
  apply ldna_in_expr_env_conc.
  assumption.
  apply ldna_in_is_filtered with (v:=v_e) (p:=p).
  apply IHH_seminj1; assumption.
  assumption.

  apply IHH_seminj2.
  apply ldna_in_expr_env_conc.
  assumption.
  apply ldna_in_is_filtered with (v:=v_e) (p:=p).
  apply IHH_seminj1; assumption.
  assumption.

  apply IHH_seminj2.
  apply ldna_in_expr_env_cons.
  assumption.
  apply ldna_in_val_to_oitval.
  apply IHH_seminj1; assumption.

  absurd(l = l); auto.
Qed.
