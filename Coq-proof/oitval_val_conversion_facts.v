Add Rec LoadPath "." as DEP_AI.

Require Import language.
Require Import values.
Require Import over_instrumented_values.

Require Import oitval_instantiation.
Require Import oitval_val_conversion.

(*----- COMPOSITION -----*)

Lemma val_to_oival_to_val :
  forall (v:val), v = oival_to_val (val_to_oival v).
Proof.
  apply (val_ind2 (fun v => v = oival_to_val (val_to_oival v)) (fun c => c = oienv_to_env (env_to_oienv c))); simpl; auto; intros; f_equal; auto.
Qed.

Lemma env_to_oienv_to_env :
  forall (c:env), c = oienv_to_env (env_to_oienv c).
Proof.
  apply (env_ind2
    (fun v => v = oitval_to_val (val_to_oitval v))
    (fun c => c = oienv_to_env (env_to_oienv c)));
  simpl; auto; intros; f_equal; auto.
Qed.

Lemma env_to_oitenv_to_env :
  forall (c:env), c = oitenv_to_env (env_to_oitenv c).
Proof.
  apply (env_ind2
    (fun v => v = oitval_to_val (val_to_oitval v))
    (fun c => c = oitenv_to_env (env_to_oitenv c)));
  simpl; auto; intros; f_equal; auto.
  apply env_to_oienv_to_env.
  apply env_to_oienv_to_env.
Qed.

Lemma conc_oitenv_env_to_oitenv :
  forall (c:env) (c':oitenv),
  conc_env c (oitenv_to_env c')
  = oitenv_to_env (conc_oitenv (env_to_oitenv c) c').
Proof.
  induction c.
  auto.
  simpl.
  intro c'.
  f_equal.
  apply val_to_oival_to_val.
  apply IHc.
Qed.

Lemma oienv_to_oitenv_env_to_oienv :
  forall (c:env),
    oienv_to_oitenv (env_to_oienv c) = env_to_oitenv c.
Proof.
  induction c.
  auto.
  simpl.
  f_equal.
  assumption.
Qed.

Lemma oitenv_to_oienv_env_to_oienv :
  forall (c:env),
   oitenv_to_oienv (env_to_oitenv c) = env_to_oienv c.
Proof.
  intros c.
  induction c.
  auto.
  simpl.
  f_equal.
  assumption.
Qed.

(*----- ASSOC IN OITENV -----*)

Lemma assoc_ident_in_oitenv_env_to_oitenv_instantiate_oitenv :
  forall (i:identifier) (c:oitenv) (c':env) (uu:oitval),
  assoc_ident_in_oitenv i c = Ident_in_oitenv uu
  -> forall (l:label) (vl:val),
    Some c' = instantiate_oitenv l vl c
    -> exists (v:val), assoc_ident_in_oitenv i (env_to_oitenv c') = Ident_in_oitenv (val_to_oitval v)
      /\ Some v = instantiate_oitval l vl uu.
Proof.
  induction c.
  intros c' uu H l vl H0.
  inversion H.
  intros c' uu0 H l vl H0.

  assert(H1:exists (v:val), Some v = instantiate_oitval l vl uu0).
  apply instantiable_oitenv with (c:=OITEnv_cons x uu c) (c':=c') (i:=i);
    assumption.

  simpl in H0.
  unfold option_map2 in H0.
  assert(H_SUM : {instantiate_oitval l vl uu = None} + {exists x, instantiate_oitval l vl uu = Some x});
    [induction (instantiate_oitval l vl uu); [right; exists a; reflexivity| left; reflexivity]
      | inversion H_SUM as [H_SUM1|H_SUM2]; [rewrite H_SUM1 in H0; inversion H0|inversion H_SUM2 as [u_inst H_SUM3_oival]; rewrite H_SUM3_oival in H0; inversion H0]];
    clear H_SUM H_SUM2 H3.

  assert(H_SUM : {instantiate_oitenv l vl c = None} + {exists x, instantiate_oitenv l vl c = Some x});
    [induction (instantiate_oitenv l vl c) as [cc|cc]; [right; exists cc; reflexivity| left; reflexivity]
      | inversion H_SUM as [H_SUM1|H_SUM2]; [rewrite H_SUM1 in H0; inversion H0|inversion H_SUM2 as [c_inst H_SUM3_oitenv]; rewrite H_SUM3_oitenv in H0; inversion H0 as [HHHH]]];
    clear H_SUM H_SUM2.

  assert(H_case:beq_identifier i x = true \/ beq_identifier i x = false).
  induction beq_identifier; auto.
  inversion H_case as [HH_case|HH_case]; clear H_case.

  simpl.
  rewrite HH_case.
  repeat f_equal.
  simpl in H; rewrite HH_case in H.
  inversion H.
  rewrite H3 in H_SUM3_oival.
  rewrite H_SUM3_oival in H1.
  inversion H1.
  exists u_inst.
  split.
  reflexivity.
  symmetry; assumption.


  simpl.
  rewrite HH_case.
  apply IHc with (uu:=uu0) (l:=l) (vl:=vl); try assumption.
  simpl in H.
  rewrite HH_case in H.
  assumption.
  symmetry in H_SUM3_oitenv; assumption.
Qed.

Ltac ind_inst_oitenv l vl uu c H :=
  assert(H_SUM : {instantiate_oitval l vl uu = None} + {exists x, instantiate_oitval l vl uu = Some x});
    [induction (instantiate_oitval l vl uu) as [vv|vv]; [right; exists vv; reflexivity| left; reflexivity]
      | inversion H_SUM as [H_SUM1|H_SUM2]; [rewrite H_SUM1 in H; inversion H|inversion H_SUM2 as [u_inst H_SUM3_oival]; clear H_SUM2; rewrite H_SUM3_oival in H; inversion H]];
    clear H_SUM;
  assert(H_SUM : {instantiate_oitenv l vl c = None} + {exists x, instantiate_oitenv l vl c = Some x});
    [induction (instantiate_oitenv l vl c) as [cc|cc]; [right; exists cc; reflexivity| left; reflexivity]
      | inversion H_SUM as [H_SUM1|H_SUM2]; [rewrite H_SUM1 in H; inversion H|inversion H_SUM2 as [c_inst H_SUM3_oitenv]; rewrite H_SUM3_oitenv in H; inversion H as [HHHH]]];
    clear H_SUM.

Lemma assoc_ident_not_in_oitenv_env_to_oitenv_instantiate_oitenv :
  forall (i:identifier) (c:oitenv),
  assoc_ident_in_oitenv i c = Ident_not_in_oitenv
  -> forall (l:label) (vl:val) (c':env),
    Some c' = instantiate_oitenv l vl c
    -> assoc_ident_in_oitenv i (env_to_oitenv c') = Ident_not_in_oitenv.
Proof.
  induction c.
  simpl.
  intros H l vl c' H0.
  inversion H0.
  auto.

  intros H l vl c' HH.

  simpl in HH.
  unfold option_map2 in HH.

  ind_inst_oitenv l vl uu c HH.
  simpl.

  inversion H.
  induction (beq_identifier i x) as [Heq|Hneq].
  inversion H2.

  rewrite H2.
  apply IHc with (l:=l) (vl:=vl).
  assumption.
  symmetry; assumption.
Qed.

Lemma oitenv_to_env_assoc :
  forall (c:env) (c':oitenv) (x:identifier) (v:val),
  c = oitenv_to_env c'
  -> assoc_ident_in_env x c = Ident_in_env v
  -> (exists (uu:oitval),
    assoc_ident_in_oitenv x c' = Ident_in_oitenv uu
    /\ v = oitval_to_val uu).
Proof.
  intros c c'.
  generalize c.
  clear c.
  induction c'; intros.

  simpl in H.
  rewrite H in H0.
  inversion H0.

  assert(beq_identifier x0 x = true \/ beq_identifier x0 x = false).
  induction beq_identifier; auto.
  inversion H1.

  simpl.
  rewrite H2.
  exists uu.
  split.
  reflexivity.
  rewrite H in H0.
  simpl in H0.
  rewrite H2 in H0.
  inversion H0.
  reflexivity.
  
  simpl.
  rewrite H2.
  apply IHc' with (c:=oitenv_to_env c').
  reflexivity.
  rewrite H in H0.
  simpl in H0.
  rewrite H2 in H0.
  assumption.
Qed.


(*----- INSTANTIATION -----*)

Lemma instantiate_oienv_to_oitenv :
  forall (l:label) (vl:val) (c:oienv),
   instantiate_oienv l vl c = instantiate_oitenv l vl (oienv_to_oitenv c).
Proof.
  intros l vl c.
  induction c.
  simpl; reflexivity.

  simpl.
  unfold option_map2.
  induction (instantiate_oival l vl u).
  rewrite IHc.
  reflexivity.
  reflexivity.
Qed.

Lemma val_to_oival_instantiate :
  forall (l:label) (vl:val) (v:val),
  Some v = instantiate_oival l vl (val_to_oival v).
Proof.
  intros l vl.
  apply (val_ind2
    (fun v => Some v = instantiate_oival l vl (val_to_oival v))
    (fun c => Some c = instantiate_oienv l vl (env_to_oienv c))); auto; intros.
  
  simpl. unfold option_map.
  rewrite <- H; auto.

  simpl. unfold option_map2.
  rewrite <- H; rewrite <- H0; auto.

  simpl. unfold option_map.
  rewrite <- H; auto.

  simpl. unfold option_map.
  rewrite <- H; auto.

  simpl. unfold option_map2.
  rewrite <- H; rewrite <- H0; auto.
Qed.

Lemma env_to_oienv_instantiate :
  forall (l:label) (vl:val) (c:env),
  Some c = instantiate_oienv l vl (env_to_oienv c).
Proof.
  intros l vl.
  apply (env_ind2
    (fun v => Some v = instantiate_oival l vl (val_to_oival v))
    (fun c => Some c = instantiate_oienv l vl (env_to_oienv c))); auto; intros.
  
  simpl. unfold option_map.
  rewrite <- H; auto.

  simpl. unfold option_map2.
  rewrite <- H; rewrite <- H0; auto.

  simpl. unfold option_map.
  rewrite <- H; auto.

  simpl. unfold option_map.
  rewrite <- H; auto.

  simpl. unfold option_map2.
  rewrite <- H; rewrite <- H0; auto.
Qed.

Lemma env_to_oitenv_instantiate :
  forall (l:label) (vl:val) (c:env),
  Some c = instantiate_oitenv l vl (env_to_oitenv c).
Proof.
  induction c.
  auto.
  
  simpl.
  unfold option_map2.
  rewrite <- val_to_oival_instantiate.
  rewrite <- IHc.
  reflexivity.
Qed.

(*----- OTHERS -----*)

Lemma commute_conc_env_to_oitenv :
  forall (c c':env),
    conc_oitenv (env_to_oitenv c) (env_to_oitenv c') = env_to_oitenv (conc_env c c').
Proof.
  induction c.
  auto.

  intros c'.
  simpl.
  f_equal.
  auto.
Qed.
